//! Bounded concrete AST instantiation, before the unique typed HIR producer.
//! Original ASTs remain intact. No cached verifier result or permission is reused.
use super::*;
use std::collections::BTreeMap;

const MAX_INSTANCES: usize = 128;
const MAX_DEPTH: usize = 48;
// AST shape remains bounded by the existing parser (block 256 / expression 128).
// Do not apply the smaller concrete-type expansion limit to ordinary blocks.
const MAX_WALK_DEPTH: usize = 512;
const MAX_VISITS: usize = 100_000;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstanceKey {
    pub definition: String,
    /// Normalized concrete types and literal consts, never caller region IDs.
    pub arguments: Vec<AstGenericArgument>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TemplateInfo {
    pub definition: String,
    pub source: crate::VirSourceId,
    pub span: ByteSpan,
    pub parameters: Vec<AstGenericParameter>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstanceInfo {
    pub key: InstanceKey,
    pub source: crate::VirSourceId,
    pub definition_span: ByteSpan,
    pub generated_name: String,
    pub uses: Vec<crate::VirSourceSpan>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InstantiationReport {
    pub templates: Vec<TemplateInfo>,
    pub instances: Vec<InstanceInfo>,
}
impl InstantiationReport {
    pub fn uninstantiated(&self) -> impl Iterator<Item = &TemplateInfo> {
        self.templates.iter().filter(|t| {
            !self
                .instances
                .iter()
                .any(|i| i.key.definition == t.definition)
        })
    }
}

#[derive(Clone)]
enum Template {
    Function(AstFunction),
    Struct(AstStruct),
}
impl Template {
    fn parameters(&self) -> &[AstGenericParameter] {
        match self {
            Self::Function(f) => &f.generics,
            Self::Struct(s) => &s.generics,
        }
    }
    fn span(&self) -> ByteSpan {
        match self {
            Self::Function(f) => f.span,
            Self::Struct(s) => s.span,
        }
    }
}
type Environment = BTreeMap<String, AstGenericArgument>;

pub(super) fn run(
    files: &[&AstFile],
    graph: &modules::ModuleGraph,
) -> Result<(Vec<AstFile>, InstantiationReport), FrontendFailure> {
    let mut worker = Instantiator {
        graph,
        templates: BTreeMap::new(),
        ids: BTreeMap::new(),
        semantic_types: BTreeMap::new(),
        arguments: Vec::new(),
        report: InstantiationReport::default(),
        output: files.iter().map(|f| (*f).clone()).collect(),
        visits: 0,
    };
    for (module, ast) in files.iter().enumerate() {
        for function in &ast.functions {
            if !function.generics.is_empty() {
                worker.add_template(module, &function.name, Template::Function(function.clone()));
            }
        }
        for structure in &ast.structs {
            if !structure.generics.is_empty() {
                worker.add_template(module, &structure.name, Template::Struct(structure.clone()));
            }
        }
        for enumeration in &ast.enums {
            if !enumeration.generics.is_empty() {
                return Err(unsupported(
                    module,
                    enumeration.span,
                    "generic enums are deferred; generic functions and structs are supported",
                ));
            }
        }
    }
    let entry_key = graph.declared_key(graph.entry_module, &graph.entry_name);
    if worker.templates.contains_key(&entry_key) {
        return Err(unsupported(
            graph.entry_module,
            files[graph.entry_module].span,
            "entry must be a concrete function; instantiate a generic entry from a concrete wrapper",
        ));
    }
    for ast in &mut worker.output {
        ast.functions.retain(|f| f.generics.is_empty());
        ast.structs.retain(|s| s.generics.is_empty());
    }
    // Roots are all concrete declarations, not just functions reachable at run time.
    for module in 0..files.len() {
        let mut ast = worker.output[module].clone();
        for s in &mut ast.structs {
            for f in &mut s.fields {
                worker.ty(module, &mut f.ty, &Environment::new(), f.span, 0)?;
            }
        }
        for e in &mut ast.enums {
            for v in &mut e.variants {
                match &mut v.payload {
                    AstEnumVariantPayload::Tuple(fs) => {
                        for f in fs {
                            worker.ty(module, &mut f.ty, &Environment::new(), f.span, 0)?;
                        }
                    }
                    AstEnumVariantPayload::Named(fs) => {
                        for f in fs {
                            worker.ty(module, &mut f.ty, &Environment::new(), f.span, 0)?;
                        }
                    }
                    AstEnumVariantPayload::Unit => {}
                }
            }
        }
        for f in &mut ast.functions {
            worker.function(module, f, &Environment::new())?;
        }
        worker.output[module] = ast;
    }
    // Register identities before processing bodies: direct recursion reuses an ID.
    let mut next = 0;
    while next < worker.report.instances.len() {
        let instance = worker.report.instances[next].clone();
        let (module, template) = worker.templates[&instance.key.definition].clone();
        let env: Environment = template
            .parameters()
            .iter()
            .zip(worker.arguments[next].iter())
            .map(|(p, a)| (p.name().to_owned(), a.clone()))
            .collect();
        match template {
            Template::Function(mut f) => {
                f.name = instance.generated_name;
                f.generics.clear();
                worker.function(module, &mut f, &env)?;
                worker.output[module].functions.push(f);
            }
            Template::Struct(mut s) => {
                s.name = instance.generated_name;
                s.generics.clear();
                for f in &mut s.fields {
                    worker.ty(module, &mut f.ty, &env, f.span, 0)?;
                }
                worker.output[module].structs.push(s);
            }
        }
        next += 1;
    }
    Ok((worker.output, worker.report))
}

fn unsupported(module: usize, span: ByteSpan, message: &'static str) -> FrontendFailure {
    let mut failure = FrontendFailure::unsupported(span, message);
    failure.source = Some(crate::VirSourceId::new(module as u32));
    failure
}

struct Instantiator<'a> {
    graph: &'a modules::ModuleGraph,
    templates: BTreeMap<String, (usize, Template)>,
    ids: BTreeMap<InstanceKey, usize>,
    semantic_types: BTreeMap<String, AstType>,
    arguments: Vec<Vec<AstGenericArgument>>,
    report: InstantiationReport,
    output: Vec<AstFile>,
    visits: usize,
}
impl Instantiator<'_> {
    fn add_template(&mut self, module: usize, name: &str, template: Template) {
        let definition = self.graph.declared_key(module, name);
        self.report.templates.push(TemplateInfo {
            definition: definition.clone(),
            source: crate::VirSourceId::new(module as u32),
            span: template.span(),
            parameters: template.parameters().to_vec(),
        });
        self.templates.insert(definition, (module, template));
    }
    fn step(&mut self, module: usize, span: ByteSpan, depth: usize) -> Result<(), FrontendFailure> {
        self.visits += 1;
        if depth > MAX_WALK_DEPTH || (!self.templates.is_empty() && self.visits > MAX_VISITS) {
            return Err(unsupported(
                module,
                span,
                "generic expansion depth/work budget exceeded",
            ));
        }
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    fn request(
        &mut self,
        module: usize,
        name: &str,
        args: &[AstGenericArgument],
        env: &Environment,
        span: ByteSpan,
        depth: usize,
        function: bool,
    ) -> Result<String, FrontendFailure> {
        self.step(module, span, depth)?;
        if depth > MAX_DEPTH {
            return Err(unsupported(
                module,
                span,
                "generic type expansion depth budget exceeded",
            ));
        }
        let definition = self.graph.key(module, name);
        let (owner, template) = self.templates.get(&definition).cloned().ok_or_else(|| {
            modules::at(
                module,
                span,
                "generic target is missing or is not a template",
            )
        })?;
        if matches!(template, Template::Function(_)) != function {
            return Err(modules::at(
                module,
                span,
                "generic target has the wrong declaration kind",
            ));
        }
        let parameters: Vec<_> = template.parameters().iter().collect();
        if parameters.len() != args.len() {
            return Err(modules::at(
                module,
                span,
                "explicit generic argument count does not match binders",
            ));
        }
        let mut arguments = Vec::new();
        for (parameter, argument) in parameters.iter().zip(args) {
            arguments.push(match (parameter, argument) {
                (AstGenericParameter::Type(_), AstGenericArgument::Type(ty)) => {
                    let mut ty = ty.clone();
                    self.ty(module, &mut ty, env, span, depth + 1)?;
                    AstGenericArgument::Type(ty)
                }
                (AstGenericParameter::Const(_), AstGenericArgument::Const(value)) => {
                    AstGenericArgument::Const(AstConstExpression::Literal(
                        self.constant(module, value, env, span)?,
                    ))
                }
                (AstGenericParameter::Const(_), AstGenericArgument::Type(AstType::Named(name))) => {
                    AstGenericArgument::Const(AstConstExpression::Literal(self.constant(
                        module,
                        &AstConstExpression::Name(name.clone()),
                        env,
                        span,
                    )?))
                }
                _ => {
                    return Err(modules::at(
                        module,
                        span,
                        "generic argument kind does not match binder",
                    ));
                }
            });
        }
        let semantic_arguments = arguments
            .iter()
            .map(|arg| match arg {
                AstGenericArgument::Type(ty) => self
                    .semantic_type(module, ty, span, 0)
                    .map(AstGenericArgument::Type),
                other => Ok(other.clone()),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let key = InstanceKey {
            definition,
            arguments: semantic_arguments,
        };
        let index = if let Some(index) = self.ids.get(&key) {
            *index
        } else {
            if self.report.instances.len() >= MAX_INSTANCES {
                return Err(unsupported(
                    module,
                    span,
                    "concrete instance budget exceeded (possibly expanding recursion)",
                ));
            }
            let index = self.report.instances.len();
            let generated_name = format!("{}${index}", name.rsplit("::").next().unwrap());
            self.ids.insert(key.clone(), index);
            self.arguments.push(arguments);
            if !function {
                self.semantic_types.insert(
                    format!("@{}", self.graph.declared_key(owner, &generated_name)),
                    AstType::Applied {
                        name: format!("@{}", key.definition),
                        arguments: key.arguments.clone(),
                    },
                );
            }
            self.report.instances.push(InstanceInfo {
                key,
                source: crate::VirSourceId::new(owner as u32),
                definition_span: template.span(),
                generated_name,
                uses: Vec::new(),
            });
            index
        };
        let instance = &mut self.report.instances[index];
        let usage = crate::VirSourceSpan {
            source: crate::VirSourceId::new(module as u32),
            span,
        };
        if !instance.uses.contains(&usage) {
            instance.uses.push(usage);
        }
        Ok(format!(
            "@{}",
            self.graph.declared_key(owner, &instance.generated_name)
        ))
    }
    fn semantic_type(
        &mut self,
        module: usize,
        ty: &AstType,
        span: ByteSpan,
        depth: usize,
    ) -> Result<AstType, FrontendFailure> {
        self.step(module, span, depth)?;
        if depth > MAX_DEPTH {
            return Err(unsupported(
                module,
                span,
                "generic type expansion depth budget exceeded",
            ));
        }
        Ok(match ty {
            AstType::Named(name) if self.semantic_types.contains_key(name) => {
                let concrete = self.semantic_types[name].clone();
                self.semantic_type(module, &concrete, span, depth + 1)?
            }
            AstType::Applied { name, arguments } => AstType::Applied {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|a| match a {
                        AstGenericArgument::Type(t) => self
                            .semantic_type(module, t, span, depth + 1)
                            .map(AstGenericArgument::Type),
                        other => Ok(other.clone()),
                    })
                    .collect::<Result<_, _>>()?,
            },
            AstType::Array { element, length } => AstType::Array {
                element: Box::new(self.semantic_type(module, element, span, depth + 1)?),
                length: *length,
            },
            AstType::Reference { pointee, mutable } => AstType::Reference {
                pointee: Box::new(self.semantic_type(module, pointee, span, depth + 1)?),
                mutable: *mutable,
            },
            AstType::Slice { element } => AstType::Slice {
                element: Box::new(self.semantic_type(module, element, span, depth + 1)?),
            },
            AstType::Tuple(elements) => AstType::Tuple(
                elements
                    .iter()
                    .map(|t| self.semantic_type(module, t, span, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            other => other.clone(),
        })
    }
    fn reject_shadow(
        &self,
        module: usize,
        name: &str,
        env: &Environment,
        span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if env.contains_key(name) {
            return Err(modules::at(
                module,
                span,
                "local bindings may not shadow generic parameters",
            ));
        }
        Ok(())
    }
    fn constant(
        &mut self,
        module: usize,
        expression: &AstConstExpression,
        env: &Environment,
        span: ByteSpan,
    ) -> Result<u64, FrontendFailure> {
        self.step(module, span, 0)?;
        match expression {
            AstConstExpression::Literal(value) => Ok(*value),
            AstConstExpression::Name(name) => match env.get(name) {
                Some(AstGenericArgument::Const(AstConstExpression::Literal(value))) => Ok(*value),
                _ => Err(modules::at(module, span, "unresolved const binder")),
            },
            AstConstExpression::Add(operands) => {
                let mut value = 0u64;
                for operand in operands {
                    value = value
                        .checked_add(self.constant(module, operand, env, span)?)
                        .ok_or_else(|| modules::at(module, span, "const arithmetic overflow"))?;
                }
                Ok(value)
            }
        }
    }
    fn ty(
        &mut self,
        module: usize,
        ty: &mut AstType,
        env: &Environment,
        span: ByteSpan,
        depth: usize,
    ) -> Result<(), FrontendFailure> {
        self.step(module, span, depth)?;
        match ty {
            AstType::Named(name) => {
                if let Some(argument) = env.get(name) {
                    let AstGenericArgument::Type(concrete) = argument else {
                        return Err(modules::at(module, span, "const binder used as a type"));
                    };
                    *ty = concrete.clone();
                } else {
                    let key = self.graph.key(module, name);
                    if self.templates.contains_key(&key) {
                        return Err(modules::at(
                            module,
                            span,
                            "generic type requires explicit arguments",
                        ));
                    }
                    *name = format!("@{key}");
                }
            }
            AstType::Applied { name, arguments } => {
                *ty = AstType::Named(self.request(
                    module,
                    name,
                    arguments,
                    env,
                    span,
                    depth + 1,
                    false,
                )?)
            }
            AstType::ConstArray { element, length } => {
                self.ty(module, element, env, span, depth + 1)?;
                *ty = AstType::Array {
                    element: element.clone(),
                    length: self.constant(module, length, env, span)?,
                };
            }
            AstType::Tuple(types) => {
                for ty in types {
                    self.ty(module, ty, env, span, depth + 1)?;
                }
            }
            AstType::Reference { pointee, .. }
            | AstType::Array {
                element: pointee, ..
            }
            | AstType::Slice { element: pointee } => {
                self.ty(module, pointee, env, span, depth + 1)?
            }
            _ => {}
        }
        Ok(())
    }
    fn function(
        &mut self,
        module: usize,
        f: &mut AstFunction,
        env: &Environment,
    ) -> Result<(), FrontendFailure> {
        for p in &mut f.parameters {
            self.reject_shadow(module, &p.name, env, p.span)?;
            self.ty(module, &mut p.ty, env, p.span, 0)?;
        }
        self.ty(module, &mut f.return_type, env, f.span, 0)?;
        self.block(module, &mut f.body, env, 0)
    }
    fn block(
        &mut self,
        module: usize,
        block: &mut AstBlock,
        env: &Environment,
        depth: usize,
    ) -> Result<(), FrontendFailure> {
        self.step(module, block.span, depth)?;
        for statement in &mut block.statements {
            match &statement.kind {
                AstStatementKind::Declare { name, .. } | AstStatementKind::Let { name, .. } => {
                    self.reject_shadow(module, name, env, statement.span)?
                }
                AstStatementKind::For { binding, .. } => {
                    self.reject_shadow(module, binding, env, statement.span)?
                }
                AstStatementKind::Match { arms, .. } => {
                    for arm in arms {
                        self.pattern(module, &arm.pattern, env)?;
                    }
                }
                _ => {}
            }
            match &mut statement.kind {
                AstStatementKind::Declare { annotation, .. } => {
                    self.ty(module, annotation, env, statement.span, 0)?
                }
                AstStatementKind::Let {
                    annotation, value, ..
                } => {
                    if let Some(ty) = annotation {
                        self.ty(module, ty, env, statement.span, 0)?;
                    }
                    self.expression(module, value, env, depth + 1)?;
                }
                AstStatementKind::Assign { destination, value } => {
                    self.place(module, destination, env, depth + 1)?;
                    self.expression(module, value, env, depth + 1)?;
                }
                AstStatementKind::Store { value, .. }
                | AstStatementKind::Evaluate { expression: value } => {
                    self.expression(module, value, env, depth + 1)?
                }
                AstStatementKind::Return { value } => {
                    if let Some(value) = value {
                        self.expression(module, value, env, depth + 1)?;
                    }
                }
                AstStatementKind::Block { block } => self.block(module, block, env, depth + 1)?,
                AstStatementKind::If {
                    condition,
                    then_block,
                    else_block,
                } => {
                    self.expression(module, condition, env, depth + 1)?;
                    self.block(module, then_block, env, depth + 1)?;
                    if let Some(block) = else_block {
                        self.block(module, block, env, depth + 1)?;
                    }
                }
                AstStatementKind::While { condition, body } => {
                    self.expression(module, condition, env, depth + 1)?;
                    self.block(module, body, env, depth + 1)?;
                }
                AstStatementKind::For {
                    start, end, body, ..
                } => {
                    self.expression(module, start, env, depth + 1)?;
                    self.expression(module, end, env, depth + 1)?;
                    self.block(module, body, env, depth + 1)?;
                }
                AstStatementKind::Match { scrutinee, arms } => {
                    self.expression(module, scrutinee, env, depth + 1)?;
                    for arm in arms {
                        if let Some(guard) = &mut arm.guard {
                            self.expression(module, guard, env, depth + 1)?;
                        }
                        self.block(module, &mut arm.body, env, depth + 1)?;
                    }
                }
                AstStatementKind::Free { .. }
                | AstStatementKind::Break
                | AstStatementKind::Continue => {}
            }
        }
        Ok(())
    }
    fn place(
        &mut self,
        module: usize,
        place: &mut AstPlace,
        env: &Environment,
        depth: usize,
    ) -> Result<(), FrontendFailure> {
        for projection in &mut place.projections {
            match projection {
                AstPlaceProjection::Index { index, .. } => {
                    self.expression(module, index, env, depth + 1)?
                }
                AstPlaceProjection::Slice { start, end, .. } => {
                    if let Some(value) = start {
                        self.expression(module, value, env, depth + 1)?;
                    }
                    if let Some(value) = end {
                        self.expression(module, value, env, depth + 1)?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
    fn pattern(
        &self,
        module: usize,
        pattern: &AstPattern,
        env: &Environment,
    ) -> Result<(), FrontendFailure> {
        match &pattern.kind {
            AstPatternKind::Binding(name) => self.reject_shadow(module, name, env, pattern.span)?,
            AstPatternKind::Variant { payload, .. } => match payload {
                AstVariantPatternPayload::Tuple(items) => {
                    for item in items {
                        self.pattern(module, item, env)?;
                    }
                }
                AstVariantPatternPayload::Named(items) => {
                    for item in items {
                        self.pattern(module, &item.pattern, env)?;
                    }
                }
                AstVariantPatternPayload::Unit => {}
            },
            _ => {}
        }
        Ok(())
    }
    fn expression(
        &mut self,
        module: usize,
        expression: &mut AstExpression,
        env: &Environment,
        depth: usize,
    ) -> Result<(), FrontendFailure> {
        self.step(module, expression.span, depth)?;
        let span = expression.span;
        match &mut expression.kind {
            AstExpressionKind::GenericCall {
                callee,
                types,
                arguments,
            } => {
                let target = self.request(module, callee, types, env, span, 0, true)?;
                for value in arguments.iter_mut() {
                    self.expression(module, value, env, depth + 1)?;
                }
                expression.kind = AstExpressionKind::Call {
                    callee: target,
                    arguments: std::mem::take(arguments),
                };
            }
            AstExpressionKind::GenericStruct {
                name,
                types,
                fields,
            } => {
                let name = self.request(module, name, types, env, span, 0, false)?;
                for field in fields.iter_mut() {
                    self.expression(module, &mut field.value, env, depth + 1)?;
                }
                expression.kind = AstExpressionKind::Struct {
                    name,
                    fields: std::mem::take(fields),
                };
            }
            AstExpressionKind::ConstRepeat { value, length } => {
                self.expression(module, value, env, depth + 1)?;
                expression.kind = AstExpressionKind::ArrayRepeat {
                    value: value.clone(),
                    length: self.constant(module, length, env, span)?,
                };
            }
            AstExpressionKind::Name(name) => {
                if let Some(AstGenericArgument::Const(AstConstExpression::Literal(value))) =
                    env.get(name)
                {
                    expression.kind = AstExpressionKind::Integer {
                        value: *value,
                        explicit_u64: false,
                        explicit_usize: true,
                    };
                }
            }
            AstExpressionKind::Call { callee, arguments } => {
                if self.templates.contains_key(&self.graph.key(module, callee)) {
                    return Err(modules::at(
                        module,
                        span,
                        "generic function requires explicit type/const arguments",
                    ));
                }
                for value in arguments {
                    self.expression(module, value, env, depth + 1)?;
                }
            }
            AstExpressionKind::Array(values)
            | AstExpressionKind::Tuple(values)
            | AstExpressionKind::Add(values) => {
                for value in values {
                    self.expression(module, value, env, depth + 1)?;
                }
            }
            AstExpressionKind::Struct { fields, .. } => {
                for field in fields {
                    self.expression(module, &mut field.value, env, depth + 1)?;
                }
            }
            AstExpressionKind::EnumVariant { payload, .. } => match payload {
                AstVariantInitializer::Unit => {}
                AstVariantInitializer::Tuple(values) => {
                    for value in values {
                        self.expression(module, value, env, depth + 1)?;
                    }
                }
                AstVariantInitializer::Named(fields) => {
                    for field in fields {
                        self.expression(module, &mut field.value, env, depth + 1)?;
                    }
                }
            },
            AstExpressionKind::ArrayRepeat { value, .. } => {
                self.expression(module, value, env, depth + 1)?
            }
            AstExpressionKind::Compare { left, right, .. } => {
                self.expression(module, left, env, depth + 1)?;
                self.expression(module, right, env, depth + 1)?;
            }
            AstExpressionKind::Allocate { element_type, .. } => {
                self.ty(module, element_type, env, span, 0)?
            }
            AstExpressionKind::Place(place)
            | AstExpressionKind::Borrow { place, .. }
            | AstExpressionKind::RawAddress { place, .. } => {
                self.place(module, place, env, depth + 1)?
            }
            AstExpressionKind::Integer { .. }
            | AstExpressionKind::Bool(_)
            | AstExpressionKind::Unit
            | AstExpressionKind::Load { .. } => {}
        }
        Ok(())
    }
}
