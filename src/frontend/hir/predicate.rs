//! Typed, erased resource effects. They name locals, never runtime expressions.
use super::*;
mod logic;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirPredicateActionKind {
    Fold {
        holder: u32,
        locals: Vec<HirLocalId>,
    },
    Unfold {
        holder: u32,
        locals: Vec<HirLocalId>,
    },
    Move {
        source: u32,
        destination: u32,
    },
    Finish {
        holder: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirPredicateAction {
    pub id: u32,
    pub predicate: HirPredicateId,
    pub function: HirFunctionId,
    pub scope: HirScopeId,
    pub kind: HirPredicateActionKind,
    pub witnesses: crate::predicate_logic::WitnessArguments<HirTypeId, HirLocalId>,
    pub span: ByteSpan,
}

pub(super) fn validate_predicate_actions(
    program: &HirProgram,
) -> Result<(), HirProgramValidationError> {
    use super::program::require;
    for predicate in program.predicates() {
        if let Some(body) = &predicate.representation {
            let valid = predicate.body.is_none()
                && predicate.binders.is_empty()
                && valid_representation(program, body, predicate.module)
                && body.bounds.iter().all(|bound| {
                    body.resources
                        .get(bound.resource as usize)
                        .and_then(|r| program.type_definition(r.pointee))
                        .is_some_and(|ty| ty.opaque.is_none_or(|module| module == predicate.module))
                });
            require(
                valid,
                "predicate",
                predicate.id.index(),
                "invalid finite predicate representation",
            )?;
        }
    }
    let mut interface_bindings = BTreeSet::new();
    require(
        program.specs().predicate_interfaces.len() <= 256,
        "predicate interface",
        0,
        "interface budget exceeded",
    )?;
    for (index, interface) in program.specs().predicate_interfaces.iter().enumerate() {
        let f = program.function_by_id(interface.function);
        let representation = program
            .predicate(interface.predicate)
            .and_then(|p| p.representation.as_ref());
        let valid = f.zip(representation).is_some_and(|(f, r)| {
            r.has_supported_interface_witnesses()
                && interface.arguments.values.is_empty()
                && interface.arguments.validate_arguments(&r.logic, &mut crate::predicate_logic::LogicBudget::default()).is_ok()
                && interface.arguments.inputs.iter().all(|(ty, input)| {
                    let actual = match input {
                        crate::predicate_logic::WitnessInput::Scalar(local) => f.signature.parameters.get(local.get() as usize).copied(),
                        crate::predicate_logic::WitnessInput::Result(index) if interface.ensures && index.get() == 0 => Some(f.signature.return_type),
                        crate::predicate_logic::WitnessInput::ResultField { base, offset, access }
                            if interface.ensures && base.get() == 0 && matches!(program.type_kind(f.signature.return_type), Some(HirTypeKind::Struct { .. } | HirTypeKind::Array { .. })) && predicate_scalar_type_at_offset(program, f.signature.return_type, *offset, f.module) == Some(*access) => Some(*access),
                        crate::predicate_logic::WitnessInput::Memory { base, offset, access, time }
                            if interface.ensures || *time == crate::predicate_logic::ObservationTime::Current => {
                            f.signature.parameters.get(base.get() as usize).and_then(|root| {
                                (predicate_input_field_type(program, *root, *offset, f.module) == Some(*access)).then_some(*access)
                            })
                        }
                        _ => None,
                    };
                    matches!((ty, actual.and_then(|ty| program.type_kind(ty))),
                        (crate::predicate_logic::LogicType::U64, Some(HirTypeKind::Integer(HirIntegerType::U64)))
                        | (crate::predicate_logic::LogicType::Usize, Some(HirTypeKind::Integer(HirIntegerType::Usize)))
                        | (crate::predicate_logic::LogicType::Bool, Some(HirTypeKind::Bool)))
                })
                && interface.parameters.len() == r.resources.len()
                && interface.fields.len() == r.resources.len()
                && f.span.start() <= interface.span.start() && interface.span.end() <= f.span.end()
                && (!interface.in_place || interface.ensures)
                && (!interface.ensures || interface.in_place || interface.parameters.iter().all(|index| *index == 0))
                && interface.parameters.iter().zip(&interface.fields).zip(&r.resources).all(|((index, path), resource)| {
                    let root = if interface.ensures && !interface.in_place { Some(f.signature.return_type) } else { f.signature.parameters.get(*index as usize).copied() };
                    let ty = root.and_then(|root| path.iter().try_fold(root, |ty, field| {
                        let def = program.type_definition(ty)?;
                        if def.opaque.is_some_and(|m| m != f.module) { return None; }
                        let HirTypeKind::Struct { fields } = &def.kind else { return None; };
                        fields.contains(field).then_some(())?;
                        Some(program.field(*field)?.ty)
                    }));
                    path.len() <= 16 && (path.is_empty() || (!interface.in_place && matches!(ty.and_then(|t| program.type_kind(t)),Some(HirTypeKind::Own { .. }))))
                        && interface_bindings.insert((interface.function, interface.ensures, interface.in_place, *index, path.clone()))
                        && (!interface.in_place || (
                            matches!(ty.and_then(|ty| program.type_kind(ty)), Some(HirTypeKind::Reference { mutability: HirMutability::Mutable, .. }))
                            && f.signature.borrow_result.is_none_or(|r| r.parameter != *index || r.projection != crate::BorrowProjection::Whole)
                            && f.signature.borrow_result_alternatives.iter().all(|a| a.relation.parameter != *index)
                        ))
                        && matches!(ty.and_then(|ty| program.type_kind(ty)), Some(HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, mutability: HirMutability::Mutable, .. }) if *pointee == resource.pointee)
                })
        });
        require(
            valid,
            "predicate interface",
            index,
            "invalid or overlapping predicate interface",
        )?;
    }
    let mut seen = BTreeMap::<u32, Vec<(HirFunctionId, ByteSpan)>>::new();
    struct Visit<'a> {
        function: HirFunctionId,
        seen: &'a mut BTreeMap<u32, Vec<(HirFunctionId, ByteSpan)>>,
    }
    impl<'h> visit::HirVisitor<'h> for Visit<'_> {
        fn visit_statement(&mut self, statement: &'h HirStatement) {
            if let HirStatementKind::Predicate { action, .. } = statement.kind {
                self.seen
                    .entry(action)
                    .or_default()
                    .push((self.function, statement.span));
            }
            visit::walk_statement(self, statement);
        }
    }
    use visit::HirVisitor;
    for function in program.functions() {
        if let Some(body) = function.body() {
            Visit {
                function: function.id,
                seen: &mut seen,
            }
            .visit_block(&body.root);
        }
    }
    require(
        program.specs().predicate_actions.len() <= 4096,
        "predicate action",
        0,
        "predicate effect budget exceeded",
    )?;
    for (index, action) in program.specs().predicate_actions.iter().enumerate() {
        let function = program.function_by_id(action.function);
        let declaration = program.predicate(action.predicate);
        let body = declaration.and_then(|p| p.representation.as_ref());
        let locals = function.and_then(|f| f.body()).map(|b| &b.locals);
        let valid = action.id as usize == index
            && valid_action_witnesses(program, action)
            && seen.remove(&action.id) == Some(vec![(action.function, action.span)])
            && function.zip(declaration).is_some_and(|(f,p)| f.module == p.module)
            && body.is_some()
            && match &action.kind {
                HirPredicateActionKind::Fold { locals: bindings, .. } | HirPredicateActionKind::Unfold { locals: bindings, .. } => {
                    body.zip(locals).is_some_and(|(body, locals)| {
                        bindings.len() == body.resources.len() && bindings.iter().collect::<BTreeSet<_>>().len() == bindings.len() && bindings.iter().zip(&body.resources).all(|(id, resource)| {
                            locals.get(id.index()).and_then(|l| program.type_definition(l.ty)).is_some_and(|t| matches!(t.kind, HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, mutability: HirMutability::Mutable, .. } if pointee == resource.pointee))
                        })
                    })
                }
                HirPredicateActionKind::Move { source, destination } => source != destination,
                HirPredicateActionKind::Finish { .. } => true,
            };
        require(
            valid,
            "predicate action",
            index,
            "invalid, missing, foreign, duplicate or mistyped predicate effect",
        )?;
    }
    require(
        seen.is_empty(),
        "predicate action",
        0,
        "statement refers to a missing predicate effect",
    )
}

impl Elaborator {
    pub(super) fn declare_predicates(
        &mut self,
        files: &[&super::super::AstFile],
    ) -> Result<(), FrontendFailure> {
        use super::super::{AstExpressionKind as E, AstLogicalExpressionKind as L};
        for (module, file) in files.iter().enumerate() {
            self.current_module = module;
            for declaration in &file.predicates {
                let bad = || {
                    FrontendFailure::unsupported(
                        declaration.span,
                        "predicate bodies require finite owned storage, validated initialization ranges and 64-bit word bounds",
                    )
                };
                if declaration.parameters.is_empty() || declaration.parameters.len() > 64 {
                    return Err(bad());
                }
                let mut resources = Vec::new();
                let mut sizes = Vec::new();
                let mut logic = crate::predicate_logic::PredicateLogic::default();
                let mut parameter_names = BTreeSet::new();
                for (position, parameter) in declaration.parameters.iter().enumerate() {
                    if !parameter_names.insert(&parameter.name) {
                        return Err(bad());
                    }
                    let ty = self.resolve_ast_type(&parameter.ty, parameter.span)?;
                    let Some(HirTypeKind::RawPointer { pointee, .. }) =
                        self.type_definition(ty).map(|t| &t.kind).cloned()
                    else {
                        let ty = self.predicate_logic_type(ty).ok_or_else(bad)?;
                        if logic.parameters.len() >= 32 {
                            return Err(bad());
                        }
                        logic
                            .parameters
                            .push(crate::predicate_logic::LogicParameter {
                                position,
                                name: parameter.name.clone(),
                                ty,
                            });
                        continue;
                    };
                    if resources.len() >= 32 {
                        return Err(bad());
                    }
                    let layout = self.ensure_layout(pointee, &mut Vec::new(), parameter.span)?;
                    let size = self.layouts[layout.index()].size_bytes;
                    if size == 0
                        || size > 4096
                        || resources
                            .iter()
                            .any(|r: &crate::PredicateStorage<HirTypeId>| r.name == parameter.name)
                    {
                        return Err(bad());
                    }
                    resources.push(crate::PredicateStorage {
                        name: parameter.name.clone(),
                        pointee,
                        initialized: Vec::new(),
                    });
                    sizes.push(size);
                }
                if resources.is_empty() {
                    return Err(bad());
                }
                let mut witnesses = Vec::new();
                let mut witness_names = BTreeSet::new();
                let mut aliases = BTreeMap::new();
                for witness in &declaration.witnesses {
                    if witness.name.is_empty()
                        || parameter_names.contains(&witness.name)
                        || !witness_names.insert(witness.name.clone())
                        || logic.existentials.len() >= 32
                    {
                        return Err(bad());
                    }
                    let ty = self.resolve_ast_type(&witness.ty, witness.span)?;
                    let logical_type = self.predicate_logic_type(ty).ok_or_else(bad)?;
                    let default = witness
                        .value
                        .as_ref()
                        .map(|value| {
                            self.predicate_logic_expression(
                                value,
                                &resources,
                                &logic,
                                Some(logical_type),
                            )
                        })
                        .transpose()?;
                    if let Some(default) = &default {
                        for node in &default.nodes {
                            if let crate::predicate_logic::LogicNodeKind::Observe {
                                resource,
                                offset,
                                ..
                            } = node.kind
                            {
                                let width = if node.ty == crate::predicate_logic::LogicType::Bool {
                                    1
                                } else {
                                    8
                                };
                                let end = offset.checked_add(width).ok_or_else(bad)?;
                                if end > sizes[resource as usize] {
                                    return Err(bad());
                                }
                                resources[resource as usize].initialized.push((offset, end));
                            }
                        }
                    }
                    // Keep the field shorthand descriptor for prefix planning;
                    // the logical binder itself is evaluated and stored by fold.
                    if let Some(super::super::AstLogicalExpression {
                        kind: L::Value(value),
                        ..
                    }) = &witness.value
                        && let Ok((index, actual, offset)) =
                            self.predicate_storage_place(value, &resources)
                        && ty == actual
                        && matches!(
                            logical_type,
                            crate::predicate_logic::LogicType::U64
                                | crate::predicate_logic::LogicType::Usize
                                | crate::predicate_logic::LogicType::Bool
                        )
                    {
                        witnesses.push(crate::PredicateWitness {
                            name: witness.name.clone(),
                            ty,
                            resource: index as u32,
                            offset,
                        });
                        aliases.insert(witness.name.clone(), value.clone());
                    }
                    logic
                        .existentials
                        .push(crate::predicate_logic::Existential {
                            name: witness.name.clone(),
                            ty: logical_type,
                            default,
                        });
                }
                let mut owned = BTreeSet::new();
                let mut bounds = Vec::new();
                let mut prefixes = Vec::new();
                for source_clause in &declaration.clauses {
                    let mut clause = source_clause.clone();
                    substitute_predicate_witnesses(&mut clause, &aliases);
                    match &clause.kind {
                        L::Value(super::super::AstExpression {
                            kind: E::Call { callee, arguments },
                            ..
                        }) if callee == "owns" && arguments.len() == 1 => {
                            let name = predicate_name(&arguments[0]).ok_or_else(bad)?;
                            let index = resources
                                .iter()
                                .position(|r| r.name == name)
                                .ok_or_else(bad)?;
                            if !owned.insert(index) {
                                return Err(bad());
                            }
                        }
                        L::InitializedRange {
                            pointer,
                            start,
                            end,
                        } => {
                            let (index, selected, offset) =
                                self.predicate_storage_place(pointer, &resources)?;
                            if predicate_number(end).is_none() {
                                let Some(HirTypeKind::Array { element, length }) =
                                    self.type_definition(selected).map(|t| &t.kind)
                                else {
                                    return Err(bad());
                                };
                                let (element, length) = (*element, *length);
                                if predicate_number(start) != Some(0) {
                                    return Err(bad());
                                }
                                let stored = if let L::Value(count) = &end.kind {
                                    self.predicate_storage_place(count, &resources).ok()
                                } else {
                                    None
                                };
                                let count =
                                    if let Some((count_resource, count_type, offset)) = stored {
                                        if count_resource != index
                                            || !matches!(
                                                self.type_definition(count_type).map(|t| &t.kind),
                                                Some(HirTypeKind::Integer(
                                                    HirIntegerType::U64 | HirIntegerType::Usize
                                                ))
                                            )
                                        {
                                            return Err(bad());
                                        }
                                        crate::PredicatePrefixCount::Stored { offset }
                                    } else {
                                        // Use the original binder expression, not the
                                        // field shorthand substituted for legacy bounds.
                                        let L::InitializedRange { end, .. } = &source_clause.kind
                                        else {
                                            unreachable!()
                                        };
                                        let expression = self.predicate_logic_expression(
                                            end, &resources, &logic, None,
                                        )?;
                                        if !matches!(
                                            expression.nodes[expression.root as usize].ty,
                                            crate::predicate_logic::LogicType::U64
                                                | crate::predicate_logic::LogicType::Usize
                                        ) {
                                            return Err(bad());
                                        }
                                        crate::PredicatePrefixCount::Logical(expression)
                                    };
                                prefixes.push(crate::PredicateInitializedPrefix {
                                    resource: index as u32,
                                    array_offset: offset,
                                    element,
                                    length,
                                    stride: self
                                        .resolved_layout(element)
                                        .ok_or_else(bad)?
                                        .size_bytes,
                                    count,
                                });
                                continue;
                            }
                            let layout = self.resolved_layout(selected).ok_or_else(bad)?;
                            let size = layout.size_bytes;
                            let element = match self.type_definition(selected).map(|t| &t.kind) {
                                Some(HirTypeKind::Array { element, .. }) => *element,
                                _ => selected,
                            };
                            let stride = self.resolved_layout(element).ok_or_else(bad)?.size_bytes;
                            let start = predicate_number(start)
                                .and_then(|n| n.checked_mul(stride))
                                .ok_or_else(bad)?;
                            let end = predicate_number(end)
                                .and_then(|n| n.checked_mul(stride))
                                .ok_or_else(bad)?;
                            // Bounds are local to the selected subobject. Checking
                            // only the allocation extent would let a field claim
                            // initialization of its uninitialized neighbours.
                            if start >= end || end > size {
                                return Err(bad());
                            }
                            resources[index].initialized.push((
                                offset.checked_add(start).ok_or_else(bad)?,
                                offset.checked_add(end).ok_or_else(bad)?,
                            ));
                        }
                        _ => {
                            let expression = self.predicate_logic_expression(
                                source_clause,
                                &resources,
                                &logic,
                                Some(crate::predicate_logic::LogicType::Bool),
                            )?;
                            // The legacy interval projection remains useful at
                            // function entry; arbitrary formulas stay in logic.
                            if let L::Binary {
                                operator,
                                left,
                                right,
                            } = &clause.kind
                                && let L::Value(value) = &left.kind
                                && let Ok((index, word, offset)) =
                                    self.predicate_storage_place(value, &resources)
                                && matches!(
                                    self.type_definition(word).map(|t| &t.kind),
                                    Some(HirTypeKind::Integer(
                                        HirIntegerType::U64 | HirIntegerType::Usize
                                    ))
                                )
                                && let Some(number) = predicate_number(right)
                            {
                                let interval = match operator {
                                    crate::Punctuation::LessEqual => Some((0, number)),
                                    crate::Punctuation::GreaterEqual => Some((number, u64::MAX)),
                                    crate::Punctuation::EqualEqual => Some((number, number)),
                                    _ => None,
                                };
                                if let Some((lower, upper)) = interval {
                                    bounds.push(crate::PredicateWordBound {
                                        resource: index as u32,
                                        offset,
                                        lower,
                                        upper,
                                    });
                                }
                            }
                            logic.constraints.push(expression);
                        }
                    }
                }
                for resource in &mut resources {
                    resource.initialized.sort_unstable();
                    resource.initialized.dedup();
                }
                if owned.len() != resources.len() || bounds.len() > 32 {
                    return Err(bad());
                }
                let id = HirPredicateId::new(self.predicates.len() as u32);
                self.predicate_names
                    .insert(self.declaration_key(&declaration.name), id);
                self.predicates.push(HirPredicate {
                    id,
                    module: HirModuleId::new(module as u32),
                    name: self.declaration_key(&declaration.name),
                    binders: Vec::new(),
                    body: None,
                    representation: Some(crate::PredicateRepresentation {
                        logic,
                        resources,
                        bounds,
                        prefixes,
                        witnesses,
                    }),
                    span: declaration.span,
                });
            }
        }
        Ok(())
    }

    /// Resolve a static subobject to allocation-relative bytes without reading
    /// memory or conferring access to an opaque module's representation.
    fn predicate_storage_place(
        &mut self,
        value: &super::super::AstExpression,
        resources: &[crate::PredicateStorage<HirTypeId>],
    ) -> Result<(usize, HirTypeId, u64), FrontendFailure> {
        use super::super::{AstExpressionKind as E, AstPlaceProjection as P};
        let bad = || {
            FrontendFailure::unsupported(
                value.span,
                "predicate initialization requires a fixed field or constant array element",
            )
        };
        let (name, projections) = match &value.kind {
            E::Name(name) => (name.as_str(), &[][..]),
            E::Place(place) => (place.base.as_str(), place.projections.as_slice()),
            _ => return Err(bad()),
        };
        let index = resources
            .iter()
            .position(|r| r.name == name)
            .ok_or_else(bad)?;
        if projections.len() >= 64 {
            return Err(bad());
        }
        let mut ty = resources[index].pointee;
        let mut offset = 0u64;
        for projection in projections {
            let (next, delta) = match projection {
                P::Field { name, span } => {
                    self.require_representation_access(ty, *span)?;
                    let Some(HirTypeKind::Struct { fields }) =
                        self.type_definition(ty).map(|t| &t.kind)
                    else {
                        return Err(bad());
                    };
                    let field = fields
                        .iter()
                        .filter_map(|id| self.fields.get(id.index()))
                        .find(|f| f.name == *name)
                        .ok_or_else(bad)?;
                    let delta = self
                        .resolved_layout(ty)
                        .ok_or_else(bad)?
                        .fields
                        .iter()
                        .find(|f| f.field == field.id)
                        .ok_or_else(bad)?
                        .offset_bytes;
                    (field.ty, delta)
                }
                P::Index { index, .. } => {
                    let E::Integer { value, .. } = index.kind else {
                        return Err(bad());
                    };
                    let Some(HirTypeKind::Array { element, length }) =
                        self.type_definition(ty).map(|t| &t.kind)
                    else {
                        return Err(bad());
                    };
                    if value >= *length {
                        return Err(bad());
                    }
                    (
                        *element,
                        value
                            .checked_mul(self.resolved_layout(*element).ok_or_else(bad)?.size_bytes)
                            .ok_or_else(bad)?,
                    )
                }
                P::TupleElement { index, .. } => {
                    let Some(HirTypeKind::Tuple(elements)) =
                        self.type_definition(ty).map(|t| &t.kind)
                    else {
                        return Err(bad());
                    };
                    let (selected, delta) =
                        predicate_tuple_fields(elements, |ty| self.resolved_layout(ty))
                            .and_then(|fields| fields.get(*index as usize).copied())
                            .ok_or_else(bad)?;
                    (selected, delta)
                }
                _ => return Err(bad()),
            };
            offset = offset.checked_add(delta).ok_or_else(bad)?;
            ty = next;
        }
        Ok((index, ty, offset))
    }

    pub(super) fn elaborate_predicate_action(
        &mut self,
        operation: super::super::AstPredicateOperation,
        name: &str,
        arguments: &[super::super::AstLogicalExpression],
        explicit: &[(String, super::super::AstLogicalExpression)],
        opened: Option<&[String]>,
        span: ByteSpan,
    ) -> Result<HirStatementKind, FrontendFailure> {
        use super::super::AstPredicateOperation as Op;
        let predicate = *self
            .predicate_names
            .get(&self.key(name))
            .ok_or_else(|| FrontendFailure::elaboration(span, "unknown predicate"))?;
        let declaration = &self.predicates[predicate.index()];
        if declaration.module.get() as usize != self.current_module {
            return Err(FrontendFailure::elaboration(
                span,
                "predicate representation is private to its defining module",
            ));
        }
        let representation = declaration.representation.as_ref().unwrap().clone();
        let resources = &representation.resources;
        if arguments.len() != resources.len() + representation.logic.parameters.len() {
            return Err(FrontendFailure::elaboration(
                span,
                "predicate binding arity mismatch",
            ));
        }
        let mut names = Vec::new();
        let mut actuals = Vec::new();
        for (position, expression) in arguments.iter().enumerate() {
            if let Some(parameter) = representation
                .logic
                .parameters
                .iter()
                .find(|p| p.position == position)
            {
                actuals.push((parameter.ty, expression.clone()));
            } else {
                let super::super::AstLogicalExpressionKind::Value(value) = &expression.kind else {
                    return Err(FrontendFailure::elaboration(
                        span,
                        "resource argument must name an owner or mutable reference local",
                    ));
                };
                names.push(
                    predicate_name(value)
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(span, "resource argument must be a local")
                        })?
                        .to_owned(),
                );
            }
        }
        let mut locals = Vec::new();
        for (name, resource) in names.iter().zip(resources) {
            let binding = self.lookup(name, span)?;
            if !matches!(self.type_definition(binding.value.ty).map(|t| &t.kind), Some(HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, mutability: HirMutability::Mutable, .. }) if *pointee == resource.pointee)
            {
                return Err(FrontendFailure::elaboration(
                    span,
                    "predicate fold/unfold requires a matching owner or mutable reference; raw addresses carry no predicate authority",
                ));
            }
            locals.push(binding.local);
        }
        let witnesses = self.predicate_action_witnesses(
            &representation,
            &names,
            &actuals,
            explicit,
            span,
            None,
        )?;
        if operation == Op::Fold
            && representation
                .logic
                .existentials
                .iter()
                .enumerate()
                .any(|(i, w)| {
                    w.default.is_none() && !witnesses.values.iter().any(|(id, _)| *id == i as u32)
                })
        {
            return Err(FrontendFailure::elaboration(
                span,
                "fold is missing an existential witness",
            ));
        }
        let holder = locals[0].get();
        let id = self.specs.predicate_actions.len() as u32;
        if let Some(opened) = opened {
            if operation != Op::Unfold || opened.len() != representation.logic.existentials.len() {
                return Err(FrontendFailure::elaboration(
                    span,
                    "opened binder arity mismatch",
                ));
            }
            let mut seen = BTreeSet::new();
            for name in opened {
                if !seen.insert(name)
                    || self.scopes.iter().any(|s| {
                        s.bindings.contains_key(name) || s.ghost_bindings.contains_key(name)
                    })
                {
                    return Err(FrontendFailure::elaboration(
                        span,
                        "opened predicate names cannot shadow existing bindings",
                    ));
                }
            }
            for (index, (name, binder)) in opened
                .iter()
                .zip(&representation.logic.existentials)
                .enumerate()
            {
                self.scopes.last_mut().unwrap().ghost_bindings.insert(
                    name.clone(),
                    (
                        binder.ty,
                        crate::predicate_logic::WitnessInput::Opened {
                            action: id,
                            holder,
                            binder: index as u32,
                        },
                    ),
                );
            }
        }
        let kind = match operation {
            Op::Fold => HirPredicateActionKind::Fold {
                holder,
                locals: locals.clone(),
            },
            Op::Unfold => HirPredicateActionKind::Unfold {
                holder,
                locals: locals.clone(),
            },
            Op::Finish => {
                locals.clear();
                HirPredicateActionKind::Finish { holder }
            }
        };
        for (_, input) in &witnesses.inputs {
            if let Some(local) = input.runtime_value()
                && !locals.contains(local)
            {
                locals.push(*local);
            }
        }
        self.specs.predicate_actions.push(HirPredicateAction {
            id,
            predicate,
            function: self.current_function.ok_or_else(|| {
                FrontendFailure::elaboration(span, "predicate effect outside function")
            })?,
            scope: self.scopes.last().unwrap().id,
            kind,
            witnesses,
            span,
        });
        Ok(HirStatementKind::Predicate { action: id, locals })
    }
}

fn predicate_name(expression: &super::super::AstExpression) -> Option<&str> {
    match &expression.kind {
        super::super::AstExpressionKind::Name(name) => Some(name),
        super::super::AstExpressionKind::Place(place) if place.projections.is_empty() => {
            Some(&place.base)
        }
        _ => None,
    }
}
fn predicate_number(expression: &super::super::AstLogicalExpression) -> Option<u64> {
    match &expression.kind {
        super::super::AstLogicalExpressionKind::Value(super::super::AstExpression {
            kind: super::super::AstExpressionKind::Integer { value, .. },
            ..
        }) => Some(*value),
        _ => None,
    }
}

fn plain_representation(program: &HirProgram, root: HirTypeId) -> bool {
    let mut work = vec![(root, 0usize, false)];
    let mut steps = 0usize;
    let mut resources = 0usize;
    while let Some((ty, depth, behind_pointer)) = work.pop() {
        steps += 1;
        if depth > 16 || steps > 4096 {
            return false;
        }
        match program.type_kind(ty) {
            Some(HirTypeKind::Unit | HirTypeKind::Bool | HirTypeKind::Integer(_)) => {}
            Some(HirTypeKind::RawPointer { .. }) => {
                if !behind_pointer {
                    resources += 1;
                }
            }
            Some(HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. })
                if !behind_pointer =>
            {
                resources += 1;
                work.push((*pointee, 0, true));
            }
            Some(HirTypeKind::Array { element, length }) if *length <= 4096 => {
                work.extend((0..*length).map(|_| (*element, depth + 1, behind_pointer)))
            }
            Some(HirTypeKind::Tuple(elements)) => {
                work.extend(elements.iter().map(|ty| (*ty, depth + 1, behind_pointer)))
            }
            Some(HirTypeKind::Struct { fields }) => {
                for id in fields {
                    let Some(field) = program.fields().get(id.index()) else {
                        return false;
                    };
                    work.push((field.ty, depth + 1, behind_pointer));
                }
            }
            _ => return false,
        }
        if work.len() > 4096 || resources > 256 {
            return false;
        }
    }
    true
}

/// Independently reconstruct a scalar leaf from canonical HIR layout. A byte
/// offset into padding or the middle of a scalar is not a word observation.
fn predicate_word_at_offset(
    program: &HirProgram,
    ty: HirTypeId,
    offset: u64,
    module: HirModuleId,
) -> bool {
    predicate_word_type_at_offset(program, ty, offset, module).is_some()
}

fn predicate_word_type_at_offset(
    program: &HirProgram,
    ty: HirTypeId,
    offset: u64,
    module: HirModuleId,
) -> Option<HirTypeId> {
    let result = predicate_scalar_type_at_offset(program, ty, offset, module)?;
    matches!(
        program.type_kind(result),
        Some(HirTypeKind::Integer(
            HirIntegerType::U64 | HirIntegerType::Usize
        ))
    )
    .then_some(result)
}

/// Shared typed storage boundary for contract and body field inputs. A
/// by-value aggregate is addressable local storage in a body; its immutable
/// parameter fields may instead lower to scalar ABI slots at a contract edge.
/// Both representations must designate the same canonical scalar leaf.
fn predicate_input_field_type(
    program: &HirProgram,
    ty: HirTypeId,
    offset: u64,
    module: HirModuleId,
) -> Option<HirTypeId> {
    let root = match program.type_kind(ty)? {
        HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. } => *pointee,
        HirTypeKind::Struct { .. } | HirTypeKind::Array { .. } => ty,
        _ => return None,
    };
    predicate_scalar_type_at_offset(program, root, offset, module)
}

fn predicate_scalar_type_at_offset(
    program: &HirProgram,
    ty: HirTypeId,
    offset: u64,
    module: HirModuleId,
) -> Option<HirTypeId> {
    let leaf = predicate_leaf_type_at_offset(program, ty, offset, module)?;
    matches!(
        program.type_kind(leaf),
        Some(HirTypeKind::Bool | HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize))
    )
    .then_some(leaf)
}

fn predicate_resource_type(
    program: &HirProgram,
    body: &crate::PredicateRepresentation<HirTypeId>,
    module: HirModuleId,
    resource: u32,
    path: &[u64],
) -> Option<HirTypeId> {
    let root = body.resources.get(resource as usize)?.pointee;
    match path {
        [] => Some(root),
        [offset] => match program.type_kind(predicate_leaf_type_at_offset(
            program, root, *offset, module,
        )?)? {
            HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. } => Some(*pointee),
            _ => None,
        },
        _ => None,
    }
}

fn predicate_leaf_type_at_offset(
    program: &HirProgram,
    mut ty: HirTypeId,
    mut offset: u64,
    module: HirModuleId,
) -> Option<HirTypeId> {
    for _ in 0..16 {
        if program
            .type_definition(ty)
            .is_none_or(|t| t.opaque.is_some_and(|owner| owner != module))
        {
            return None;
        }
        match program.type_kind(ty) {
            Some(HirTypeKind::Own { .. } | HirTypeKind::Reference { .. }) => {
                return (offset == 0).then_some(ty);
            }
            Some(HirTypeKind::Bool) => {
                return (offset == 0 && program.layout_of(ty).is_some_and(|l| l.size_bytes == 1))
                    .then_some(ty);
            }
            Some(HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize)) => {
                return (offset == 0 && program.layout_of(ty).is_some_and(|l| l.size_bytes == 8))
                    .then_some(ty);
            }
            Some(HirTypeKind::Array { element, length }) => {
                let size = program.layout_of(*element)?.size_bytes;
                if size == 0 || offset / size >= *length {
                    return None;
                }
                offset %= size;
                ty = *element;
            }
            Some(HirTypeKind::Struct { .. }) => {
                let (field, base) = program.layout_of(ty).and_then(|l| {
                    l.fields.iter().find_map(|f| {
                        let field = program.fields().get(f.field.index())?;
                        let size = program.layout_of(field.ty)?.size_bytes;
                        (offset >= f.offset_bytes && offset - f.offset_bytes < size)
                            .then_some((field.ty, f.offset_bytes))
                    })
                })?;
                ty = field;
                offset -= base;
            }
            Some(HirTypeKind::Tuple(elements)) => {
                let (element, base) = predicate_tuple_fields(elements, |ty| program.layout_of(ty))?
                    .into_iter()
                    .find(|(element, base)| {
                        program.layout_of(*element).is_some_and(|layout| {
                            offset >= *base && offset - *base < layout.size_bytes
                        })
                    })?;
                ty = element;
                offset -= base;
            }
            _ => return None,
        }
    }
    None
}

fn predicate_tuple_fields<'a>(
    elements: &[HirTypeId],
    layout: impl Fn(HirTypeId) -> Option<&'a HirLayout>,
) -> Option<Vec<(HirTypeId, u64)>> {
    let mut offset = 0u64;
    let mut fields = Vec::new();
    for ty in elements {
        let layout = layout(*ty)?;
        let alignment = layout.alignment;
        if alignment == 0 {
            return None;
        }
        offset = offset.checked_add(alignment - 1)? / alignment * alignment;
        fields.push((*ty, offset));
        offset = offset.checked_add(layout.size_bytes)?;
    }
    Some(fields)
}

fn predicate_array_at(
    program: &HirProgram,
    ty: HirTypeId,
    offset: u64,
    element: HirTypeId,
    length: u64,
    module: HirModuleId,
) -> bool {
    let mut pending = vec![(ty, 0u64)];
    let mut steps = 0;
    while let Some((ty, base)) = pending.pop() {
        steps += 1;
        if steps > 4096 {
            return false;
        }
        if program
            .type_definition(ty)
            .is_none_or(|t| t.opaque.is_some_and(|m| m != module))
        {
            continue;
        }
        match program.type_kind(ty) {
            Some(HirTypeKind::Array {
                element: e,
                length: n,
            }) => {
                if base == offset && *e == element && *n == length {
                    return true;
                }
                let Some(size) = program.layout_of(*e).map(|l| l.size_bytes) else {
                    continue;
                };
                if size > 0 && offset >= base && (offset - base) / size < *n {
                    pending.push((*e, base + (offset - base) / size * size));
                }
            }
            Some(HirTypeKind::Struct { .. }) => {
                let Some(layout) = program.layout_of(ty) else {
                    continue;
                };
                for f in &layout.fields {
                    let Some(field) = program.fields().get(f.field.index()) else {
                        continue;
                    };
                    if let Some(base) = base.checked_add(f.offset_bytes) {
                        pending.push((field.ty, base));
                    }
                }
            }
            _ => {}
        }
    }
    false
}

fn valid_representation(
    program: &HirProgram,
    body: &crate::PredicateRepresentation<HirTypeId>,
    module: HirModuleId,
) -> bool {
    if !body.has_valid_projected_witnesses() {
        return false;
    }
    if body
        .logic
        .validate(
            &body
                .resources
                .iter()
                .map(|r| r.name.as_str())
                .collect::<Vec<_>>(),
            &|r, o, a, t| logic_observation(program, body, module, r, o, a, t),
            &|resource, path| predicate_resource_type(program, body, module, resource, path),
        )
        .is_err()
    {
        return false;
    }
    if body.resources.is_empty() || body.resources.len() > 32 || body.bounds.len() > 32 {
        return false;
    }
    let mut names = BTreeSet::new();
    for resource in &body.resources {
        let Some(layout) = program.layout_of(resource.pointee) else {
            return false;
        };
        if resource.name.is_empty()
            || !names.insert(&resource.name)
            || !plain_representation(program, resource.pointee)
            || !(1..=4096).contains(&layout.size_bytes)
            || resource.initialized.len() > 32
            || resource
                .initialized
                .iter()
                .any(|(start, end)| start >= end || *end > layout.size_bytes)
        {
            return false;
        }
    }
    if body.witnesses.len() > 32
        || body.witnesses.iter().any(|w| {
            let Some(resource) = body.resources.get(w.resource as usize) else {
                return true;
            };
            w.name.is_empty()
                || !names.insert(&w.name)
                || !matches!(
                    program.type_kind(w.ty),
                    Some(HirTypeKind::Bool)
                        | Some(HirTypeKind::Integer(
                            HirIntegerType::U64 | HirIntegerType::Usize
                        ))
                )
                || predicate_scalar_type_at_offset(program, resource.pointee, w.offset, module)
                    != Some(w.ty)
                || w.offset
                    .checked_add(
                        if matches!(program.type_kind(w.ty), Some(HirTypeKind::Bool)) {
                            1
                        } else {
                            8
                        },
                    )
                    .is_none_or(|end| {
                        !resource
                            .initialized
                            .iter()
                            .any(|(a, b)| *a <= w.offset && *b >= end)
                    })
        })
    {
        return false;
    }
    if body.prefixes.len() > 32
        || body.prefixes.iter().any(|prefix| {
            let Some(resource) = body.resources.get(prefix.resource as usize) else {
                return true;
            };
            (match &prefix.count {
                crate::PredicatePrefixCount::Stored { offset } => {
                    !predicate_word_at_offset(program, resource.pointee, *offset, module)
                }
                crate::PredicatePrefixCount::Logical(expression) => !matches!(
                    expression.validate(
                        &body
                            .logic
                            .parameters
                            .iter()
                            .map(|p| p.ty)
                            .collect::<Vec<_>>(),
                        &body
                            .logic
                            .existentials
                            .iter()
                            .map(|w| w.ty)
                            .collect::<Vec<_>>(),
                        &|r, o, a, t| logic_observation(program, body, module, r, o, a, t),
                        &|r, path| path
                            .is_empty()
                            .then(|| body.resources.get(r as usize).map(|r| r.pointee))
                            .flatten(),
                        &mut crate::predicate_logic::LogicBudget::default(),
                    ),
                    Ok(crate::predicate_logic::LogicType::U64
                        | crate::predicate_logic::LogicType::Usize)
                ),
            }) || !predicate_array_at(
                program,
                resource.pointee,
                prefix.array_offset,
                prefix.element,
                prefix.length,
                module,
            ) || program
                .layout_of(prefix.element)
                .is_none_or(|l| l.size_bytes != prefix.stride)
                || !matches!(
                    program.type_kind(prefix.element),
                    Some(
                        HirTypeKind::Bool
                            | HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize)
                    )
                )
                || !crate::vir::prefix_bounds_valid(prefix, &body.bounds)
        })
    {
        return false;
    }
    for bound in &body.bounds {
        let Some(resource) = body.resources.get(bound.resource as usize) else {
            return false;
        };
        if !predicate_word_at_offset(program, resource.pointee, bound.offset, module)
            || bound.lower > bound.upper
            || bound.offset % 8 != 0
            || program.layout_of(resource.pointee).is_none_or(|layout| {
                bound
                    .offset
                    .checked_add(8)
                    .is_none_or(|end| end > layout.size_bytes)
            })
        {
            return false;
        }
    }
    true
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirPredicateInterface {
    pub predicate: HirPredicateId,
    pub function: HirFunctionId,
    pub ensures: bool,
    /// An ensures clause returning mutable parameter permissions in place.
    pub in_place: bool,
    /// Parameter indices, or `[0]` for an ordinary result postcondition.
    pub parameters: Vec<u32>,
    pub fields: Vec<Vec<HirFieldId>>,
    pub arguments: crate::predicate_logic::WitnessArguments<HirTypeId, HirLocalId>,
    pub span: ByteSpan,
}

impl Elaborator {
    pub(super) fn predicate_contract(
        &mut self,
        clause: &super::super::AstFunctionClause,
    ) -> Result<bool, FrontendFailure> {
        use super::super::{AstExpressionKind as E, AstLogicalExpressionKind as L};
        let (callee, arguments) = match &clause.expression.kind {
            L::Call { callee, arguments } => (callee, arguments.clone()),
            L::Value(super::super::AstExpression {
                kind: E::Call { callee, arguments },
                ..
            }) => (
                callee,
                arguments
                    .iter()
                    .map(|value| super::super::AstLogicalExpression {
                        span: value.span,
                        kind: L::Value(value.clone()),
                    })
                    .collect(),
            ),
            _ => return Ok(false),
        };
        let Some(id) = self.predicate_names.get(&self.key(callee)).copied() else {
            return Ok(false);
        };
        let body = self.predicates[id.index()]
            .representation
            .as_ref()
            .unwrap()
            .clone();
        if !body.has_supported_interface_witnesses() {
            return Err(FrontendFailure::unsupported(
                clause.span,
                "predicate witness projection does not match its typed field observation",
            ));
        }
        if clause.effect.is_some()
            || body.resources.len() + body.logic.parameters.len() != arguments.len()
        {
            return Err(FrontendFailure::elaboration(
                clause.span,
                "predicate interface binding arity mismatch",
            ));
        }
        let mut resource_arguments = Vec::new();
        let mut actuals = Vec::new();
        for (position, argument) in arguments.iter().enumerate() {
            if let Some(parameter) = body
                .logic
                .parameters
                .iter()
                .find(|p| p.position == position)
            {
                actuals.push((
                    parameter.ty,
                    logic::contract_logical_expression(argument, 0, clause.ensures)?,
                ));
            } else {
                let L::Value(value) = &argument.kind else {
                    return Err(FrontendFailure::unsupported(
                        argument.span,
                        "predicate resource actual requires a parameter or owner field",
                    ));
                };
                resource_arguments.push(value);
            }
        }
        let logical_arguments = self.predicate_action_witnesses(
            &body,
            &[],
            &actuals,
            &[],
            clause.span,
            Some((clause.ensures, self.return_type)),
        )?;
        let arguments = resource_arguments;
        let resources = &body.resources;
        let function = self.current_function.unwrap();
        let in_place = clause.ensures
            && arguments.iter().all(|a| {
                !matches!(&a.kind, E::Name(name) if name == "result")
                    && !matches!(&a.kind, E::Place(place) if place.base == "result")
            });
        let mut parameters = Vec::new();
        let mut paths = Vec::new();
        for (argument, resource) in arguments.iter().zip(resources) {
            let (name, projections) = match &argument.kind {
                E::Name(name) => (name.as_str(), &[][..]),
                E::Place(place) => (place.base.as_str(), place.projections.as_slice()),
                _ => {
                    return Err(FrontendFailure::unsupported(
                        argument.span,
                        "predicate interface requires a parameter or owner field",
                    ));
                }
            };
            let (index, mut ty) = if clause.ensures && !in_place {
                if name != "result" || (projections.is_empty() && arguments.len() != 1) {
                    return Err(FrontendFailure::unsupported(
                        clause.span,
                        "predicate result interface requires a single owner or mutable reference result",
                    ));
                }
                (0, self.return_type)
            } else {
                let binding = self.lookup(name, argument.span)?;
                // Parameters occupy the initial local slots; locals are not in
                // scope while elaborating the signature's clauses.
                (binding.local.get(), binding.value.ty)
            };
            let mut path = Vec::new();
            if !projections.is_empty() && (in_place || projections.len() > 16) {
                return Err(FrontendFailure::unsupported(
                    argument.span,
                    "predicate field path exceeds budget or uses an in-place postcondition",
                ));
            }
            for projection in projections {
                let super::super::AstPlaceProjection::Field { name, span } = projection else {
                    return Err(FrontendFailure::unsupported(
                        argument.span,
                        "predicate ABI projection requires a struct field",
                    ));
                };
                self.require_representation_access(ty, *span)?;
                let Some(HirTypeKind::Struct { fields }) =
                    self.type_definition(ty).map(|t| &t.kind)
                else {
                    return Err(FrontendFailure::unsupported(
                        *span,
                        "predicate ABI projection requires a struct field",
                    ));
                };
                let field = fields
                    .iter()
                    .filter_map(|id| self.fields.get(id.index()))
                    .find(|f| f.name == *name)
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(*span, "unknown predicate ABI field")
                    })?;
                path.push(field.id);
                ty = field.ty;
            }
            if !path.is_empty()
                && !matches!(
                    self.type_definition(ty).map(|t| &t.kind),
                    Some(HirTypeKind::Own { .. })
                )
            {
                return Err(FrontendFailure::unsupported(
                    argument.span,
                    "predicate ABI field must own its resource",
                ));
            }
            paths.push(path);
            if !matches!(self.type_definition(ty).map(|t| &t.kind), Some(HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, mutability: HirMutability::Mutable, .. }) if *pointee == resource.pointee)
            {
                return Err(FrontendFailure::elaboration(
                    argument.span,
                    "predicate interface requires a matching owner or mutable reference type",
                ));
            }
            if in_place
                && !matches!(
                    self.type_definition(ty).map(|t| &t.kind),
                    Some(HirTypeKind::Reference {
                        mutability: HirMutability::Mutable,
                        ..
                    })
                )
            {
                return Err(FrontendFailure::elaboration(
                    argument.span,
                    "in-place predicate postconditions require mutable reference parameters",
                ));
            }
            parameters.push(index);
        }
        self.specs.predicate_interfaces.push(HirPredicateInterface {
            predicate: id,
            function,
            ensures: clause.ensures,
            in_place,
            parameters,
            fields: paths,
            arguments: logical_arguments,
            span: clause.span,
        });
        Ok(true)
    }
}

/// Substitution is confined to this declaration's logical body. Runtime code,
/// contracts, pointer arguments and projection bases never see these names.
fn substitute_predicate_witnesses(
    expression: &mut super::super::AstLogicalExpression,
    aliases: &BTreeMap<String, super::super::AstExpression>,
) {
    use super::super::{AstExpressionKind as E, AstLogicalExpressionKind as L};
    match &mut expression.kind {
        L::Call { arguments, .. } => {
            for argument in arguments {
                substitute_predicate_witnesses(argument, aliases);
            }
        }
        L::Value(value) => {
            if let E::Name(name) = &value.kind
                && let Some(witness) = aliases.get(name)
            {
                *value = witness.clone();
            }
        }
        L::Binary { left, right, .. } => {
            substitute_predicate_witnesses(left, aliases);
            substitute_predicate_witnesses(right, aliases);
        }
        L::Not(value) => substitute_predicate_witnesses(value, aliases),
        L::InitializedRange { start, end, .. } | L::ResourceRange { start, end, .. } => {
            substitute_predicate_witnesses(start, aliases);
            substitute_predicate_witnesses(end, aliases);
        }
    }
}

fn logic_observation(
    program: &HirProgram,
    body: &crate::PredicateRepresentation<HirTypeId>,
    module: HirModuleId,
    resource: u32,
    offset: u64,
    access: HirTypeId,
    time: crate::predicate_logic::ObservationTime,
) -> Option<crate::predicate_logic::LogicType<HirTypeId>> {
    use crate::predicate_logic::{LogicType, ObservationTime};

    if time != ObservationTime::Current {
        return None;
    }
    let r = body.resources.get(resource as usize)?;
    if predicate_scalar_type_at_offset(program, r.pointee, offset, module) != Some(access) {
        return None;
    }
    match program.type_kind(access)? {
        HirTypeKind::Bool => Some(LogicType::Bool),
        HirTypeKind::Integer(HirIntegerType::U64) => Some(LogicType::U64),
        HirTypeKind::Integer(HirIntegerType::Usize) => Some(LogicType::Usize),
        _ => None,
    }
}

fn valid_action_witnesses(program: &HirProgram, action: &HirPredicateAction) -> bool {
    use crate::predicate_logic::*;
    let Some(function) = program.function_by_id(action.function) else {
        return false;
    };
    let Some(body) = program
        .predicate(action.predicate)
        .and_then(|p| p.representation.as_ref())
    else {
        return false;
    };
    let Some(locals) = function.body().map(|b| &b.locals) else {
        return false;
    };
    if action.witnesses.inputs.iter().any(|(ty, id)| {
        let id = match id {
            WitnessInput::Result(_) | WitnessInput::ResultField { .. } => return true,
            WitnessInput::Memory { base, offset, access, time } => {
                let Some(local) = locals.get(base.index()) else { return true; };
                return *time!=crate::predicate_logic::ObservationTime::Current
                    || predicate_input_field_type(program,local.ty,*offset,function.module)!=Some(*access)
                    || !matches!((ty,program.type_kind(*access)),
                        (LogicType::U64,Some(HirTypeKind::Integer(HirIntegerType::U64)))
                        | (LogicType::Usize,Some(HirTypeKind::Integer(HirIntegerType::Usize)))
                        | (LogicType::Bool,Some(HirTypeKind::Bool)));
            }
            WitnessInput::Scalar(id) => id,
            WitnessInput::Opened { action: opened, holder, binder } => {
                let Some(open) = program.specs().predicate_actions.get(*opened as usize) else { return true; };
                return open.id >= action.id || open.function != action.function
                    || open.predicate != action.predicate
                    || !matches!(open.kind, HirPredicateActionKind::Unfold { holder: h, .. } if h == *holder)
                    || !matches!(action.kind,
                        HirPredicateActionKind::Fold { holder: h, .. }
                        | HirPredicateActionKind::Finish { holder: h } if h == *holder)
                    || body.logic.existentials.get(*binder as usize).is_none_or(|b| b.ty != *ty);
            }
        };
        let actual = locals.get(id.index()).and_then(|l| program.type_kind(l.ty));
        !matches!(
            (ty, actual),
            (
                LogicType::U64,
                Some(HirTypeKind::Integer(HirIntegerType::U64))
            ) | (
                LogicType::Usize,
                Some(HirTypeKind::Integer(HirIntegerType::Usize))
            ) | (LogicType::Bool, Some(HirTypeKind::Bool))
        )
    }) {
        return false;
    }
    if !matches!(action.kind, HirPredicateActionKind::Fold { .. }) {
        return action.witnesses.values.is_empty()
            && action
                .witnesses
                .validate_arguments(&body.logic, &mut LogicBudget::default())
                .is_ok();
    }
    action
        .witnesses
        .validate(
            &body.logic,
            &|r, o, a, t| logic_observation(program, body, function.module, r, o, a, t),
            &|r, path| predicate_resource_type(program, body, function.module, r, path),
            &mut LogicBudget::default(),
        )
        .is_ok()
}
