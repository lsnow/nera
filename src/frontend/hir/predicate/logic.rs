//! Declaration-scoped predicate terms. Names become typed binder indices before
//! lowering; there is no textual substitution of arbitrary witness expressions.
use super::*;
use crate::frontend::{
    AstExpressionKind as E, AstLogicalExpression as L, AstLogicalExpressionKind as K,
};
use crate::predicate_logic::*;
impl Elaborator {
    pub(super) fn predicate_logic_type(&self, ty: HirTypeId) -> Option<LogicType<HirTypeId>> {
        match self.type_definition(ty)?.kind {
            HirTypeKind::Bool => Some(LogicType::Bool),
            HirTypeKind::Integer(HirIntegerType::U64) => Some(LogicType::U64),
            HirTypeKind::Integer(HirIntegerType::Usize) => Some(LogicType::Usize),
            HirTypeKind::RawPointer { pointee, .. } => Some(LogicType::Resource(pointee)),
            _ => None,
        }
    }
    pub(super) fn predicate_logic_expression(
        &mut self,
        expression: &L,
        resources: &[crate::PredicateStorage<HirTypeId>],
        logic: &PredicateLogic<HirTypeId>,
        expected: Option<LogicType<HirTypeId>>,
    ) -> Result<LogicExpression<HirTypeId>, FrontendFailure> {
        let mut nodes = Vec::new();
        self.predicate_logic_node(expression, resources, logic, expected, &mut nodes, 0)?;
        let root = (nodes.len() - 1) as u32;
        Ok(LogicExpression { nodes, root })
    }
    fn predicate_logic_node(
        &mut self,
        expression: &L,
        resources: &[crate::PredicateStorage<HirTypeId>],
        logic: &PredicateLogic<HirTypeId>,
        expected: Option<LogicType<HirTypeId>>,
        nodes: &mut Vec<LogicNode<HirTypeId>>,
        depth: usize,
    ) -> Result<u32, FrontendFailure> {
        let bad = || {
            FrontendFailure::unsupported(
                expression.span,
                "predicate expression is unbound, ill-typed or outside the bounded pure profile",
            )
        };
        if depth >= MAX_EXPRESSION_DEPTH || nodes.len() >= MAX_EXPRESSION_NODES {
            return Err(FrontendFailure::unsupported(
                expression.span,
                "predicate expression budget exceeded",
            ));
        }
        let (ty, kind) = match &expression.kind {
            K::Value(value) => match &value.kind {
                E::Integer {
                    value,
                    explicit_u64,
                    explicit_usize,
                } => {
                    let ty = if *explicit_usize {
                        LogicType::Usize
                    } else if *explicit_u64 {
                        LogicType::U64
                    } else {
                        expected
                            .filter(|t| matches!(t, LogicType::U64 | LogicType::Usize))
                            .unwrap_or(LogicType::U64)
                    };
                    (ty, LogicNodeKind::Word(*value))
                }
                E::Bool(value) => (LogicType::Bool, LogicNodeKind::Bool(*value)),
                E::Name(name) => {
                    if let Some((index, p)) = logic
                        .parameters
                        .iter()
                        .enumerate()
                        .find(|(_, p)| p.name == *name)
                    {
                        (
                            p.ty,
                            LogicNodeKind::Binder(LogicBinder::Parameter(index as u32)),
                        )
                    } else if let Some((index, w)) = logic
                        .existentials
                        .iter()
                        .enumerate()
                        .find(|(_, w)| w.name == *name)
                    {
                        (
                            w.ty,
                            LogicNodeKind::Binder(LogicBinder::Existential(index as u32)),
                        )
                    } else if let Some((index, r)) =
                        resources.iter().enumerate().find(|(_, r)| r.name == *name)
                    {
                        (
                            LogicType::Resource(r.pointee),
                            LogicNodeKind::Resource {
                                resource: index as u32,
                                path: vec![],
                            },
                        )
                    } else {
                        return Err(bad());
                    }
                }
                E::Place(place) if place.projections.is_empty() => {
                    let value = super::super::super::AstExpression {
                        kind: E::Name(place.base.clone()),
                        span: value.span,
                    };
                    return self.predicate_logic_node(
                        &L {
                            kind: K::Value(value),
                            span: expression.span,
                        },
                        resources,
                        logic,
                        expected,
                        nodes,
                        depth + 1,
                    );
                }
                E::Place(_) => {
                    let (resource, access, offset) =
                        self.predicate_storage_place(value, resources)?;
                    if let Some(
                        HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. },
                    ) = self.type_definition(access).map(|t| &t.kind)
                    {
                        (
                            LogicType::Resource(*pointee),
                            LogicNodeKind::Resource {
                                resource: resource as u32,
                                path: vec![offset],
                            },
                        )
                    } else {
                        let ty = self.predicate_logic_type(access).ok_or_else(bad)?;
                        if matches!(ty, LogicType::Resource(_)) {
                            return Err(bad());
                        }
                        (
                            ty,
                            LogicNodeKind::Observe {
                                resource: resource as u32,
                                offset,
                                access,
                                time: ObservationTime::Current,
                            },
                        )
                    }
                }
                _ => return Err(bad()),
            },
            K::Not(value) => {
                let operand = self.predicate_logic_node(
                    value,
                    resources,
                    logic,
                    Some(LogicType::Bool),
                    nodes,
                    depth + 1,
                )?;
                (LogicType::Bool, LogicNodeKind::Not(operand))
            }
            K::Binary {
                operator,
                left,
                right,
            } => {
                use crate::Punctuation as P;
                if *operator == P::Star {
                    let (operand, factor, literal) = if let Some(n) = predicate_number(right) {
                        (left, n, right)
                    } else if let Some(n) = predicate_number(left) {
                        (right, n, left)
                    } else {
                        return Err(bad());
                    };
                    let operand = self.predicate_logic_node(
                        operand,
                        resources,
                        logic,
                        expected.filter(|t| matches!(t, LogicType::U64 | LogicType::Usize)),
                        nodes,
                        depth + 1,
                    )?;
                    let ty = nodes[operand as usize].ty;
                    if !matches!(ty, LogicType::U64 | LogicType::Usize) {
                        return Err(bad());
                    }
                    if let K::Value(value) = &literal.kind
                        && let E::Integer {
                            explicit_u64,
                            explicit_usize,
                            ..
                        } = value.kind
                        && ((explicit_u64 && ty != LogicType::U64)
                            || (explicit_usize && ty != LogicType::Usize))
                    {
                        return Err(bad());
                    }
                    (ty, LogicNodeKind::Scale { operand, factor })
                } else {
                    let boolean = matches!(operator, P::LogicalAnd | P::LogicalOr);
                    let hint = if boolean {
                        Some(LogicType::Bool)
                    } else {
                        expected.filter(|t| matches!(t, LogicType::U64 | LogicType::Usize))
                    };
                    // Infer an unsuffixed literal from its typed peer; this is
                    // literal typing, never a conversion of a bound value.
                    let (a, b) = if matches!(
                        &left.kind,
                        K::Value(crate::frontend::AstExpression {
                            kind: E::Integer {
                                explicit_u64: false,
                                explicit_usize: false,
                                ..
                            },
                            ..
                        })
                    ) {
                        let b = self.predicate_logic_node(
                            right,
                            resources,
                            logic,
                            hint,
                            nodes,
                            depth + 1,
                        )?;
                        let a = self.predicate_logic_node(
                            left,
                            resources,
                            logic,
                            Some(nodes[b as usize].ty),
                            nodes,
                            depth + 1,
                        )?;
                        (a, b)
                    } else {
                        let a = self.predicate_logic_node(
                            left,
                            resources,
                            logic,
                            hint,
                            nodes,
                            depth + 1,
                        )?;
                        let b = self.predicate_logic_node(
                            right,
                            resources,
                            logic,
                            Some(nodes[a as usize].ty),
                            nodes,
                            depth + 1,
                        )?;
                        (a, b)
                    };
                    let input = nodes[a as usize].ty;
                    if input != nodes[b as usize].ty {
                        return Err(bad());
                    }
                    let numeric = matches!(input, LogicType::U64 | LogicType::Usize);
                    let kind = match operator {
                        P::Plus if numeric => LogicNodeKind::Add(a, b),
                        P::Minus if numeric => LogicNodeKind::Sub(a, b),
                        P::EqualEqual => LogicNodeKind::Equal(a, b),
                        P::Less if numeric => LogicNodeKind::Less(a, b),
                        P::LessEqual if numeric => LogicNodeKind::LessEqual(a, b),
                        P::Greater if numeric => LogicNodeKind::Less(b, a),
                        P::GreaterEqual if numeric => LogicNodeKind::LessEqual(b, a),
                        P::NotEqual => {
                            let id = nodes.len() as u32;
                            nodes.push(LogicNode {
                                ty: LogicType::Bool,
                                kind: LogicNodeKind::Equal(a, b),
                            });
                            LogicNodeKind::Not(id)
                        }
                        P::LogicalAnd if input == LogicType::Bool => LogicNodeKind::And(a, b),
                        P::LogicalOr if input == LogicType::Bool => LogicNodeKind::Or(a, b),
                        _ => return Err(bad()),
                    };
                    (
                        if matches!(operator, P::Plus | P::Minus) {
                            input
                        } else {
                            LogicType::Bool
                        },
                        kind,
                    )
                }
            }
            _ => return Err(bad()),
        };
        if expected.is_some_and(|e| e != ty) {
            return Err(bad());
        }
        if nodes.len() >= MAX_EXPRESSION_NODES {
            return Err(bad());
        }
        let id = nodes.len() as u32;
        nodes.push(LogicNode { ty, kind });
        Ok(id)
    }
}

impl Elaborator {
    fn predicate_contract_fields(
        &mut self,
        expression: &mut L,
        return_type: HirTypeId,
        logic: &mut PredicateLogic<HirTypeId>,
        arguments: &mut WitnessArguments<HirTypeId, HirLocalId>,
        time: ObservationTime,
        depth: usize,
    ) -> Result<(), FrontendFailure> {
        if depth >= MAX_EXPRESSION_DEPTH {
            return Err(FrontendFailure::unsupported(
                expression.span,
                "logical field depth exceeded",
            ));
        }
        match &mut expression.kind {
            K::Call {
                callee,
                arguments: values,
            } if callee == "old" && values.len() == 1 => {
                let mut inner = values[0].clone();
                self.predicate_contract_fields(
                    &mut inner,
                    return_type,
                    logic,
                    arguments,
                    ObservationTime::Entry,
                    depth + 1,
                )?;
                *expression = inner;
            }
            K::Value(value) if matches!(&value.kind, E::Place(place) if !place.projections.is_empty()) =>
            {
                let E::Place(place) = &value.kind else {
                    unreachable!()
                };
                let name = place.base.clone();
                let (base, root) = if name == "result" {
                    (HirLocalId::new(0), return_type)
                } else {
                    let binding = self.lookup(&name, value.span)?;
                    let root = match self.type_definition(binding.value.ty).map(|t| &t.kind) {
                        Some(
                            HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. },
                        ) => *pointee,
                        Some(HirTypeKind::Struct { .. } | HirTypeKind::Array { .. }) => {
                            binding.value.ty
                        }
                        _ => {
                            return Err(FrontendFailure::unsupported(
                                value.span,
                                "predicate observation requires typed owner, reference or aggregate storage",
                            ));
                        }
                    };
                    (binding.local, root)
                };
                let resources = [crate::PredicateStorage {
                    name: name.clone(),
                    pointee: root,
                    initialized: vec![],
                }];
                let (_, access, offset) = self.predicate_storage_place(value, &resources)?;
                let ty = self
                    .predicate_logic_type(access)
                    .filter(|ty| !matches!(ty, LogicType::Resource(_)))
                    .ok_or_else(|| {
                        FrontendFailure::unsupported(
                            value.span,
                            "logical field must be u64, usize or bool",
                        )
                    })?;
                let input = if name == "result" {
                    WitnessInput::ResultField {
                        base,
                        offset,
                        access,
                    }
                } else {
                    WitnessInput::Memory {
                        base,
                        offset,
                        access,
                        time,
                    }
                };
                let index = if let Some(index) = arguments
                    .inputs
                    .iter()
                    .position(|entry| *entry == (ty, input))
                {
                    index
                } else {
                    if arguments.inputs.len() >= MAX_LOGIC_PARAMETERS {
                        return Err(FrontendFailure::unsupported(
                            value.span,
                            "logical input budget exceeded",
                        ));
                    }
                    let index = arguments.inputs.len();
                    arguments.inputs.push((ty, input));
                    logic.parameters.push(LogicParameter {
                        position: index,
                        name: format!("$field_{index}"),
                        ty,
                    });
                    index
                };
                value.kind = E::Name(logic.parameters[index].name.clone());
            }
            K::Not(value) => self.predicate_contract_fields(
                value,
                return_type,
                logic,
                arguments,
                time,
                depth + 1,
            )?,
            K::Binary { left, right, .. } => {
                self.predicate_contract_fields(
                    left,
                    return_type,
                    logic,
                    arguments,
                    time,
                    depth + 1,
                )?;
                self.predicate_contract_fields(
                    right,
                    return_type,
                    logic,
                    arguments,
                    time,
                    depth + 1,
                )?;
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn predicate_action_witnesses(
        &mut self,
        body: &crate::PredicateRepresentation<HirTypeId>,
        names: &[String],
        actuals: &[(LogicType<HirTypeId>, L)],
        explicit: &[(String, L)],
        span: ByteSpan,
        contract_result: Option<(bool, HirTypeId)>,
    ) -> Result<WitnessArguments<HirTypeId, HirLocalId>, FrontendFailure> {
        let mut resources = body.resources.clone();
        for (resource, name) in resources.iter_mut().zip(names) {
            resource.name = name.clone();
        }
        let mut logic = PredicateLogic::default();
        let mut result = WitnessArguments::default();
        let mut seen = BTreeSet::new();
        for (actual_index, entry) in actuals
            .iter()
            .map(|(ty, e)| (Some(*ty), "", e))
            .chain(explicit.iter().map(|(n, e)| (None, n.as_str(), e)))
            .enumerate()
        {
            let (actual_type, name, expression) = entry;
            let (index, expected) = if let Some(ty) = actual_type {
                (actual_index, ty)
            } else {
                let (index, binder) = body
                    .logic
                    .existentials
                    .iter()
                    .enumerate()
                    .find(|(_, w)| w.name == name)
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(span, "unknown existential witness")
                    })?;
                if !seen.insert(index) {
                    return Err(FrontendFailure::elaboration(
                        span,
                        "duplicate existential witness",
                    ));
                }
                (index, binder.ty)
            };
            let mut normalized = expression.clone();
            if contract_result.is_some() || actual_type.is_some() {
                let return_type = contract_result
                    .map(|(_, ty)| ty)
                    .unwrap_or(self.return_type);
                self.predicate_contract_fields(
                    &mut normalized,
                    return_type,
                    &mut logic,
                    &mut result,
                    ObservationTime::Current,
                    0,
                )?;
            }
            let expression = &normalized;
            let mut pending = vec![expression];
            while let Some(term) = pending.pop() {
                match &term.kind {
                    K::Value(value) => {
                        if let Some(name) = predicate_name(value)
                            && !(actual_type.is_none() && resources.iter().any(|r| r.name == name))
                            && !logic
                                .parameters
                                .iter()
                                .any(|p: &LogicParameter<HirTypeId>| p.name == name)
                        {
                            let (ty, input) = if let Some((_, result_ty)) =
                                contract_result.filter(|_| name == "result")
                            {
                                let ty = self
                                    .predicate_logic_type(result_ty)
                                    .filter(|ty| !matches!(ty, LogicType::Resource(_)))
                                    .ok_or_else(|| {
                                        FrontendFailure::elaboration(
                                            value.span,
                                            "predicate logical result must be a scalar",
                                        )
                                    })?;
                                (ty, WitnessInput::Result(HirLocalId::new(0)))
                            } else if let Some(binding) = self
                                .scopes
                                .iter()
                                .rev()
                                .find_map(|s| s.ghost_bindings.get(name))
                                .copied()
                            {
                                binding
                            } else {
                                let binding = self.lookup(name, value.span)?;
                                let ty = self
                                    .predicate_logic_type(binding.value.ty)
                                    .filter(|ty| !matches!(ty, LogicType::Resource(_)))
                                    .ok_or_else(|| {
                                        FrontendFailure::elaboration(
                                            value.span,
                                            "witness input must be u64, usize or bool",
                                        )
                                    })?;
                                (ty, WitnessInput::Scalar(binding.local))
                            };
                            result.inputs.push((ty, input));
                            logic.parameters.push(LogicParameter {
                                position: logic.parameters.len(),
                                name: name.into(),
                                ty,
                            });
                            if result.inputs.len() > MAX_LOGIC_PARAMETERS {
                                return Err(FrontendFailure::unsupported(
                                    span,
                                    "logical input budget exceeded",
                                ));
                            }
                        }
                    }
                    K::Not(value) => pending.push(value),
                    K::Binary { left, right, .. } => {
                        pending.push(right);
                        pending.push(left);
                    }
                    _ => {
                        return Err(FrontendFailure::unsupported(
                            span,
                            "witness must be a pure expression",
                        ));
                    }
                }
            }
            let value = self.predicate_logic_expression(
                expression,
                if actual_type.is_some() {
                    &[]
                } else {
                    &resources
                },
                &logic,
                Some(expected),
            )?;
            if actual_type.is_some() {
                result.arguments.push(value);
            } else {
                result.values.push((index as u32, value));
            }
        }
        Ok(result)
    }
}

/// Contract calls use runtime AST argument containers. Convert only the pure
/// scalar subset before applying the same bounded predicate term checker.
pub(super) fn contract_expression(
    value: &crate::frontend::AstExpression,
    depth: usize,
    allow_old: bool,
) -> Result<L, FrontendFailure> {
    if depth >= MAX_EXPRESSION_DEPTH {
        return Err(FrontendFailure::unsupported(
            value.span,
            "logical argument depth exceeded",
        ));
    }
    let kind = match &value.kind {
        E::Call { callee, arguments } if callee == "old" => {
            if !allow_old || arguments.len() != 1 {
                return Err(FrontendFailure::unsupported(
                    value.span,
                    "predicate old requires one pure entry expression in ensures",
                ));
            }
            // Preserve the coordinate until typed field inputs are extracted.
            // Scalar parameters already denote entry slots; fields require an
            // actual boundary memory snapshot. This never emits a runtime call.
            return Ok(L {
                span: value.span,
                kind: K::Call {
                    callee: "old".into(),
                    arguments: vec![contract_expression(&arguments[0], depth + 1, false)?],
                },
            });
        }
        E::Add(terms) if !terms.is_empty() && terms.len() <= MAX_EXPRESSION_DEPTH - depth => {
            let mut terms = terms.iter();
            let mut result = contract_expression(terms.next().unwrap(), depth + 1, allow_old)?;
            for term in terms {
                result = L {
                    span: value.span,
                    kind: K::Binary {
                        operator: crate::Punctuation::Plus,
                        left: Box::new(result),
                        right: Box::new(contract_expression(term, depth + 1, allow_old)?),
                    },
                };
            }
            return Ok(result);
        }
        E::Compare {
            predicate,
            left,
            right,
            ..
        } => {
            use crate::Punctuation as P;
            use crate::frontend::AstIntegerPredicate as C;
            K::Binary {
                operator: match predicate {
                    C::Equal => P::EqualEqual,
                    C::NotEqual => P::NotEqual,
                    C::LessThan => P::Less,
                    C::LessOrEqual => P::LessEqual,
                    C::GreaterThan => P::Greater,
                    C::GreaterOrEqual => P::GreaterEqual,
                },
                left: Box::new(contract_expression(left, depth + 1, allow_old)?),
                right: Box::new(contract_expression(right, depth + 1, allow_old)?),
            }
        }
        E::Name(name) if name == "result" && !allow_old => {
            return Err(FrontendFailure::unsupported(
                value.span,
                "result is unavailable in a precondition or old expression",
            ));
        }
        E::Place(place) if place.base == "result" && !allow_old => {
            return Err(FrontendFailure::unsupported(
                value.span,
                "result is unavailable in a precondition or old expression",
            ));
        }
        E::Name(_) | E::Integer { .. } | E::Bool(_) => K::Value(value.clone()),
        E::Place(_) => K::Value(value.clone()),
        _ => {
            return Err(FrontendFailure::unsupported(
                value.span,
                "predicate contract actual must be a pure scalar argument",
            ));
        }
    };
    Ok(L {
        span: value.span,
        kind,
    })
}

/// Normalize specification actuals into the same bounded typed kernel used by
/// local fold actions. Explicit old retains its boundary coordinate until
/// typed scalar or memory inputs have been extracted.
pub(super) fn contract_logical_expression(
    expression: &L,
    depth: usize,
    allow_old: bool,
) -> Result<L, FrontendFailure> {
    if depth >= MAX_EXPRESSION_DEPTH {
        return Err(FrontendFailure::unsupported(
            expression.span,
            "logical argument depth exceeded",
        ));
    }
    let kind = match &expression.kind {
        K::Value(value) => return contract_expression(value, depth, allow_old),
        K::Not(operand) => K::Not(Box::new(contract_logical_expression(
            operand,
            depth + 1,
            allow_old,
        )?)),
        K::Binary {
            operator,
            left,
            right,
        } => K::Binary {
            operator: *operator,
            left: Box::new(contract_logical_expression(left, depth + 1, allow_old)?),
            right: Box::new(contract_logical_expression(right, depth + 1, allow_old)?),
        },
        K::Call { callee, arguments } if callee == "old" && allow_old && arguments.len() == 1 => {
            return Ok(L {
                span: expression.span,
                kind: K::Call {
                    callee: "old".into(),
                    arguments: vec![contract_logical_expression(
                        &arguments[0],
                        depth + 1,
                        false,
                    )?],
                },
            });
        }
        _ => {
            return Err(FrontendFailure::unsupported(
                expression.span,
                "predicate contract actual must be a pure scalar entry expression",
            ));
        }
    };
    Ok(L {
        span: expression.span,
        kind,
    })
}
