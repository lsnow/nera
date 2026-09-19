//! Contract and loop assertions are elaborated without runtime expression evaluation.
use super::*;
use crate::Punctuation as P;
use crate::frontend::{AstLogicalExpression, AstLogicalExpressionKind as L};

impl Elaborator {
    pub(super) fn elaborate_loop_invariants(
        &mut self,
        loop_id: HirLoopId,
        invariants: &[super::super::AstLoopInvariant],
    ) -> Result<(), FrontendFailure> {
        for invariant in invariants {
            let function = self.current_function.expect("loop function");
            let id = HirSpecLoopInvariantId::new(self.specs.loop_invariants.len() as u32);
            let clause = HirSpecClauseId::new(self.specs.clauses.len() as u32);
            self.loop_spec_context = Some(loop_id);
            let root = self.observation_root(clause, &invariant.expression, invariant.span);
            self.loop_spec_context = None;
            let root = root?;
            let location = HirSpecLocation::LoopHead { function, loop_id };
            self.specs.clauses.push(HirSpecClause {
                id: clause,
                owner: HirSpecClauseOwner::LoopInvariant(id),
                location,
                root,
                span: invariant.span,
            });
            self.specs.loop_invariants.push(HirSpecLoopInvariant {
                id,
                function,
                loop_id,
                location,
                clause,
                span: invariant.span,
            });
        }
        Ok(())
    }
    pub(super) fn elaborate_function_clauses(
        &mut self,
        clauses: &[super::super::AstFunctionClause],
    ) -> Result<(), FrontendFailure> {
        let function = self.current_function.expect("function contract");
        let contract = self.function_declarations[function.index()].contract;
        for clause in clauses {
            let position = if clause.ensures {
                HirSpecContractPosition::Ensures
            } else {
                HirSpecContractPosition::Requires
            };
            let id = HirSpecClauseId::new(self.specs.clauses.len() as u32);
            self.contract_position = Some(position);
            let root = if let Some(write) = clause.effect {
                self.contract_footprint(id, &clause.expression, write)
            } else {
                self.contract_root(id, &clause.expression)
            };
            self.contract_position = None;
            let root = root?;
            self.specs.clauses.push(HirSpecClause {
                id,
                owner: HirSpecClauseOwner::Contract { contract, position },
                location: if clause.ensures {
                    HirSpecLocation::FunctionResult { function }
                } else {
                    HirSpecLocation::FunctionEntry { function }
                },
                root,
                span: clause.span,
            });
        }
        Ok(())
    }
    fn observation_root(
        &mut self,
        clause: HirSpecClauseId,
        expression: &AstLogicalExpression,
        span: ByteSpan,
    ) -> Result<HirSpecRoot, FrontendFailure> {
        let resource = match &expression.kind {
            L::Binary {
                operator: P::LogicalOr,
                left,
                right,
            } if self.loop_spec_context.is_some()
                && matches!(
                    right.kind,
                    L::ResourceRange { .. }
                        | L::InitializedRange { .. }
                        | L::Value(AstExpression {
                            kind: AstExpressionKind::Call { .. },
                            ..
                        })
                ) =>
            {
                let unless = self.logical_term(clause, left, 0)?;
                if self.specs.terms[unless.index()].ty != self.core_types.bool_ {
                    return Err(FrontendFailure::elaboration(
                        span,
                        "conditional invariant requires a Bool guard",
                    ));
                }
                let guard = self.spec_term(
                    clause,
                    self.core_types.bool_,
                    HirSpecTermKind::Not(unless),
                    left.span,
                );
                let HirSpecRoot::Assertion(body) =
                    self.observation_root(clause, right, right.span)?
                else {
                    return Err(FrontendFailure::unsupported(
                        span,
                        "conditional invariant requires a resource observation",
                    ));
                };
                Some(crate::SpecAssertionKind::Conditional { guard, body })
            }
            L::Value(value) => self.local_resource(clause, value)?,
            L::InitializedRange {
                pointer,
                start,
                end,
            }
            | L::ResourceRange {
                pointer,
                start,
                end,
                ..
            } => {
                if matches!(expression.kind, L::ResourceRange { .. })
                    && self.loop_spec_context.is_none()
                {
                    return Err(FrontendFailure::unsupported(
                        span,
                        "local permission assertions are not implemented",
                    ));
                }
                let builtin = match expression.kind {
                    L::ResourceRange { writable: true, .. } => "writable",
                    L::ResourceRange {
                        writable: false, ..
                    } => "readable",
                    _ => "initialized",
                };
                let (pointer, mut layout) =
                    self.resource_pointer(builtin, pointer, expression.span)?;
                if self.loop_spec_context.is_some()
                    && let Some(HirTypeKind::Array { element, .. }) =
                        self.type_definition(layout).map(|t| &t.kind)
                {
                    layout = *element;
                }
                let stride = self.initialized_stride(layout, expression.span)?;
                let start = self.logical_term(clause, start, 0)?;
                let end = self.logical_term(clause, end, 0)?;
                self.spec_words(start, end, expression.span)?;
                let start_bytes = self.spec_term(
                    clause,
                    self.specs.terms[start.index()].ty,
                    HirSpecTermKind::CheckedScale {
                        operand: start,
                        stride,
                    },
                    expression.span,
                );
                let end_bytes = self.spec_term(
                    clause,
                    self.specs.terms[end.index()].ty,
                    HirSpecTermKind::CheckedScale {
                        operand: end,
                        stride,
                    },
                    expression.span,
                );
                Some(if let L::ResourceRange { writable, .. } = expression.kind {
                    let memory = crate::SpecMemoryClaim {
                        pointer,
                        authority: pointer,
                        start_bytes,
                        end_bytes,
                        layout,
                        access: if writable {
                            crate::SpecAccess::Write
                        } else {
                            crate::SpecAccess::Read
                        },
                    };
                    if writable {
                        crate::SpecAssertionKind::Permission(memory)
                    } else {
                        crate::SpecAssertionKind::PointsTo {
                            memory,
                            value: None,
                        }
                    }
                } else {
                    crate::SpecAssertionKind::Initialized {
                        pointer,
                        start_bytes,
                        end_bytes,
                        layout,
                    }
                })
            }
            _ => None,
        };
        let root = if let Some(kind) = resource {
            let id = HirSpecAssertionId::new(self.specs.assertions.len() as u32);
            self.specs.assertions.push(HirSpecAssertion {
                id,
                clause,
                kind,
                span: expression.span,
            });
            HirSpecRoot::Assertion(id)
        } else {
            let root = self.logical_term(clause, expression, 0)?;
            if self.specs.terms[root.index()].ty != self.core_types.bool_ {
                return Err(FrontendFailure::elaboration(
                    expression.span,
                    "specification requires a boolean logical expression",
                ));
            }
            root.into()
        };
        Ok(root)
    }

    pub(super) fn spec_term(
        &mut self,
        clause: HirSpecClauseId,
        ty: HirTypeId,
        kind: HirSpecTermKind,
        span: ByteSpan,
    ) -> HirSpecTermId {
        let id = HirSpecTermId::new(self.specs.terms.len() as u32);
        self.specs.terms.push(HirSpecTerm {
            id,
            clause,
            ty,
            kind,
            span,
        });
        id
    }

    pub(super) fn logical_term(
        &mut self,
        clause: HirSpecClauseId,
        expression: &AstLogicalExpression,
        depth: usize,
    ) -> Result<HirSpecTermId, FrontendFailure> {
        let span = expression.span;
        if depth >= 128 {
            return Err(FrontendFailure::unsupported(
                span,
                "logical expression depth budget exceeded",
            ));
        }
        let (ty, kind) = match &expression.kind {
            L::InitializedRange { .. } | L::ResourceRange { .. } => {
                return Err(FrontendFailure::unsupported(
                    span,
                    "resource assertions cannot be operands of Bool connectives",
                ));
            }
            L::Value(value) => return self.local_spec_term(clause, value),
            L::Not(operand) => {
                let operand = self.logical_term(clause, operand, depth + 1)?;
                if self.specs.terms[operand.index()].ty != self.core_types.bool_ {
                    return Err(FrontendFailure::elaboration(
                        span,
                        "logical negation requires Bool",
                    ));
                }
                (self.core_types.bool_, HirSpecTermKind::Not(operand))
            }
            L::Binary {
                operator,
                left,
                right,
            } => {
                let unsuffixed = |e: &AstLogicalExpression| {
                    matches!(
                        &e.kind,
                        L::Value(AstExpression {
                            kind: AstExpressionKind::Integer {
                                explicit_u64: false,
                                explicit_usize: false,
                                ..
                            },
                            ..
                        })
                    )
                };
                let left_literal = unsuffixed(left);
                let right_literal = unsuffixed(right);
                let left = self.logical_term(clause, left, depth + 1)?;
                let right = self.logical_term(clause, right, depth + 1)?;
                if self.specs.terms[left.index()].ty != self.specs.terms[right.index()].ty
                    && self.spec_words(left, right, span).is_ok()
                {
                    if left_literal {
                        self.specs.terms[left.index()].ty = self.specs.terms[right.index()].ty;
                    } else if right_literal {
                        self.specs.terms[right.index()].ty = self.specs.terms[left.index()].ty;
                    }
                }
                let ty = self.specs.terms[left.index()].ty;
                if ty != self.specs.terms[right.index()].ty {
                    return Err(FrontendFailure::elaboration(
                        span,
                        "logical operands must have the same type",
                    ));
                }
                let boolean = self.core_types.bool_;
                match operator {
                    P::LogicalAnd | P::LogicalOr => {
                        if ty != boolean {
                            return Err(FrontendFailure::elaboration(
                                span,
                                "logical connective requires Bool operands",
                            ));
                        }
                        (
                            boolean,
                            if *operator == P::LogicalAnd {
                                HirSpecTermKind::And(vec![left, right])
                            } else {
                                HirSpecTermKind::Or(vec![left, right])
                            },
                        )
                    }
                    P::EqualEqual | P::NotEqual => {
                        let equality = HirSpecTermKind::Equal { left, right };
                        (
                            boolean,
                            if *operator == P::NotEqual {
                                let equal = self.spec_term(clause, boolean, equality, span);
                                HirSpecTermKind::Not(equal)
                            } else {
                                equality
                            },
                        )
                    }
                    _ => {
                        self.spec_words(left, right, span)?;
                        match operator {
                            P::Plus => (ty, HirSpecTermKind::CheckedAdd { left, right }),
                            P::Minus => (ty, HirSpecTermKind::CheckedSub { left, right }),
                            P::Star => {
                                let (operand, stride) = if let HirSpecTermKind::U64(stride) =
                                    self.specs.terms[right.index()].kind
                                {
                                    (left, stride)
                                } else if let HirSpecTermKind::U64(stride) =
                                    self.specs.terms[left.index()].kind
                                {
                                    (right, stride)
                                } else {
                                    return Err(FrontendFailure::unsupported(
                                        span,
                                        "logical multiplication requires a literal constant scale",
                                    ));
                                };
                                (ty, HirSpecTermKind::CheckedScale { operand, stride })
                            }
                            P::Less => (boolean, HirSpecTermKind::LessThan { left, right }),
                            P::LessEqual => (boolean, HirSpecTermKind::LessOrEqual { left, right }),
                            P::Greater => (
                                boolean,
                                HirSpecTermKind::LessThan {
                                    left: right,
                                    right: left,
                                },
                            ),
                            P::GreaterEqual => (
                                boolean,
                                HirSpecTermKind::LessOrEqual {
                                    left: right,
                                    right: left,
                                },
                            ),
                            _ => {
                                return Err(FrontendFailure::unsupported(
                                    span,
                                    "logical operator is not implemented",
                                ));
                            }
                        }
                    }
                }
            }
        };
        Ok(self.spec_term(clause, ty, kind, span))
    }

    fn local_resource(
        &mut self,
        clause: HirSpecClauseId,
        expression: &AstExpression,
    ) -> Result<Option<HirSpecAssertionKind>, FrontendFailure> {
        let AstExpressionKind::Call { callee, arguments } = &expression.kind else {
            return Ok(None);
        };
        if !matches!(callee.as_str(), "alive" | "initialized") {
            return Ok(None);
        }
        let [argument] = arguments.as_slice() else {
            return Err(FrontendFailure::unsupported(
                expression.span,
                "this resource assertion form is not implemented",
            ));
        };
        let (pointer, pointee) = self.resource_pointer(callee, argument, expression.span)?;
        Ok(Some(if callee == "alive" {
            crate::SpecAssertionKind::Alive(pointer)
        } else {
            let bytes = self.initialized_stride(pointee, argument.span)?;
            let start_bytes = self.spec_term(
                clause,
                self.core_types.u64_,
                HirSpecTermKind::U64(0),
                expression.span,
            );
            let end_bytes = self.spec_term(
                clause,
                self.core_types.u64_,
                HirSpecTermKind::U64(bytes),
                expression.span,
            );
            crate::SpecAssertionKind::Initialized {
                pointer,
                start_bytes,
                end_bytes,
                layout: pointee,
            }
        }))
    }

    fn resource_pointer(
        &self,
        callee: &str,
        argument: &AstExpression,
        span: ByteSpan,
    ) -> Result<(HirSpecSnapshot, HirTypeId), FrontendFailure> {
        if self.lookup(callee, span).is_ok()
            || self
                .function_names
                .contains_key(&self.graph.key(self.current_module, callee))
        {
            return Err(FrontendFailure::unsupported(
                span,
                "resource builtin is shadowed; user calls are not evaluated in Spec",
            ));
        }
        let name = match (&argument.kind, callee) {
            (AstExpressionKind::Place(place), "alive") if matches!(place.projections.as_slice(), [AstPlaceProjection::Field { name, .. }] if name == "region") => {
                &place.base
            }
            (AstExpressionKind::Name(name), "initialized" | "writable" | "readable") => name,
            _ => {
                return Err(FrontendFailure::unsupported(
                    argument.span,
                    "expected alive(pointer.region) or initialized(pointer)",
                ));
            }
        };
        let binding = self.lookup(name, argument.span)?;
        if matches!(callee, "writable" | "readable")
            && matches!(
                self.type_definition(binding.value.ty).map(|t| &t.kind),
                Some(HirTypeKind::RawPointer { .. })
            )
        {
            return Err(FrontendFailure::unsupported(
                argument.span,
                "a raw pointer does not carry readable/writable authority; use its owner or reference",
            ));
        }
        let pointee = self.pointee_type(binding.value.ty).ok_or_else(|| {
            FrontendFailure::elaboration(
                argument.span,
                "resource observation requires a pointer, owner or reference",
            )
        })?;
        let pointer = HirSpecSnapshot::Local {
            function: self.current_function.unwrap(),
            local: binding.local,
        };
        Ok((pointer, pointee))
    }

    pub(super) fn initialized_stride(
        &self,
        pointee: HirTypeId,
        span: ByteSpan,
    ) -> Result<u64, FrontendFailure> {
        if pointee == self.core_types.u64_ || pointee == self.core_types.usize_ {
            Ok(8)
        } else if pointee == self.core_types.bool_ {
            Ok(1)
        } else {
            Err(FrontendFailure::unsupported(
                span,
                "initialized observation currently supports Bool/U64 pointees",
            ))
        }
    }

    fn local_spec_term(
        &mut self,
        clause: HirSpecClauseId,
        expression: &AstExpression,
    ) -> Result<HirSpecTermId, FrontendFailure> {
        let span = expression.span;
        let (ty, kind) = match &expression.kind {
            AstExpressionKind::Integer {
                value,
                explicit_usize,
                ..
            } => (
                if *explicit_usize {
                    self.core_types.usize_
                } else {
                    self.core_types.u64_
                },
                HirSpecTermKind::U64(*value),
            ),
            AstExpressionKind::Bool(value) => {
                (self.core_types.bool_, HirSpecTermKind::Bool(*value))
            }
            AstExpressionKind::Name(name) => {
                if name == "result" {
                    if self.contract_position != Some(HirSpecContractPosition::Ensures)
                        || ![
                            self.core_types.bool_,
                            self.core_types.u64_,
                            self.core_types.usize_,
                        ]
                        .contains(&self.return_type)
                    {
                        return Err(FrontendFailure::unsupported(
                            span,
                            "result requires a scalar function postcondition",
                        ));
                    }
                    return Ok(self.spec_term(
                        clause,
                        self.return_type,
                        HirSpecTermKind::Snapshot(HirSpecSnapshot::Result {
                            function: self.current_function.unwrap(),
                        }),
                        span,
                    ));
                }
                let binding = self.lookup(name, span)?;
                if ![
                    self.core_types.bool_,
                    self.core_types.u64_,
                    self.core_types.usize_,
                ]
                .contains(&binding.value.ty)
                {
                    return Err(FrontendFailure::unsupported(
                        span,
                        "specification snapshots currently require Bool, U64 or 64-bit usize values",
                    ));
                }
                (
                    binding.value.ty,
                    HirSpecTermKind::Snapshot(match self.contract_position {
                        Some(HirSpecContractPosition::Ensures) => HirSpecSnapshot::EntryParameter {
                            function: self.current_function.unwrap(),
                            parameter: binding.local.get(),
                        },
                        None | Some(HirSpecContractPosition::Requires) => HirSpecSnapshot::Local {
                            function: self.current_function.unwrap(),
                            local: binding.local,
                        },
                    }),
                )
            }
            AstExpressionKind::Load { pointer } if self.contract_position.is_some() => {
                return self.contract_memory_term(clause, pointer, &[], false, span);
            }
            AstExpressionKind::Place(place) if self.contract_position.is_some() => {
                return self.contract_memory_term(
                    clause,
                    &place.base,
                    &place.projections,
                    false,
                    span,
                );
            }
            AstExpressionKind::Call { callee, arguments }
                if callee == "len" && self.contract_position.is_some() =>
            {
                return self.contract_length(clause, arguments, span);
            }
            AstExpressionKind::Call { callee, arguments } if callee == "old" => {
                if let Some(loop_id) = self.loop_spec_context {
                    let [
                        AstExpression {
                            kind: AstExpressionKind::Name(name),
                            ..
                        },
                    ] = arguments.as_slice()
                    else {
                        return Err(FrontendFailure::unsupported(
                            span,
                            "loop old requires one outer scalar local",
                        ));
                    };
                    let binding = self.lookup(name, span)?;
                    if !matches!(
                        self.type_definition(binding.value.ty).map(|t| &t.kind),
                        Some(
                            HirTypeKind::Bool
                                | HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize)
                        )
                    ) {
                        return Err(FrontendFailure::unsupported(
                            span,
                            "loop old cannot snapshot memory or permissions",
                        ));
                    }
                    return Ok(self.spec_term(
                        clause,
                        binding.value.ty,
                        HirSpecTermKind::Snapshot(HirSpecSnapshot::LoopEntry {
                            function: self.current_function.unwrap(),
                            loop_id,
                            local: binding.local,
                        }),
                        span,
                    ));
                }
                if self.contract_position == Some(HirSpecContractPosition::Ensures)
                    && let [
                        AstExpression {
                            kind: AstExpressionKind::Call { callee, arguments },
                            ..
                        },
                    ] = arguments.as_slice()
                    && callee == "len"
                    && matches!(arguments.as_slice(), [AstExpression { kind: AstExpressionKind::Name(name), .. }] if name != "result")
                {
                    return self.contract_length(clause, arguments, span);
                }
                if self.contract_position == Some(HirSpecContractPosition::Ensures)
                    && let [
                        AstExpression {
                            kind: AstExpressionKind::Load { pointer },
                            ..
                        },
                    ] = arguments.as_slice()
                {
                    return self.contract_memory_term(clause, pointer, &[], true, span);
                }
                if self.contract_position == Some(HirSpecContractPosition::Ensures)
                    && let [
                        AstExpression {
                            kind: AstExpressionKind::Place(place),
                            ..
                        },
                    ] = arguments.as_slice()
                {
                    return self.contract_memory_term(
                        clause,
                        &place.base,
                        &place.projections,
                        true,
                        span,
                    );
                }
                if self.contract_position != Some(HirSpecContractPosition::Ensures)
                    || !matches!(arguments.as_slice(), [AstExpression { kind: AstExpressionKind::Name(name), .. }] if name != "result")
                {
                    return Err(FrontendFailure::unsupported(
                        span,
                        "old requires one scalar input parameter in ensures",
                    ));
                }
                return self.local_spec_term(clause, &arguments[0]);
            }
            _ => {
                return Err(FrontendFailure::unsupported(
                    span,
                    "unsupported static assertion expression; calls, loads, allocations and borrows are not evaluated in Spec",
                ));
            }
        };
        Ok(self.spec_term(clause, ty, kind, span))
    }

    pub(super) fn spec_words(
        &self,
        left: HirSpecTermId,
        right: HirSpecTermId,
        span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if [left, right].iter().all(|id| {
            [self.core_types.u64_, self.core_types.usize_]
                .contains(&self.specs.terms[id.index()].ty)
        }) {
            Ok(())
        } else {
            Err(FrontendFailure::elaboration(
                span,
                "logical arithmetic requires U64 operands",
            ))
        }
    }

    fn contract_memory_term(
        &mut self,
        clause: HirSpecClauseId,
        name: &str,
        projections: &[crate::frontend::AstPlaceProjection],
        old: bool,
        span: ByteSpan,
    ) -> Result<HirSpecTermId, FrontendFailure> {
        let fail = || {
            FrontendFailure::unsupported(
                span,
                "contract memory observations require a scalar pointer parameter or result; old(result) is not defined",
            )
        };
        let (parameter, ty) = if name == "result" {
            if old || self.contract_position != Some(HirSpecContractPosition::Ensures) {
                return Err(fail());
            }
            (None, self.return_type)
        } else {
            let binding = self.lookup(name, span)?;
            (Some(binding.local.get()), binding.value.ty)
        };
        let pointee = match self.type_definition(ty).map(|ty| &ty.kind) {
            Some(HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. }) => *pointee,
            Some(HirTypeKind::Slice { .. }) => ty,
            _ => return Err(fail()),
        };
        use crate::frontend::AstPlaceProjection as A;
        use crate::{SpecMemoryIndex as I, SpecMemoryProjection as M};
        let (pointee, projection) = match projections {
            [] => (pointee, M::Cell),
            [A::Field { name, .. }] => {
                let field = self
                    .fields
                    .iter()
                    .find(|f| f.owner == pointee && f.name == *name)
                    .ok_or_else(fail)?;
                (field.ty, M::Field(field.id))
            }
            [A::Index { index, .. }] => {
                let element = match self.type_definition(pointee).map(|t| &t.kind) {
                    Some(
                        HirTypeKind::Array { element, .. } | HirTypeKind::Slice { element, .. },
                    ) => *element,
                    _ => return Err(fail()),
                };
                let index = match &index.kind {
                    AstExpressionKind::Integer { value, .. } => I::Constant(*value),
                    AstExpressionKind::Name(name) => {
                        let binding = self.lookup(name, index.span)?;
                        if binding.value.ty != self.core_types.usize_ {
                            return Err(fail());
                        }
                        I::Parameter(binding.local.get())
                    }
                    _ => return Err(fail()),
                };
                (element, M::Index(index))
            }
            _ => return Err(fail()),
        };
        if ![
            self.core_types.bool_,
            self.core_types.u64_,
            self.core_types.usize_,
        ]
        .contains(&pointee)
        {
            return Err(fail());
        }
        Ok(self.spec_term(
            clause,
            pointee,
            HirSpecTermKind::Snapshot(HirSpecSnapshot::Memory {
                function: self.current_function.unwrap(),
                parameter,
                old,
                projection,
            }),
            span,
        ))
    }
}
