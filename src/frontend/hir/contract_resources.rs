//! Source resource contracts refine typed inputs; they never execute a borrow.
use super::*;
use crate::frontend::{AstLogicalExpression, AstLogicalExpressionKind as L};
use crate::{SpecAccess, SpecAssertionKind as A, SpecMemoryClaim};

impl Elaborator {
    pub(super) fn contract_root(
        &mut self,
        clause: HirSpecClauseId,
        expression: &AstLogicalExpression,
    ) -> Result<HirSpecRoot, FrontendFailure> {
        let span = expression.span;
        let builtin = match &expression.kind {
            L::ResourceRange { writable, .. } => {
                Some(if *writable { "writable" } else { "readable" })
            }
            L::InitializedRange { .. } => Some("initialized"),
            L::Value(AstExpression {
                kind: AstExpressionKind::Call { callee, .. },
                ..
            }) if matches!(callee.as_str(), "initialized" | "disjoint") => Some(callee.as_str()),
            _ => None,
        };
        if let Some(name) = builtin {
            self.contract_builtin_available(name, span)?;
        }
        let kind = match &expression.kind {
            L::Value(AstExpression {
                kind: AstExpressionKind::Call { callee, arguments },
                ..
            }) if callee == "disjoint" => {
                let [left, right] = arguments.as_slice() else {
                    return Err(FrontendFailure::unsupported(
                        span,
                        "disjoint requires two explicit Place ranges",
                    ));
                };
                Some(A::Disjoint {
                    left: self.contract_range(clause, left)?,
                    right: self.contract_range(clause, right)?,
                })
            }
            L::ResourceRange {
                pointer,
                start,
                end,
                ..
            }
            | L::InitializedRange {
                pointer,
                start,
                end,
            } => {
                let writable = matches!(&expression.kind, L::ResourceRange { writable: true, .. });
                let (pointer, layout) = self.contract_resource_pointer(pointer)?;
                let stride = self.initialized_stride(layout, span)?;
                let a = self.logical_term(clause, start, 0)?;
                let b = self.logical_term(clause, end, 0)?;
                self.spec_words(a, b, span)?;
                let start_bytes = self.spec_term(
                    clause,
                    self.specs.terms[a.index()].ty,
                    HirSpecTermKind::CheckedScale { operand: a, stride },
                    span,
                );
                let end_bytes = self.spec_term(
                    clause,
                    self.specs.terms[b.index()].ty,
                    HirSpecTermKind::CheckedScale { operand: b, stride },
                    span,
                );
                if matches!(expression.kind, L::InitializedRange { .. }) {
                    Some(A::Initialized {
                        pointer,
                        layout,
                        start_bytes,
                        end_bytes,
                    })
                } else {
                    let memory = SpecMemoryClaim {
                        pointer,
                        authority: pointer,
                        layout,
                        start_bytes,
                        end_bytes,
                        access: if writable {
                            SpecAccess::Write
                        } else {
                            SpecAccess::Read
                        },
                    };
                    Some(if writable {
                        A::Permission(memory)
                    } else {
                        A::PointsTo {
                            memory,
                            value: None,
                        }
                    })
                }
            }
            L::Value(AstExpression {
                kind: AstExpressionKind::Call { callee, arguments },
                ..
            }) if callee == "initialized" => {
                let [argument] = arguments.as_slice() else {
                    return Err(FrontendFailure::unsupported(
                        span,
                        "initialized requires one pointer or an explicit range",
                    ));
                };
                let (pointer, layout) = self.contract_resource_pointer(argument)?;
                let width = self.initialized_stride(layout, span)?;
                let start_bytes =
                    self.spec_term(clause, self.core_types.u64_, HirSpecTermKind::U64(0), span);
                let end_bytes = self.spec_term(
                    clause,
                    self.core_types.u64_,
                    HirSpecTermKind::U64(width),
                    span,
                );
                Some(A::Initialized {
                    pointer,
                    layout,
                    start_bytes,
                    end_bytes,
                })
            }
            _ => None,
        };
        if let Some(kind) = kind {
            let id = HirSpecAssertionId::new(self.specs.assertions.len() as u32);
            self.specs.assertions.push(HirSpecAssertion {
                id,
                clause,
                kind,
                span,
            });
            Ok(HirSpecRoot::Assertion(id))
        } else {
            let root = self.logical_term(clause, expression, 0)?;
            if self.specs.terms[root.index()].ty != self.core_types.bool_ {
                return Err(FrontendFailure::elaboration(
                    span,
                    "function contract requires Bool or a standalone resource clause",
                ));
            }
            Ok(root.into())
        }
    }

    pub(super) fn contract_footprint(
        &mut self,
        clause: HirSpecClauseId,
        expression: &AstLogicalExpression,
        write: bool,
    ) -> Result<HirSpecRoot, FrontendFailure> {
        let range = match &expression.kind {
            L::Value(AstExpression {
                kind: AstExpressionKind::Unit,
                ..
            }) => None,
            L::Value(AstExpression {
                kind: AstExpressionKind::Load { pointer },
                ..
            }) => {
                let argument = AstExpression {
                    kind: AstExpressionKind::Name(pointer.clone()),
                    span: expression.span,
                };
                let (pointer, layout) = self.contract_resource_pointer(&argument)?;
                let width = self.initialized_stride(layout, expression.span)?;
                let start_bytes = self.spec_term(
                    clause,
                    self.core_types.u64_,
                    HirSpecTermKind::U64(0),
                    expression.span,
                );
                let end_bytes = self.spec_term(
                    clause,
                    self.core_types.u64_,
                    HirSpecTermKind::U64(width),
                    expression.span,
                );
                Some(crate::SpecMemoryRange {
                    pointer,
                    layout,
                    start_bytes,
                    end_bytes,
                })
            }
            L::Value(value) => Some(self.contract_range(clause, value)?),
            _ => {
                return Err(FrontendFailure::unsupported(
                    expression.span,
                    "effect requires () or p[start..end]",
                ));
            }
        };
        let id = HirSpecAssertionId::new(self.specs.assertions.len() as u32);
        self.specs.assertions.push(HirSpecAssertion {
            id,
            clause,
            kind: crate::SpecAssertionKind::Footprint { write, range },
            span: expression.span,
        });
        Ok(HirSpecRoot::Assertion(id))
    }

    fn contract_range(
        &mut self,
        clause: HirSpecClauseId,
        expression: &AstExpression,
    ) -> Result<crate::SpecMemoryRange<HirSpecSnapshot, HirSpecTermId, HirTypeId>, FrontendFailure>
    {
        let fail = || {
            FrontendFailure::unsupported(
                expression.span,
                "disjoint requires p[start..end] with explicit endpoints",
            )
        };
        let AstExpressionKind::Place(place) = &expression.kind else {
            return Err(fail());
        };
        let [
            AstPlaceProjection::Slice {
                start: Some(start),
                end: Some(end),
                ..
            },
        ] = place.projections.as_slice()
        else {
            return Err(fail());
        };
        let argument = AstExpression {
            span: place.span,
            kind: AstExpressionKind::Name(place.base.clone()),
        };
        let (pointer, layout) = self.contract_resource_pointer(&argument)?;
        let stride = self.initialized_stride(layout, expression.span)?;
        let a = self.logical_term(
            clause,
            &AstLogicalExpression {
                span: start.span,
                kind: L::Value((**start).clone()),
            },
            0,
        )?;
        let b = self.logical_term(
            clause,
            &AstLogicalExpression {
                span: end.span,
                kind: L::Value((**end).clone()),
            },
            0,
        )?;
        self.spec_words(a, b, expression.span)?;
        let start_bytes = self.spec_term(
            clause,
            self.specs.terms[a.index()].ty,
            HirSpecTermKind::CheckedScale { operand: a, stride },
            start.span,
        );
        let end_bytes = self.spec_term(
            clause,
            self.specs.terms[b.index()].ty,
            HirSpecTermKind::CheckedScale { operand: b, stride },
            end.span,
        );
        Ok(crate::SpecMemoryRange {
            pointer,
            start_bytes,
            end_bytes,
            layout,
        })
    }

    fn contract_resource_pointer(
        &self,
        argument: &AstExpression,
    ) -> Result<(HirSpecSnapshot, HirTypeId), FrontendFailure> {
        let fail = || {
            FrontendFailure::unsupported(
                argument.span,
                "resource contract requires an Own/reference/slice parameter or result",
            )
        };
        let AstExpressionKind::Name(name) = &argument.kind else {
            return Err(fail());
        };
        let function = self.current_function.unwrap();
        let (snapshot, ty) = if name == "result" {
            if self.contract_position != Some(HirSpecContractPosition::Ensures) {
                return Err(fail());
            }
            (HirSpecSnapshot::Result { function }, self.return_type)
        } else {
            let binding = self.lookup(name, argument.span)?;
            (
                HirSpecSnapshot::Local {
                    function,
                    local: binding.local,
                },
                binding.value.ty,
            )
        };
        let element = match self.type_definition(ty).map(|t| &t.kind) {
            Some(HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. }) => *pointee,
            Some(HirTypeKind::Slice { element, .. }) => *element,
            _ => return Err(fail()),
        };
        let element = match self.type_definition(element).map(|t| &t.kind) {
            Some(HirTypeKind::Slice { element, .. }) => *element,
            _ => element,
        };
        self.initialized_stride(element, argument.span)?;
        Ok((snapshot, element))
    }

    pub(super) fn contract_length(
        &mut self,
        clause: HirSpecClauseId,
        arguments: &[AstExpression],
        span: ByteSpan,
    ) -> Result<HirSpecTermId, FrontendFailure> {
        self.contract_builtin_available("len", span)?;
        let fail = || {
            FrontendFailure::unsupported(
                span,
                "len in a contract requires one slice parameter or result",
            )
        };
        let [
            AstExpression {
                kind: AstExpressionKind::Name(name),
                ..
            },
        ] = arguments
        else {
            return Err(fail());
        };
        let (parameter, ty) = if name == "result" {
            if self.contract_position != Some(HirSpecContractPosition::Ensures) {
                return Err(fail());
            }
            (None, self.return_type)
        } else {
            let binding = self.lookup(name, span)?;
            (Some(binding.local.get()), binding.value.ty)
        };
        let ty = match self.type_definition(ty).map(|t| &t.kind) {
            Some(HirTypeKind::Reference { pointee, .. }) => *pointee,
            _ => ty,
        };
        if !matches!(
            self.type_definition(ty).map(|t| &t.kind),
            Some(HirTypeKind::Slice { .. })
        ) {
            return Err(fail());
        }
        Ok(self.spec_term(
            clause,
            self.core_types.usize_,
            HirSpecTermKind::Snapshot(HirSpecSnapshot::Length {
                function: self.current_function.unwrap(),
                parameter,
                entry: parameter.is_some()
                    && self.contract_position == Some(HirSpecContractPosition::Ensures),
            }),
            span,
        ))
    }

    fn contract_builtin_available(
        &self,
        name: &str,
        span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if self.lookup(name, span).is_ok()
            || self
                .function_names
                .contains_key(&self.graph.key(self.current_module, name))
        {
            return Err(FrontendFailure::unsupported(
                span,
                "resource builtin is shadowed; user calls are not evaluated in Spec",
            ));
        }
        Ok(())
    }
}
