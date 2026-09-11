//! Inferred borrow signatures use parameter-owned anonymous regions, not generic instances.
//! Source relations close result regions without exposing region variables in surface syntax.
use super::*;
use crate::frontend::AstFunction;

/// Private construction state, never a public/validated HIR signature.
pub(super) struct SignatureDraft {
    pub(super) owner: HirFunctionId,
    parameters: Vec<HirTypeId>,
    result: PendingResult,
}

impl SignatureDraft {
    pub(super) fn parameter_type(&self, index: u32) -> Option<HirTypeId> {
        self.parameters.get(index as usize).copied()
    }

    pub(super) fn borrow_candidates(&self) -> Option<&[u32]> {
        match &self.result {
            PendingResult::Value(_) => None,
            PendingResult::Borrow { candidates, .. } => Some(candidates),
        }
    }

    pub(super) fn result_is_mutable(&self) -> Option<bool> {
        match self.result {
            PendingResult::Borrow { mutable, .. } => Some(mutable),
            PendingResult::Value(_) => None,
        }
    }
}

enum PendingResult {
    Value(HirTypeId),
    Borrow {
        pointee: HirTypeId,
        mutable: bool,
        candidates: Vec<u32>,
    },
}

type ClosedBorrowSignature = (
    Vec<HirTypeId>,
    HirTypeId,
    Option<crate::BorrowResultRelation>,
    Vec<crate::BorrowResultAlternative>,
);

impl Elaborator {
    pub(super) fn draft_borrow_signature(
        &mut self,
        function: &AstFunction,
        owner: HirFunctionId,
    ) -> Result<SignatureDraft, FrontendFailure> {
        if !function.generics.is_empty() {
            return Err(FrontendFailure::elaboration(
                function.span,
                "unresolved generic binder reached typed HIR",
            ));
        }
        let mut parameters = Vec::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let ty = self.parameter_type(&parameter.ty, owner, index, parameter.span)?;
            parameters.push(ty);
        }
        let result = match &function.return_type {
            AstType::Reference { pointee, mutable } => PendingResult::Borrow {
                pointee: self.reference_pointee(pointee, *mutable, function.span)?,
                mutable: *mutable,
                candidates: parameters
                    .iter()
                    .enumerate()
                    .filter_map(|(index, ty)| self.reference_region(*ty).map(|_| index as u32))
                    .collect(),
            },
            other => PendingResult::Value(self.signature_type(other, function.span)?),
        };
        Ok(SignatureDraft {
            owner,
            parameters,
            result,
        })
    }

    /// Closes the current bounded whole-view capability. The draft
    /// separates the candidate set from the resolved type/region; subsequent
    /// body inference can refine it without inventing a provisional region.
    pub(super) fn close_borrow_signature(
        &mut self,
        function: &AstFunction,
        draft: SignatureDraft,
        inferred_source: Option<super::borrow_inference::InferredBorrowSource>,
    ) -> Result<ClosedBorrowSignature, FrontendFailure> {
        let (result, relation, alternatives) = match draft.result {
            PendingResult::Value(ty) => (ty, None, Vec::new()),
            PendingResult::Borrow {
                pointee: expected,
                mutable,
                candidates,
            } => {
                let inferred_source = inferred_source.or(match candidates.as_slice() {
                    [index] => Some(
                        super::borrow_inference::InferredBorrowSource::Unconditional(
                            crate::BorrowResultRelation::whole(
                                *index,
                                if mutable {
                                    crate::BorrowAccess::Mutable
                                } else {
                                    crate::BorrowAccess::Shared
                                },
                            ),
                        ),
                    ),
                    _ => None,
                }).ok_or_else(|| {
                        FrontendFailure::unsupported(
                            function.span,
                            "returned reference source could not be reduced to a supported input relation",
                        )
                    })?;
                match inferred_source {
                    super::borrow_inference::InferredBorrowSource::Unconditional(relation) => {
                        let index = relation.parameter;
                        if !candidates.contains(&index) {
                            return Err(FrontendFailure::unsupported(
                                function.span,
                                "returned reference source is not a direct reference parameter",
                            ));
                        }
                        let parameter = draft.parameters[index as usize];
                        let access = if mutable {
                            crate::BorrowAccess::Mutable
                        } else {
                            crate::BorrowAccess::Shared
                        };
                        if relation.access != access {
                            return Err(FrontendFailure::unsupported(
                                function.span,
                                "returned reference access does not match its inferred projection",
                            ));
                        }
                        let HirTypeKind::Reference {
                            pointee: source_pointee,
                            mutability: source_mutability,
                            region: source_region,
                        } = self.types[parameter.index()].kind
                        else {
                            return Err(FrontendFailure::unsupported(
                                function.span,
                                "returned reference source is not a reference parameter",
                            ));
                        };
                        if mutable && source_mutability != HirMutability::Mutable {
                            return Err(FrontendFailure::unsupported(
                                function.span,
                                "a shared source cannot produce a mutable returned projection",
                            ));
                        }
                        let result = if relation.projection == crate::BorrowProjection::Whole {
                            if source_pointee != expected
                                || (source_mutability == HirMutability::Mutable) != mutable
                            {
                                return Err(FrontendFailure::unsupported(
                                    function.span,
                                    "whole returned references must preserve pointee and mutability",
                                ));
                            }
                            parameter
                        } else {
                            let region = HirRegionId::new(
                                u32::try_from(self.regions.len()).map_err(|_| {
                                    FrontendFailure::elaboration(function.span, "too many regions")
                                })?,
                            );
                            self.regions.push(HirRegion {
                                id: region,
                                owner: HirRegionOwner::Function(draft.owner),
                                origin: HirRegionOrigin::Result,
                                span: function.span,
                            });
                            self.region_constraints.push(HirRegionConstraint {
                                id: HirRegionConstraintId::new(self.region_constraints.len() as u32),
                                owner: draft.owner,
                                subregion: region,
                                superregion: source_region,
                                span: function.span,
                            });
                            self.intern_reference_type(
                                expected,
                                if mutable {
                                    HirMutability::Mutable
                                } else {
                                    HirMutability::Const
                                },
                                region,
                                function.span,
                            )?
                        };
                        (result, Some(relation), Vec::new())
                    }
                    super::borrow_inference::InferredBorrowSource::Conditional(alternatives) => {
                        for alternative in &alternatives {
                            let parameter = draft
                                .parameters
                                .get(alternative.relation.parameter as usize)
                                .copied()
                                .ok_or_else(|| {
                                    FrontendFailure::unsupported(
                                        function.span,
                                        "conditional returned reference source is not a parameter",
                                    )
                                })?;
                            if !matches!(self.types[parameter.index()].kind, HirTypeKind::Reference { pointee, mutability, .. } if pointee == expected && (mutability == HirMutability::Mutable) == mutable)
                            {
                                return Err(FrontendFailure::unsupported(
                                    function.span,
                                    "conditional returned references must preserve one common whole-view type",
                                ));
                            }
                        }
                        let region =
                            HirRegionId::new(u32::try_from(self.regions.len()).map_err(|_| {
                                FrontendFailure::elaboration(function.span, "too many regions")
                            })?);
                        self.regions.push(HirRegion {
                            id: region,
                            owner: HirRegionOwner::Function(draft.owner),
                            origin: HirRegionOrigin::Result,
                            span: function.span,
                        });
                        for source in alternatives
                            .iter()
                            .map(|a| a.relation.parameter)
                            .collect::<BTreeSet<_>>()
                        {
                            let superregion = self
                                .reference_region(draft.parameters[source as usize])
                                .ok_or_else(|| {
                                    FrontendFailure::unsupported(
                                        function.span,
                                        "conditional borrow source is not a reference",
                                    )
                                })?;
                            self.region_constraints.push(HirRegionConstraint { id: HirRegionConstraintId::new(self.region_constraints.len() as u32), owner: draft.owner, subregion: region, superregion, span: function.span });
                        }
                        let result = self.intern_reference_type(
                            expected,
                            if mutable {
                                HirMutability::Mutable
                            } else {
                                HirMutability::Const
                            },
                            region,
                            function.span,
                        )?;
                        (result, None, alternatives)
                    }
                }
            }
        };
        Ok((draft.parameters, result, relation, alternatives))
    }

    pub(super) fn reference_region(&self, ty: HirTypeId) -> Option<HirRegionId> {
        match self.types[ty.index()].kind {
            HirTypeKind::Reference { region, .. } => Some(region),
            _ => None,
        }
    }

    pub(super) fn region_contains(
        &self,
        owner: HirFunctionId,
        sub: HirRegionId,
        sup: HirRegionId,
    ) -> bool {
        let mut pending = vec![sub];
        let mut seen = BTreeSet::new();
        while let Some(region) = pending.pop() {
            if region == sup {
                return true;
            }
            if seen.insert(region) {
                pending.extend(
                    self.region_constraints
                        .iter()
                        .filter(|c| c.owner == owner && c.subregion == region)
                        .map(|c| c.superregion),
                );
            }
        }
        false
    }

    pub(super) fn check_call_region_constraints(
        &self,
        declaration: &FunctionDeclaration,
        arguments: &[HirExpression],
        span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let substitution: BTreeMap<_, _> = declaration
            .signature
            .parameters
            .iter()
            .zip(arguments)
            .filter_map(|(p, a)| Some((self.reference_region(*p)?, self.reference_region(a.ty)?)))
            .collect();
        let owner = self.current_function.expect("call inside a function");
        for constraint in self
            .region_constraints
            .iter()
            .filter(|c| c.owner == declaration.id)
        {
            // Local reborrow edges in an already elaborated body are not signature requirements.
            let (Some(sub), Some(sup)) = (
                substitution.get(&constraint.subregion),
                substitution.get(&constraint.superregion),
            ) else {
                continue;
            };
            if !self.region_contains(owner, *sub, *sup) {
                return Err(FrontendFailure::elaboration(
                    span,
                    "call region requirement is not established by caller regions",
                ));
            }
        }
        Ok(())
    }
}
