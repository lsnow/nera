//! Canonical, immutable identities for verifier findings.

use crate::{
    ByteSpan, ResolvedVirUnit, VirContractPosition, VirLocation, VirOriginId, VirSourceId,
    VirSpecClauseId, VirSpecClauseOwner, VirSpecLocation, VirSpecProveId, VirTrustEntryId,
};

/// The concrete specification entity responsible for a finding.
///
/// A logical location is deliberately insufficient: several clauses and
/// proof entities may share the same function entry, result, or runtime point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VerifierSpecEntity {
    Clause(VirSpecClauseId),
    Prove(VirSpecProveId),
    TrustEntry(VirTrustEntryId),
}

/// Stable location identity for every published verifier result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VerifierFindingSite {
    Runtime(VirLocation),
    Spec {
        location: VirSpecLocation,
        entity: VerifierSpecEntity,
        /// Concrete runtime occurrence when one logical entity is checked at
        /// several program points, such as an `ensures` at multiple returns.
        occurrence: Option<VirLocation>,
    },
}

impl VerifierFindingSite {
    #[must_use]
    pub const fn function(self) -> crate::VirFunctionId {
        match self {
            Self::Runtime(location) => location.function(),
            Self::Spec { location, .. } => location.function(),
        }
    }
}

/// Canonical source identity resolved from exactly one validated VIR source map.
///
/// A postcondition clause may have several concrete return occurrences; that
/// occurrence is part of its ordered site so two checks never collapse merely
/// because they refer to the same clause definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VerifierFinding {
    site: VerifierFindingSite,
    origin: VirOriginId,
    source: VirSourceId,
    source_span: ByteSpan,
}

impl VerifierFinding {
    pub(super) fn loop_invariant(
        unit: &ResolvedVirUnit<'_>,
        invariant: &crate::VirSpecLoopInvariant,
        source_block: crate::VirBlockId,
    ) -> Option<Self> {
        let boundary = invariant.boundary.as_ref()?;
        if !boundary
            .entries
            .iter()
            .chain(&boundary.back_edges)
            .any(|e| e.source == source_block)
        {
            return None;
        }
        let source = unit
            .as_unit()
            .source_map
            .source_span_for_origin(invariant.origin)?;
        Some(Self {
            site: VerifierFindingSite::Spec {
                location: invariant.location,
                entity: VerifierSpecEntity::Clause(invariant.clause),
                occurrence: Some(VirLocation::Terminator {
                    function: invariant.function,
                    block: source_block,
                }),
            },
            origin: invariant.origin,
            source: source.source,
            source_span: source.span,
        })
    }
    #[must_use]
    pub const fn site(self) -> VerifierFindingSite {
        self.site
    }

    #[must_use]
    pub const fn origin(self) -> VirOriginId {
        self.origin
    }

    #[must_use]
    pub const fn source(self) -> VirSourceId {
        self.source
    }

    #[must_use]
    pub const fn source_span(self) -> ByteSpan {
        self.source_span
    }

    #[must_use]
    pub const fn source_position(self) -> crate::VirSourceSpan {
        crate::VirSourceSpan {
            source: self.source,
            span: self.source_span,
        }
    }

    #[must_use]
    pub const fn occurrence(self) -> Option<VirLocation> {
        match self.site {
            VerifierFindingSite::Runtime(_) => None,
            VerifierFindingSite::Spec { occurrence, .. } => occurrence,
        }
    }

    pub(super) fn runtime(
        unit: &ResolvedVirUnit<'_>,
        location: VirLocation,
        cached_span: ByteSpan,
    ) -> Option<Self> {
        let source_map = &unit.as_unit().source_map;
        let origin = source_map.origin_at(location)?.id;
        let resolved = source_map.source_span_for_origin(origin)?;
        (resolved.span == cached_span).then_some(Self {
            site: VerifierFindingSite::Runtime(location),
            origin,
            source: resolved.source,
            source_span: resolved.span,
        })
    }

    pub(super) fn clause(
        unit: &ResolvedVirUnit<'_>,
        clause_id: VirSpecClauseId,
        occurrence: Option<VirLocation>,
    ) -> Option<Self> {
        let clause = unit.as_unit().specs.clause(clause_id)?;
        if let (
            VirSpecClauseOwner::LoopInvariant(id),
            Some(VirLocation::Terminator { function, block }),
        ) = (clause.owner, occurrence)
        {
            let invariant = unit
                .as_unit()
                .specs
                .loop_invariants()
                .get(id.get() as usize)?;
            return (function == invariant.function)
                .then(|| Self::loop_invariant(unit, invariant, block))
                .flatten();
        }
        if occurrence.is_some()
            && (!matches!(
                clause.owner,
                VirSpecClauseOwner::Contract {
                    position: VirContractPosition::Ensures,
                    ..
                }
            ) || !matches!(clause.location, VirSpecLocation::FunctionResult { .. }))
        {
            return None;
        }
        let origin = clause.origin.origin();
        Self::spec(
            unit,
            clause.location,
            VerifierSpecEntity::Clause(clause_id),
            origin,
            occurrence,
        )
    }

    pub(super) fn prove(unit: &ResolvedVirUnit<'_>, prove_id: VirSpecProveId) -> Option<Self> {
        let prove = unit
            .as_unit()
            .specs
            .proves()
            .get(prove_id.get() as usize)
            .filter(|prove| prove.id == prove_id)?;
        let clause = unit.as_unit().specs.clause(prove.clause)?;
        matches!(clause.owner, VirSpecClauseOwner::Prove(owner) if owner == prove_id)
            .then_some(())?;
        (clause.location == prove.location).then_some(())?;
        Self::spec(
            unit,
            prove.location,
            VerifierSpecEntity::Prove(prove_id),
            prove.origin,
            None,
        )
    }

    pub(super) fn trust_entry(
        unit: &ResolvedVirUnit<'_>,
        entry_id: VirTrustEntryId,
    ) -> Option<Self> {
        let entry = unit
            .as_unit()
            .specs
            .trust_entries()
            .get(entry_id.get() as usize)
            .filter(|entry| entry.id == entry_id)?;
        let clause = unit.as_unit().specs.clause(entry.clause)?;
        matches!(clause.owner, VirSpecClauseOwner::TrustEntry(owner) if owner == entry_id)
            .then_some(())?;
        (clause.location == entry.scope.location()).then_some(())?;
        Self::spec(
            unit,
            entry.scope.location(),
            VerifierSpecEntity::TrustEntry(entry_id),
            entry.origin,
            None,
        )
    }

    fn spec(
        unit: &ResolvedVirUnit<'_>,
        location: VirSpecLocation,
        entity: VerifierSpecEntity,
        origin: VirOriginId,
        occurrence: Option<VirLocation>,
    ) -> Option<Self> {
        let resolved = unit.as_unit().source_map.source_span_for_origin(origin)?;
        if let Some(runtime) = occurrence {
            let VirLocation::Terminator { function, block } = runtime else {
                return None;
            };
            if function != location.function()
                || !unit
                    .as_unit()
                    .runtime
                    .functions
                    .iter()
                    .find(|candidate| candidate.id == function)
                    .and_then(|function| {
                        function
                            .blocks
                            .iter()
                            .find(|candidate| candidate.id == block)
                    })
                    .is_some_and(|block| {
                        matches!(
                            block.terminator.terminator,
                            crate::VirTerminator::Return { .. }
                        )
                    })
            {
                return None;
            }
        }
        Some(Self {
            site: VerifierFindingSite::Spec {
                location,
                entity,
                occurrence,
            },
            origin,
            source: resolved.source,
            source_span: resolved.span,
        })
    }
}
