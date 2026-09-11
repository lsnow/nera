//! Read-only, instruction/case-bound resource observations. Never proof inputs.
use std::collections::BTreeSet;

use super::relation::audit::SourceIndex;
use crate::{
    AbstractAllocationId, AbstractPointer, AbstractProvenance, AbstractValue, CfgAnalysisConfig,
    LivenessState, OwnershipState, PathCondition, ResourceObligation, ResourceObligationKind,
    ResourceState, VerifierFinding, VirInstruction, VirValueId,
};

pub const PROVENANCE_OBSERVATION_VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointerObservation {
    pub value: VirValueId,
    pub before: Option<AbstractPointer>,
    pub after: Option<AbstractPointer>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InstanceFact {
    pub size_bytes: u64,
    pub liveness: LivenessState,
    pub ownership: OwnershipState,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstanceObservation {
    pub allocation: AbstractAllocationId,
    pub before: Option<InstanceFact>,
    pub after: Option<InstanceFact>,
}

/// The containing instruction's obligations retain their original ordinals.
/// query_ordinals refer to relation_queries with this finding/case and no edge.
/// Numeric witnesses remain in that journal, not promoted to resource proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenanceEvidence {
    pub version: u32,
    pub finding: VerifierFinding,
    pub config: CfgAnalysisConfig,
    pub case_ordinal: usize,
    pub guard: PathCondition,
    pub instruction: VirInstruction,
    pub sources: Vec<VerifierFinding>,
    pub sources_truncated: bool,
    pub pointers: Vec<PointerObservation>,
    pub instances: Vec<InstanceObservation>,
    pub obligations: Vec<ResourceObligation>,
    pub query_ordinals: Vec<usize>,
}

/// Classification is obligation-local. Unknown arithmetic at the same site
/// is not automatically the cause of a failed resource obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProvenanceIssue {
    UnknownOrigin,
    InstanceRelation,
    DifferentInstances,
    InactiveInstance,
    ObjectBoundary,
    MissingDomainPath,
    OnePastAccess,
    MissingPermission,
    MissingInitialization,
    PrecisionLimit,
    UnsupportedOperation,
}

impl ProvenanceEvidence {
    pub(crate) fn weight(&self) -> usize {
        1usize
            .saturating_add(self.pointers.len())
            .saturating_add(self.instances.len())
            .saturating_add(self.obligations.len())
            .saturating_add(self.query_ordinals.len())
    }
    #[must_use]
    pub fn issue(&self, obligation: ResourceObligation) -> Option<ProvenanceIssue> {
        use ProvenanceIssue as I;
        use ResourceObligationKind as K;
        if obligation.is_proven() {
            return None;
        }
        Some(match obligation.kind() {
            K::PointerProvenanceKnown { .. } => I::UnknownOrigin,
            K::PointerSameInstance { left, right } => {
                let source = |id| {
                    self.pointers
                        .iter()
                        .find(|p| p.value == id)
                        .and_then(|p| p.before)
                        .map(|p| p.provenance())
                };
                match (source(left), source(right)) {
                    (Some(AbstractProvenance::Known(a)), Some(AbstractProvenance::Known(b)))
                        if a != b =>
                    {
                        I::DifferentInstances
                    }
                    _ => I::InstanceRelation,
                }
            }
            K::AllocationLive { .. } | K::ObjectAllocationLive { .. } => I::InactiveInstance,
            K::PointerCompatibleDomain { .. } => {
                if self
                    .pointers
                    .iter()
                    .any(|p| p.before.is_some_and(|p| p.paths().domain.is_none()))
                {
                    I::MissingDomainPath
                } else {
                    I::ObjectBoundary
                }
            }
            K::PointerDomainContains { .. }
            | K::AccessWithinBounds { .. }
            | K::ObjectWithinBounds { .. } => {
                if self
                    .pointers
                    .iter()
                    .any(|p| p.before.is_some_and(|p| one_past(p, &self.instances)))
                    && matches!(
                        self.instruction,
                        VirInstruction::Load { .. }
                            | VirInstruction::Write { .. }
                            | VirInstruction::Store { .. }
                            | VirInstruction::Initialize { .. }
                    )
                {
                    I::OnePastAccess
                } else {
                    I::ObjectBoundary
                }
            }
            K::PermissionAvailable { .. }
            | K::PermissionMatchesAllocation { .. }
            | K::PermissionCoversAccess { .. }
            | K::PermissionWritable { .. }
            | K::PermissionCanFree { .. }
            | K::PermissionCoversAllocation { .. } => I::MissingPermission,
            K::MemoryInitialized { .. } | K::ObjectValueBytesInitialized { .. } => {
                I::MissingInitialization
            }
            K::AllocationInstanceFresh { .. }
            | K::LoanPairQueriesWithinBudget { .. }
            | K::ObjectStateWithinBudget { .. } => I::PrecisionLimit,
            K::ObjectMoveSupported { .. } | K::ObjectBuiltinDroppable { .. } => {
                I::UnsupportedOperation
            }
            _ => return None,
        })
    }
}

fn one_past(pointer: AbstractPointer, instances: &[InstanceObservation]) -> bool {
    let Some(offset) = pointer.offset_bytes().exact_value() else {
        return false;
    };
    match pointer.domain() {
        crate::VirPointerDomain::Restricted(range) => range
            .bounds()
            .is_some_and(|(_, end)| end == crate::SymbolicRangeBound::constant(offset)),
        crate::VirPointerDomain::Allocation => instances.iter().any(|i| {
            pointer.provenance() == AbstractProvenance::Known(i.allocation)
                && i.before.is_some_and(|fact| offset == fact.size_bytes)
        }),
        crate::VirPointerDomain::Unknown => false,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenanceNote {
    pub case_ordinal: usize,
    pub issue: ProvenanceIssue,
    pub sources: Vec<VerifierFinding>,
    pub sources_truncated: bool,
}

impl ProvenanceIssue {
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::UnknownOrigin => "unknown pointer origin",
            Self::InstanceRelation => "same live instance not established",
            Self::DifferentInstances => "distinct abstract allocation instances",
            Self::InactiveInstance => "allocation is dead or only maybe live",
            Self::ObjectBoundary => "object/arithmetic domain boundary not established",
            Self::MissingDomainPath => {
                "domain path unavailable (unknown or bounded path precision)"
            }
            Self::OnePastAccess => "one-past address cannot authorize a nonempty access",
            Self::MissingPermission => "missing or incompatible access authority",
            Self::MissingInitialization => "initialized value not established",
            Self::PrecisionLimit => "resource precision/budget limit",
            Self::UnsupportedOperation => "unsupported object operation",
        }
    }
}

fn pointer(state: &ResourceState, id: VirValueId) -> Option<AbstractPointer> {
    match state.value(id) {
        Some(AbstractValue::Pointer(p)) => Some(*p),
        _ => None,
    }
}

fn instance(state: &ResourceState, id: AbstractAllocationId) -> Option<InstanceFact> {
    state.allocation(id).map(|a| InstanceFact {
        size_bytes: a.size_bytes(),
        liveness: a.liveness(),
        ownership: a.ownership(),
    })
}

pub(crate) struct Capture<'a> {
    pub finding: VerifierFinding,
    pub config: CfgAnalysisConfig,
    pub case_ordinal: usize,
    pub instruction: &'a VirInstruction,
    pub before: &'a ResourceState,
    pub after: &'a ResourceState,
    pub obligations: &'a [ResourceObligation],
    pub query_count: usize,
    pub sources: &'a SourceIndex,
}

impl Capture<'_> {
    pub(crate) fn record(self) -> Option<ProvenanceEvidence> {
        let mut values = BTreeSet::new();
        let mut memory_result = false;
        self.instruction.visit_operands(|v| {
            values.insert(v);
        });
        self.instruction.visit_results(|v| {
            memory_result |= matches!(
                v.ty,
                crate::VirType::Pointer { .. } | crate::VirType::Permission
            );
            values.insert(v.id);
        });
        if !memory_result
            && !values.iter().any(|id| {
                matches!(
                    self.before.value(*id),
                    Some(AbstractValue::Pointer(_) | AbstractValue::Permission(_))
                )
            })
        {
            return None;
        }
        // Include aliases invalidated by a fresh slot or opaque call, even if
        // that alias is not an explicit operand of the invalidating instruction.
        for (&id, value) in self.before.values() {
            if matches!(value, AbstractValue::Pointer(_)) && self.after.value(id) != Some(value) {
                values.insert(id);
            }
        }
        let pointers: Vec<_> = values
            .iter()
            .filter_map(|&value| {
                let before = pointer(self.before, value);
                let after = pointer(self.after, value);
                (before.is_some() || after.is_some()).then_some(PointerObservation {
                    value,
                    before,
                    after,
                })
            })
            .collect();
        let mut allocations = BTreeSet::new();
        for p in &pointers {
            for pointer in [p.before, p.after].into_iter().flatten() {
                if let AbstractProvenance::Known(id) = pointer.provenance() {
                    allocations.insert(id);
                }
            }
        }
        for &id in self
            .before
            .allocations()
            .keys()
            .chain(self.after.allocations().keys())
        {
            if instance(self.before, id) != instance(self.after, id) {
                allocations.insert(id);
            }
        }
        if pointers.is_empty()
            && allocations.is_empty()
            && !self.obligations.iter().any(|o| {
                matches!(
                    o.kind(),
                    ResourceObligationKind::AllocationInstanceFresh { .. }
                )
            })
        {
            return None;
        }
        let instances = allocations
            .into_iter()
            .map(|allocation| InstanceObservation {
                allocation,
                before: instance(self.before, allocation),
                after: instance(self.after, allocation),
            })
            .collect();
        for fact in self.before.path_condition().facts().into_iter().flatten() {
            match *fact {
                crate::PathFact::Boolean { value, .. } => {
                    values.insert(value);
                }
                crate::PathFact::Comparison { left, right, .. } => {
                    values.insert(left);
                    values.insert(right);
                }
            }
        }
        let (sources, sources_truncated) = self.sources.values(values);
        Some(ProvenanceEvidence {
            version: PROVENANCE_OBSERVATION_VERSION,
            finding: self.finding,
            config: self.config,
            case_ordinal: self.case_ordinal,
            guard: self.before.path_condition().clone(),
            instruction: self.instruction.clone(),
            sources,
            sources_truncated,
            pointers,
            instances,
            obligations: self.obligations.to_vec(),
            query_ordinals: (0..self.query_count).collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AbstractAllocation, GuaranteedAlignment, U64Interval, VirLocation, VirRegionId};

    #[test]
    fn fresh_instance_observation_includes_non_operand_invalidated_alias() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "fresh.nera",
            "fn main() -> u64 { let p=alloc<u64>(1); free(p); return 0; }",
        ));
        let program = output.vir().unwrap().resolve().unwrap();
        let function = &program.runtime().functions[0];
        let block = &function.blocks[0];
        let (ordinal, instruction) = block
            .instructions
            .iter()
            .enumerate()
            .find(|(_, i)| matches!(i.instruction, VirInstruction::Allocate { .. }))
            .unwrap();
        let location = VirLocation::Instruction {
            function: function.id,
            block: block.id,
            ordinal: ordinal as u64,
        };
        let finding =
            VerifierFinding::runtime(&program, location, instruction.source_span).unwrap();
        let id = AbstractAllocationId::new(77);
        let alias = VirValueId::new(999);
        let fresh = AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap();
        let mut old = fresh.clone();
        old.set_liveness(LivenessState::Dead);
        old.set_ownership(OwnershipState::Unowned);
        let mut before = ResourceState::new();
        before.define_allocation(id, old).unwrap();
        before
            .define_value(
                alias,
                AbstractValue::Pointer(
                    AbstractPointer::new(
                        AbstractProvenance::Known(id),
                        U64Interval::exact(0),
                        GuaranteedAlignment::new(8).unwrap(),
                    )
                    .with_memory_access(Some(crate::VirMemoryAccess::core_u64())),
                ),
            )
            .unwrap();
        let mut after = before.clone();
        after.introduce_allocation_instance(id, fresh).unwrap();
        let sources = SourceIndex::new(&program, function);
        let evidence = Capture {
            finding,
            config: CfgAnalysisConfig::default(),
            case_ordinal: 0,
            instruction: &instruction.instruction,
            before: &before,
            after: &after,
            obligations: &[],
            query_count: 0,
            sources: &sources,
        }
        .record()
        .unwrap();
        let alias = evidence.pointers.iter().find(|p| p.value == alias).unwrap();
        assert_eq!(
            alias.before.unwrap().provenance(),
            AbstractProvenance::Known(id)
        );
        assert_eq!(
            alias.after.unwrap().provenance(),
            AbstractProvenance::Unknown
        );
        assert_eq!(
            alias.after.unwrap().paths(),
            crate::VirPointerPaths::default()
        );
        assert_eq!(
            evidence.instances[0].before.unwrap().liveness,
            LivenessState::Dead
        );
        assert_eq!(
            evidence.instances[0].after.unwrap().liveness,
            LivenessState::Live
        );
        // Recording does not change either the retired state or the new state.
        assert_eq!(pointer(&before, alias.value), alias.before);
        assert_eq!(pointer(&after, alias.value), alias.after);
    }
}
