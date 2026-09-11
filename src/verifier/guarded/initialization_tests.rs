//! Finite concretization oracle for the product of byte/value/representation/
//! payload facts. It intentionally does not calculate expected results by join.
use super::*;
use crate::{
    AbstractAllocation, AbstractAllocationId, AbstractByteRange, AbstractPermission,
    AbstractPointer, AbstractProvenance, AccessPermission, ActiveVariantState, ByteRange,
    FreeCapability, GuaranteedAlignment, InitializationClass, MovePathState, ObjectStateKey,
    PathFact, ResourcePayloadKey, TypedResourcePayload, U64Interval, VirMemoryAccess, VirValueId,
    VirVariantId,
};

fn allocation_id() -> AbstractAllocationId {
    AbstractAllocationId::new(0)
}
fn object_key() -> ObjectStateKey {
    ObjectStateKey::new(0, VirMemoryAccess::core_u64())
}
fn payload_key() -> ResourcePayloadKey {
    ResourcePayloadKey::new(8, VirMemoryAccess::core_u64())
}
fn byte(offset: u64) -> ByteRange {
    ByteRange::new(offset, offset + 1).unwrap()
}

fn sample(ordinal: u32, branch: bool) -> ResourceState {
    let mut allocation = AbstractAllocation::new_local(16, 8).unwrap();
    // Four possibilities per byte: uninitialized, initialized but not known
    // valid, valid initialized, unknown. Unrelated padding stays unknown.
    allocation
        .forget_initialization(ByteRange::new(2, 8).unwrap())
        .unwrap();
    for offset in 0..2 {
        match (ordinal >> (offset * 2)) & 3 {
            0 => {}
            1 => allocation.mark_initialized(byte(offset)).unwrap(),
            2 => {
                allocation.mark_initialized(byte(offset)).unwrap();
                allocation.mark_valid(byte(offset)).unwrap();
            }
            _ => allocation.forget_initialization(byte(offset)).unwrap(),
        }
    }
    allocation
        .set_active_variant(
            object_key(),
            ActiveVariantState::Exact(VirVariantId::new((ordinal >> 4) & 1)),
        )
        .unwrap();
    let payload = if ordinal & 32 == 0 {
        MovePathState::Moved
    } else {
        let provenance =
            AbstractProvenance::Known(AbstractAllocationId::new(1 + ((ordinal >> 4) & 1)));
        MovePathState::available(TypedResourcePayload::new(
            AbstractPointer::new(
                provenance,
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            ),
            AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            ),
        ))
    };
    allocation
        .set_resource_payload(payload_key(), payload)
        .unwrap();
    let mut state = ResourceState::new();
    state
        .define_allocation(allocation_id(), allocation)
        .unwrap();
    state.conjoin_path_fact(PathFact::boolean(VirValueId::new(0), branch));
    state
}

fn covers(output: &ResourceState, input: &ResourceState, branch: bool) -> bool {
    if !output.path_condition().facts().is_some_and(|facts| facts.iter().all(|fact| {
        matches!(*fact, PathFact::Boolean { value, expected } if value == VirValueId::new(0) && expected == branch)
    })) { return false; }
    let output = output.allocation(allocation_id()).unwrap();
    let input = input.allocation(allocation_id()).unwrap();
    for offset in 0..16 {
        let range = byte(offset);
        let out = output.initialization().classify(range);
        let incoming = input.initialization().classify(range);
        if out != InitializationClass::MaybeInitialized && out != incoming {
            return false;
        }
        if output.valid_value_bytes().contains(range) && !input.valid_value_bytes().contains(range)
        {
            return false;
        }
    }
    let tag_covered = output
        .active_variant(object_key())
        .alternatives()
        .is_none_or(|tags| {
            input
                .active_variant(object_key())
                .alternatives()
                .unwrap()
                .is_subset(&tags)
        });
    let payload_covered = match output.resource_payload(payload_key()) {
        MovePathState::Unknown => true,
        exact => exact == input.resource_payload(payload_key()),
    };
    tag_covered && payload_covered
}

#[test]
fn initialization_guarded_concretization_covers_all_axes_after_budget_collapse() {
    for left in 0..64 {
        for right in 0..64 {
            let inputs = [sample(left, false), sample(right, true)];
            for max_cases in [1, 2] {
                for max_guard_atoms in [0, 1] {
                    for reduction in [
                        GuardedReduction::Selective,
                        GuardedReduction::PreserveGuards,
                    ] {
                        let output = ConditionalResourceState::from_cases(
                            inputs.to_vec(),
                            BTreeSet::new(),
                            GuardedStateLimits {
                                max_cases,
                                max_guard_atoms,
                            },
                            reduction,
                        )
                        .unwrap();
                        for (index, input) in inputs.iter().enumerate() {
                            assert!(
                                output
                                    .cases()
                                    .iter()
                                    .any(|case| covers(case, input, index != 0)),
                                "lost byte/validity/tag/payload alternative {left}/{right}, case={max_cases}, guard={max_guard_atoms}"
                            );
                        }
                    }
                }
            }
        }
    }
}
