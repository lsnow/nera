use std::collections::{BTreeMap, BTreeSet, btree_map::Entry};
use std::error::Error;
use std::fmt;

use crate::{
    VirBorrowRegionId, VirIntegerPredicate, VirLoanId, VirLoanKind, VirMemoryAccess, VirRegionId,
    VirValueId, VirVariantId,
};

mod bytes;
mod cfg_projection;
mod contents;
mod initialization;
mod instance;
mod loan;
mod loop_frame;
mod loop_partition;
mod object;
mod pointer;
mod scalar;
mod state;
use super::relation::{
    difference::{DifferenceLimits, DifferencePremise},
    state::RelationState,
};
use initialization::InitializationPrefixes;
use state::ExpressionRemapper;
#[cfg(test)]
use state::join_loans;

pub use bytes::*;
pub use loan::*;
pub use object::*;
pub use pointer::*;
pub use scalar::*;
pub use state::*;

/// Maximum number of disjoint definite byte ranges retained in one set.
///
/// Dropping ranges only loses proof precision: a byte absent from both
/// initialization sets is unknown rather than assumed initialized.
pub const VERIFIER_BYTE_SET_MAX_RANGES: usize = 4_096;

/// Maximum number of exact enum subobjects tracked in one allocation.
pub const VERIFIER_OBJECT_STATE_MAX_ENTRIES: usize = 1_024;

/// Maximum number of typed resource move paths retained in one allocation.
///
/// Exceeding the budget only replaces the requested path with `Unknown`; it
/// never creates an available owner.
pub const VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES: usize = 1_024;

/// Maximum number of active enum alternatives retained across a CFG join.
pub const VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES: usize = 256;

/// Maximum canonical allocation-relative offsets retained for one place.
pub const VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES: usize = 256;

/// Maximum number of live or maybe-live loans retained in one resource case.
pub const VERIFIER_MAX_ACTIVE_LOANS_PER_CASE: usize = 256;

/// Maximum number of available shared-reference authorities for one loan.
pub const VERIFIER_MAX_ALIASES_PER_LOAN: usize = 256;

/// Maximum parent chain followed while validating one reborrow transfer.
pub const VERIFIER_MAX_REBORROW_DEPTH: usize = 64;

/// Maximum region constraints consulted for one function analysis.
pub const VERIFIER_MAX_REGION_CONSTRAINTS_PER_FUNCTION: usize = 4_096;

#[cfg(test)]
mod tests {
    use super::*;

    fn range(start: u64, end: u64) -> ByteRange {
        ByteRange::new(start, end).expect("test range must be valid")
    }

    fn allocation(size: u64) -> AbstractAllocation {
        AbstractAllocation::new(VirRegionId::new(0), size, 8)
            .expect("test allocation must be valid")
    }

    #[test]
    fn byte_set_normalizes_insert_remove_and_intersection() {
        let mut bytes = ByteSet::new();
        bytes.insert(range(8, 16));
        bytes.insert(range(0, 8));
        bytes.insert(range(24, 32));
        assert_eq!(bytes.ranges(), &[range(0, 16), range(24, 32)]);

        bytes.remove(range(4, 28));
        assert_eq!(bytes.ranges(), &[range(0, 4), range(28, 32)]);
        assert!(bytes.contains(range(1, 3)));
        assert!(!bytes.contains(range(3, 29)));

        let other = ByteSet::single(range(2, 30));
        assert_eq!(bytes.union(&other).ranges(), &[range(0, 32)]);
        assert_eq!(
            bytes.intersection(&other).ranges(),
            &[range(2, 4), range(28, 30)]
        );
    }

    #[test]
    fn byte_set_matches_a_small_concrete_bitmap_model() {
        fn from_mask(mask: u8) -> ByteSet {
            let mut result = ByteSet::new();
            for byte in 0..8 {
                if mask & (1 << byte) != 0 {
                    result.insert(range(byte, byte + 1));
                }
            }
            result
        }

        for left_mask in u8::MIN..=u8::MAX {
            let left = from_mask(left_mask);
            for right_mask in u8::MIN..=u8::MAX {
                let right = from_mask(right_mask);
                let intersection = left.intersection(&right);
                assert_eq!(intersection, from_mask(left_mask & right_mask));
                assert_eq!(left.is_disjoint(&right), left_mask & right_mask == 0);
            }
        }
    }

    #[test]
    fn byte_and_object_state_budgets_only_lose_precision() {
        let mut bytes = ByteSet::new();
        for index in 0..=VERIFIER_BYTE_SET_MAX_RANGES {
            let start = u64::try_from(index).unwrap() * 2;
            bytes.insert(range(start, start + 1));
        }
        assert_eq!(bytes.ranges().len(), VERIFIER_BYTE_SET_MAX_RANGES);
        assert!(!bytes.is_precise());
        assert!(!bytes.contains(range(
            u64::try_from(VERIFIER_BYTE_SET_MAX_RANGES).unwrap() * 2,
            u64::try_from(VERIFIER_BYTE_SET_MAX_RANGES).unwrap() * 2 + 1,
        )));

        let access = VirMemoryAccess::core_u64();
        let mut objects = ObjectState::new();
        for offset in 0..VERIFIER_OBJECT_STATE_MAX_ENTRIES {
            assert!(objects.set_active_variant(
                ObjectStateKey::new(u64::try_from(offset).unwrap(), access),
                ActiveVariantState::Exact(VirVariantId::new(0)),
            ));
        }
        assert!(!objects.set_active_variant(
            ObjectStateKey::new(
                u64::try_from(VERIFIER_OBJECT_STATE_MAX_ENTRIES).unwrap(),
                access,
            ),
            ActiveVariantState::Exact(VirVariantId::new(0)),
        ));
        assert!(!objects.is_precise());
        assert_eq!(
            objects.active_variant(ObjectStateKey::new(
                VERIFIER_OBJECT_STATE_MAX_ENTRIES as u64,
                access,
            )),
            ActiveVariantState::Unknown
        );

        let allocation_id = AbstractAllocationId::new(7);
        let payload = TypedResourcePayload::new(
            AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            ),
            AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(range(0, 8)),
                AccessPermission::Write,
                FreeCapability::Yes,
            ),
        );
        let mut payloads = ObjectState::new();
        for offset in 0..VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES {
            assert!(payloads.set_resource_payload(
                ResourcePayloadKey::new(u64::try_from(offset).unwrap(), access),
                MovePathState::available(payload),
            ));
        }
        assert!(!payloads.set_resource_payload(
            ResourcePayloadKey::new(
                u64::try_from(VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES).unwrap(),
                access,
            ),
            MovePathState::available(payload),
        ));
        assert!(!payloads.is_precise());
        assert_eq!(
            payloads.resource_payload(ResourcePayloadKey::new(
                VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES as u64,
                access,
            )),
            MovePathState::Unknown
        );

        let left = ActiveVariantState::Alternatives(
            (0..VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES)
                .map(|variant| VirVariantId::new(u32::try_from(variant).unwrap()))
                .collect(),
        );
        assert_eq!(
            left.join(&ActiveVariantState::Exact(VirVariantId::new(
                u32::try_from(VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES).unwrap(),
            ))),
            ActiveVariantState::Unknown
        );
    }

    #[test]
    fn only_authority_free_ended_tombstones_can_ignore_historical_footprint_changes() {
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        for activity in [
            LoanActivity::Ended,
            LoanActivity::Active,
            LoanActivity::MaybeActive,
        ] {
            for has_authority in [false, true] {
                let make = |start| {
                    let mut loan = AbstractLoan::new(
                        provenance,
                        range(0, 32),
                        VirLoanKind::Mutable,
                        VirBorrowRegionId::new(0),
                        None,
                        activity,
                    )
                    .with_footprint(Some(MemoryFootprint {
                        provenance,
                        access: VirMemoryAccess::core_u64(),
                        stride_bytes: 8,
                        range: AbstractByteRange::Exact(range(start, start + 8)),
                        envelope: range(start, start + 8),
                    }));
                    if has_authority {
                        loan = loan.with_authority(VirValueId::new(0));
                    }
                    BTreeMap::from([(VirLoanId::new(0), loan)])
                };
                let (joined, lost) = join_loans(&make(0), &make(8)).unwrap();
                assert_eq!(lost, activity != LoanActivity::Ended || has_authority);
                assert_eq!(joined[&VirLoanId::new(0)].activity(), activity);
                assert_eq!(
                    joined[&VirLoanId::new(0)].authorities().is_empty(),
                    !has_authority
                );
            }
        }
    }

    #[test]
    fn initialization_join_keeps_only_definite_common_bytes() {
        let mut left = allocation(32);
        let mut right = allocation(32);
        left.mark_initialized(range(0, 16)).unwrap();
        right.mark_initialized(range(8, 24)).unwrap();

        let joined = left.join(AbstractAllocationId::new(0), &right).unwrap();
        assert_eq!(
            joined.initialization().classify(range(8, 16)),
            InitializationClass::Initialized
        );
        assert_eq!(
            joined.initialization().classify(range(24, 32)),
            InitializationClass::Uninitialized
        );
        assert_eq!(
            joined.initialization().classify(range(0, 8)),
            InitializationClass::MaybeInitialized
        );
        assert_eq!(
            joined.initialization().classify(range(16, 24)),
            InitializationClass::MaybeInitialized
        );
    }

    #[test]
    fn allocation_updates_preserve_disjoint_initialization_facts() {
        let mut value = allocation(24);
        value.mark_initialized(range(8, 16)).unwrap();
        assert!(
            value
                .initialization()
                .initialized()
                .is_disjoint(value.initialization().uninitialized())
        );
        value.forget_initialization(range(12, 20)).unwrap();
        assert_eq!(
            value.initialization().classify(range(12, 20)),
            InitializationClass::MaybeInitialized
        );
        value.mark_uninitialized(range(8, 16)).unwrap();
        assert_eq!(
            value.initialization().classify(range(8, 16)),
            InitializationClass::Uninitialized
        );
        assert_eq!(
            value.mark_initialized(range(16, 25)),
            Err(AbstractAllocationError::RangeOutOfBounds {
                range: range(16, 25),
                size_bytes: 24,
            })
        );
    }

    #[test]
    fn liveness_ownership_and_permission_joins_lose_path_specific_certainty() {
        assert_eq!(
            LivenessState::Live.join(LivenessState::Dead),
            LivenessState::MaybeLive
        );
        assert_eq!(
            OwnershipState::Owned.join(OwnershipState::Unowned),
            OwnershipState::MaybeOwned
        );

        let allocation = AbstractAllocationId::new(4);
        let mut left = AbstractPermission::new(
            AbstractProvenance::Known(allocation),
            AbstractByteRange::Exact(range(0, 16)),
            AccessPermission::Write,
            FreeCapability::Yes,
        );
        let right = AbstractPermission::new(
            AbstractProvenance::Known(allocation),
            AbstractByteRange::Exact(range(8, 16)),
            AccessPermission::Read,
            FreeCapability::No,
        );
        left.mark_consumed();
        let joined = left.join(right);
        assert_eq!(joined.range(), AbstractByteRange::Unknown);
        assert_eq!(joined.access(), AccessPermission::MaybeWrite);
        assert_eq!(joined.free_capability(), FreeCapability::Maybe);
        assert_eq!(joined.availability(), PermissionAvailability::MaybeConsumed);
    }

    #[test]
    fn pointer_join_tracks_interval_provenance_and_alignment() {
        let u64_access = VirMemoryAccess::core_u64();
        let left = AbstractPointer::new(
            AbstractProvenance::Known(AbstractAllocationId::new(0)),
            U64Interval::exact(8),
            GuaranteedAlignment::new(8).unwrap(),
        )
        .with_memory_access(Some(u64_access));
        let right = AbstractPointer::new(
            AbstractProvenance::Known(AbstractAllocationId::new(1)),
            U64Interval::exact(24),
            GuaranteedAlignment::new(4).unwrap(),
        )
        .with_memory_access(Some(u64_access));
        let joined = left.join(right);
        assert_eq!(joined.provenance(), AbstractProvenance::Unknown);
        assert_eq!(joined.offset_bytes(), U64Interval::new(8, 24).unwrap());
        assert_eq!(joined.alignment().bytes(), 4);
        assert_eq!(joined.memory_access(), Some(u64_access));

        let incompatible = right.with_memory_access(Some(VirMemoryAccess::new(
            crate::VirTypeId::new(1),
            crate::VirLayoutId::new(1),
        )));
        assert_eq!(left.join(incompatible).memory_access(), None);
        assert_eq!(left.widen(incompatible).memory_access(), None);
    }

    #[test]
    fn interval_widening_accelerates_only_outward_moving_bounds() {
        let current = U64Interval::new(4, 8).unwrap();
        assert_eq!(current.widen(current), current);
        assert_eq!(
            current.widen(U64Interval::new(2, 8).unwrap()),
            U64Interval::new(0, 8).unwrap()
        );
        assert_eq!(
            current.widen(U64Interval::new(4, 16).unwrap()),
            U64Interval::new(4, u64::MAX).unwrap()
        );
        assert_eq!(
            current.widen(U64Interval::new(2, 16).unwrap()),
            U64Interval::unknown()
        );
    }

    #[test]
    fn path_conditions_detect_direct_contradiction_and_intersect_at_join() {
        let shared = PathFact::boolean(VirValueId::new(0), true);
        let left_only = PathFact::comparison(
            VirIntegerPredicate::LessThan,
            VirValueId::new(1),
            VirValueId::new(2),
        );
        let mut left = PathCondition::empty();
        left.conjoin(shared);
        left.conjoin(left_only);
        let mut right = PathCondition::empty();
        right.conjoin(shared);
        right.conjoin(left_only.negated());

        let joined = left.join(&right);
        assert!(joined.implies(shared));
        assert!(!joined.implies(left_only));

        right.conjoin(shared.negated());
        assert_eq!(right, PathCondition::Unreachable);
        assert_eq!(left.join(&right), left);
    }

    #[test]
    fn path_conditions_simplify_reflexive_comparisons() {
        let value = VirValueId::new(3);
        let mut true_fact = PathCondition::empty();
        true_fact.conjoin(PathFact::comparison(
            VirIntegerPredicate::LessOrEqual,
            value,
            value,
        ));
        assert_eq!(true_fact, PathCondition::empty());

        let mut false_fact = PathCondition::empty();
        false_fact.conjoin(PathFact::comparison(
            VirIntegerPredicate::LessThan,
            value,
            value,
        ));
        assert_eq!(false_fact, PathCondition::unreachable());
    }

    #[test]
    fn comparison_normalization_is_operand_order_independent() {
        assert_eq!(
            PathFact::comparison(
                VirIntegerPredicate::LessThan,
                VirValueId::new(9),
                VirValueId::new(2),
            ),
            PathFact::comparison(
                VirIntegerPredicate::GreaterThan,
                VirValueId::new(2),
                VirValueId::new(9),
            )
        );
    }

    #[test]
    fn primitive_joins_are_commutative_idempotent_and_associative() {
        fn assert_laws<T: Copy + fmt::Debug + PartialEq>(values: &[T], join: impl Fn(T, T) -> T) {
            for &left in values {
                assert_eq!(join(left, left), left);
                for &right in values {
                    assert_eq!(join(left, right), join(right, left));
                    for &third in values {
                        assert_eq!(
                            join(join(left, right), third),
                            join(left, join(right, third))
                        );
                    }
                }
            }
        }

        assert_laws(
            &[
                LivenessState::Live,
                LivenessState::Dead,
                LivenessState::MaybeLive,
            ],
            LivenessState::join,
        );
        assert_laws(
            &[
                OwnershipState::Owned,
                OwnershipState::Unowned,
                OwnershipState::MaybeOwned,
            ],
            OwnershipState::join,
        );
        assert_laws(
            &[
                FreeCapability::Yes,
                FreeCapability::No,
                FreeCapability::Maybe,
            ],
            FreeCapability::join,
        );
        assert_laws(
            &[
                PermissionAvailability::Available,
                PermissionAvailability::Consumed,
                PermissionAvailability::MaybeConsumed,
            ],
            PermissionAvailability::join,
        );
        assert_laws(
            &[
                AbstractBool::True,
                AbstractBool::False,
                AbstractBool::Unknown,
            ],
            AbstractBool::join,
        );
        assert_laws(
            &[
                AccessPermission::Read,
                AccessPermission::Write,
                AccessPermission::MaybeWrite,
            ],
            AccessPermission::join,
        );
        assert_laws(
            &[
                AbstractProvenance::Known(AbstractAllocationId::new(0)),
                AbstractProvenance::Known(AbstractAllocationId::new(1)),
                AbstractProvenance::Unknown,
            ],
            AbstractProvenance::join,
        );
        assert_laws(
            &[
                AbstractByteRange::Exact(range(0, 8)),
                AbstractByteRange::Exact(range(8, 16)),
                AbstractByteRange::Symbolic {
                    start: SymbolicRangeBound::constant(0),
                    end: SymbolicRangeBound::new(
                        AffineExpression::identity(VirValueId::new(9)),
                        U64Interval::new(8, 16).unwrap(),
                    ),
                },
                AbstractByteRange::Unknown,
            ],
            AbstractByteRange::join,
        );
        assert_laws(
            &[
                GuaranteedAlignment::new(1).unwrap(),
                GuaranteedAlignment::new(4).unwrap(),
                GuaranteedAlignment::new(16).unwrap(),
            ],
            GuaranteedAlignment::join,
        );

        let intervals = [
            U64Interval::exact(0),
            U64Interval::new(0, 8).unwrap(),
            U64Interval::new(4, 16).unwrap(),
            U64Interval::unknown(),
        ];
        assert_laws(&intervals, U64Interval::join);

        let permissions = [
            AbstractPermission::new(
                AbstractProvenance::Known(AbstractAllocationId::new(0)),
                AbstractByteRange::Exact(range(0, 8)),
                AccessPermission::Write,
                FreeCapability::Yes,
            ),
            AbstractPermission::new(
                AbstractProvenance::Known(AbstractAllocationId::new(1)),
                AbstractByteRange::Exact(range(8, 16)),
                AccessPermission::Read,
                FreeCapability::No,
            ),
            {
                let mut permission = AbstractPermission::new(
                    AbstractProvenance::Unknown,
                    AbstractByteRange::Unknown,
                    AccessPermission::Write,
                    FreeCapability::Maybe,
                );
                permission.availability = PermissionAvailability::MaybeConsumed;
                permission
            },
        ];
        assert_laws(&permissions, AbstractPermission::join);
    }

    #[test]
    fn resource_join_merges_common_facts_and_drops_path_local_definitions() {
        let allocation_id = AbstractAllocationId::new(0);
        let mut left = ResourceState::new();
        let mut right = ResourceState::new();
        left.define_allocation(allocation_id, allocation(32))
            .unwrap();
        let mut dead = allocation(32);
        dead.mark_dead();
        right.define_allocation(allocation_id, dead).unwrap();

        let pointer_id = VirValueId::new(0);
        left.define_value(
            pointer_id,
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            )),
        )
        .unwrap();
        right
            .define_value(
                pointer_id,
                AbstractValue::Pointer(AbstractPointer::new(
                    AbstractProvenance::Known(allocation_id),
                    U64Interval::exact(8),
                    GuaranteedAlignment::new(8).unwrap(),
                )),
            )
            .unwrap();
        left.define_value(
            VirValueId::new(9),
            AbstractValue::U64(U64Interval::exact(1)),
        )
        .unwrap();

        let joined = left.join(&right).unwrap();
        assert_eq!(
            joined.allocation(allocation_id).unwrap().liveness(),
            LivenessState::MaybeLive
        );
        assert_eq!(
            joined.allocation(allocation_id).unwrap().ownership(),
            OwnershipState::MaybeOwned
        );
        let Some(AbstractValue::Pointer(pointer)) = joined.value(pointer_id) else {
            panic!("common pointer fact must remain")
        };
        assert_eq!(pointer.offset_bytes(), U64Interval::new(0, 8).unwrap());
        assert!(joined.value(VirValueId::new(9)).is_none());
    }

    #[test]
    fn resource_payload_join_is_atomic_and_never_recreates_a_moved_owner() {
        let allocation_id = AbstractAllocationId::new(7);
        let pointer = AbstractPointer::new(
            AbstractProvenance::Known(allocation_id),
            U64Interval::exact(0),
            GuaranteedAlignment::new(8).unwrap(),
        );
        let permission = AbstractPermission::new(
            AbstractProvenance::Known(allocation_id),
            AbstractByteRange::Exact(range(0, 8)),
            AccessPermission::Write,
            FreeCapability::Yes,
        );
        let available = MovePathState::available(TypedResourcePayload::new(pointer, permission));
        assert_eq!(available.join(&available), available);
        assert_eq!(
            MovePathState::Moved.join(&MovePathState::Moved),
            MovePathState::Moved
        );
        assert_eq!(
            available.join(&MovePathState::Moved),
            MovePathState::Unknown
        );
        assert_eq!(
            MovePathState::Moved.join(&available),
            MovePathState::Unknown
        );

        let other = MovePathState::available(TypedResourcePayload::new(
            AbstractPointer::new(
                AbstractProvenance::Known(AbstractAllocationId::new(8)),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            ),
            permission,
        ));
        assert_eq!(available.join(&other), MovePathState::Unknown);
    }

    #[test]
    fn dynamic_object_offsets_are_bounded_and_canonical() {
        let base = AbstractObjectOffsets::Exact(16);
        let offsets = base.offset_by_index(U64Interval::new(1, 3).unwrap(), 8);
        assert_eq!(offsets.candidates(), Some(vec![24, 32, 40]));
        assert_eq!(
            base.offset_by_index(
                U64Interval::new(
                    0,
                    u64::try_from(VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES).unwrap(),
                )
                .unwrap(),
                8,
            ),
            AbstractObjectOffsets::Unknown
        );
        assert_eq!(
            AbstractObjectOffsets::Exact(8).join(AbstractObjectOffsets::Exact(24)),
            AbstractObjectOffsets::Unknown
        );
    }

    #[test]
    fn resource_join_rejects_inconsistent_immutable_metadata_and_value_kinds() {
        let allocation_id = AbstractAllocationId::new(0);
        let mut left = ResourceState::new();
        let mut right = ResourceState::new();
        left.define_allocation(allocation_id, allocation(8))
            .unwrap();
        right
            .define_allocation(allocation_id, allocation(16))
            .unwrap();
        assert_eq!(
            left.join(&right),
            Err(ResourceJoinError::AllocationSizeMismatch {
                allocation: allocation_id,
            })
        );

        let mut left = ResourceState::new();
        let mut right = ResourceState::new();
        let value = VirValueId::new(0);
        left.define_value(value, AbstractValue::U64(U64Interval::exact(1)))
            .unwrap();
        right
            .define_value(value, AbstractValue::Bool(AbstractBool::True))
            .unwrap();
        assert_eq!(
            left.join(&right),
            Err(ResourceJoinError::ValueKindMismatch { value })
        );
    }

    #[test]
    fn complete_resource_join_obeys_semilattice_laws() {
        fn state(
            initialized: ByteRange,
            liveness: LivenessState,
            ownership: OwnershipState,
            offset: u64,
            path_fact: PathFact,
        ) -> ResourceState {
            let allocation_id = AbstractAllocationId::new(0);
            let mut allocation = allocation(24);
            allocation.mark_initialized(initialized).unwrap();
            allocation.set_liveness(liveness);
            allocation.set_ownership(ownership);

            let mut state = ResourceState::new();
            state.define_allocation(allocation_id, allocation).unwrap();
            state
                .define_value(
                    VirValueId::new(0),
                    AbstractValue::Pointer(AbstractPointer::new(
                        AbstractProvenance::Known(allocation_id),
                        U64Interval::exact(offset),
                        GuaranteedAlignment::new(8).unwrap(),
                    )),
                )
                .unwrap();
            state.conjoin_path_fact(PathFact::boolean(VirValueId::new(1), true));
            state.conjoin_path_fact(path_fact);
            state
        }

        let states = [
            state(
                range(0, 8),
                LivenessState::Live,
                OwnershipState::Owned,
                0,
                PathFact::boolean(VirValueId::new(2), true),
            ),
            state(
                range(8, 16),
                LivenessState::Dead,
                OwnershipState::Unowned,
                8,
                PathFact::boolean(VirValueId::new(3), true),
            ),
            state(
                range(4, 12),
                LivenessState::MaybeLive,
                OwnershipState::MaybeOwned,
                16,
                PathFact::boolean(VirValueId::new(4), true),
            ),
        ];

        for left in &states {
            assert_eq!(left.join(left).unwrap(), *left);
            for right in &states {
                assert_eq!(left.join(right).unwrap(), right.join(left).unwrap());
                for third in &states {
                    assert_eq!(
                        left.join(right).unwrap().join(third).unwrap(),
                        left.join(&right.join(third).unwrap()).unwrap()
                    );
                }
            }
        }
    }

    #[test]
    fn state_definitions_are_unique_and_unreachable_is_join_identity() {
        let mut state = ResourceState::new();
        let allocation_id = AbstractAllocationId::new(0);
        state
            .define_allocation(allocation_id, allocation(8))
            .unwrap();
        assert_eq!(
            state.define_allocation(allocation_id, allocation(16)),
            Err(ResourceStateDefinitionError::DuplicateAllocation(
                allocation_id
            ))
        );
        assert_eq!(
            state
                .allocation(allocation_id)
                .expect("original allocation remains")
                .size_bytes(),
            8
        );

        let value = VirValueId::new(0);
        state
            .define_value(value, AbstractValue::Bool(AbstractBool::True))
            .unwrap();
        assert_eq!(
            state.define_value(value, AbstractValue::Bool(AbstractBool::False)),
            Err(ResourceStateDefinitionError::DuplicateValue(value))
        );
        assert_eq!(
            state.value(value),
            Some(&AbstractValue::Bool(AbstractBool::True))
        );
        assert_eq!(state.join(&ResourceState::unreachable()).unwrap(), state);
    }

    #[test]
    fn allocation_identity_namespaces_and_summary_instances_are_disjoint() {
        let value = VirValueId::new(7);
        let external = AbstractAllocationId::new(value.get());
        let local = AbstractAllocationId::vir_allocation_site(value);
        let frame_local = AbstractAllocationId::vir_local_storage_site(value);
        let first_summary = AbstractAllocationId::contract_instance(3, value.get());
        let second_summary = AbstractAllocationId::contract_instance(4, value.get());
        let entry_payload = AbstractAllocationId::abi_entry_payload(1, 2, value.get());
        let call_payload = AbstractAllocationId::abi_call_payload(3, 0, value.get());

        assert_ne!(external, local);
        assert_ne!(external, first_summary);
        assert_ne!(local, first_summary);
        assert_ne!(external, frame_local);
        assert_ne!(local, frame_local);
        assert_ne!(frame_local, first_summary);
        assert_ne!(first_summary, second_summary);
        assert_ne!(first_summary, entry_payload);
        assert_ne!(entry_payload, call_payload);
        assert_eq!(external.get(), local.get());
        assert_eq!(external.get(), first_summary.get());
        assert_eq!(external.get(), frame_local.get());
        assert_eq!(external.to_string(), "external:7");
        assert_eq!(local.to_string(), "site:%7");
        assert_eq!(frame_local.to_string(), "local-storage:%7");
        assert_eq!(first_summary.to_string(), "summary:3:7");
        assert_eq!(entry_payload.to_string(), "abi-entry:1:2:7");
        assert_eq!(call_payload.to_string(), "abi-call:3:0:7");
    }

    #[test]
    fn affine_expressions_track_scaling_offsets_and_guaranteed_alignment() {
        let root = AffineExpression::identity(VirValueId::new(0));
        let doubled = root.checked_add(root).expect("doubling cannot overflow");
        let scaled = doubled
            .checked_add(doubled)
            .and_then(|value| value.checked_add(value))
            .expect("scaling by eight cannot overflow");
        let advanced = scaled
            .checked_add(AffineExpression::constant(8))
            .expect("small addend cannot overflow");

        assert_eq!(scaled.scale(), 8);
        assert_eq!(scaled.addend(), 0);
        assert_eq!(scaled.guaranteed_alignment().bytes(), 8);
        assert_eq!(advanced.scale(), 8);
        assert_eq!(advanced.addend(), 8);
        assert_eq!(advanced.guaranteed_alignment().bytes(), 8);
        assert_eq!(root.checked_scale(8), Some(scaled));
        assert_eq!(root.checked_scale(0), Some(AffineExpression::constant(0)));
        assert!(
            AffineExpression::constant(u64::MAX)
                .checked_add(AffineExpression::constant(1))
                .is_none()
        );
    }

    #[test]
    fn two_root_affine_budget_and_cfg_projection_drop_missing_terms() {
        let a = AffineExpression::identity(VirValueId::new(0))
            .checked_scale(32)
            .unwrap();
        let b = AffineExpression::identity(VirValueId::new(1))
            .checked_scale(8)
            .unwrap();
        let sum = a.checked_add(b).unwrap();
        assert_eq!(sum, b.checked_add(a).unwrap());
        assert!(!sum.is_constant());
        assert_eq!(sum.root(), None);
        assert_eq!(sum.guaranteed_alignment().bytes(), 8);
        assert!(
            sum.checked_add(AffineExpression::identity(VirValueId::new(2)))
                .is_none()
        );
        assert!(sum.checked_scale(u64::MAX).is_none());
        assert!(
            sum.rename_root(&BTreeMap::from([(VirValueId::new(0), VirValueId::new(10))]))
                .is_none()
        );
        let renamed = sum
            .rename_root(&BTreeMap::from([
                (VirValueId::new(0), VirValueId::new(10)),
                (VirValueId::new(1), VirValueId::new(10)),
            ]))
            .unwrap();
        assert_eq!(
            renamed,
            AffineExpression::identity(VirValueId::new(10))
                .checked_scale(40)
                .unwrap()
        );
        let mut state = ResourceState::new();
        for id in 0..2 {
            state
                .define_value(
                    VirValueId::new(id),
                    AbstractValue::U64(U64Interval::new(0, 2).unwrap()),
                )
                .unwrap();
        }
        let range = AbstractByteRange::from_bounds(
            SymbolicRangeBound::new(sum, U64Interval::new(0, 80).unwrap()),
            SymbolicRangeBound::new(
                sum.checked_add_constant(8).unwrap(),
                U64Interval::new(8, 88).unwrap(),
            ),
        );
        let partial = ExpressionRemapper::new(&state, &[(VirValueId::new(0), VirValueId::new(10))]);
        assert_eq!(partial.range(range), AbstractByteRange::Unknown);
        let complete = ExpressionRemapper::new(
            &state,
            &[
                (VirValueId::new(0), VirValueId::new(10)),
                (VirValueId::new(1), VirValueId::new(11)),
            ],
        );
        assert_ne!(complete.range(range), AbstractByteRange::Unknown);
    }

    #[test]
    fn cfg_projection_renames_symbols_inside_permissions() {
        let source_word = VirValueId::new(0);
        let source_permission = VirValueId::new(1);
        let target_word = VirValueId::new(10);
        let target_permission = VirValueId::new(11);
        let expression = AffineExpression::identity(source_word);
        let mut state = ResourceState::new();
        state
            .define_value(
                source_word,
                AbstractValue::U64(U64Interval::new(8, 24).unwrap()),
            )
            .unwrap();
        state.set_word_expression(source_word, expression);
        state
            .define_value(
                source_permission,
                AbstractValue::Permission(AbstractPermission::new(
                    AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    AbstractByteRange::Symbolic {
                        start: SymbolicRangeBound::constant(0),
                        end: SymbolicRangeBound::new(expression, U64Interval::new(8, 24).unwrap()),
                    },
                    AccessPermission::Write,
                    FreeCapability::No,
                )),
            )
            .unwrap();
        let renames = [
            (source_word, target_word),
            (source_permission, target_permission),
        ];

        let projected = state.project_cfg_case(&renames).unwrap();
        assert_eq!(
            projected.word_expression(target_word),
            Some(AffineExpression::identity(target_word))
        );
        let Some(AbstractValue::Permission(permission)) =
            projected.value(target_permission).copied()
        else {
            panic!("permission must project")
        };
        let AbstractByteRange::Symbolic { end, .. } = permission.range() else {
            panic!("symbolic range must be retained")
        };
        assert_eq!(end.expression(), AffineExpression::identity(target_word));
    }

    #[test]
    fn footprint_projection_renames_pointer_loan_and_stored_payload_together() {
        let source = VirValueId::new(0);
        let authority = VirValueId::new(1);
        let target = VirValueId::new(10);
        let target_authority = VirValueId::new(11);
        let storage = AbstractAllocationId::new(0);
        let provenance = AbstractProvenance::Known(storage);
        let access = VirMemoryAccess::core_u64();
        let start = SymbolicRangeBound::new(
            AffineExpression::identity(source),
            U64Interval::new(0, 8).unwrap(),
        );
        let footprint = MemoryFootprint {
            provenance,
            access,
            stride_bytes: 8,
            range: AbstractByteRange::from_bounds(start, start.checked_add_constant(8).unwrap()),
            envelope: range(0, 16),
        };
        let pointer = AbstractPointer::new(
            provenance,
            start.interval(),
            GuaranteedAlignment::new(8).unwrap(),
        )
        .with_offset_expression(Some(start.expression()))
        .with_memory_access(Some(access))
        .with_slice_footprint(Some(footprint));
        let id = VirLoanId::new(0);
        let permission = AbstractPermission::new(
            provenance,
            footprint.range,
            AccessPermission::Read,
            FreeCapability::No,
        )
        .with_authority(PermissionAuthority::Loan(id));
        let key = ResourcePayloadKey::new(0, access);
        let mut allocation = allocation(16);
        allocation
            .set_resource_payload(
                key,
                MovePathState::available(TypedResourcePayload::new(pointer, permission)),
            )
            .unwrap();
        let mut state = ResourceState::new();
        state.define_allocation(storage, allocation).unwrap();
        state
            .define_value(source, AbstractValue::U64(start.interval()))
            .unwrap();
        state
            .define_value(authority, AbstractValue::Permission(permission))
            .unwrap();
        state
            .define_loan(
                id,
                AbstractLoan::new(
                    provenance,
                    footprint.envelope,
                    VirLoanKind::Shared,
                    VirBorrowRegionId::new(0),
                    None,
                    LoanActivity::Active,
                )
                .with_footprint(Some(footprint))
                .with_authority(authority),
            )
            .unwrap();
        for keep_symbol in [true, false] {
            let mut renames = vec![(authority, target_authority)];
            if keep_symbol {
                renames.push((source, target));
            }
            let remapper = ExpressionRemapper::new(&state, &renames);
            let projected = state.project_cfg_edge(&renames);
            let loan = projected.loan(id).unwrap();
            assert_eq!(loan.activity(), LoanActivity::Active);
            assert_eq!(loan.range(), footprint.envelope);
            assert!(loan.has_value_authority(target_authority));
            let selected = remapper.pointer(pointer).slice_footprint().unwrap();
            assert_eq!(selected.range, loan.actual_range());
            let MovePathState::Available(payload) =
                projected.allocation(storage).unwrap().resource_payload(key)
            else {
                panic!("payload must survive")
            };
            assert_eq!(payload.pointer().slice_footprint(), Some(selected));
            assert_eq!(payload.permission().range(), selected.range);
            if keep_symbol {
                assert_eq!(
                    selected.range.bounds().unwrap().0.expression().root(),
                    Some(target)
                );
            } else {
                assert_eq!(selected.range, AbstractByteRange::Unknown);
            }
        }
    }

    #[test]
    fn footprint_join_and_widen_never_promote_an_envelope_to_authority() {
        let id = VirLoanId::new(0);
        let envelope = range(0, 32);
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        let base = AbstractLoan::new(
            provenance,
            envelope,
            VirLoanKind::Shared,
            VirBorrowRegionId::new(0),
            None,
            LoanActivity::Active,
        );
        assert_eq!(base.actual_range(), AbstractByteRange::Unknown);
        let footprint = MemoryFootprint {
            provenance,
            access: VirMemoryAccess::core_u64(),
            stride_bytes: 8,
            range: AbstractByteRange::Exact(range(8, 16)),
            envelope,
        };
        let left = base.clone().with_footprint(Some(footprint));
        for other in [
            None,
            Some(MemoryFootprint {
                range: AbstractByteRange::Exact(range(16, 24)),
                ..footprint
            }),
            Some(MemoryFootprint {
                stride_bytes: 4,
                ..footprint
            }),
        ] {
            let right = base.clone().with_footprint(other);
            let mut a = ResourceState::new();
            let mut b = ResourceState::new();
            a.define_loan(id, left.clone()).unwrap();
            b.define_loan(id, right).unwrap();
            for joined in [a.join(&b).unwrap(), a.widen(&b).unwrap()] {
                let loan = joined.loan(id).unwrap();
                assert_eq!(loan.range(), envelope);
                assert_eq!(loan.actual_range(), AbstractByteRange::Unknown);
                assert_eq!(loan.activity(), LoanActivity::Active);
            }
        }
    }

    #[test]
    fn invalid_ranges_intervals_allocations_and_alignments_fail_closed() {
        assert!(matches!(
            ByteRange::new(2, 1),
            Err(ByteRangeError::Reversed { .. })
        ));
        assert!(matches!(
            ByteRange::from_start_and_length(u64::MAX, 1),
            Err(ByteRangeError::EndOverflow { .. })
        ));
        assert!(U64Interval::new(2, 1).is_err());
        assert!(GuaranteedAlignment::new(3).is_err());
        assert_eq!(
            AbstractAllocation::new(VirRegionId::new(0), 0, 8),
            Err(AbstractAllocationError::ZeroSize)
        );
    }
}
