use super::*;

fn snapshot(epoch: u64, boolean: bool) -> ScalarCellSnapshot {
    ScalarCellSnapshot {
        epoch,
        allocation: AbstractAllocationId::new(0),
        bytes: ByteRange::new(0, if boolean { 1 } else { 8 }).unwrap(),
        access: if boolean {
            VirMemoryAccess::new(crate::VirTypeId::new(99), crate::VirLayoutId::new(99))
        } else {
            VirMemoryAccess::core_u64()
        },
    }
}

#[test]
fn snapshots_need_real_live_initialized_valid_cells() {
    for boolean in [false, true] {
        let snapshot = snapshot(1, boolean);
        let unknown = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::unknown())
        };
        let mut a = AbstractAllocation::new_local(16, 8).unwrap();
        let before = a.clone();
        assert!(!a.seed_cell_snapshot(snapshot));
        assert_eq!(a, before);
        a.mark_initialized(snapshot.bytes).unwrap();
        a.mark_valid(snapshot.bytes).unwrap();
        assert!(!a.seed_cell_snapshot(snapshot));
        a.record_scalar_content(snapshot.bytes, snapshot.access, unknown);
        assert!(a.seed_cell_snapshot(snapshot));
        let seeded = a.clone();
        assert!(a.seed_cell_snapshot(ScalarCellSnapshot {
            epoch: 2,
            ..snapshot
        }));
        assert_eq!(a, seeded, "surviving identity must not be replaced");
        a.mark_dead();
        assert!(!a.seed_cell_snapshot(snapshot));
    }
}

#[test]
fn snapshots_follow_values_and_are_not_recovered_from_equal_intervals() {
    for boolean in [false, true] {
        let first = snapshot(1, boolean);
        let second = ScalarCellSnapshot { epoch: 2, ..first };
        let unknown = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::unknown())
        };
        let mut a = AbstractAllocation::new_local(16, 8).unwrap();
        a.mark_initialized(ByteRange::new(0, 16).unwrap()).unwrap();
        a.mark_valid(ByteRange::new(0, 16).unwrap()).unwrap();
        a.record_scalar_content(first.bytes, first.access, unknown);
        assert!(a.seed_cell_snapshot(first));
        let initial = a.clone();
        let target = ByteRange::new(8, 8 + first.bytes.end()).unwrap();
        a.copy_scalar_contents(&initial, first.bytes, 8);
        assert_eq!(
            a.scalar_origin(target, first.access),
            initial.scalar_origin(first.bytes, first.access)
        );
        assert_eq!(
            a.bool_origin(target, first.access),
            initial.bool_origin(first.bytes, first.access)
        );
        a.record_scalar_content(first.bytes, first.access, unknown);
        assert_eq!(a.scalar_origin(first.bytes, first.access), None);
        assert_eq!(a.bool_origin(first.bytes, first.access), None);
        assert!(a.seed_cell_snapshot(second));
        let joined = a.join(first.allocation, &initial).unwrap();
        assert_eq!(joined.scalar_origin(first.bytes, first.access), None);
        assert_eq!(joined.bool_origin(first.bytes, first.access), None);
        if boolean {
            assert_ne!(
                a.bool_origin(first.bytes, first.access),
                initial.bool_origin(first.bytes, first.access)
            );
        } else {
            assert_ne!(
                a.scalar_origin(first.bytes, first.access),
                initial.scalar_origin(first.bytes, first.access)
            );
        }
    }
}
