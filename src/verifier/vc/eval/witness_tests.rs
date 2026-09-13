use super::tests::function;
use super::*;
use crate::VirSpecType;

#[test]
fn witness_availability_is_distinct_from_symbolic_truth() {
    let function = function();
    let mut arena = VcArena::default();
    let root = arena
        .intern(
            VcTerm::Snapshot(VirSpecSnapshot::Result {
                function: function.id,
                slot: 0,
            }),
            16,
        )
        .unwrap();
    for (values, ty, available) in [
        (vec![], VirSpecType::Bool, false),
        (
            vec![AbstractValue::Bool(AbstractBool::Unknown)],
            VirSpecType::Bool,
            true,
        ),
        (
            vec![AbstractValue::U64(U64Interval::unknown())],
            VirSpecType::U64,
            true,
        ),
        (
            vec![AbstractValue::U64(U64Interval::unknown())],
            VirSpecType::Bool,
            false,
        ),
    ] {
        assert_eq!(
            validate_witness(
                &arena,
                root,
                ty,
                SnapshotValues::Results(&values),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            )
            .is_some(),
            available
        );
    }
    let reflexive = arena.intern(VcTerm::Equal(root, root), 16).unwrap();
    assert_eq!(
        evaluate_bool(
            &arena,
            reflexive,
            &BTreeSet::new(),
            SnapshotValues::Results(&[]),
            &function,
            &mut VcQueryBudget::new(VcLimits::default())
        ),
        Some(AbstractBool::Unknown)
    );
}

#[test]
fn witness_validation_checks_hidden_free_names_and_charges_its_work() {
    let function = function();
    let mut arena = VcArena::default();
    let truth = arena.intern(VcTerm::Bool(true), 16).unwrap();
    let free = arena.intern(VcTerm::Binder(0), 16).unwrap();
    let hidden = arena.intern(VcTerm::Or(vec![truth, free]), 16).unwrap();
    let values = SnapshotValues::Results(&[]);
    assert!(
        validate_witness(
            &arena,
            hidden,
            VirSpecType::Bool,
            values,
            &function,
            &mut VcQueryBudget::new(VcLimits::default())
        )
        .is_none()
    );
    for limits in [
        VcLimits {
            max_query_steps: 0,
            ..Default::default()
        },
        VcLimits {
            max_queries: 0,
            ..Default::default()
        },
    ] {
        assert!(
            validate_witness(
                &arena,
                truth,
                VirSpecType::Bool,
                values,
                &function,
                &mut VcQueryBudget::new(limits)
            )
            .is_none()
        );
    }
}
