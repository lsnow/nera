use super::*;
use crate::verifier::vc::VcLimits;
use crate::{AbstractAllocationId, AbstractByteRange, AbstractProvenance, ByteRange, VirValueId};

fn footprint(start: u64, end: u64, write: bool, allocation: u32) -> SpecFootprint {
    SpecFootprint {
        provenance: AbstractProvenance::Known(AbstractAllocationId::vir_allocation_site(
            VirValueId::new(allocation),
        )),
        range: AbstractByteRange::Exact(ByteRange::new(start, end).unwrap()),
        access: if write {
            AccessPermission::Write
        } else {
            AccessPermission::Read
        },
    }
}

#[test]
fn matching_two_resources_agrees_with_an_independent_finite_byte_set_model() {
    let state = ResourceState::new();
    for a in 0..5 {
        for b in a..5 {
            for c in 0..5 {
                for d in c..5 {
                    for left_write in [false, true] {
                        for right_write in [false, true] {
                            for allocation in [0, 1] {
                                let mut ledger = MatchLedger::new(1);
                                let mut budget = VcQueryBudget::new(VcLimits::default());
                                assert_eq!(
                                    ledger.reserve(
                                        &state,
                                        footprint(a, b, left_write, 0),
                                        &mut budget
                                    ),
                                    Some(ObligationStatus::Proven)
                                );
                                let overlaps =
                                    allocation == 0 && (a..b).any(|byte| (c..d).contains(&byte));
                                let accepted = !(overlaps && (left_write || right_write));
                                assert_eq!(
                                    ledger.reserve(
                                        &state,
                                        footprint(c, d, right_write, allocation),
                                        &mut budget
                                    ),
                                    Some(if accepted {
                                        ObligationStatus::Proven
                                    } else {
                                        ObligationStatus::Refuted
                                    })
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn scratch_ledger_is_bounded_conservative_and_commits_no_partial_reservation() {
    let state = ResourceState::new();
    for limits in [
        VcLimits {
            max_queries: 0,
            ..VcLimits::default()
        },
        VcLimits {
            max_query_steps: 0,
            ..VcLimits::default()
        },
    ] {
        let mut ledger = MatchLedger::new(4);
        let mut budget = VcQueryBudget::new(limits);
        assert_eq!(
            ledger.reserve(&state, footprint(0, 8, true, 0), &mut budget),
            Some(ObligationStatus::Proven)
        );
        assert_eq!(
            ledger.reserve(&state, footprint(8, 16, true, 0), &mut budget),
            None
        );
        assert_eq!(ledger.used.len(), 1);
    }
    let mut ledger = MatchLedger::new(4);
    let mut budget = VcQueryBudget::new(VcLimits::default());
    ledger
        .reserve(&state, footprint(0, 8, true, 0), &mut budget)
        .unwrap();
    let mut uncertain = footprint(8, 16, true, 0);
    uncertain.range = AbstractByteRange::Unknown;
    assert_eq!(
        ledger.reserve(&state, uncertain, &mut budget),
        Some(ObligationStatus::Unknown)
    );
    assert_eq!(ledger.used.len(), 1);
    assert_eq!(
        ledger.reserve(&state, footprint(0, 8, true, 0), &mut budget),
        Some(ObligationStatus::Refuted)
    );
    assert_eq!(ledger.used.len(), 1);
    assert_eq!(
        ledger.reserve(&state, footprint(8, 16, true, 0), &mut budget),
        Some(ObligationStatus::Proven)
    );
    assert_eq!(state, ResourceState::new());
}
