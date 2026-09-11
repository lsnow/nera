//! Read-only query journal. Records never feed the resource transfer.
//! Replay is exact recomputation by the trusted Rust kernel, not a certificate
//! checker. No global cache, wall-clock cutoff, or solver-supplied facts.
mod replay;
mod sources;
pub use replay::{RelationReplayCache, replay_query_evidence};
pub(crate) use sources::SourceIndex;

use std::cell::{Cell, RefCell};

use super::{RelationComparison, RelationTerm, difference::*, range::*};
use crate::{
    AbstractByteRange, AbstractPointer, AbstractProvenance, ObligationStatus, PathCondition,
    ResourceState, SymbolicRangeBound, VerifierFinding,
};

/// Independent of closure/branch/pair budgets. Overflow fails CFG analysis,
/// rather than publishing a partially audited successful verification.
pub const MAX_QUERIES_PER_SITE: usize = 4096;
pub const RELATION_THEORY: &str = "u64-nonwrapping/difference-i128/affine2/halfopen-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryGoal {
    Compare(DifferenceGoal),
    Ordered(SymbolicRangeBound, SymbolicRangeBound),
    Contained(AbstractByteRange, AbstractByteRange),
    CoversAccess(AbstractByteRange, AbstractPointer, u64),
    // Two full pointer snapshots must not inflate every scalar/range query.
    NonOverlapping(AbstractPointer, Box<AbstractPointer>, u64),
    Disjoint(
        AbstractProvenance,
        AbstractByteRange,
        AbstractProvenance,
        AbstractByteRange,
    ),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryWitness {
    Comparison {
        left: Option<crate::U64Interval>,
        right: Option<crate::U64Interval>,
        difference: Option<DifferenceEvidence>,
        stop: Option<DifferenceStop>,
    },
    Bounds(Vec<BoundEvidence>),
    Disjoint(Option<Box<DisjointEvidence>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QueryOutcome {
    Proven,
    /// Negation is implied by abstract premises; NOT a reachable execution.
    RefutedCondition,
    MissingRelation,
    BudgetExhausted,
    UnsupportedTheory,
    InconsistentPremises,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryObservation {
    pub theory: &'static str,
    pub goal: QueryGoal,
    pub guard: PathCondition,
    /// Closed, valid facts at the exact query point (including call effects).
    pub relations: Vec<DifferencePremise>,
    pub precision_losses: Vec<super::state::RelationPrecisionLoss>,
    pub limits: DifferenceLimits,
    pub status: ObligationStatus,
    pub outcome: QueryOutcome,
    pub witness: QueryWitness,
    pub kernel_version: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryEvidence {
    pub config: crate::CfgAnalysisConfig,
    /// Structural source dependencies; incoming edges are candidate producers,
    /// not additional logical premises. The guard identifies the effective case.
    pub sources: Vec<VerifierFinding>,
    pub sources_truncated: bool,
    pub finding: VerifierFinding,
    pub case_ordinal: usize,
    /// Separates then/else projections at the same terminator.
    pub edge_ordinal: Option<u8>,
    pub query_ordinal: usize,
    pub query: QueryObservation,
}

/// A site-local journal, not part of ResourceState equality or CFG joins.
#[derive(Default)]
pub(crate) struct QueryLog {
    records: RefCell<Vec<QueryObservation>>,
    overflow: Cell<bool>,
}

impl QueryLog {
    pub(crate) fn finish(self) -> Option<Vec<QueryObservation>> {
        (!self.overflow.get()).then(|| self.records.into_inner())
    }

    fn record(
        &self,
        state: &ResourceState,
        goal: QueryGoal,
        limits: DifferenceLimits,
        status: ObligationStatus,
        witness: QueryWitness,
    ) -> ObligationStatus {
        let mut records = self.records.borrow_mut();
        if records.len() >= MAX_QUERIES_PER_SITE {
            self.overflow.set(true);
        } else {
            records.push(QueryObservation {
                theory: RELATION_THEORY,
                goal,
                guard: state.path_condition().clone(),
                relations: state.relations().premises(),
                precision_losses: state
                    .relations()
                    .precision_losses()
                    .iter()
                    .copied()
                    .collect(),
                limits,
                status,
                outcome: outcome(status, &witness),
                witness,
                kernel_version: super::RELATION_KERNEL_VERSION,
            });
        }
        status
    }

    pub(crate) fn compare(
        &self,
        state: &ResourceState,
        comparison: RelationComparison,
        left: RelationTerm,
        right: RelationTerm,
        limits: DifferenceLimits,
    ) -> ObligationStatus {
        let (status, difference, stop) =
            super::local::compare_observed(state, comparison, left, right, limits);
        self.record(
            state,
            QueryGoal::Compare(DifferenceGoal {
                comparison,
                left,
                right,
            }),
            limits,
            status,
            QueryWitness::Comparison {
                left: super::local::interval(state, left),
                right: super::local::interval(state, right),
                difference,
                stop,
            },
        )
    }

    pub(crate) fn contained(
        &self,
        state: &ResourceState,
        outer: AbstractByteRange,
        inner: AbstractByteRange,
        limits: DifferenceLimits,
    ) -> ObligationStatus {
        let (status, bounds) = super::range::contained(state, outer, inner, limits);
        self.record(
            state,
            QueryGoal::Contained(outer, inner),
            limits,
            status,
            QueryWitness::Bounds(bounds),
        )
    }

    pub(crate) fn ordered(
        &self,
        state: &ResourceState,
        left: SymbolicRangeBound,
        right: SymbolicRangeBound,
        limits: DifferenceLimits,
    ) -> ObligationStatus {
        let bound = super::range::ordered(state, left, right, limits);
        self.record(
            state,
            QueryGoal::Ordered(left, right),
            limits,
            bound.status,
            QueryWitness::Bounds(vec![bound]),
        )
    }

    pub(crate) fn covers_access(
        &self,
        state: &ResourceState,
        outer: AbstractByteRange,
        pointer: AbstractPointer,
        width: u64,
        limits: DifferenceLimits,
    ) -> ObligationStatus {
        let (status, bounds) = super::range::covers_access(state, outer, pointer, width, limits);
        self.record(
            state,
            QueryGoal::CoversAccess(outer, pointer, width),
            limits,
            status,
            QueryWitness::Bounds(bounds),
        )
    }

    pub(crate) fn disjoint(
        &self,
        state: &ResourceState,
        a: AbstractProvenance,
        left: AbstractByteRange,
        b: AbstractProvenance,
        right: AbstractByteRange,
        limits: DifferenceLimits,
    ) -> ObligationStatus {
        let (status, proof) = super::range::disjoint(state, a, left, b, right, limits);
        self.record(
            state,
            QueryGoal::Disjoint(a, left, b, right),
            limits,
            status,
            QueryWitness::Disjoint(proof.map(Box::new)),
        )
    }

    pub(crate) fn non_overlapping(
        &self,
        state: &ResourceState,
        left: AbstractPointer,
        right: AbstractPointer,
        width: u64,
        limits: DifferenceLimits,
    ) -> ObligationStatus {
        let (status, proof) = super::range::non_overlapping(state, left, right, width, limits);
        self.record(
            state,
            QueryGoal::NonOverlapping(left, Box::new(right), width),
            limits,
            status,
            QueryWitness::Disjoint(proof.map(Box::new)),
        )
    }
}

fn outcome(status: ObligationStatus, witness: &QueryWitness) -> QueryOutcome {
    if status == ObligationStatus::Proven {
        return QueryOutcome::Proven;
    }
    if status == ObligationStatus::Refuted {
        return QueryOutcome::RefutedCondition;
    }
    let mut stops = Vec::new();
    fn bound(b: &BoundEvidence, stops: &mut Vec<DifferenceStop>) {
        stops.extend(b.stop);
        stops.extend(b.difference.as_ref().map(|e| e.stop));
    }
    fn disjoint(d: &DisjointEvidence, stops: &mut Vec<DifferenceStop>) {
        stops.extend(d.index_stop);
        for attempt in &d.failed_bands {
            disjoint(&attempt.proof, stops);
        }
        for b in &d.orders {
            bound(b, stops);
        }
        stops.extend(d.index_separation.as_ref().map(|e| e.stop));
        if let Some(b) = &d.bands {
            disjoint(&b.proof, stops);
        }
    }
    match witness {
        QueryWitness::Comparison {
            difference, stop, ..
        } => {
            stops.extend(*stop);
            stops.extend(difference.as_ref().map(|e| e.stop));
        }
        QueryWitness::Bounds(bounds) => {
            for b in bounds {
                bound(b, &mut stops);
            }
        }
        QueryWitness::Disjoint(Some(d)) => disjoint(d, &mut stops),
        QueryWitness::Disjoint(None) => {}
    }
    if stops.contains(&DifferenceStop::Budget) {
        QueryOutcome::BudgetExhausted
    } else if stops.contains(&DifferenceStop::InvalidInput)
        || stops.contains(&DifferenceStop::ArithmeticOverflow)
    {
        QueryOutcome::UnsupportedTheory
    } else if stops.contains(&DifferenceStop::Inconsistent) {
        QueryOutcome::InconsistentPremises
    } else {
        QueryOutcome::MissingRelation
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AbstractValue, AffineExpression, U64Interval, VirValueId};

    #[test]
    fn projection_budget_and_unsupported_theory_are_not_missing_relations() {
        let mut state = ResourceState::new();
        for id in 0..2 {
            state
                .define_value(
                    VirValueId::new(id),
                    AbstractValue::U64(U64Interval::new(0, 4).unwrap()),
                )
                .unwrap();
        }
        let log = QueryLog::default();
        log.compare(
            &state,
            RelationComparison::LessThan,
            word(VirValueId::new(0)),
            word(VirValueId::new(1)),
            DifferenceLimits {
                max_variables: 0,
                ..Default::default()
            },
        );
        log.compare(
            &state,
            RelationComparison::LessThan,
            word(VirValueId::new(0)),
            word(VirValueId::new(1)),
            Default::default(),
        );
        let bound = |id, scale| {
            SymbolicRangeBound::new(
                AffineExpression::identity(VirValueId::new(id))
                    .checked_scale(scale)
                    .unwrap(),
                U64Interval::new(0, 4 * scale).unwrap(),
            )
        };
        log.ordered(&state, bound(0, 2), bound(1, 3), Default::default());
        let records = log.finish().unwrap();
        assert_eq!(
            records.iter().map(|r| r.outcome).collect::<Vec<_>>(),
            [
                QueryOutcome::BudgetExhausted,
                QueryOutcome::MissingRelation,
                QueryOutcome::UnsupportedTheory
            ]
        );
    }

    #[test]
    fn journal_limit_never_changes_resource_state_or_fast_path_answer() {
        let state = ResourceState::new();
        let before = state.clone();
        let log = QueryLog::default();
        for _ in 0..=MAX_QUERIES_PER_SITE {
            assert_eq!(
                log.compare(
                    &state,
                    RelationComparison::LessThan,
                    RelationTerm::Constant(0),
                    RelationTerm::Constant(1),
                    Default::default()
                ),
                ObligationStatus::Proven
            );
        }
        assert!(log.finish().is_none());
        assert_eq!(state, before);
    }

    #[test]
    fn finite_interval_models_agree_and_small_budgets_cannot_invent_success() {
        for lo in 0..4 {
            for hi in lo..4 {
                for bound in 0..5 {
                    let mut state = ResourceState::new();
                    state
                        .define_value(
                            VirValueId::new(0),
                            AbstractValue::U64(U64Interval::new(lo, hi).unwrap()),
                        )
                        .unwrap();
                    for steps in [0, 1, 8, 65536] {
                        let log = QueryLog::default();
                        let status = log.compare(
                            &state,
                            RelationComparison::LessThan,
                            word(VirValueId::new(0)),
                            RelationTerm::Constant(bound),
                            DifferenceLimits {
                                max_steps: steps,
                                ..Default::default()
                            },
                        );
                        if status == ObligationStatus::Proven {
                            assert!((lo..=hi).all(|x| x < bound));
                        }
                        if status == ObligationStatus::Refuted {
                            assert!((lo..=hi).all(|x| x >= bound));
                        }
                        assert_eq!(log.finish().unwrap()[0].status, status);
                    }
                }
            }
        }
    }
}
