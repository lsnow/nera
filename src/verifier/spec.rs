use std::collections::BTreeSet;

use crate::{
    ResolvedVirUnit, VirFunction, VirFunctionId, VirLocation, VirSpecClauseId, VirSpecClauseKind,
    VirSpecLocation, VirSpecProveId, VirSpecSnapshot, VirSpecTermId, VirSpecTermKind,
    VirTrustEntryId, VirTrustPolicyKind, VirTrustScope,
};

use super::cfg::{FunctionCfgAnalysis, FunctionReturnState};
use super::finding::VerifierFinding;
use super::resource::{AbstractBool, AbstractValue, PathFact, ResourceState, U64Interval};
use super::transfer::ObligationStatus;

/// Final result of one typed `Prove` obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SpecProof {
    prove: VirSpecProveId,
    finding: VerifierFinding,
    status: ObligationStatus,
}

impl SpecProof {
    #[must_use]
    pub const fn prove(self) -> VirSpecProveId {
        self.prove
    }

    #[must_use]
    pub const fn function(self) -> VirFunctionId {
        self.finding.site().function()
    }

    #[must_use]
    pub const fn location(self) -> VirSpecLocation {
        match self.finding.site() {
            super::finding::VerifierFindingSite::Spec { location, .. } => location,
            super::finding::VerifierFindingSite::Runtime(_) => {
                unreachable!()
            }
        }
    }

    #[must_use]
    pub const fn status(self) -> ObligationStatus {
        self.status
    }

    #[must_use]
    pub const fn finding(self) -> VerifierFinding {
        self.finding
    }

    #[must_use]
    pub const fn source_span(self) -> crate::ByteSpan {
        self.finding.source_span()
    }
}

/// One validated assumption that actually entered the proof environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TrustReportEntry {
    id: VirTrustEntryId,
    scope: VirTrustScope,
    policy: VirTrustPolicyKind,
    clause: VirSpecClauseId,
    finding: VerifierFinding,
}

impl TrustReportEntry {
    #[must_use]
    pub const fn id(self) -> VirTrustEntryId {
        self.id
    }

    #[must_use]
    pub const fn scope(self) -> VirTrustScope {
        self.scope
    }

    #[must_use]
    pub const fn policy(self) -> VirTrustPolicyKind {
        self.policy
    }

    #[must_use]
    pub const fn clause(self) -> VirSpecClauseId {
        self.clause
    }

    #[must_use]
    pub const fn finding(self) -> VerifierFinding {
        self.finding
    }

    #[must_use]
    pub const fn origin(self) -> crate::VirOriginId {
        self.finding.origin()
    }

    #[must_use]
    pub const fn source_span(self) -> crate::ByteSpan {
        self.finding.source_span()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum PureTerm {
    Bool(bool),
    U64(u64),
    Binder(u32),
    Snapshot(VirSpecSnapshot),
    Equal(Box<Self>, Box<Self>),
    LessThan(Box<Self>, Box<Self>),
    LessOrEqual(Box<Self>, Box<Self>),
    Not(Box<Self>),
    And(Vec<Self>),
    Or(Vec<Self>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PureValue {
    Bool(AbstractBool),
    U64(U64Interval),
}

pub(super) fn prove_function_specs(
    unit: &ResolvedVirUnit<'_>,
    function: &VirFunction,
    cfg: &FunctionCfgAnalysis,
) -> Option<Vec<SpecProof>> {
    unit.as_unit()
        .specs
        .proves()
        .iter()
        .filter(|prove| prove.function == function.id)
        .map(|prove| {
            let clause = unit
                .as_unit()
                .specs
                .clause(prove.clause)
                .expect("validated Prove clause remains present");
            let VirSpecClauseKind::Logic { root } = clause.kind else {
                unreachable!("validated Prove owns a logic clause")
            };
            let term = normalize(unit, root);
            let trusted = trusted_terms(unit, function.id, prove.location);
            let status = prove_at_location(function, cfg, prove.location, &term, &trusted);
            Some(SpecProof {
                prove: prove.id,
                finding: VerifierFinding::prove(unit, prove.id)?,
                status,
            })
        })
        .collect()
}

pub(super) fn collect_trust_entries(unit: &ResolvedVirUnit<'_>) -> Option<Vec<TrustReportEntry>> {
    unit.as_unit()
        .specs
        .trust_entries()
        .iter()
        .map(|entry| {
            Some(TrustReportEntry {
                id: entry.id,
                scope: entry.scope,
                policy: entry.policy,
                clause: entry.clause,
                finding: VerifierFinding::trust_entry(unit, entry.id)?,
            })
        })
        .collect()
}

fn trusted_terms(
    unit: &ResolvedVirUnit<'_>,
    function: VirFunctionId,
    location: VirSpecLocation,
) -> BTreeSet<PureTerm> {
    unit.as_unit()
        .specs
        .trust_entries()
        .iter()
        .filter(|entry| entry.scope.function() == function && entry.scope.location() == location)
        .map(|entry| {
            let clause = unit
                .as_unit()
                .specs
                .clause(entry.clause)
                .expect("validated trust clause remains present");
            let VirSpecClauseKind::Logic { root } = clause.kind else {
                unreachable!("validated trust entry owns a logic clause")
            };
            normalize(unit, root)
        })
        .collect()
}

fn normalize(unit: &ResolvedVirUnit<'_>, id: VirSpecTermId) -> PureTerm {
    let term = &unit.as_unit().specs.terms()[id.get() as usize];
    let child = |id| Box::new(normalize(unit, id));
    match &term.kind {
        VirSpecTermKind::Bool(value) => PureTerm::Bool(*value),
        VirSpecTermKind::U64(value) => PureTerm::U64(*value),
        VirSpecTermKind::Binder(id) => PureTerm::Binder(id.get()),
        VirSpecTermKind::Snapshot(snapshot) => PureTerm::Snapshot(*snapshot),
        VirSpecTermKind::Equal { left, right } => PureTerm::Equal(child(*left), child(*right)),
        VirSpecTermKind::LessThan { left, right } => {
            PureTerm::LessThan(child(*left), child(*right))
        }
        VirSpecTermKind::LessOrEqual { left, right } => {
            PureTerm::LessOrEqual(child(*left), child(*right))
        }
        VirSpecTermKind::Not(operand) => PureTerm::Not(child(*operand)),
        VirSpecTermKind::And(operands) => {
            PureTerm::And(operands.iter().map(|id| normalize(unit, *id)).collect())
        }
        VirSpecTermKind::Or(operands) => {
            PureTerm::Or(operands.iter().map(|id| normalize(unit, *id)).collect())
        }
    }
}

fn prove_at_location(
    function: &VirFunction,
    cfg: &FunctionCfgAnalysis,
    location: VirSpecLocation,
    term: &PureTerm,
    trusted: &BTreeSet<PureTerm>,
) -> ObligationStatus {
    match location {
        VirSpecLocation::FunctionEntry { .. } => status(eval(
            term,
            trusted,
            SnapshotValues::State(cfg.function_entry_state()),
            function,
        )),
        VirSpecLocation::FunctionResult { .. } => aggregate_results(
            cfg.returns()
                .iter()
                .map(|returned| prove_return(term, trusted, returned, function)),
        ),
        VirSpecLocation::Runtime(location) => {
            let Some(block) = location.block().and_then(|id| cfg.block(id)) else {
                return if matches!(location, VirLocation::FunctionEntry { .. }) {
                    status(eval(
                        term,
                        trusted,
                        SnapshotValues::State(cfg.function_entry_state()),
                        function,
                    ))
                } else {
                    ObligationStatus::Unknown
                };
            };
            let state = match location {
                VirLocation::BlockEntry { .. } | VirLocation::BlockParameter { .. } => {
                    block.entry_state()
                }
                VirLocation::Terminator { .. } => block.exit_state(),
                VirLocation::Instruction { ordinal, .. } => block
                    .instruction_states()
                    .get(ordinal as usize)
                    .unwrap_or_else(|| block.exit_state()),
                VirLocation::CallEdge { instruction, .. } => block
                    .instruction_states()
                    .get(instruction as usize)
                    .unwrap_or_else(|| block.exit_state()),
                VirLocation::FunctionEntry { .. } => unreachable!(),
            };
            status(eval(term, trusted, SnapshotValues::State(state), function))
        }
    }
}

fn prove_return(
    term: &PureTerm,
    trusted: &BTreeSet<PureTerm>,
    returned: &FunctionReturnState,
    function: &VirFunction,
) -> ObligationStatus {
    status(eval(
        term,
        trusted,
        SnapshotValues::Results(returned.values()),
        function,
    ))
}

fn aggregate_results(results: impl Iterator<Item = ObligationStatus>) -> ObligationStatus {
    let mut any = false;
    let mut unknown = false;
    for result in results {
        any = true;
        match result {
            ObligationStatus::Refuted => return ObligationStatus::Refuted,
            ObligationStatus::Unknown => unknown = true,
            ObligationStatus::Proven => {}
        }
    }
    if !any || unknown {
        ObligationStatus::Unknown
    } else {
        ObligationStatus::Proven
    }
}

#[derive(Clone, Copy)]
enum SnapshotValues<'a> {
    State(&'a ResourceState),
    Results(&'a [AbstractValue]),
}

fn eval(
    term: &PureTerm,
    trusted: &BTreeSet<PureTerm>,
    values: SnapshotValues<'_>,
    function: &VirFunction,
) -> PureValue {
    if trusted.contains(term) {
        return PureValue::Bool(AbstractBool::True);
    }
    match term {
        PureTerm::Bool(value) => PureValue::Bool(if *value {
            AbstractBool::True
        } else {
            AbstractBool::False
        }),
        PureTerm::U64(value) => PureValue::U64(U64Interval::exact(*value)),
        PureTerm::Binder(_) => PureValue::Bool(AbstractBool::Unknown),
        PureTerm::Snapshot(snapshot) => snapshot_value(*snapshot, values, function),
        PureTerm::Equal(left, right) => {
            if left == right {
                PureValue::Bool(AbstractBool::True)
            } else {
                PureValue::Bool(equal(
                    eval(left, trusted, values, function),
                    eval(right, trusted, values, function),
                ))
            }
        }
        PureTerm::LessThan(left, right) => PureValue::Bool(compare(
            eval(left, trusted, values, function),
            eval(right, trusted, values, function),
            false,
        )),
        PureTerm::LessOrEqual(left, right) => PureValue::Bool(compare(
            eval(left, trusted, values, function),
            eval(right, trusted, values, function),
            true,
        )),
        PureTerm::Not(operand) => {
            PureValue::Bool(match bool_value(eval(operand, trusted, values, function)) {
                AbstractBool::True => AbstractBool::False,
                AbstractBool::False => AbstractBool::True,
                AbstractBool::Unknown => AbstractBool::Unknown,
            })
        }
        PureTerm::And(operands) => PureValue::Bool(eval_and(
            operands
                .iter()
                .map(|operand| bool_value(eval(operand, trusted, values, function))),
        )),
        PureTerm::Or(operands) => PureValue::Bool(eval_or(
            operands
                .iter()
                .map(|operand| bool_value(eval(operand, trusted, values, function))),
        )),
    }
}

fn snapshot_value(
    snapshot: VirSpecSnapshot,
    values: SnapshotValues<'_>,
    function: &VirFunction,
) -> PureValue {
    let value = match (snapshot, values) {
        (
            VirSpecSnapshot::Parameter {
                function: owner,
                slot,
            },
            SnapshotValues::State(state),
        ) if owner == function.id => function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .and_then(|block| block.parameters.get(slot as usize))
            .and_then(|parameter| state.value(parameter.id))
            .copied(),
        (
            VirSpecSnapshot::Result {
                function: owner,
                slot,
            },
            SnapshotValues::Results(results),
        ) if owner == function.id => results.get(slot as usize).copied(),
        (
            VirSpecSnapshot::Value {
                function: owner,
                value,
            },
            SnapshotValues::State(state),
        ) if owner == function.id => state.value(value).copied().map(|abstract_value| {
            if abstract_value == AbstractValue::Bool(AbstractBool::Unknown)
                && state
                    .path_condition()
                    .implies(PathFact::boolean(value, true))
            {
                AbstractValue::Bool(AbstractBool::True)
            } else if abstract_value == AbstractValue::Bool(AbstractBool::Unknown)
                && state
                    .path_condition()
                    .implies(PathFact::boolean(value, false))
            {
                AbstractValue::Bool(AbstractBool::False)
            } else {
                abstract_value
            }
        }),
        _ => None,
    };
    match value {
        Some(AbstractValue::Bool(value)) => PureValue::Bool(value),
        Some(AbstractValue::U64(value)) => PureValue::U64(value),
        _ => PureValue::Bool(AbstractBool::Unknown),
    }
}

const fn bool_value(value: PureValue) -> AbstractBool {
    match value {
        PureValue::Bool(value) => value,
        PureValue::U64(_) => AbstractBool::Unknown,
    }
}

fn equal(left: PureValue, right: PureValue) -> AbstractBool {
    match (left, right) {
        (PureValue::Bool(left), PureValue::Bool(right)) => match (left, right) {
            (AbstractBool::True, AbstractBool::True)
            | (AbstractBool::False, AbstractBool::False) => AbstractBool::True,
            (AbstractBool::True, AbstractBool::False)
            | (AbstractBool::False, AbstractBool::True) => AbstractBool::False,
            _ => AbstractBool::Unknown,
        },
        (PureValue::U64(left), PureValue::U64(right)) => {
            if left.upper() < right.lower() || right.upper() < left.lower() {
                AbstractBool::False
            } else if left.exact_value() == right.exact_value() && left.exact_value().is_some() {
                AbstractBool::True
            } else {
                AbstractBool::Unknown
            }
        }
        _ => AbstractBool::Unknown,
    }
}

const fn compare(left: PureValue, right: PureValue, or_equal: bool) -> AbstractBool {
    let (PureValue::U64(left), PureValue::U64(right)) = (left, right) else {
        return AbstractBool::Unknown;
    };
    if (or_equal && left.upper() <= right.lower()) || (!or_equal && left.upper() < right.lower()) {
        AbstractBool::True
    } else if (or_equal && left.lower() > right.upper())
        || (!or_equal && left.lower() >= right.upper())
    {
        AbstractBool::False
    } else {
        AbstractBool::Unknown
    }
}

fn eval_and(values: impl Iterator<Item = AbstractBool>) -> AbstractBool {
    let mut unknown = false;
    for value in values {
        match value {
            AbstractBool::False => return AbstractBool::False,
            AbstractBool::Unknown => unknown = true,
            AbstractBool::True => {}
        }
    }
    if unknown {
        AbstractBool::Unknown
    } else {
        AbstractBool::True
    }
}

fn eval_or(values: impl Iterator<Item = AbstractBool>) -> AbstractBool {
    let mut unknown = false;
    for value in values {
        match value {
            AbstractBool::True => return AbstractBool::True,
            AbstractBool::Unknown => unknown = true,
            AbstractBool::False => {}
        }
    }
    if unknown {
        AbstractBool::Unknown
    } else {
        AbstractBool::False
    }
}

const fn status(value: PureValue) -> ObligationStatus {
    match bool_value(value) {
        AbstractBool::True => ObligationStatus::Proven,
        AbstractBool::False => ObligationStatus::Refuted,
        AbstractBool::Unknown => ObligationStatus::Unknown,
    }
}
