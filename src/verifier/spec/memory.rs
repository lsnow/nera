//! Bounded occurrence matching against one current guarded resource case.
//! Normalized terms may share structure; resource occurrences never do.
use super::*;
use crate::verifier::{
    resource::ResourceState,
    transfer::{
        SpecFootprint, SpecMemoryQuery, query_spec_memory, spec_alive, spec_footprint,
        spec_same_allocation, spec_scalar_contents,
    },
    vc::{evaluate_u64, validate_witness},
};
use crate::{SpecAssertionKind as A, VirSpecAssertionId, VirSpecSnapshot, VirValueId};
use std::collections::BTreeMap;

pub(super) fn contains_exists(
    unit: &ResolvedVirUnit<'_>,
    root: VirSpecAssertionId,
    limits: VcLimits,
    budget: &mut VcQueryBudget,
) -> Option<bool> {
    // Inspect the whole DAG before matching: failure of a selected witness is
    // not refutation of an existential, even if a sibling fails first or later.
    let mut pending = vec![root];
    let mut visited = BTreeSet::new();
    let mut exists = false;
    while let Some(id) = pending.pop() {
        budget.charge(1)?;
        if !visited.insert(id) {
            continue;
        }
        if visited.len() > limits.max_nodes {
            budget.exhausted = true;
            return None;
        }
        match &unit
            .as_unit()
            .specs
            .assertions()
            .get(id.get() as usize)?
            .kind
        {
            A::Exists { body, .. } => {
                exists = true;
                pending.push(*body);
            }
            A::Separation(children) => {
                budget.charge(children.len())?;
                pending.extend(children.iter().copied());
            }
            _ => {}
        }
    }
    Some(exists)
}

pub(super) fn prove(
    unit: &ResolvedVirUnit<'_>,
    function: &VirFunction,
    root: VirSpecAssertionId,
    values: SnapshotValues<'_>,
    normalizer: &mut VcNormalizer,
    budget: &mut VcQueryBudget,
    config: crate::CfgAnalysisConfig,
) -> (ObligationStatus, Option<SpecFailure>) {
    let context = MatchContext {
        unit,
        function,
        config,
        values,
    };
    context.prove(root, normalizer, budget)
}

enum Frame {
    Visit(VirSpecAssertionId),
    Exit(u32),
}

#[derive(Clone, Copy)]
struct MatchContext<'a, 'unit> {
    unit: &'a ResolvedVirUnit<'unit>,
    function: &'a VirFunction,
    config: crate::CfgAnalysisConfig,
    values: SnapshotValues<'a>,
}

impl MatchContext<'_, '_> {
    fn values(&self) -> Option<SnapshotValues<'_>> {
        match self.values {
            SnapshotValues::State(state) if !state.path_condition().is_reachable() => None,
            values => Some(values),
        }
    }

    fn state(&self) -> Option<&ResourceState> {
        match self.values {
            SnapshotValues::State(state) => Some(state),
            _ => None,
        }
    }

    fn prove(
        &self,
        root: VirSpecAssertionId,
        normalizer: &mut VcNormalizer,
        budget: &mut VcQueryBudget,
    ) -> (ObligationStatus, Option<SpecFailure>) {
        let Self { unit, config, .. } = *self;
        let mut ledger =
            super::separation::MatchLedger::new(config.max_region_pairs_per_instruction);
        let mut pending = vec![Frame::Visit(root)];
        let mut bindings = BTreeMap::new();
        let mut failure = SpecFailure::InsufficientFacts;
        let result = (|| {
            while let Some(frame) = pending.pop() {
                budget.charge(1)?;
                let id = match frame {
                    Frame::Visit(id) => id,
                    Frame::Exit(binder) => {
                        bindings.remove(&binder)?;
                        continue;
                    }
                };
                let kind = &unit
                    .as_unit()
                    .specs
                    .assertions()
                    .get(id.get() as usize)?
                    .kind;
                if let A::Separation(children) = kind {
                    budget.charge(children.len())?;
                    pending.extend(children.iter().rev().copied().map(Frame::Visit));
                    continue;
                }
                if let A::Exists {
                    binder,
                    body,
                    witness,
                } = kind
                {
                    failure = SpecFailure::InvalidWitness;
                    let ty = unit
                        .as_unit()
                        .specs
                        .binders()
                        .get(binder.get() as usize)?
                        .ty;
                    // Substitute in the OUTER environment; never bind a witness to
                    // itself or reuse source-term results from another instance.
                    let witness = normalizer
                        .normalize_bound(unit, (*witness)?, &bindings)
                        .ok()?;
                    validate_witness(
                        normalizer.arena(),
                        witness,
                        ty,
                        self.values()?,
                        self.function,
                        budget,
                    )?;
                    if bindings.insert(binder.get(), witness).is_some() {
                        return None;
                    }
                    pending.push(Frame::Exit(binder.get()));
                    pending.push(Frame::Visit(*body));
                    failure = SpecFailure::InsufficientFacts;
                    continue;
                }
                if matches!(kind, A::PointsTo { value: Some(_), .. }) {
                    failure = SpecFailure::UnsupportedTheory;
                }
                let (status, footprint) = self.leaf(kind, &bindings, normalizer, budget)?;
                if !status.is_proven() {
                    if status == ObligationStatus::Refuted {
                        failure = if matches!(kind, A::Pure(_)) {
                            SpecFailure::FalsePredicate
                        } else {
                            SpecFailure::ResourceConflict
                        };
                    }
                    return Some(status);
                }
                if let Some(footprint) = footprint {
                    let status = ledger.reserve(self.state()?, footprint, budget)?;
                    if !status.is_proven() {
                        failure = SpecFailure::ResourceConflict;
                        return Some(status);
                    }
                }
            }
            Some(ObligationStatus::Proven)
        })();
        let status = result.unwrap_or(ObligationStatus::Unknown);
        (status, (!status.is_proven()).then_some(failure))
    }

    fn leaf(
        &self,
        kind: &crate::VirSpecAssertionKind,
        bindings: &BTreeMap<u32, VcTermId>,
        normalizer: &mut VcNormalizer,
        budget: &mut VcQueryBudget,
    ) -> Option<(ObligationStatus, Option<SpecFootprint>)> {
        let Self {
            unit,
            function,
            config,
            ..
        } = *self;
        if let A::Pure(root) = kind {
            let term = normalizer.normalize_bound(unit, *root, bindings).ok()?;
            return Some((
                status(evaluate_bool(
                    normalizer.arena(),
                    term,
                    &BTreeSet::new(),
                    self.values()?,
                    function,
                    budget,
                )),
                None,
            ));
        }
        let state = self.state()?;
        if !state.path_condition().is_reachable()
            || state
                .relations()
                .precision_losses()
                .contains(&crate::verifier::relation::state::RelationPrecisionLoss::Inconsistent)
        {
            return None;
        }
        let snapshot = |s| snapshot_id(s, function);
        if let A::Disjoint { left, right } = kind {
            let mut range = |r: &crate::SpecMemoryRange<
                VirSpecSnapshot,
                crate::VirSpecTermId,
                crate::VirMemoryAccess,
            >|
             -> Option<SpecMemoryQuery> {
                Some(SpecMemoryQuery {
                    pointer: snapshot(r.pointer)?,
                    authority: None,
                    start: self.number(r.start_bytes, bindings, normalizer, budget)?,
                    end: self.number(r.end_bytes, bindings, normalizer, budget)?,
                    layout: r.layout,
                    access: crate::AccessPermission::Read,
                    initialized: false,
                    valid: false,
                })
            };
            let left = range(left)?;
            let right = range(right)?;
            return Some((
                crate::verifier::transfer::query_spec_disjoint(
                    state,
                    &unit.as_unit().memory,
                    left,
                    right,
                    config,
                    budget,
                )?,
                None,
            ));
        }
        budget.begin_query()?;
        budget.charge(1)?;
        let query = match kind {
            A::Alive(pointer) => return Some((spec_alive(state, snapshot(*pointer)?), None)),
            A::SameAllocation { left, right } => {
                return Some((
                    spec_same_allocation(state, snapshot(*left)?, snapshot(*right)?),
                    None,
                ));
            }
            A::Initialized {
                pointer,
                start_bytes,
                end_bytes,
                layout,
            } => SpecMemoryQuery {
                pointer: snapshot(*pointer)?,
                authority: None,
                start: self.number(*start_bytes, bindings, normalizer, budget)?,
                end: self.number(*end_bytes, bindings, normalizer, budget)?,
                layout: *layout,
                access: crate::AccessPermission::Read,
                initialized: true,
                valid: false,
            },
            A::Permission(memory) | A::PointsTo { memory, .. } => SpecMemoryQuery {
                pointer: snapshot(memory.pointer)?,
                authority: Some(snapshot(memory.authority)?),
                start: self.number(memory.start_bytes, bindings, normalizer, budget)?,
                end: self.number(memory.end_bytes, bindings, normalizer, budget)?,
                layout: memory.layout,
                access: match memory.access {
                    crate::SpecAccess::Read => crate::AccessPermission::Read,
                    crate::SpecAccess::Write => crate::AccessPermission::Write,
                },
                initialized: matches!(kind, A::PointsTo { .. }),
                valid: matches!(kind, A::PointsTo { .. }),
            },
            _ => return None,
        };
        let mut status = query_spec_memory(state, &unit.as_unit().memory, query, config, budget)?;
        if status.is_proven()
            && let A::PointsTo {
                value: Some(value), ..
            } = kind
        {
            let contents = spec_scalar_contents(state, &unit.as_unit().memory, query, budget);
            let root = normalizer.normalize_bound(unit, *value, bindings).ok()?;
            let expected = match unit.as_unit().memory.kind(query.layout.ty) {
                Some(crate::VirMemoryTypeKind::Bool) => evaluate_bool(
                    normalizer.arena(),
                    root,
                    &BTreeSet::new(),
                    self.values()?,
                    function,
                    budget,
                )
                .filter(|b| *b != AbstractBool::Unknown)
                .map(crate::AbstractValue::Bool),
                _ => evaluate_u64(normalizer.arena(), root, self.values()?, function, budget)
                    .map(|v| crate::AbstractValue::U64(crate::U64Interval::exact(v))),
            };
            status = match (contents, expected) {
                (Some(values), Some(expected)) if values.iter().all(|v| *v == expected) => {
                    ObligationStatus::Proven
                }
                (Some(values), Some(expected))
                    if values.iter().any(|v| scalar_disjoint(*v, expected)) =>
                {
                    ObligationStatus::Refuted
                }
                _ => ObligationStatus::Unknown,
            };
        }
        {
            let footprint = if status.is_proven() && query.authority.is_some() {
                Some(spec_footprint(state, query)?)
            } else {
                None
            };
            Some((status, footprint))
        }
    }
    fn number(
        &self,
        term: crate::VirSpecTermId,
        bindings: &BTreeMap<u32, VcTermId>,
        normalizer: &mut VcNormalizer,
        budget: &mut VcQueryBudget,
    ) -> Option<u64> {
        let term = normalizer.normalize_bound(self.unit, term, bindings).ok()?;
        evaluate_u64(
            normalizer.arena(),
            term,
            self.values()?,
            self.function,
            budget,
        )
    }
}

fn scalar_disjoint(a: crate::AbstractValue, b: crate::AbstractValue) -> bool {
    match (a, b) {
        (crate::AbstractValue::U64(a), crate::AbstractValue::U64(b)) => a.intersection(b).is_none(),
        (crate::AbstractValue::Bool(a), crate::AbstractValue::Bool(b)) => {
            a != AbstractBool::Unknown && b != AbstractBool::Unknown && a != b
        }
        _ => false,
    }
}

fn snapshot_id(snapshot: VirSpecSnapshot, function: &VirFunction) -> Option<VirValueId> {
    match snapshot {
        VirSpecSnapshot::Value {
            function: owner,
            value,
        } if owner == function.id => Some(value),
        VirSpecSnapshot::Parameter {
            function: owner,
            slot,
        } if owner == function.id => function
            .blocks
            .iter()
            .find(|b| b.id == function.entry)?
            .parameters
            .get(slot as usize)
            .map(|p| p.id),
        _ => None,
    }
}
