//! Entry-bound effect upper bounds. Reads existing transfer events only;
//! declarations never replace real effects or manufacture frame facts.
use super::*;
use crate::verifier::{
    cfg::FunctionCfgAnalysis,
    summary::EffectKind,
    transfer::{SpecMemoryQuery, query_spec_memory, spec_range_footprint},
    vc::{SnapshotValues, VcLimits, VcNormalizer, VcQueryBudget, evaluate_contract_u64},
};
use crate::{SpecAssertionKind as A, VirSpecSnapshot as S};

pub(in crate::verifier) fn check(
    unit: &ResolvedVirUnit<'_>,
    function: &crate::VirFunction,
    cfg: &FunctionCfgAnalysis,
    inputs: &[VirValueId],
    config: crate::CfgAnalysisConfig,
) -> Vec<ContractCheck> {
    let state = cfg.function_entry_state();
    let mut snapshots = BTreeMap::new();
    for (slot, id) in inputs.iter().enumerate() {
        if let Some(value) = state.value(*id) {
            snapshots.insert(
                S::Parameter {
                    function: function.id,
                    slot: slot as u32,
                },
                (*value, state.word_expression(*id)),
            );
        }
    }
    let values = SnapshotValues::Bound {
        state,
        snapshots: &snapshots,
    };
    let mut normalizer = VcNormalizer::new(VcLimits::default());
    let mut budget = VcQueryBudget::new(VcLimits::default());
    budget.relation_limits = config.relation_limits;
    let mut declarations = [Vec::new(), Vec::new()];
    let mut coverage = [Vec::new(), Vec::new()];
    let mut statuses = [ObligationStatus::Proven; 2];
    let specs = &unit.as_unit().specs;
    for id in &specs.contract(function.contract).unwrap().clauses {
        let clause = specs.clause(*id).unwrap();
        let VirSpecClauseKind::Assertion { root } = clause.kind else {
            continue;
        };
        let A::Footprint { write, range } = &specs.assertions()[root.get() as usize].kind else {
            continue;
        };
        let kind = usize::from(*write);
        declarations[kind].push(ContractFactOrigin {
            clause: *id,
            position: VirContractPosition::Requires,
            source: clause.origin,
            source_span: unit
                .as_unit()
                .source_map
                .source_span_for_origin(clause.origin.origin())
                .unwrap()
                .span,
        });
        let Some(range) = range else { continue };
        let selected = (|| {
            // Reject unsupported observations before normalization can erase
            // their definedness. Footprint bounds are entry scalar values.
            if specs.terms().iter().any(|t| {
                t.clause == *id
                    && matches!(
                        t.kind,
                        crate::VirSpecTermKind::Snapshot(
                            S::Memory { .. } | S::Result { .. } | S::EntryParameter { .. }
                        )
                    )
            }) {
                return None;
            }
            let S::Parameter {
                function: owner,
                slot,
            } = range.pointer
            else {
                return None;
            };
            if owner != function.id {
                return None;
            }
            let pointer = *inputs.get(slot as usize)?;
            let start = normalizer.normalize(unit, range.start_bytes).ok()?;
            let end = normalizer.normalize(unit, range.end_bytes).ok()?;
            let query = SpecMemoryQuery {
                pointer,
                authority: None,
                start: evaluate_contract_u64(normalizer.arena(), start, values, &mut budget)?,
                end: evaluate_contract_u64(normalizer.arena(), end, values, &mut budget)?,
                layout: range.layout,
                access: AccessPermission::Read,
                initialized: false,
                valid: false,
            };
            if !query_spec_memory(state, &unit.as_unit().memory, query, config, &mut budget)?
                .is_proven()
            {
                return None;
            }
            let footprint = spec_range_footprint(state, query)?;
            let AbstractProvenance::Known(id) = footprint.provenance else {
                return None;
            };
            let AbstractByteRange::Exact(range) = footprint.range else {
                return None;
            };
            Some((id, range))
        })();
        if let Some(selected) = selected {
            coverage[kind].push(selected);
        } else {
            statuses[kind] = ObligationStatus::Unknown;
        }
    }
    if declarations.iter().all(Vec::is_empty) {
        return Vec::new();
    }
    let journal = &cfg.summary_events;
    let mut work = 0usize;
    for event in &journal.events {
        let kind = match event.kind {
            EffectKind::Read => 0,
            EffectKind::Write => 1,
            // Lifetime and free authority remain checked by real transfer;
            // a writes declaration neither suppresses nor authorizes them.
            EffectKind::Free | EffectKind::Allocate => continue,
        };
        if declarations[kind].is_empty() {
            continue;
        }
        let Some(pointer) = event.pointer else {
            statuses[kind] = ObligationStatus::Unknown;
            continue;
        };
        let AbstractProvenance::Known(id) = pointer.provenance() else {
            statuses[kind] = ObligationStatus::Unknown;
            continue;
        };
        // Stack storage cannot escape safe return checking. A function-local
        // heap slot known dead on every return is private too; unknown or
        // possibly escaping heap storage stays conservatively observable.
        if matches!(id, AbstractAllocationId::VirLocalStorageSite(_))
            || (matches!(id, AbstractAllocationId::VirAllocationSite(_))
                && !state.allocations().contains_key(&id)
                && !cfg.returns().is_empty()
                && cfg.returns().iter().all(|r| {
                    r.state()
                        .allocation(id)
                        .is_some_and(|a| a.liveness() == LivenessState::Dead)
                }))
        {
            continue;
        }
        let AbstractByteRange::Exact(actual) = event.range else {
            statuses[kind] = ObligationStatus::Unknown;
            continue;
        };
        let mut ranges = Vec::new();
        for (source, range) in &coverage[kind] {
            work = work.saturating_add(1);
            if work > config.max_region_pairs_per_instruction {
                statuses[kind] = ObligationStatus::Unknown;
                break;
            }
            if *source == id {
                ranges.push(*range);
            }
        }
        if work > config.max_region_pairs_per_instruction {
            break;
        }
        if !covers(&mut ranges, actual) && statuses[kind].is_proven() {
            let ambiguous_input_alias = matches!(
                id,
                AbstractAllocationId::AbiEntryPayload { leaf: u32::MAX, .. }
            ) && coverage[kind].iter().any(|(other, _)| {
                *other != id
                    && matches!(
                        other,
                        AbstractAllocationId::AbiEntryPayload { leaf: u32::MAX, .. }
                    )
            });
            statuses[kind] = if ambiguous_input_alias {
                ObligationStatus::Unknown
            } else {
                ObligationStatus::Refuted
            };
        }
    }
    if journal.incomplete
        || journal.audit_overflow
        || work > config.max_region_pairs_per_instruction
    {
        statuses = [ObligationStatus::Unknown; 2];
    }
    declarations
        .into_iter()
        .enumerate()
        .flat_map(|(kind, origins)| {
            origins.into_iter().map(move |origin| ContractCheck {
                clause: origin.clause,
                origin,
                status: statuses[kind],
            })
        })
        .collect()
}

fn covers(ranges: &mut [ByteRange], actual: ByteRange) -> bool {
    ranges.sort_by_key(|r| r.start());
    let mut cursor = actual.start();
    for range in ranges {
        if cursor >= actual.end() {
            return true;
        }
        if range.start() > cursor {
            break;
        }
        cursor = cursor.max(range.end());
    }
    cursor >= actual.end()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_union_matches_independent_finite_byte_sets() {
        for a in 0..=5 {
            for b in a..=5 {
                for c in 0..=5 {
                    for d in c..=5 {
                        for lo in 0..=5 {
                            for hi in lo..=5 {
                                let expected =
                                    (lo..hi).all(|i| (a..b).contains(&i) || (c..d).contains(&i));
                                assert_eq!(
                                    covers(
                                        &mut [
                                            ByteRange::new(a, b).unwrap(),
                                            ByteRange::new(c, d).unwrap()
                                        ],
                                        ByteRange::new(lo, hi).unwrap()
                                    ),
                                    expected
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}
