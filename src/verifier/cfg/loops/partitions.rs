//! Untrusted, finite comparison thresholds. No runtime value or resource is
//! assumed by discovery; thresholds only select a disjunctive widening policy.
use super::*;

pub(in crate::verifier::cfg) fn discover(function: &VirFunction, limit: usize) -> Vec<u64> {
    if limit == 0
        || function
            .blocks
            .iter()
            .map(|b| b.instructions.len())
            .sum::<usize>()
            > 65_536
    {
        return Vec::new();
    }
    let constants: BTreeMap<_, _> = function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter_map(|i| match i.instruction {
            VirInstruction::Constant {
                result,
                value: crate::VirConstant::U64(value),
            } => Some((result.id, value)),
            _ => None,
        })
        .collect();
    let mut cuts = BTreeSet::new();
    for instruction in function.blocks.iter().flat_map(|b| &b.instructions) {
        if let VirInstruction::Compare { left, right, .. } = instruction.instruction {
            for value in [left, right].iter().filter_map(|id| constants.get(id)) {
                cuts.insert(*value);
                if let Some(after) = value.checked_add(1) {
                    cuts.insert(after);
                }
            }
        }
    }
    cuts.remove(&0);
    cuts.into_iter().take(limit.min(16)).collect()
}
