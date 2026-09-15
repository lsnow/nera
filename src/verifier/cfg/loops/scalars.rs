//! A syntactic def-use proof of loop-invariant SSA carriers. No values are
//! guessed from first-iteration equality; instruction-produced values are top.
use super::*;

pub(super) fn unchanged(
    function: &VirFunction,
    boundary: &crate::VirLoopBoundary,
) -> BTreeSet<VirValueId> {
    let header = function
        .blocks
        .iter()
        .find(|b| b.id == boundary.header)
        .unwrap();
    let mut origins: BTreeMap<VirValueId, Option<VirValueId>> = header
        .parameters
        .iter()
        .filter(|p| matches!(p.ty, VirType::Bool | VirType::U64))
        .map(|p| (p.id, Some(p.id)))
        .collect();
    let mut edges = Vec::new();
    let mut back = Vec::new();
    let Some(reachable) = reachable_blocks(function, boundary) else {
        return BTreeSet::new();
    };
    for block in function.blocks.iter().filter(|b| reachable.contains(&b.id)) {
        for instruction in &block.instructions {
            instruction.instruction.visit_results(|value| {
                origins.insert(value.id, None);
            });
        }
        let targets: Vec<_> = match &block.terminator.terminator {
            VirTerminator::Jump { target } => vec![target],
            VirTerminator::Branch {
                then_target,
                else_target,
                ..
            } => vec![then_target, else_target],
            VirTerminator::Return { .. } => vec![],
        };
        for target in targets {
            if !boundary.blocks.contains(&target.block) {
                continue;
            }
            let destination = function
                .blocks
                .iter()
                .find(|b| b.id == target.block)
                .unwrap();
            for (source, parameter) in target.arguments.iter().zip(&destination.parameters) {
                if matches!(parameter.ty, VirType::Bool | VirType::U64) {
                    if target.block == boundary.header {
                        back.push((*source, parameter.id));
                    } else {
                        edges.push((*source, parameter.id));
                    }
                }
            }
        }
    }
    let mut work = 0;
    loop {
        let mut changed = false;
        for &(source, target) in &edges {
            work += 1;
            if work > 65_536 {
                return BTreeSet::new();
            }
            if let Some(origin) = origins.get(&source).copied() {
                let next = origins
                    .get(&target)
                    .map_or(origin, |old| if *old == origin { origin } else { None });
                if origins.get(&target) != Some(&next) {
                    origins.insert(target, next);
                    changed = true;
                }
            }
        }
        if !changed {
            // Unknown incoming phi arms must not inherit another arm's origin.
            for &(source, target) in &edges {
                if !origins.contains_key(&source) && origins.get(&target) != Some(&None) {
                    origins.insert(target, None);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
    header
        .parameters
        .iter()
        .filter(|p| {
            matches!(p.ty, VirType::Bool | VirType::U64)
                && back
                    .iter()
                    .filter(|(_, target)| *target == p.id)
                    .all(|(source, _)| origins.get(source) == Some(&Some(p.id)))
        })
        .map(|p| p.id)
        .collect()
}

pub(super) fn reachable_blocks(
    function: &VirFunction,
    boundary: &crate::VirLoopBoundary,
) -> Option<BTreeSet<VirBlockId>> {
    let mut reachable = BTreeSet::from([boundary.header]);
    let mut work = 0;
    loop {
        let before = reachable.len();
        for block in &function.blocks {
            work += 1;
            if work > 65_536 {
                return None;
            }
            if !reachable.contains(&block.id) {
                continue;
            }
            let targets: Vec<_> = match &block.terminator.terminator {
                VirTerminator::Jump { target } => vec![target.block],
                VirTerminator::Branch {
                    then_target,
                    else_target,
                    ..
                } => vec![then_target.block, else_target.block],
                VirTerminator::Return { .. } => vec![],
            };
            reachable.extend(
                targets
                    .into_iter()
                    .filter(|id| boundary.blocks.contains(id)),
            );
        }
        if reachable.len() == before {
            break;
        }
    }
    Some(reachable)
}
