//! Structural loop interface. This is not an inductive proof.
use crate::{VirBlockId, VirBlockTarget, VirFunction, VirTerminator, VirType, VirValueId};
use std::collections::BTreeSet;
mod resources;
mod scalar;
pub(crate) use resources::{ResourceLoopAtom, resource_atom};
pub(crate) use scalar::{ScalarLoopAtom, ScalarOperand, scalar_atoms};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirLoopBinding {
    pub local: u32,
    pub entry: VirValueId,
    pub head: VirValueId,
    pub ty: VirType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirLoopEdge {
    pub source: VirBlockId,
    /// 0 = jump/true, 1 = false; None target denotes a return.
    pub arm: u8,
    pub target: Option<VirBlockId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirLoopBoundary {
    pub loop_id: u32,
    pub preheader: VirBlockId,
    pub header: VirBlockId,
    pub condition: VirBlockId,
    pub latch: Option<VirBlockId>,
    pub blocks: Vec<VirBlockId>,
    pub entries: Vec<VirLoopEdge>,
    pub back_edges: Vec<VirLoopEdge>,
    pub exits: Vec<VirLoopEdge>,
    pub bindings: Vec<VirLoopBinding>,
}

fn targets(t: &VirTerminator) -> Vec<(u8, Option<&VirBlockTarget>)> {
    match t {
        VirTerminator::Jump { target } => vec![(0, Some(target))],
        VirTerminator::Branch {
            then_target,
            else_target,
            ..
        } => vec![(0, Some(then_target)), (1, Some(else_target))],
        VirTerminator::Return { .. } => vec![(0, None)],
    }
}

impl VirLoopBoundary {
    /// Producer computes complete edge lists after all CFG passes. Validation
    /// recomputes them independently from the actual runtime terminators.
    pub(crate) fn edges(
        &self,
        function: &VirFunction,
    ) -> (Vec<VirLoopEdge>, Vec<VirLoopEdge>, Vec<VirLoopEdge>) {
        let members: BTreeSet<_> = self.blocks.iter().copied().collect();
        let (mut entries, mut back, mut exits) = (Vec::new(), Vec::new(), Vec::new());
        for b in &function.blocks {
            for (arm, target) in targets(&b.terminator.terminator) {
                let edge = VirLoopEdge {
                    source: b.id,
                    arm,
                    target: target.map(|t| t.block),
                };
                let inside = members.contains(&b.id);
                if !inside && target.is_some_and(|t| members.contains(&t.block)) {
                    entries.push(edge);
                }
                if inside && target.is_some_and(|t| t.block == self.header) {
                    back.push(edge);
                }
                if inside && target.is_none_or(|t| !members.contains(&t.block)) {
                    exits.push(edge);
                }
            }
        }
        entries.sort();
        back.sort();
        exits.sort();
        (entries, back, exits)
    }

    pub(crate) fn valid(&self, function: &VirFunction) -> bool {
        let members: BTreeSet<_> = self.blocks.iter().copied().collect();
        if self.blocks.is_empty()
            || members.len() != self.blocks.len()
            || !self.blocks.windows(2).all(|w| w[0] < w[1])
            || !members.contains(&self.header)
            || !members.contains(&self.condition)
            || members.contains(&self.preheader)
            || members.contains(&function.entry)
            || self.latch.is_some_and(|l| !members.contains(&l))
            || members
                .iter()
                .any(|id| !function.blocks.iter().any(|b| b.id == *id))
        {
            return false;
        }
        let (entries, back, exits) = self.edges(function);
        if entries != self.entries
            || back != self.back_edges
            || exits != self.exits
            || entries.len() != 1
            || entries[0].source != self.preheader
            || entries[0].target != Some(self.header)
            || back
                .iter()
                .any(|e| self.latch.is_some_and(|l| l != e.source))
        {
            return false;
        }
        let Some(pre) = function.blocks.iter().find(|b| b.id == self.preheader) else {
            return false;
        };
        let VirTerminator::Jump { target } = &pre.terminator.terminator else {
            return false;
        };
        let Some(header) = function.blocks.iter().find(|b| b.id == self.header) else {
            return false;
        };
        if target.block != self.header || target.arguments.len() != header.parameters.len() {
            return false;
        }
        // Require one connected structural region. Follow internal edges in
        // both directions: a for-loop's generated latch still belongs to the
        // loop when every body path breaks/returns, making that latch dead.
        // The complete single-entry check above independently ensures that
        // every executable member is entered through the header; connectivity
        // alone must never be used as a runtime reachability claim.
        let mut reached = BTreeSet::from([self.header]);
        loop {
            let before = reached.len();
            for b in &function.blocks {
                if members.contains(&b.id) {
                    for (_, t) in targets(&b.terminator.terminator) {
                        if let Some(t) = t
                            && members.contains(&t.block)
                            && (reached.contains(&b.id) || reached.contains(&t.block))
                        {
                            reached.insert(b.id);
                            reached.insert(t.block);
                        }
                    }
                }
            }
            if reached.len() == before {
                break;
            }
        }
        if reached != members
            || !function.blocks.iter().any(|b| {
                b.id == self.condition
                    && matches!(b.terminator.terminator, VirTerminator::Branch { .. })
            })
        {
            return false;
        }
        // The designated condition must dominate iteration completion and all
        // exits, not merely be some branch nested in the body.
        let mut without = BTreeSet::new();
        if self.header != self.condition {
            without.insert(self.header);
        }
        loop {
            let before = without.len();
            for b in &function.blocks {
                if without.contains(&b.id) {
                    for (_, t) in targets(&b.terminator.terminator) {
                        if let Some(t) = t
                            && t.block != self.condition
                            && members.contains(&t.block)
                        {
                            without.insert(t.block);
                        }
                    }
                }
            }
            if before == without.len() {
                break;
            }
        }
        if back
            .iter()
            .chain(&exits)
            .any(|e| without.contains(&e.source))
        {
            return false;
        }
        if !self.bindings.windows(2).all(|w| w[0].local < w[1].local) {
            return false;
        }
        self.bindings.iter().all(|binding| {
            if !matches!(binding.ty, VirType::U64 | VirType::Bool) {
                return false;
            }
            header
                .parameters
                .iter()
                .position(|p| p.id == binding.head && p.ty == binding.ty)
                .is_some_and(|slot| target.arguments[slot] == binding.entry)
        })
    }
}
