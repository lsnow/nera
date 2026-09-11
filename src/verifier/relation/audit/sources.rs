//! Bounded structural source dependencies, never logical premises.
use super::*;
#[derive(Default)]
pub(crate) struct SourceIndex(
    std::collections::BTreeMap<crate::VirValueId, (Vec<VerifierFinding>, Vec<crate::VirValueId>)>,
);

impl SourceIndex {
    pub(crate) fn new(program: &crate::ResolvedVirUnit<'_>, function: &crate::VirFunction) -> Self {
        use crate::{VirLocation, VirTerminator};
        let mut index = Self::default();
        for block in &function.blocks {
            for parameter in &block.parameters {
                let entry = index.0.entry(parameter.id).or_default();
                if block.id == function.entry {
                    let location = VirLocation::FunctionEntry {
                        function: function.id,
                    };
                    if let Some(origin) = program.as_unit().source_map.origin_at(location) {
                        if let Some(span) = program
                            .as_unit()
                            .source_map
                            .source_span_for_origin(origin.id)
                        {
                            entry
                                .0
                                .extend(VerifierFinding::runtime(program, location, span.span));
                        }
                    }
                }
            }
            for (ordinal, instruction) in block.instructions.iter().enumerate() {
                let location = VirLocation::Instruction {
                    function: function.id,
                    block: block.id,
                    ordinal: ordinal as u64,
                };
                let finding = VerifierFinding::runtime(program, location, instruction.source_span);
                let mut operands = Vec::new();
                instruction.instruction.visit_operands(|v| operands.push(v));
                instruction.instruction.visit_results(|v| {
                    let entry = index.0.entry(v.id).or_default();
                    entry.0.extend(finding);
                    entry.1.extend_from_slice(&operands);
                });
            }
            let location = VirLocation::Terminator {
                function: function.id,
                block: block.id,
            };
            let finding = VerifierFinding::runtime(program, location, block.terminator.source_span);
            let (targets, condition) = match &block.terminator.terminator {
                VirTerminator::Jump { target } => (vec![target], None),
                VirTerminator::Branch {
                    condition,
                    then_target,
                    else_target,
                } => (vec![then_target, else_target], Some(*condition)),
                _ => (Vec::new(), None),
            };
            for target in targets {
                if let Some(destination) = function.blocks.iter().find(|b| b.id == target.block) {
                    for (p, a) in destination.parameters.iter().zip(&target.arguments) {
                        let entry = index.0.entry(p.id).or_default();
                        entry.0.extend(finding);
                        entry.1.push(*a);
                        entry.1.extend(condition);
                    }
                }
            }
        }
        index
    }

    pub(crate) fn sources(&self, query: &QueryObservation) -> (Vec<VerifierFinding>, bool) {
        use std::collections::BTreeSet;
        let mut pending = BTreeSet::new();
        fn term(t: RelationTerm, out: &mut BTreeSet<crate::VirValueId>) {
            match t {
                RelationTerm::Value { value, .. } => {
                    out.insert(value);
                }
                RelationTerm::PointerOffset { pointer, .. } => {
                    out.insert(pointer);
                }
                _ => {}
            }
        }
        fn bound(b: SymbolicRangeBound, out: &mut BTreeSet<crate::VirValueId>) {
            out.extend(b.expression().terms().into_iter().flatten().map(|(v, _)| v));
        }
        fn range(r: AbstractByteRange, out: &mut BTreeSet<crate::VirValueId>) {
            if let Some((a, b)) = r.bounds() {
                bound(a, out);
                bound(b, out);
            }
        }
        match query.goal {
            QueryGoal::Compare(g) => {
                term(g.left, &mut pending);
                term(g.right, &mut pending);
            }
            QueryGoal::Ordered(a, b) => {
                bound(a, &mut pending);
                bound(b, &mut pending);
            }
            QueryGoal::Contained(a, b) | QueryGoal::Disjoint(_, a, _, b) => {
                range(a, &mut pending);
                range(b, &mut pending);
            }
            QueryGoal::CoversAccess(r, p, w) => {
                range(r, &mut pending);
                range(access_range(p, w), &mut pending);
            }
            QueryGoal::NonOverlapping(a, ref b, w) => {
                range(access_range(a, w), &mut pending);
                range(access_range(**b, w), &mut pending);
            }
        }
        for p in &query.relations {
            match *p {
                DifferencePremise::Interval { value, .. } => {
                    pending.insert(value);
                }
                DifferencePremise::Bound { left, right, .. }
                | DifferencePremise::EqualOffset { left, right, .. }
                | DifferencePremise::Compare { left, right, .. } => {
                    term(left, &mut pending);
                    term(right, &mut pending);
                }
            }
        }
        for fact in query.guard.facts().into_iter().flatten() {
            match *fact {
                crate::PathFact::Boolean { value, .. } => {
                    pending.insert(value);
                }
                crate::PathFact::Comparison { left, right, .. } => {
                    pending.insert(left);
                    pending.insert(right);
                }
            }
        }
        self.values(pending)
    }

    pub(crate) fn values(
        &self,
        mut pending: std::collections::BTreeSet<crate::VirValueId>,
    ) -> (Vec<VerifierFinding>, bool) {
        use std::collections::BTreeSet;
        let mut visited = BTreeSet::new();
        let mut sources = BTreeSet::new();
        while let Some(value) = pending.pop_first() {
            if visited.contains(&value) {
                continue;
            }
            if visited.len() >= 128 {
                return (sources.into_iter().collect(), true);
            }
            visited.insert(value);
            if let Some((origins, operands)) = self.0.get(&value) {
                for origin in origins {
                    if sources.len() >= 128 && !sources.contains(origin) {
                        return (sources.into_iter().collect(), true);
                    }
                    sources.insert(*origin);
                }
                for operand in operands {
                    if pending.len() >= 128 && !pending.contains(operand) {
                        return (sources.into_iter().collect(), true);
                    }
                    pending.insert(*operand);
                }
            }
        }
        (sources.into_iter().collect(), false)
    }
}
