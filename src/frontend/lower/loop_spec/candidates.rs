//! Bounded discovery only. Every emitted candidate still needs induction.
use super::*;
use crate::*;

const MAX_CANDIDATES: usize = 32;
const MAX_WORK: usize = 65_536;
pub(super) const MAX_INTERFACES: usize = 16;
pub(super) const MAX_BLOCKS: u32 = 512;
pub(super) const MAX_LOCALS: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Operand {
    Head(VirValueId),
    Constant(u64),
}

pub(in crate::frontend::lower) fn infer(
    runtime: &RuntimeVirProgram,
    sources: &VirSourceMap,
    loops: &[LoopSpec],
    specs: &mut VirSpecEnvironment,
) {
    for function in &runtime.functions {
        // Explicit clauses override discovery for their own loop only. Other
        // loops still need interfaces, including children of an explicit loop.
        let mut boundaries: Vec<_> = loops
            .iter()
            .filter(|l| {
                l.function == function.id
                    && !specs.loop_invariants().iter().any(|i| {
                        i.function == function.id
                            && i.boundary
                                .as_ref()
                                .is_some_and(|b| b.header == l.boundary.header)
                    })
            })
            .collect();
        if boundaries.is_empty()
            || boundaries.len() > MAX_INTERFACES
            || function.blocks.len() > MAX_BLOCKS as usize
            || function
                .blocks
                .iter()
                .map(|b| b.instructions.len())
                .sum::<usize>()
                > 4096
        {
            continue;
        }
        boundaries.sort_by_key(|l| l.loop_id);
        // Only nested regions form a discovery dependency. A non-admitted
        // sibling must not suppress a usable interface elsewhere in the CFG.
        let mut groups: BTreeMap<VirBlockId, Vec<&LoopSpec>> = BTreeMap::new();
        for boundary in boundaries {
            let outer = loops
                .iter()
                .filter(|l| {
                    l.function == function.id
                        && boundary
                            .boundary
                            .blocks
                            .iter()
                            .all(|id| l.boundary.blocks.contains(id))
                })
                .max_by_key(|l| l.boundary.blocks.len())
                .unwrap();
            groups
                .entry(outer.boundary.header)
                .or_default()
                .push(boundary);
        }
        let before = specs.loop_invariants().len();
        let mut work = MAX_WORK;
        for group in groups.values() {
            let mut trial = specs.clone();
            let group_start = trial.loop_invariants().len();
            let complete = group.iter().all(|l| {
                discover(function, sources, &l.boundary, &mut trial, &mut work).is_some()
                    && trial.loop_invariants().len() - before <= MAX_CANDIDATES
            });
            if complete
                && trial.loop_invariants()[group_start..].iter().all(|i| {
                    let b = i.boundary.as_ref().unwrap();
                    b.valid(function) && b.induction_profile(function, &trial, &runtime.functions)
                })
            {
                *specs = trial;
            }
        }
    }
}

fn targets(t: &VirTerminator) -> Vec<&VirBlockTarget> {
    match t {
        VirTerminator::Jump { target } => vec![target],
        VirTerminator::Branch {
            then_target,
            else_target,
            ..
        } => vec![then_target, else_target],
        VirTerminator::Return { .. } => vec![],
    }
}

fn discover(
    function: &VirFunction,
    sources: &VirSourceMap,
    original: &VirLoopBoundary,
    specs: &mut VirSpecEnvironment,
    work: &mut usize,
) -> Option<()> {
    let mut boundary = original.clone();
    (boundary.entries, boundary.back_edges, boundary.exits) = boundary.edges(function);
    let header = function.blocks.iter().find(|b| b.id == boundary.header)?;
    let pre = function
        .blocks
        .iter()
        .find(|b| b.id == boundary.preheader)?;
    let VirTerminator::Jump { target } = &pre.terminator.terminator else {
        return None;
    };
    // Include hidden for-bound carriers without adding runtime SSA values.
    let mut local = boundary
        .bindings
        .iter()
        .map(|b| b.local)
        .max()
        .unwrap_or(0)
        .checked_add(1)?;
    for (p, entry) in header.parameters.iter().zip(&target.arguments) {
        if matches!(p.ty, VirType::U64 | VirType::Bool)
            && !boundary.bindings.iter().any(|b| b.head == p.id)
        {
            boundary.bindings.push(VirLoopBinding {
                local,
                entry: *entry,
                head: p.id,
                ty: p.ty,
            });
            local = local.checked_add(1)?;
        }
    }
    let mut aliases: BTreeMap<_, Option<Operand>> = header
        .parameters
        .iter()
        .map(|p| (p.id, Some(Operand::Head(p.id))))
        .collect();
    // Constants are independent of first-iteration values; other results are unknown.
    for b in &function.blocks {
        for i in &b.instructions {
            i.instruction.visit_results(|v| {
                aliases.insert(v.id, None);
            });
            if let VirInstruction::Constant {
                result,
                value: VirConstant::U64(n),
            } = i.instruction
            {
                aliases.insert(result.id, Some(Operand::Constant(n)));
            }
        }
    }
    loop {
        let mut changed = false;
        for b in function
            .blocks
            .iter()
            .filter(|b| boundary.blocks.contains(&b.id))
        {
            for target in targets(&b.terminator.terminator) {
                if target.block == boundary.header || !boundary.blocks.contains(&target.block) {
                    continue;
                }
                let dest = function.blocks.iter().find(|b| b.id == target.block)?;
                for (source, p) in target.arguments.iter().zip(&dest.parameters) {
                    *work = work.checked_sub(1)?;
                    if let Some(origin) = aliases.get(source).copied() {
                        let next = aliases
                            .get(&p.id)
                            .map_or(origin, |old| if *old == origin { origin } else { None });
                        if aliases.get(&p.id) != Some(&next) {
                            aliases.insert(p.id, next);
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    let operand = |id| aliases.get(&id).copied().flatten();
    let condition = function
        .blocks
        .iter()
        .find(|b| b.id == boundary.condition)?;
    let VirTerminator::Branch {
        condition: guard, ..
    } = condition.terminator.terminator
    else {
        return None;
    };
    let (counter, bound) = condition
        .instructions
        .iter()
        .find_map(|i| match i.instruction {
            VirInstruction::Compare {
                result,
                predicate: VirIntegerPredicate::LessThan,
                left,
                right,
            } if result.id == guard => {
                let left = operand(left)?;
                let Operand::Head(counter) = left else {
                    return None;
                };
                Some((counter, operand(right)?))
            }
            _ => None,
        })?;
    let origin = sources
        .origin_at(VirLocation::BlockEntry {
            function: function.id,
            block: header.id,
        })?
        .id;
    let mut writer = Writer {
        function: function.id,
        boundary,
        origin,
        specs,
    };
    writer.upper_bound(counter, bound);
    let mut prefixes = BTreeSet::new();
    for b in function
        .blocks
        .iter()
        .filter(|b| writer.boundary.blocks.contains(&b.id))
    {
        for i in &b.instructions {
            *work = work.checked_sub(1)?;
            if let VirInstruction::IndexAddress {result, base, index, element, stride_bytes, ..} = i.instruction
                && operand(index) == Some(Operand::Head(counter))
                && let Some(Operand::Head(base)) = operand(base)
                && b.instructions.iter().any(|i| matches!(i.instruction,
                    VirInstruction::Write {pointer, ..} | VirInstruction::Initialize {pointer, ..} if pointer == result.id)) {
                prefixes.insert((base, element, stride_bytes));
            }
        }
    }
    if prefixes.len() > 8 {
        return None;
    }
    for (base, element, stride) in prefixes {
        writer.prefix(base, counter, element, stride);
    }
    Some(())
}

struct Writer<'a> {
    function: VirFunctionId,
    boundary: VirLoopBoundary,
    origin: VirOriginId,
    specs: &'a mut VirSpecEnvironment,
}
impl Writer<'_> {
    fn term(&mut self, ty: VirSpecType, kind: VirSpecTermKind) -> VirSpecTermId {
        let id = VirSpecTermId::new(self.specs.terms().len() as u32);
        let clause = VirSpecClauseId::new(self.specs.clauses().len() as u32);
        self.specs.terms_mut().push(VirSpecTerm {
            id,
            clause,
            ty,
            kind,
            origin: self.origin,
        });
        id
    }
    fn operand(&mut self, o: Operand) -> VirSpecTermId {
        self.term(
            VirSpecType::U64,
            match o {
                Operand::Constant(n) => VirSpecTermKind::U64(n),
                Operand::Head(value) => VirSpecTermKind::Snapshot(VirSpecSnapshot::Value {
                    function: self.function,
                    value,
                }),
            },
        )
    }
    fn finish(&mut self, kind: VirSpecClauseKind) {
        let id = VirSpecLoopInvariantId::new(self.specs.loop_invariants().len() as u32);
        let clause = VirSpecClauseId::new(self.specs.clauses().len() as u32);
        let location = VirSpecLocation::Runtime(VirLocation::BlockEntry {
            function: self.function,
            block: self.boundary.header,
        });
        self.specs.clauses_mut().push(VirSpecClause {
            id: clause,
            owner: VirSpecClauseOwner::LoopInvariant(id),
            location,
            origin: VirSpecClauseOrigin::InferredLoop {
                origin: self.origin,
            },
            kind,
        });
        self.specs.loop_invariants_mut().push(VirSpecLoopInvariant {
            id,
            function: self.function,
            location,
            clause,
            origin: self.origin,
            boundary: Some(self.boundary.clone()),
        });
    }
    fn upper_bound(&mut self, counter: VirValueId, bound: Operand) {
        let left = self.operand(Operand::Head(counter));
        let right = self.operand(bound);
        let root = self.term(
            VirSpecType::Bool,
            VirSpecTermKind::LessOrEqual { left, right },
        );
        self.finish(VirSpecClauseKind::Logic { root });
    }
    fn prefix(
        &mut self,
        pointer: VirValueId,
        counter: VirValueId,
        layout: VirMemoryAccess,
        stride: u64,
    ) {
        let start_bytes = self.operand(Operand::Constant(0));
        let operand = self.operand(Operand::Head(counter));
        let end_bytes = self.term(
            VirSpecType::U64,
            VirSpecTermKind::CheckedScale { operand, stride },
        );
        let root = VirSpecAssertionId::new(self.specs.assertions().len() as u32);
        let clause = VirSpecClauseId::new(self.specs.clauses().len() as u32);
        self.specs.assertions_mut().push(VirSpecAssertion {
            id: root,
            clause,
            origin: self.origin,
            kind: SpecAssertionKind::Initialized {
                pointer: VirSpecSnapshot::Value {
                    function: self.function,
                    value: pointer,
                },
                start_bytes,
                end_bytes,
                layout,
            },
        });
        self.finish(VirSpecClauseKind::Assertion { root });
    }
}
