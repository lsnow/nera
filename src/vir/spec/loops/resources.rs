//! Resource observations supported by the stable-resource loop interface.
//! This is admission/decoding only, never an authority producer.
use super::*;
use crate::{
    SpecAccess, SpecAssertionKind as A, VirInstruction as I, VirMemoryAccess, VirSpecEnvironment,
    VirSpecSnapshot as S, VirSpecTermId, VirSpecTermKind as T,
};

#[derive(Clone, Copy, Debug)]
pub(crate) enum ResourceLoopAtom {
    Alive(VirValueId),
    Range {
        pointer: VirValueId,
        authority: Option<VirValueId>,
        start: VirSpecTermId,
        end: VirSpecTermId,
        layout: VirMemoryAccess,
        access: SpecAccess,
        initialized: bool,
    },
}

pub(crate) fn resource_atom(
    specs: &VirSpecEnvironment,
    root: crate::VirSpecAssertionId,
) -> Option<ResourceLoopAtom> {
    let value = |s| match s {
        S::Value { value, .. } => Some(value),
        _ => None,
    };
    let atom = match &specs.assertions().get(root.get() as usize)?.kind {
        A::Alive(pointer) => ResourceLoopAtom::Alive(value(*pointer)?),
        A::Initialized {
            pointer,
            start_bytes,
            end_bytes,
            layout,
        } => ResourceLoopAtom::Range {
            pointer: value(*pointer)?,
            authority: None,
            start: *start_bytes,
            end: *end_bytes,
            layout: *layout,
            access: SpecAccess::Read,
            initialized: true,
        },
        a @ (A::Permission(memory)
        | A::PointsTo {
            memory,
            value: None,
        }) => ResourceLoopAtom::Range {
            pointer: value(memory.pointer)?,
            authority: Some(value(memory.authority)?),
            start: memory.start_bytes,
            end: memory.end_bytes,
            layout: memory.layout,
            access: memory.access,
            initialized: matches!(a, A::PointsTo { .. }),
        },
        _ => return None,
    };
    if let ResourceLoopAtom::Range { start, end, .. } = atom {
        for id in [start, end] {
            let term = |id: VirSpecTermId| specs.terms().get(id.get() as usize);
            let leaf = |id| {
                matches!(
                    term(id).map(|t| &t.kind),
                    Some(T::U64(_) | T::Snapshot(S::Value { .. }))
                )
            };
            if !leaf(id)
                && !matches!(term(id).map(|t| &t.kind), Some(T::CheckedScale { operand, .. }) if leaf(*operand))
            {
                return None;
            }
        }
    }
    Some(atom)
}

pub(super) fn stable_resource_instruction(instruction: &I) -> bool {
    matches!(
        instruction,
        I::Constant { .. }
            | I::Call { .. }
            | I::WordAdd { .. }
            | I::Compare { .. }
            | I::Check { .. }
            | I::Load { .. }
            | I::Write { .. }
            | I::Initialize { .. }
            | I::Store { .. }
            | I::FieldAddress { .. }
            | I::TupleElementAddress { .. }
            | I::ObjectLeafAddress { .. }
            | I::IndexAddress { .. }
            | I::SliceAddress { .. }
            | I::SliceRange { .. }
            | I::PointerOffset { .. }
            | I::RawAddress { .. }
            | I::Free { .. }
            | I::DropOwn { .. }
            | I::LoanBegin { .. }
            | I::LoanEnd { .. }
            | I::LoanReborrow { .. }
            | I::LoanAliasShared { .. }
            | I::LoanAliasAuthority { .. }
            | I::LoanReborrowAuthority { .. }
            | I::LoanEndAuthority { .. }
            | I::PermissionMove { .. }
    )
}

/// Calls may only transitively use the monotone-initialization instruction
/// profile. This is an effect admission bound, never callee correctness proof.
pub(super) fn stable_calls(
    function: &VirFunction,
    boundary: &VirLoopBoundary,
    functions: &[VirFunction],
) -> bool {
    let mut pending: Vec<_> = function
        .blocks
        .iter()
        .filter(|b| boundary.blocks.contains(&b.id))
        .flat_map(|b| &b.instructions)
        .filter_map(|i| match &i.instruction {
            I::Call { target, .. } => Some(target),
            _ => None,
        })
        .collect();
    let mut seen = BTreeSet::new();
    let mut work = 65_536usize;
    while let Some(target) = pending.pop() {
        let Some(callee) = functions.iter().find(|f| {
            f.name == target.symbol
                && f.signature == target.signature
                && f.contract == target.contract
        }) else {
            return false;
        };
        if !seen.insert(callee.id) {
            continue;
        }
        if seen.len() > 64 {
            return false;
        }
        for i in callee.blocks.iter().flat_map(|b| &b.instructions) {
            let Some(remaining) = work.checked_sub(1) else {
                return false;
            };
            work = remaining;
            if !stable_resource_instruction(&i.instruction) {
                return false;
            }
            if let I::Call { target, .. } = &i.instruction {
                pending.push(target);
            }
        }
    }
    true
}
