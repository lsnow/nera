//! Loop observations and a conservative actual-effect frame. No resource
//! instruction is reimplemented here; access checks and effects use transfer.
use super::*;
use crate::verifier::spec::separation::MatchLedger;
use crate::verifier::transfer::{SymbolicSpecMemoryQuery, query_symbolic_spec_memory, spec_alive};
use crate::vir::ResourceLoopAtom as A;
use crate::{
    AffineExpression, SymbolicRangeBound, VirSpecEnvironment, VirSpecSnapshot as S, VirSpecTermId,
    VirSpecTermKind as T,
};

fn bound(
    specs: &VirSpecEnvironment,
    id: VirSpecTermId,
    state: &ResourceState,
) -> Option<SymbolicRangeBound> {
    let term = &specs.terms().get(id.get() as usize)?.kind;
    let leaf = |id: VirSpecTermId| match specs.terms().get(id.get() as usize)?.kind {
        T::U64(n) => Some(AffineExpression::constant(n)),
        T::Snapshot(S::Value { value, .. }) => Some(AffineExpression::identity(value)),
        _ => None,
    };
    let expression = match term {
        T::CheckedScale { operand, stride } => leaf(*operand)?.checked_scale(*stride)?,
        _ => leaf(id)?,
    };
    Some(SymbolicRangeBound::new(
        expression,
        expression.interval(|id| match state.value(id)? {
            AbstractValue::U64(value) => Some(*value),
            _ => None,
        })?,
    ))
}

fn query(
    specs: &VirSpecEnvironment,
    atom: A,
    state: &ResourceState,
) -> Option<SymbolicSpecMemoryQuery> {
    let A::Range {
        pointer,
        authority,
        start,
        end,
        layout,
        access,
        initialized,
    } = atom
    else {
        return None;
    };
    Some(SymbolicSpecMemoryQuery {
        pointer,
        authority,
        start: bound(specs, start, state)?,
        end: bound(specs, end, state)?,
        layout,
        access: match access {
            crate::SpecAccess::Read => crate::AccessPermission::Read,
            crate::SpecAccess::Write => crate::AccessPermission::Write,
        },
        initialized,
    })
}

pub(super) fn check(
    unit: &ResolvedVirUnit<'_>,
    atom: A,
    state: &ResourceState,
    ledger: &mut MatchLedger,
    config: CfgAnalysisConfig,
    budget: &mut VcQueryBudget,
) -> ObligationStatus {
    if let A::Alive(pointer) = atom {
        return spec_alive(state, pointer);
    }
    let Some(query) = query(&unit.as_unit().specs, atom, state) else {
        return ObligationStatus::Unknown;
    };
    let Some((status, footprint)) =
        query_symbolic_spec_memory(state, &unit.as_unit().memory, query, config, budget)
    else {
        return ObligationStatus::Unknown;
    };
    if status.is_proven() && query.authority.is_some() {
        ledger
            .reserve(state, footprint, budget)
            .unwrap_or(ObligationStatus::Unknown)
    } else {
        status
    }
}

pub(super) fn assume_initialized(
    unit: &ResolvedVirUnit<'_>,
    atom: A,
    state: &mut ResourceState,
    config: CfgAnalysisConfig,
) -> bool {
    if !matches!(
        atom,
        A::Range {
            initialized: true,
            ..
        }
    ) {
        return true;
    }
    let Some(query) = query(&unit.as_unit().specs, atom, state) else {
        return false;
    };
    // Geometry is a consequence of the scalar head premises. It is not proof
    // of initialization: the latter remains a provisional induction premise.
    let mut budget = VcQueryBudget::new(VcLimits::default());
    budget.relation_limits = config.relation_limits;
    let geometry = SymbolicSpecMemoryQuery {
        initialized: false,
        authority: None,
        ..query
    };
    if !query_symbolic_spec_memory(state, &unit.as_unit().memory, geometry, config, &mut budget)
        .is_some_and(|(status, _)| status.is_proven())
        || budget.exhausted
    {
        return false;
    }
    let Some(AbstractValue::Pointer(pointer)) = state.value(query.pointer).copied() else {
        return false;
    };
    let memory = &unit.as_unit().memory;
    let source = pointer.memory_access().unwrap();
    let stride = memory.object_shape(query.layout).unwrap().size_bytes();
    let length = memory.object_shape(source).unwrap().size_bytes() / stride;
    state.assume_loop_initialized(
        pointer,
        query.layout,
        (query.start.expression(), query.end.expression()),
        stride,
        length,
    )
}

/// Propagate only allocation provenance through the runtime SSA def-use graph.
/// Exact offsets are deliberately not guessed. EffectJournal then classifies
/// the real instructions using the same effect semantics as function frames.
/// Unknown/multiple origins havoc all entry allocations; not just one alias.
pub(super) fn modified_allocations(
    unit: &ResolvedVirUnit<'_>,
    function: &VirFunction,
    boundary: &crate::VirLoopBoundary,
    entry: &ResourceState,
    registry: Option<&super::super::super::summary::SummaryRegistry>,
) -> Result<BTreeSet<AbstractAllocationId>, CfgAnalysisError> {
    use crate::VirInstruction as I;
    let mut origins: BTreeMap<VirValueId, AbstractProvenance> = entry
        .values()
        .iter()
        .filter_map(|(id, value)| match value {
            AbstractValue::Pointer(p) => Some((*id, p.provenance())),
            _ => None,
        })
        .collect();
    let mut edges = Vec::new();
    let blocks: Vec<_> = function
        .blocks
        .iter()
        .filter(|b| boundary.blocks.contains(&b.id))
        .collect();
    for block in &blocks {
        for instruction in &block.instructions {
            if let I::Call {
                target,
                arguments,
                results,
            } = &instruction.instruction
            {
                // Admitted pointer results can only originate from arguments.
                // Union all possible inputs; never guess a selected borrow arm.
                for result in results
                    .iter()
                    .filter(|r| matches!(r.ty, VirType::Pointer { .. }))
                {
                    edges.extend(
                        arguments
                            .iter()
                            .zip(&target.signature.parameters)
                            .filter(|(_, ty)| matches!(ty, VirType::Pointer { .. }))
                            .map(|(arg, _)| (*arg, result.id)),
                    );
                }
            }
            match instruction.instruction {
                I::FieldAddress { result, base, .. }
                | I::TupleElementAddress { result, base, .. }
                | I::ObjectLeafAddress { result, base, .. }
                | I::IndexAddress { result, base, .. }
                | I::PointerOffset { result, base, .. }
                | I::RawAddress { result, base, .. } => edges.push((base, result.id)),
                I::SliceAddress {
                    pointer_result,
                    base,
                    ..
                }
                | I::SliceRange {
                    pointer_result,
                    base,
                    ..
                } => edges.push((base, pointer_result.id)),
                I::LoanBegin {
                    effect,
                    reference_result,
                    ..
                }
                | I::LoanReborrow {
                    effect,
                    reference_result,
                    ..
                }
                | I::LoanAliasShared {
                    effect,
                    reference_result,
                    ..
                } => edges.push((effect.source_pointer, reference_result.id)),
                I::LoanAliasAuthority {
                    effect,
                    reference_result,
                    ..
                }
                | I::LoanReborrowAuthority {
                    effect,
                    reference_result,
                    ..
                } => edges.push((effect.source_pointer, reference_result.id)),
                _ => {}
            }
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
            if target.block == boundary.header {
                continue;
            }
            if let Some(destination) = blocks.iter().find(|b| b.id == target.block) {
                edges.extend(
                    target
                        .arguments
                        .iter()
                        .copied()
                        .zip(&destination.parameters)
                        .filter(|(_, p)| matches!(p.ty, VirType::Pointer { .. }))
                        .map(|(source, p)| (source, p.id)),
                );
            }
        }
    }
    let mut work = 0usize;
    loop {
        let mut changed = false;
        for &(source, target) in &edges {
            work += 1;
            if work > 65_536 {
                return Err(CfgAnalysisError::LoopInvariantResourceStateUnsupported);
            }
            if let Some(value) = origins.get(&source).copied() {
                let next = origins.get(&target).map_or(value, |old| old.join(value));
                if origins.get(&target) != Some(&next) {
                    origins.insert(target, next);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    // A phi with even one unknown incoming origin cannot be narrowed to its
    // other, known incoming allocation. Conservatively discard the frame.
    if edges
        .iter()
        .any(|(source, _)| !origins.contains_key(source))
    {
        return Ok(entry.allocations().keys().copied().collect());
    }
    // No admitted callee can obtain another allocation from globals, storage,
    // pointer payloads or a fresh allocation. Conservatively havoc every actual
    // pointer argument's allocation; unknown origins lose the entire frame.
    let mut call_modified = BTreeSet::new();
    for block in &blocks {
        for instruction in &block.instructions {
            if let I::Call {
                target, arguments, ..
            } = &instruction.instruction
            {
                if registry.is_some_and(|r| r.preserves_loop_contents(target)) {
                    continue;
                }
                for (arg, ty) in arguments.iter().zip(&target.signature.parameters) {
                    if matches!(ty, VirType::Pointer { .. }) {
                        if let Some(AbstractProvenance::Known(id)) = origins.get(arg) {
                            call_modified.insert(*id);
                        } else {
                            call_modified.extend(entry.allocations().keys().copied());
                        }
                    }
                }
            }
        }
    }
    let mut observations = ResourceState::new();
    for (id, provenance) in origins {
        observations
            .define_value(
                id,
                AbstractValue::Pointer(crate::AbstractPointer::new(
                    provenance,
                    U64Interval::unknown(),
                    crate::GuaranteedAlignment::one(),
                )),
            )
            .unwrap();
    }
    let journal = std::cell::RefCell::new(super::super::super::summary::EffectJournal::default());
    let context = super::super::super::summary::SummaryTransferContext {
        site: None,
        case_ordinal: 0,
        audit_limit: 65_536,
        registry: None,
        journal: &journal,
        limit: 65_536,
    };
    for block in blocks {
        for instruction in &block.instructions {
            context.observe(
                &observations,
                &instruction.instruction,
                &unit.as_unit().memory,
            );
        }
    }
    let journal = journal.into_inner();
    if journal.incomplete {
        return Err(CfgAnalysisError::LoopInvariantResourceStateUnsupported);
    }
    let mut modified = call_modified;
    for event in journal.events {
        if event.kind != super::super::super::summary::EffectKind::Write {
            continue;
        }
        if let Some(AbstractProvenance::Known(id)) = event.pointer.map(|p| p.provenance()) {
            modified.insert(id);
        } else {
            modified.extend(entry.allocations().keys().copied());
        }
    }
    Ok(modified)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_write_origins_keep_separate_frames_but_unknown_aliases_havoc_all() {
        let source = "fn main(){let p=alloc<u64>(1); let q=alloc<u64>(1); let mut i=0;
            while i<3 {invariant i<=3; *p=i; i=i+1;} free(p); free(q); return;}";
        let output = crate::analyze(&crate::SourceFile::from_text("loop-frame.nera", source));
        let resolved = output.vir().unwrap().resolve().unwrap();
        let f = &resolved.as_unit().runtime.functions[0];
        let boundary = resolved.as_unit().specs.loop_invariants()[0]
            .boundary
            .as_ref()
            .unwrap();
        let header = f.blocks.iter().find(|b| b.id == boundary.header).unwrap();
        let pointer_ids: Vec<_> = header
            .parameters
            .iter()
            .filter(|p| matches!(p.ty, VirType::Pointer { .. }))
            .map(|p| p.id)
            .collect();
        assert_eq!(pointer_ids.len(), 2);
        let a = AbstractAllocationId::new(0);
        let b = AbstractAllocationId::new(1);
        let mut entry = ResourceState::new();
        for id in [a, b] {
            entry
                .define_allocation(id, crate::AbstractAllocation::new_local(8, 8).unwrap())
                .unwrap();
        }
        for (pointer, id) in pointer_ids.iter().zip([a, b]) {
            entry
                .define_value(
                    *pointer,
                    AbstractValue::Pointer(crate::AbstractPointer::new(
                        AbstractProvenance::Known(id),
                        U64Interval::exact(0),
                        crate::GuaranteedAlignment::one(),
                    )),
                )
                .unwrap();
        }
        let modified = modified_allocations(&resolved, f, boundary, &entry, None).unwrap();
        assert_eq!(modified.len(), 1);
        let written = *modified.first().unwrap();
        let pointer = pointer_ids[usize::from(written == b)];
        *entry.value_mut(pointer).unwrap() = AbstractValue::Pointer(crate::AbstractPointer::new(
            AbstractProvenance::Unknown,
            U64Interval::unknown(),
            crate::GuaranteedAlignment::one(),
        ));
        assert_eq!(
            modified_allocations(&resolved, f, boundary, &entry, None).unwrap(),
            BTreeSet::from([a, b])
        );
    }
}
