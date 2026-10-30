//! Explicit-fold and source-call candidates for existential loop abstraction. A declaration is
//! only a candidate: entry/backedge resource checks and ordinary checked call
//! transfer must independently establish every package and its representation.
use super::*;

pub(super) fn repacked_declarations(
    unit: &ResolvedVirUnit<'_>,
    function: &VirFunction,
    boundary: &crate::VirLoopBoundary,
) -> Result<BTreeSet<crate::VirPredicateId>, CfgAnalysisError> {
    let unsupported = || CfgAnalysisError::LoopInvariantResourceStateUnsupported;
    let mut work = 65_536usize;
    let mut charge = || {
        work = work.checked_sub(1).ok_or_else(unsupported)?;
        Ok::<_, CfgAnalysisError>(())
    };
    let mut interfaces = BTreeMap::<_, (BTreeSet<_>, BTreeSet<_>)>::new();
    for interface in unit.as_unit().specs.predicate_interfaces() {
        charge()?;
        let (requires, ensures) = interfaces.entry(interface.function).or_default();
        if interface.ensures { ensures } else { requires }.insert(interface.predicate);
    }
    let mut declarations = BTreeSet::new();
    for action in unit.as_unit().specs.predicate_actions() {
        charge()?;
        if action.location.function() == function.id
            && action
                .location
                .block()
                .is_some_and(|block| boundary.blocks.contains(&block))
            && matches!(action.kind, crate::VirPredicateActionKind::Fold { .. })
        {
            declarations.insert(action.predicate);
        }
    }
    for instruction in function
        .blocks
        .iter()
        .filter(|block| boundary.blocks.contains(&block.id))
        .flat_map(|block| &block.instructions)
    {
        charge()?;
        let crate::VirInstruction::Call { target, .. } = &instruction.instruction else {
            continue;
        };
        let mut callee = None;
        for candidate in &unit.as_unit().runtime.functions {
            charge()?;
            if candidate.name == target.symbol
                && candidate.signature == target.signature
                && candidate.contract == target.contract
                && callee.replace(candidate.id).is_some()
            {
                return Err(unsupported());
            }
        }
        let callee = callee.ok_or_else(unsupported)?;
        if let Some((requires, ensures)) = interfaces.get(&callee) {
            for predicate in requires.intersection(ensures) {
                charge()?;
                declarations.insert(*predicate);
            }
        }
    }
    Ok(declarations)
}

// Bind syntax candidates to actual packages in each entry world. Holder labels
// can differ after a CFG join; declaration membership never creates a package.
pub(super) fn repacked_holders(
    state: &ResourceState,
    declarations: &BTreeSet<crate::VirPredicateId>,
) -> BTreeSet<crate::verifier::PredicateHolder> {
    state
        .predicate_instances()
        .iter()
        .filter_map(|(holder, instance)| {
            (instance.is_folded() && declarations.contains(&instance.declaration()))
                .then_some(*holder)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn explicit_folds_select_declarations_independently_of_local_holder_labels() {
        let source = include_str!("../../../../spec/cases/verify/predicate-loop-write.nera");
        let output = crate::analyze(&crate::SourceFile::from_text("fold-loop.nera", source));
        let unit = output.vir().unwrap().resolve().unwrap();
        let invariant = &unit.as_unit().specs.loop_invariants()[0];
        let function = unit
            .as_unit()
            .runtime
            .functions
            .iter()
            .find(|f| f.id == invariant.function)
            .unwrap();
        let boundary = invariant.boundary.as_ref().unwrap();
        let candidates = repacked_declarations(&unit, function, boundary).unwrap();
        assert_eq!(candidates.len(), 1);
        for action in unit
            .as_unit()
            .specs
            .predicate_actions()
            .iter()
            .filter(|action| {
                action.location.function() == function.id
                    && action
                        .location
                        .block()
                        .is_some_and(|b| boundary.blocks.contains(&b))
                    && matches!(action.kind, crate::VirPredicateActionKind::Fold { .. })
            })
        {
            assert!(candidates.contains(&action.predicate));
        }
        // Candidate declarations never manufacture entry packages.
        assert!(repacked_holders(&ResourceState::new(), &candidates).is_empty());
    }

    #[test]
    fn call_candidates_require_matching_input_and_output_declarations() {
        let source = include_str!("../../../../spec/cases/verify/predicate-loop-call.nera");
        for (source, expected) in [
            (source.to_owned(), 1),
            (source.replace("requires Ready(p);", ""), 0),
            (source.replace("ensures Ready(result);", ""), 0),
        ] {
            let output = crate::analyze(&crate::SourceFile::from_text("call-loop.nera", source));
            let unit = output.vir().unwrap().resolve().unwrap();
            let invariant = &unit.as_unit().specs.loop_invariants()[0];
            let function = unit
                .as_unit()
                .runtime
                .functions
                .iter()
                .find(|f| f.id == invariant.function)
                .unwrap();
            let boundary = invariant.boundary.as_ref().unwrap();
            assert!(
                !unit
                    .as_unit()
                    .specs
                    .predicate_actions()
                    .iter()
                    .any(|action| {
                        action.location.function() == function.id
                            && action
                                .location
                                .block()
                                .is_some_and(|b| boundary.blocks.contains(&b))
                            && matches!(action.kind, crate::VirPredicateActionKind::Fold { .. })
                    })
            );
            assert_eq!(
                repacked_declarations(&unit, function, boundary)
                    .unwrap()
                    .len(),
                expected
            );
        }
    }
}
