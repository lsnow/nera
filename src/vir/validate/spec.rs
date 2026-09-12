//! Validation of VIR contracts and pure specification arenas.

use super::*;

pub(super) fn validate_specs(unit: &VirUnit) -> Result<(), VirValidationError> {
    let functions = unit
        .runtime
        .functions
        .iter()
        .map(|function| (function.id, function))
        .collect::<BTreeMap<_, _>>();
    let mut owners = BTreeSet::new();

    for (index, clause) in unit.specs.clauses().iter().enumerate() {
        let expected = VirSpecClauseId::new(index as u32);
        if clause.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseSpecClauseId {
                    expected,
                    found: clause.id,
                },
            ));
        }
    }

    for (index, contract) in unit.specs.contracts().iter().enumerate() {
        let expected = crate::vir::VirContractId::new(index as u32);
        if contract.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDenseContractId {
                expected,
                found: contract.id,
            }));
        }
        let Some(function) = functions.get(&contract.function).copied() else {
            return Err(program_error(
                VirValidationErrorKind::ContractFunctionMismatch {
                    contract: contract.id,
                    function: contract.function,
                },
            ));
        };
        if !owners.insert(contract.function) {
            return Err(function_error(
                function,
                VirValidationErrorKind::DuplicateFunctionContract(contract.function),
                function.source_span,
            ));
        }
        if function.contract != contract.id {
            return Err(function_error(
                function,
                VirValidationErrorKind::ContractFunctionMismatch {
                    contract: contract.id,
                    function: contract.function,
                },
                function.source_span,
            ));
        }
        if function.signature != contract.signature {
            return Err(function_error(
                function,
                VirValidationErrorKind::ContractSignatureMismatch(contract.id),
                function.source_span,
            ));
        }
        validate_contract(unit, function, contract)?;
    }

    for function in &unit.runtime.functions {
        if !owners.contains(&function.id) {
            return Err(function_error(
                function,
                VirValidationErrorKind::MissingFunctionContract(function.id),
                function.source_span,
            ));
        }
        for block in &function.blocks {
            for instruction in &block.instructions {
                let VirInstruction::Call { target, .. } = &instruction.instruction else {
                    continue;
                };
                let Some(contract) = unit.specs.contract(target.contract) else {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::MissingCallContract(target.contract),
                        instruction.source_span,
                    ));
                };
                if contract.signature != target.signature {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::CallContractSignatureMismatch(target.contract),
                        instruction.source_span,
                    ));
                }
            }
        }
    }
    validate_pure_specs(unit, &functions)
}

fn validate_contract(
    unit: &VirUnit,
    function: &VirFunction,
    contract: &crate::vir::VirContract,
) -> Result<(), VirValidationError> {
    let function_source_span = unit
        .source_map
        .source_span(VirLocation::FunctionEntry {
            function: function.id,
        })
        .expect("validated source map covers every function entry");
    let expected_binders = contract
        .signature
        .parameters
        .iter()
        .copied()
        .enumerate()
        .map(|(slot, ty)| (crate::vir::VirContractPosition::Requires, slot as u32, ty))
        .chain(
            contract
                .signature
                .results
                .iter()
                .copied()
                .enumerate()
                .map(|(slot, ty)| (crate::vir::VirContractPosition::Ensures, slot as u32, ty)),
        )
        .collect::<Vec<_>>();
    if contract.binders.len() != expected_binders.len() {
        let binder = contract
            .binders
            .get(
                expected_binders
                    .len()
                    .min(contract.binders.len())
                    .saturating_sub(1),
            )
            .map_or(crate::vir::VirContractBinderId::new(0), |binder| binder.id);
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderLayoutMismatch {
                contract: contract.id,
                binder,
            },
            function.source_span,
        ));
    }
    for (index, (binder, expected_layout)) in
        contract.binders.iter().zip(expected_binders).enumerate()
    {
        let expected_id = crate::vir::VirContractBinderId::new(index as u32);
        if binder.id != expected_id {
            return Err(function_error(
                function,
                VirValidationErrorKind::NonDenseContractBinderId {
                    contract: contract.id,
                    expected: expected_id,
                    found: binder.id,
                },
                function.source_span,
            ));
        }
        if (binder.position, binder.slot, binder.ty) != expected_layout {
            return Err(function_error(
                function,
                VirValidationErrorKind::ContractBinderLayoutMismatch {
                    contract: contract.id,
                    binder: binder.id,
                },
                function.source_span,
            ));
        }
    }
    for (index, resource) in contract.resources.iter().enumerate() {
        let expected = crate::vir::VirContractResourceId::new(index as u32);
        if resource.id != expected {
            return Err(function_error(
                function,
                VirValidationErrorKind::NonDenseContractResourceId {
                    contract: contract.id,
                    expected,
                    found: resource.id,
                },
                function.source_span,
            ));
        }
    }

    let mut used_resources = BTreeSet::new();
    let mut summarized_resources = BTreeSet::new();
    let mut defined_binders = BTreeSet::new();
    let mut previous_clause = None;
    for clause_id in &contract.clauses {
        if previous_clause.is_some_and(|previous| previous >= *clause_id) {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseOwner(*clause_id),
                function.source_span,
            ));
        }
        previous_clause = Some(*clause_id);
        let Some(clause) = unit.specs.clause(*clause_id) else {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseOwner(*clause_id),
                function.source_span,
            ));
        };
        let Some(position) = contract_clause_position(contract.id, clause) else {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
                function.source_span,
            ));
        };
        let expected_location = match position {
            crate::vir::VirContractPosition::Requires => {
                crate::vir::VirSpecLocation::FunctionEntry {
                    function: function.id,
                }
            }
            crate::vir::VirContractPosition::Ensures => {
                crate::vir::VirSpecLocation::FunctionResult {
                    function: function.id,
                }
            }
        };
        if clause.location != expected_location {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseLocation(clause.id),
                function.source_span,
            ));
        }
        let origin_id = clause.origin.origin();
        let Some(source_span) = unit.source_map.source_span_for_origin(origin_id) else {
            return Err(function_error(
                function,
                VirValidationErrorKind::UnknownSpecClauseOrigin(origin_id),
                function.source_span,
            ));
        };
        if source_span.source != function_source_span.source
            || !span_contains(function_source_span.span, source_span.span)
        {
            return Err(function_error(
                function,
                VirValidationErrorKind::SpecClauseOriginOutsideFunction(clause.id),
                source_span.span,
            ));
        }
        if matches!(clause.origin, VirSpecClauseOrigin::InferredType { .. })
            && !matches!(clause.kind, VirSpecClauseKind::Resource(_))
        {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidInferredTypeClause(clause.id),
                source_span.span,
            ));
        }
        match &clause.kind {
            VirSpecClauseKind::Resource(summary) => {
                if contract
                    .resources
                    .get(summary.resource.get() as usize)
                    .is_none_or(|resource| resource.id != summary.resource)
                {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::MissingContractResource(summary.resource),
                        source_span.span,
                    ));
                }
                used_resources.insert(summary.resource);
                if !summarized_resources.insert((position, summary.resource)) {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::DuplicateContractResourceSummary(summary.resource),
                        source_span.span,
                    ));
                }
                if summary.size_bytes == 0
                    || summary.alignment == 0
                    || !summary.alignment.is_power_of_two()
                {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::InvalidContractAllocation(clause.id),
                        source_span.span,
                    ));
                }
                if matches!(summary.liveness, crate::vir::VirContractLiveness::Dead)
                    && matches!(summary.ownership, crate::vir::VirContractOwnership::Owned)
                {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::DeadOwnedContractResource(clause.id),
                        source_span.span,
                    ));
                }
                for pointer in &summary.pointers {
                    validate_pointer_clause_binder(
                        function,
                        contract,
                        clause,
                        pointer.binder,
                        &mut defined_binders,
                        source_span.span,
                    )?;
                    if pointer.offset_lower > pointer.offset_upper {
                        return Err(function_error(
                            function,
                            VirValidationErrorKind::InvalidContractRange(clause.id),
                            source_span.span,
                        ));
                    }
                    if pointer.alignment == 0 || !pointer.alignment.is_power_of_two() {
                        return Err(function_error(
                            function,
                            VirValidationErrorKind::InvalidContractAlignment(clause.id),
                            source_span.span,
                        ));
                    }
                }
                for permission in &summary.permissions {
                    validate_clause_binder(
                        function,
                        contract,
                        clause,
                        permission.binder,
                        VirType::Permission,
                        &mut defined_binders,
                        source_span.span,
                    )?;
                    if permission.start_byte >= permission.end_byte
                        || permission.end_byte > summary.size_bytes
                    {
                        return Err(function_error(
                            function,
                            VirValidationErrorKind::InvalidContractRange(clause.id),
                            source_span.span,
                        ));
                    }
                }
            }
            VirSpecClauseKind::U64Range {
                binder,
                lower,
                upper,
            } => {
                validate_clause_binder(
                    function,
                    contract,
                    clause,
                    *binder,
                    VirType::U64,
                    &mut defined_binders,
                    source_span.span,
                )?;
                if lower > upper {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::InvalidContractRange(clause.id),
                        source_span.span,
                    ));
                }
            }
            VirSpecClauseKind::BoolValue { binder, .. } => validate_clause_binder(
                function,
                contract,
                clause,
                *binder,
                VirType::Bool,
                &mut defined_binders,
                source_span.span,
            )?,
            VirSpecClauseKind::Logic { .. } => {}
        }
    }
    for resource in &contract.resources {
        if !used_resources.contains(&resource.id) {
            return Err(function_error(
                function,
                VirValidationErrorKind::UnusedContractResource(resource.id),
                function.source_span,
            ));
        }
    }
    Ok(())
}

fn validate_pure_specs(
    unit: &VirUnit,
    functions: &BTreeMap<VirFunctionId, &VirFunction>,
) -> Result<(), VirValidationError> {
    const MAX_SPEC_TERM_DEPTH: usize = 256;

    let mut predicate_names = BTreeSet::new();
    for (index, predicate) in unit.specs.predicates().iter().enumerate() {
        let expected = crate::vir::VirPredicateId::new(index as u32);
        if predicate.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDensePredicateId {
                expected,
                found: predicate.id,
            }));
        }
        let mut predicate_binders = BTreeSet::new();
        if predicate.name.is_empty()
            || !predicate_names.insert(predicate.name.as_str())
            || unit
                .source_map
                .source_span_for_origin(predicate.origin)
                .is_none()
            || !predicate.binders.iter().all(|binder_id| {
                predicate_binders.insert(*binder_id)
                    && unit
                        .specs
                        .binders()
                        .get(binder_id.get() as usize)
                        .is_some_and(|binder| {
                            binder.id == *binder_id
                                && binder.owner
                                    == crate::vir::VirSpecBinderOwner::Predicate(predicate.id)
                        })
            })
        {
            return Err(program_error(VirValidationErrorKind::InvalidPredicate(
                predicate.id,
            )));
        }
        if predicate.body.is_some() {
            return Err(program_error(
                VirValidationErrorKind::PredicateBodyFeatureGated(predicate.id),
            ));
        }
    }

    let mut binder_names = BTreeSet::new();
    for (index, binder) in unit.specs.binders().iter().enumerate() {
        let expected = VirSpecBinderId::new(index as u32);
        if binder.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseSpecBinderId {
                    expected,
                    found: binder.id,
                },
            ));
        }
        let owner_valid = match binder.owner {
            crate::vir::VirSpecBinderOwner::Clause(clause_id) => unit
                .specs
                .clause(clause_id)
                .and_then(|clause| {
                    clause_owner_function(unit, clause)
                        .map(|function| origin_belongs_to_function(unit, function, binder.origin))
                })
                .unwrap_or(false),
            crate::vir::VirSpecBinderOwner::Predicate(predicate_id) => unit
                .specs
                .predicates()
                .get(predicate_id.get() as usize)
                .is_some_and(|predicate| {
                    predicate.id == predicate_id
                        && predicate.binders.contains(&binder.id)
                        && origins_are_nested(unit, predicate.origin, binder.origin)
                }),
        };
        if binder.name.is_empty()
            || !binder_names.insert((binder.owner, binder.name.as_str()))
            || !owner_valid
            || unit
                .source_map
                .source_span_for_origin(binder.origin)
                .is_none()
        {
            return Err(program_error(VirValidationErrorKind::InvalidSpecBinder(
                binder.id,
            )));
        }
    }

    let mut depths = Vec::with_capacity(unit.specs.terms().len());
    for (index, term) in unit.specs.terms().iter().enumerate() {
        let expected = VirSpecTermId::new(index as u32);
        if term.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDenseSpecTermId {
                expected,
                found: term.id,
            }));
        }
        let Some(clause) = unit.specs.clause(term.clause) else {
            return Err(program_error(VirValidationErrorKind::InvalidSpecTerm(
                term.id,
            )));
        };
        let Some(function) = clause_owner_function(unit, clause) else {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            ));
        };
        if !origin_belongs_to_function(unit, function, term.origin) {
            return Err(program_error(VirValidationErrorKind::InvalidSpecTerm(
                term.id,
            )));
        }
        let child = |id: VirSpecTermId| {
            unit.specs
                .terms()
                .get(id.get() as usize)
                .filter(|child| child.id == id && id.get() < term.id.get())
                .filter(|child| child.clause == term.clause)
        };
        let (valid, depth) = match &term.kind {
            crate::vir::VirSpecTermKind::Bool(_) => (term.ty == crate::vir::VirSpecType::Bool, 1),
            crate::vir::VirSpecTermKind::U64(_) => (term.ty == crate::vir::VirSpecType::U64, 1),
            crate::vir::VirSpecTermKind::Binder(id) => {
                let valid = unit
                    .specs
                    .binders()
                    .get(id.get() as usize)
                    .is_some_and(|binder| {
                        binder.id == *id
                            && binder.owner == crate::vir::VirSpecBinderOwner::Clause(term.clause)
                            && binder.ty == term.ty
                    });
                (valid, 1)
            }
            crate::vir::VirSpecTermKind::Snapshot(snapshot) => {
                (validate_spec_snapshot(unit, clause, term.ty, *snapshot), 1)
            }
            crate::vir::VirSpecTermKind::Equal { left, right } => {
                let valid = term.ty == crate::vir::VirSpecType::Bool
                    && child(*left)
                        .zip(child(*right))
                        .is_some_and(|(left, right)| left.ty == right.ty);
                (valid, spec_binary_depth(&depths, *left, *right))
            }
            crate::vir::VirSpecTermKind::LessThan { left, right }
            | crate::vir::VirSpecTermKind::LessOrEqual { left, right } => {
                let valid = term.ty == crate::vir::VirSpecType::Bool
                    && child(*left).is_some_and(|left| left.ty == crate::vir::VirSpecType::U64)
                    && child(*right).is_some_and(|right| right.ty == crate::vir::VirSpecType::U64);
                (valid, spec_binary_depth(&depths, *left, *right))
            }
            crate::vir::VirSpecTermKind::Not(operand) => {
                let valid = term.ty == crate::vir::VirSpecType::Bool
                    && child(*operand)
                        .is_some_and(|operand| operand.ty == crate::vir::VirSpecType::Bool);
                (valid, spec_unary_depth(&depths, *operand))
            }
            crate::vir::VirSpecTermKind::And(operands)
            | crate::vir::VirSpecTermKind::Or(operands) => {
                let valid = term.ty == crate::vir::VirSpecType::Bool
                    && operands.len() >= 2
                    && operands.iter().all(|operand| {
                        child(*operand)
                            .is_some_and(|operand| operand.ty == crate::vir::VirSpecType::Bool)
                    });
                (valid, spec_nary_depth(&depths, operands))
            }
        };
        if !valid {
            let kind = if matches!(term.kind, crate::vir::VirSpecTermKind::Snapshot(_)) {
                VirValidationErrorKind::InvalidSpecSnapshot(term.id)
            } else {
                VirValidationErrorKind::InvalidSpecTerm(term.id)
            };
            return Err(program_error(kind));
        }
        if depth > MAX_SPEC_TERM_DEPTH {
            return Err(program_error(
                VirValidationErrorKind::SpecTermDepthExceeded(term.id),
            ));
        }
        depths.push(depth);
    }

    for clause in unit.specs.clauses() {
        let Some(function) = clause_owner_function(unit, clause) else {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            ));
        };
        if !clause_owner_has_backlink(unit, clause) {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            ));
        }
        if !spec_location_exists(unit, clause.location)
            || clause.location.function() != function
            || !origin_belongs_to_function(unit, function, clause.origin.origin())
        {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseLocation(clause.id),
            ));
        }
        if matches!(clause.origin, VirSpecClauseOrigin::InferredType { .. })
            && !matches!(clause.kind, VirSpecClauseKind::Resource(_))
        {
            return Err(program_error(
                VirValidationErrorKind::InvalidInferredTypeClause(clause.id),
            ));
        }
        match clause.kind {
            VirSpecClauseKind::Logic { root } => {
                if !unit
                    .specs
                    .terms()
                    .get(root.get() as usize)
                    .is_some_and(|term| {
                        term.id == root
                            && term.clause == clause.id
                            && term.ty == crate::vir::VirSpecType::Bool
                    })
                {
                    return Err(program_error(VirValidationErrorKind::InvalidSpecTerm(root)));
                }
            }
            _ if !matches!(
                clause.owner,
                crate::vir::VirSpecClauseOwner::Contract { .. }
            ) =>
            {
                return Err(program_error(
                    VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
                ));
            }
            _ => {}
        }
    }

    for (index, prove) in unit.specs.proves().iter().enumerate() {
        let expected = crate::vir::VirSpecProveId::new(index as u32);
        if prove.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDenseSpecProveId {
                expected,
                found: prove.id,
            }));
        }
        let valid = functions.contains_key(&prove.function)
            && spec_location_exists(unit, prove.location)
            && prove.location.function() == prove.function
            && unit.specs.clause(prove.clause).is_some_and(|clause| {
                clause.owner == crate::vir::VirSpecClauseOwner::Prove(prove.id)
                    && clause.location == prove.location
                    && matches!(clause.kind, VirSpecClauseKind::Logic { .. })
            })
            && origin_belongs_to_function(unit, prove.function, prove.origin);
        if !valid {
            return Err(program_error(VirValidationErrorKind::InvalidSpecProve(
                prove.id,
            )));
        }
    }

    for (index, entry) in unit.specs.trust_entries().iter().enumerate() {
        let expected = crate::vir::VirTrustEntryId::new(index as u32);
        if entry.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseTrustEntryId {
                    expected,
                    found: entry.id,
                },
            ));
        }
        if entry.policy != crate::vir::VirTrustPolicyKind::EntryPointAssumption
            || entry.scope
                != (crate::vir::VirTrustScope::FunctionEntry {
                    function: unit.runtime.entry,
                })
        {
            return Err(program_error(VirValidationErrorKind::TrustPolicyDenied(
                entry.id,
            )));
        }
        let valid = functions.contains_key(&entry.scope.function())
            && unit.specs.clause(entry.clause).is_some_and(|clause| {
                clause.owner == crate::vir::VirSpecClauseOwner::TrustEntry(entry.id)
                    && clause.location == entry.scope.location()
                    && clause.origin
                        == crate::vir::VirSpecClauseOrigin::Explicit {
                            origin: entry.origin,
                        }
                    && matches!(clause.kind, VirSpecClauseKind::Logic { .. })
            })
            && origin_belongs_to_function(unit, entry.scope.function(), entry.origin);
        if !valid {
            return Err(program_error(VirValidationErrorKind::InvalidTrustEntry(
                entry.id,
            )));
        }
    }

    for (index, invariant) in unit.specs.loop_invariants().iter().enumerate() {
        let expected = crate::vir::VirSpecLoopInvariantId::new(index as u32);
        if invariant.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseSpecLoopInvariantId {
                    expected,
                    found: invariant.id,
                },
            ));
        }
    }
    if let Some(invariant) = unit.specs.loop_invariants().first() {
        return Err(program_error(
            VirValidationErrorKind::LoopInvariantFeatureGated(invariant.id),
        ));
    }
    Ok(())
}

fn clause_owner_function(
    unit: &VirUnit,
    clause: &crate::vir::VirSpecClause,
) -> Option<VirFunctionId> {
    match clause.owner {
        crate::vir::VirSpecClauseOwner::Contract { contract, .. } => unit
            .specs
            .contract(contract)
            .map(|contract| contract.function),
        crate::vir::VirSpecClauseOwner::Prove(prove_id) => unit
            .specs
            .proves()
            .get(prove_id.get() as usize)
            .filter(|prove| prove.id == prove_id)
            .map(|prove| prove.function),
        crate::vir::VirSpecClauseOwner::TrustEntry(entry_id) => unit
            .specs
            .trust_entries()
            .get(entry_id.get() as usize)
            .filter(|entry| entry.id == entry_id)
            .map(|entry| entry.scope.function()),
        crate::vir::VirSpecClauseOwner::LoopInvariant(invariant_id) => unit
            .specs
            .loop_invariants()
            .get(invariant_id.get() as usize)
            .filter(|invariant| invariant.id == invariant_id)
            .map(|invariant| invariant.function),
    }
}

fn clause_owner_has_backlink(unit: &VirUnit, clause: &crate::vir::VirSpecClause) -> bool {
    match clause.owner {
        crate::vir::VirSpecClauseOwner::Contract { contract, .. } => unit
            .specs
            .contract(contract)
            .is_some_and(|contract| contract.clauses.contains(&clause.id)),
        crate::vir::VirSpecClauseOwner::Prove(prove_id) => unit
            .specs
            .proves()
            .get(prove_id.get() as usize)
            .is_some_and(|prove| prove.id == prove_id && prove.clause == clause.id),
        crate::vir::VirSpecClauseOwner::TrustEntry(entry_id) => unit
            .specs
            .trust_entries()
            .get(entry_id.get() as usize)
            .is_some_and(|entry| entry.id == entry_id && entry.clause == clause.id),
        crate::vir::VirSpecClauseOwner::LoopInvariant(invariant_id) => unit
            .specs
            .loop_invariants()
            .get(invariant_id.get() as usize)
            .is_some_and(|invariant| invariant.id == invariant_id && invariant.clause == clause.id),
    }
}

fn origins_are_nested(unit: &VirUnit, parent: VirOriginId, child: VirOriginId) -> bool {
    unit.source_map
        .source_span_for_origin(parent)
        .zip(unit.source_map.source_span_for_origin(child))
        .is_some_and(|(parent, child)| {
            parent.source == child.source && span_contains(parent.span, child.span)
        })
}

fn spec_location_exists(unit: &VirUnit, location: crate::vir::VirSpecLocation) -> bool {
    match location {
        crate::vir::VirSpecLocation::FunctionEntry { function }
        | crate::vir::VirSpecLocation::FunctionResult { function } => unit
            .runtime
            .functions
            .iter()
            .any(|candidate| candidate.id == function),
        crate::vir::VirSpecLocation::Runtime(location) => {
            unit.source_map.origin_at(location).is_some()
        }
    }
}

fn origin_belongs_to_function(
    unit: &VirUnit,
    function: VirFunctionId,
    origin: VirOriginId,
) -> bool {
    unit.source_map
        .source_span(VirLocation::FunctionEntry { function })
        .zip(unit.source_map.source_span_for_origin(origin))
        .is_some_and(|(function_span, origin_span)| {
            function_span.source == origin_span.source
                && span_contains(function_span.span, origin_span.span)
        })
}

fn validate_spec_snapshot(
    unit: &VirUnit,
    clause: &crate::vir::VirSpecClause,
    ty: crate::vir::VirSpecType,
    snapshot: crate::vir::VirSpecSnapshot,
) -> bool {
    match snapshot {
        crate::vir::VirSpecSnapshot::Parameter { function, slot } => unit
            .runtime
            .functions
            .iter()
            .find(|candidate| candidate.id == function)
            .and_then(|function| function.signature.parameters.get(slot as usize))
            .is_some_and(|runtime_ty| {
                clause.location == crate::vir::VirSpecLocation::FunctionEntry { function }
                    && spec_type_matches_runtime(ty, *runtime_ty)
            }),
        crate::vir::VirSpecSnapshot::Result { function, slot } => unit
            .runtime
            .functions
            .iter()
            .find(|candidate| candidate.id == function)
            .and_then(|function| function.signature.results.get(slot as usize))
            .is_some_and(|runtime_ty| {
                clause.location == crate::vir::VirSpecLocation::FunctionResult { function }
                    && spec_type_matches_runtime(ty, *runtime_ty)
            }),
        crate::vir::VirSpecSnapshot::Value { function, value } => {
            validate_runtime_snapshot(unit, clause, ty, function, value)
        }
    }
}

fn validate_runtime_snapshot(
    unit: &VirUnit,
    clause: &crate::vir::VirSpecClause,
    ty: crate::vir::VirSpecType,
    function_id: VirFunctionId,
    value: VirValueId,
) -> bool {
    let crate::vir::VirSpecLocation::Runtime(location) = clause.location else {
        return false;
    };
    if location.function() != function_id {
        return false;
    }
    let Some(block_id) = location.block() else {
        return false;
    };
    let Some(function) = unit
        .runtime
        .functions
        .iter()
        .find(|function| function.id == function_id)
    else {
        return false;
    };
    let Some(block) = function.blocks.iter().find(|block| block.id == block_id) else {
        return false;
    };
    if let Some(parameter) = block
        .parameters
        .iter()
        .find(|parameter| parameter.id == value)
    {
        return spec_type_matches_runtime(ty, parameter.ty);
    }
    for (definition, instruction) in block.instructions.iter().enumerate() {
        let mut found = None;
        instruction.instruction.visit_results(|result| {
            if result.id == value {
                found = Some(result.ty);
            }
        });
        let Some(runtime_ty) = found else { continue };
        let available = match location {
            VirLocation::Instruction { ordinal, .. } => definition as u64 <= ordinal,
            VirLocation::CallEdge { instruction, .. } => definition as u64 <= instruction,
            VirLocation::Terminator { .. } => true,
            VirLocation::FunctionEntry { .. }
            | VirLocation::BlockEntry { .. }
            | VirLocation::BlockParameter { .. } => false,
        };
        return available && spec_type_matches_runtime(ty, runtime_ty);
    }
    false
}

const fn spec_type_matches_runtime(spec: crate::vir::VirSpecType, runtime: VirType) -> bool {
    matches!(
        (spec, runtime),
        (crate::vir::VirSpecType::Bool, VirType::Bool)
            | (crate::vir::VirSpecType::U64, VirType::U64)
    )
}

fn spec_unary_depth(depths: &[usize], operand: VirSpecTermId) -> usize {
    depths
        .get(operand.get() as usize)
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}

fn spec_binary_depth(depths: &[usize], left: VirSpecTermId, right: VirSpecTermId) -> usize {
    depths
        .get(left.get() as usize)
        .zip(depths.get(right.get() as usize))
        .and_then(|(left, right)| left.max(right).checked_add(1))
        .unwrap_or(usize::MAX)
}

fn spec_nary_depth(depths: &[usize], operands: &[VirSpecTermId]) -> usize {
    operands
        .iter()
        .map(|operand| depths.get(operand.get() as usize).copied())
        .collect::<Option<Vec<_>>>()
        .and_then(|depths| depths.into_iter().max())
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}

fn validate_clause_binder(
    function: &VirFunction,
    contract: &crate::vir::VirContract,
    clause: &crate::vir::VirSpecClause,
    binder_id: crate::vir::VirContractBinderId,
    expected_type: VirType,
    defined_binders: &mut BTreeSet<crate::vir::VirContractBinderId>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let Some(position) = contract_clause_position(contract.id, clause) else {
        return Err(function_error(
            function,
            VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            source_span,
        ));
    };
    let Some(binder) = contract.binders.get(binder_id.get() as usize) else {
        return Err(function_error(
            function,
            VirValidationErrorKind::MissingContractBinder(binder_id),
            source_span,
        ));
    };
    if binder.id != binder_id {
        return Err(function_error(
            function,
            VirValidationErrorKind::MissingContractBinder(binder_id),
            source_span,
        ));
    }
    if binder.position != position {
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderPositionMismatch(binder_id),
            source_span,
        ));
    }
    if binder.ty != expected_type {
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderTypeMismatch(binder_id),
            source_span,
        ));
    }
    if !defined_binders.insert(binder_id) {
        return Err(function_error(
            function,
            VirValidationErrorKind::DuplicateContractBinderFact(binder_id),
            source_span,
        ));
    }
    Ok(())
}

fn validate_pointer_clause_binder(
    function: &VirFunction,
    contract: &crate::vir::VirContract,
    clause: &crate::vir::VirSpecClause,
    binder_id: crate::vir::VirContractBinderId,
    defined_binders: &mut BTreeSet<crate::vir::VirContractBinderId>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let Some(binder) = contract.binders.get(binder_id.get() as usize) else {
        return Err(function_error(
            function,
            VirValidationErrorKind::MissingContractBinder(binder_id),
            source_span,
        ));
    };
    if !matches!(binder.ty, VirType::Pointer { .. }) {
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderTypeMismatch(binder_id),
            source_span,
        ));
    }
    validate_clause_binder(
        function,
        contract,
        clause,
        binder_id,
        binder.ty,
        defined_binders,
        source_span,
    )
}

fn contract_clause_position(
    contract: crate::vir::VirContractId,
    clause: &crate::vir::VirSpecClause,
) -> Option<crate::vir::VirContractPosition> {
    match clause.owner {
        crate::vir::VirSpecClauseOwner::Contract {
            contract: owner,
            position,
        } if owner == contract => Some(position),
        _ => None,
    }
}
