use super::*;

#[test]
fn imports_require_actual_caller_tokens_and_publish_the_complete_group() {
    let output = crate::analyze(&crate::SourceFile::from_text(
        "borrow-import.nera",
        "fn main()->u64{return 0;} fn consume(a:&mut u64,b:&mut u64)->u64{return *a;}",
    ));
    let runtime = output.vir().unwrap().runtime();
    let function = &runtime.functions[1];
    let entry = function
        .blocks
        .iter()
        .find(|b| b.id == function.entry)
        .unwrap();
    let abi = &runtime.abis.function(function.id).unwrap().signature;
    let span = ByteSpan::empty();
    let mut caller = RuntimeLoanShadow::new(100);
    let mut frame = BlockFrame {
        values: BTreeMap::new(),
        consumed_permissions: BTreeSet::new(),
        loan_authorities: BTreeMap::new(),
    };
    let mut imports = Vec::new();
    for (index, binding) in abi.parameters().iter().enumerate() {
        let crate::VirType::Pointer { access } =
            entry.parameters[binding.parameter_slots()[0] as usize].ty
        else {
            panic!("pointer slot");
        };
        let range = VirLoanRange {
            start_bytes: 0,
            end_bytes: 8,
        };
        let pointer = VirRuntimePointer {
            allocation: index as u64,
            offset_bytes: 0,
            access,
            paths: crate::VirPointerPaths::default(),
            view_range: Some(range),
            domain: crate::VirPointerDomain::Restricted(range),
        };
        let permission = VirRuntimePermission {
            allocation: pointer.allocation,
            start_bytes: 0,
            end_bytes: 8,
            can_free_when_complete: false,
        };
        let id = VirLoanId::new(index as u32);
        let authority = caller.fresh_authority(id, span).unwrap();
        caller.loans.insert(
            id,
            RuntimeLoan {
                allocation: pointer.allocation,
                range,
                envelope: range,
                kind: VirLoanKind::Mutable,
                region: crate::VirBorrowRegionId::new(0),
                parent: None,
                pointee: access,
                activity: RuntimeLoanActivity::Active,
                authorities: BTreeSet::from([authority.token]),
            },
        );
        imports.push(RuntimeBorrowImport {
            parameter: index as u32,
            authority,
            pointer,
            permission,
        });
        frame.values.insert(
            entry.parameters[binding.parameter_slots()[0] as usize].id,
            VirRuntimeValue::Pointer(pointer),
        );
        frame.values.insert(
            entry.parameters[*binding.parameter_slots().last().unwrap() as usize].id,
            VirRuntimeValue::Permission(permission),
        );
    }
    let limits = RuntimeLoanLimits {
        active_loans: 8,
        aliases_per_loan: 8,
        reborrow_depth: 8,
    };
    for mutation in 0..9 {
        let mut incoming = imports.clone();
        let mut source = caller.clone();
        let mut budget = limits;
        match mutation {
            0 => incoming[1].authority.token.invocation = 99,
            1 => incoming[1].pointer.offset_bytes = 1,
            2 => incoming[1].permission.can_free_when_complete = true,
            3 => {
                incoming.pop();
            }
            4 => incoming.push(incoming[1]),
            5 => {
                source
                    .loans
                    .get_mut(&incoming[1].authority.loan)
                    .unwrap()
                    .activity = RuntimeLoanActivity::Ended
            }
            6 => {
                source
                    .loans
                    .get_mut(&incoming[1].authority.loan)
                    .unwrap()
                    .kind = VirLoanKind::Shared
            }
            7 => budget.active_loans = 1,
            _ => {
                let mut extra = incoming[1];
                extra.parameter = 99;
                incoming.push(extra);
            }
        }
        let mut callee = RuntimeLoanShadow::new(101);
        let mut arguments = frame.clone();
        assert!(
            callee
                .import_parameters(
                    &mut arguments,
                    function,
                    runtime,
                    &source,
                    &incoming,
                    budget,
                    span
                )
                .is_err(),
            "mutation {mutation}"
        );
        assert!(callee.loans.is_empty());
        assert_eq!(callee.next_authority, 0);
        assert_eq!(arguments.values, frame.values);
        assert_eq!(arguments.loan_authorities, frame.loan_authorities);
        assert_eq!(arguments.consumed_permissions, frame.consumed_permissions);
    }
    let mut callee = RuntimeLoanShadow::new(101);
    callee
        .import_parameters(
            &mut frame, function, runtime, &caller, &imports, limits, span,
        )
        .unwrap();
    assert_eq!(callee.loans.len(), 2);
    for (index, binding) in abi.parameters().iter().enumerate() {
        let permission = entry.parameters[*binding.parameter_slots().last().unwrap() as usize].id;
        let authority = frame.loan_authority(permission).unwrap();
        assert_eq!(authority.loan, crate::vir::interface_loan_id(index as u32));
        assert_eq!(authority.token.invocation, 101);
        assert_ne!(authority.token, imports[index].authority.token);
        assert!(
            callee.loans[&authority.loan]
                .authorities
                .contains(&authority.token)
        );
        assert!(
            caller.loans[&imports[index].authority.loan]
                .authorities
                .contains(&imports[index].authority.token)
        );
    }
    let outputs: Vec<_> = function
        .signature
        .results
        .iter()
        .enumerate()
        .map(|(slot, _)| VirValueId::new(1000 + slot as u32))
        .collect();
    let mut returned = BlockFrame {
        values: BTreeMap::new(),
        consumed_permissions: BTreeSet::new(),
        loan_authorities: BTreeMap::new(),
    };
    for (slot, ty) in function.signature.results.iter().enumerate() {
        if *ty == crate::VirType::U64 {
            returned
                .values
                .insert(outputs[slot], VirRuntimeValue::U64(42));
        }
    }
    let mut returned_permissions = Vec::new();
    for binding in abi.parameters() {
        let input = entry.parameters[*binding.parameter_slots().last().unwrap() as usize].id;
        for slot in binding.result_slots() {
            let output = outputs[*slot as usize];
            returned.values.insert(output, frame.values[&input].clone());
            returned
                .loan_authorities
                .insert(output, frame.loan_authority(input).unwrap());
            returned_permissions.push(output);
        }
    }
    assert_eq!(returned_permissions.len(), 2);
    for mutation in 0..5 {
        let mut broken = returned.clone();
        let second = returned_permissions[1];
        if mutation == 4 {
            broken
                .loan_authorities
                .get_mut(&second)
                .unwrap()
                .token
                .invocation = 99;
        } else {
            let VirRuntimeValue::Permission(permission) = broken.values.get_mut(&second).unwrap()
            else {
                unreachable!()
            };
            match mutation {
                0 => permission.allocation = 99,
                1 => permission.end_bytes = 7,
                2 => permission.end_bytes = 9,
                _ => permission.can_free_when_complete = true,
            }
        }
        let mut attempt = callee.clone();
        assert!(
            attempt
                .export_parameters(&broken, &outputs, abi, span)
                .is_err(),
            "export mutation {mutation}"
        );
        for (id, original) in &callee.loans {
            assert_eq!(attempt.loans[id].activity, original.activity);
            assert_eq!(attempt.loans[id].authorities, original.authorities);
        }
        assert_eq!(attempt.next_authority, callee.next_authority);
    }
    let receipts = callee
        .export_parameters(&returned, &outputs, abi, span)
        .unwrap();
    for (index, binding) in abi.parameters().iter().enumerate() {
        let id = crate::vir::interface_loan_id(index as u32);
        for slot in binding.result_slots() {
            assert_eq!(receipts[*slot as usize], Some(id));
        }
        assert_eq!(callee.loans[&id].activity, RuntimeLoanActivity::Ended);
        assert!(callee.loans[&id].authorities.is_empty());
    }
    callee.finish(span).unwrap();
    assert!(
        callee
            .export_parameters(&returned, &outputs, abi, span)
            .is_err(),
        "retired tokens cannot be exported twice"
    );
}
