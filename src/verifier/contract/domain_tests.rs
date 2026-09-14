use super::*;

#[test]
fn legacy_contracts_cannot_widen_domains_on_inputs_or_outputs() {
    let output = crate::analyze(&crate::SourceFile::from_text(
        "domain-contract.nera",
        "fn identity(p: Own<u64>) -> Own<u64> { return p; }",
    ));
    let resolved = output.vir().unwrap().resolve().unwrap();
    let contracts = instantiate_contracts(&resolved).unwrap();
    let function = &resolved.runtime().functions[0];
    let contract = contracts.get(function.contract).unwrap();
    let parameters: Vec<_> = function.blocks[0]
        .parameters
        .iter()
        .map(|p| (p.id, p.ty))
        .collect();
    let ids: Vec<_> = parameters.iter().map(|p| p.0).collect();
    let original = entry_state(contract, &parameters).unwrap();
    for (domain, proven) in [
        (crate::VirPointerDomain::Allocation, true),
        (
            crate::VirPointerDomain::Restricted(AbstractByteRange::Exact(
                ByteRange::new(0, 8).unwrap(),
            )),
            true,
        ),
        (
            crate::VirPointerDomain::Restricted(AbstractByteRange::Exact(
                ByteRange::new(0, 4).unwrap(),
            )),
            false,
        ),
        (crate::VirPointerDomain::Unknown, false),
    ] {
        let mut state = original.clone();
        let Some(AbstractValue::Pointer(pointer)) = state.value_mut(ids[0]) else {
            panic!("pointer parameter")
        };
        *pointer = pointer.with_domain(domain);
        let (_, checks) = check_preconditions(&state, &ids, contract, Default::default());
        assert_eq!(
            checks.iter().all(|c| c.status == ObligationStatus::Proven),
            proven
        );
        let values: Vec<_> = ids.iter().map(|id| *state.value(*id).unwrap()).collect();
        let checks = check_postconditions(&state, &values, contract);
        assert_eq!(
            checks.iter().all(|c| c.status == ObligationStatus::Proven),
            proven
        );
    }
    // Equal numeric extent is insufficient when a carrier is a nominal
    // subobject. Neither input nor output may reconstruct it as a root.
    for domain in [
        None,
        Some(
            crate::VirNominalPath::root(crate::VirMemoryAccess::core_u64())
                .extend(&[crate::VirObjectPathSegment::TupleElement(0)])
                .unwrap(),
        ),
    ] {
        let mut state = original.clone();
        let Some(AbstractValue::Pointer(pointer)) = state.value_mut(ids[0]) else {
            panic!("pointer parameter")
        };
        *pointer = pointer.with_paths(crate::VirPointerPaths {
            object: domain,
            domain,
        });
        let (_, checks) = check_preconditions(&state, &ids, contract, Default::default());
        assert!(checks.iter().any(|c| c.status == ObligationStatus::Unknown));
        let values: Vec<_> = ids.iter().map(|id| *state.value(*id).unwrap()).collect();
        assert!(
            check_postconditions(&state, &values, contract)
                .iter()
                .any(|c| c.status == ObligationStatus::Unknown)
        );
    }
}
