//! Independent runtime shadow mutations; no verifier result is consulted.
use super::*;
use crate::{VirLoanRange, VirPointerDomain, VirPointerPaths};

fn setup() -> (Interpreter, VirRuntimePointer) {
    let mut interpreter = Interpreter::new(VirInterpreterConfig::default());
    for id in [0, 1] {
        interpreter.allocations.insert(
            id,
            Allocation {
                size_bytes: 32,
                alignment: 8,
                kind: RuntimeAllocationKind::Heap,
                live: true,
                bytes: BTreeMap::new(),
                objects: Vec::new(),
                resource_payloads: BTreeMap::new(),
            },
        );
    }
    let pointer = VirRuntimePointer {
        allocation: 0,
        offset_bytes: 8,
        access: VirMemoryAccess::core_u64(),
        paths: VirPointerPaths::root(VirMemoryAccess::core_u64()),
        view_range: None,
        domain: VirPointerDomain::Restricted(VirLoanRange {
            start_bytes: 8,
            end_bytes: 24,
        }),
    };
    (interpreter, pointer)
}

fn pair(
    interpreter: &Interpreter,
    a: VirRuntimePointer,
    b: VirRuntimePointer,
) -> Result<(VirRuntimePointer, VirRuntimePointer), VirExecutionError> {
    let frame = BlockFrame {
        values: BTreeMap::from([
            (VirValueId::new(0), VirRuntimeValue::Pointer(a)),
            (VirValueId::new(1), VirRuntimeValue::Pointer(b)),
        ]),
        consumed_permissions: BTreeSet::new(),
        loan_authorities: BTreeMap::new(),
    };
    interpreter.pointer_pair(
        &frame,
        VirValueId::new(0),
        VirValueId::new(1),
        ByteSpan::empty(),
    )
}

#[test]
fn malformed_domain_metadata_faults_even_when_the_queried_offset_fits() {
    let (interpreter, base) = setup();
    for range in [
        VirLoanRange {
            start_bytes: 8,
            end_bytes: 33,
        },
        VirLoanRange {
            start_bytes: 24,
            end_bytes: 8,
        },
        VirLoanRange {
            start_bytes: 0,
            end_bytes: u64::MAX,
        },
    ] {
        let bad = VirRuntimePointer {
            domain: VirPointerDomain::Restricted(range),
            ..base
        };
        assert!(matches!(
            pair(&interpreter, bad, bad).unwrap_err().kind(),
            VirExecutionErrorKind::PointerDomainViolation { .. }
        ));
    }
}

#[test]
fn runtime_relations_require_live_instance_exact_domain_and_known_path() {
    let (mut interpreter, base) = setup();
    let one_past = VirRuntimePointer {
        offset_bytes: 24,
        ..base
    };
    assert!(pair(&interpreter, base, one_past).is_ok());
    for other in [
        VirRuntimePointer {
            allocation: 1,
            ..base
        },
        VirRuntimePointer {
            paths: VirPointerPaths::default(),
            ..base
        },
        VirRuntimePointer {
            domain: VirPointerDomain::Restricted(VirLoanRange {
                start_bytes: 0,
                end_bytes: 24,
            }),
            ..base
        },
    ] {
        assert_eq!(
            pair(&interpreter, base, other).unwrap_err().kind(),
            &VirExecutionErrorKind::PointerRelationIncompatible
        );
    }
    for other in [
        VirRuntimePointer {
            domain: VirPointerDomain::Unknown,
            ..base
        },
        VirRuntimePointer {
            offset_bytes: 7,
            ..base
        },
        VirRuntimePointer {
            offset_bytes: 25,
            ..base
        },
    ] {
        assert!(matches!(
            pair(&interpreter, other, other).unwrap_err().kind(),
            VirExecutionErrorKind::PointerDomainViolation { .. }
        ));
    }
    // A one-past address is comparable but cannot authorize even one byte.
    assert!(
        interpreter
            .check_domain(one_past, 24, 25, ByteSpan::empty())
            .is_err()
    );
    interpreter.allocations.get_mut(&0).unwrap().live = false;
    assert_eq!(
        pair(&interpreter, base, base).unwrap_err().kind(),
        &VirExecutionErrorKind::UseAfterFree { allocation: 0 }
    );
    interpreter.allocations.get_mut(&0).unwrap().kind = RuntimeAllocationKind::LocalStorage;
    assert_eq!(
        pair(&interpreter, base, base).unwrap_err().kind(),
        &VirExecutionErrorKind::UseAfterLifetimeEnd { allocation: 0 }
    );
}

#[test]
fn empty_selected_domain_has_an_endpoint_but_no_accessible_byte() {
    let (interpreter, base) = setup();
    let empty = VirRuntimePointer {
        offset_bytes: 24,
        domain: VirPointerDomain::Restricted(VirLoanRange {
            start_bytes: 24,
            end_bytes: 24,
        }),
        ..base
    };
    assert!(pair(&interpreter, empty, empty).is_ok());
    assert!(
        interpreter
            .check_domain(empty, 24, 25, ByteSpan::empty())
            .is_err()
    );
}
