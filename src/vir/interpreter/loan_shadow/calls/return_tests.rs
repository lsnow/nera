use super::*;

fn parent(
    kind: VirLoanKind,
) -> (
    RuntimeLoanShadow,
    RuntimeLoanAuthority,
    VirRuntimePermission,
) {
    let mut shadow = RuntimeLoanShadow::new(10);
    let id = VirLoanId::new(0);
    let authority = shadow.fresh_authority(id, ByteSpan::empty()).unwrap();
    let range = VirLoanRange {
        start_bytes: 8,
        end_bytes: 24,
    };
    shadow.loans.insert(
        id,
        RuntimeLoan {
            allocation: 7,
            range,
            envelope: range,
            kind,
            region: crate::VirBorrowRegionId::new(0),
            parent: None,
            pointee: crate::VirMemoryAccess::core_u64(),
            activity: RuntimeLoanActivity::Active,
            authorities: BTreeSet::from([authority.token]),
        },
    );
    (
        shadow,
        authority,
        VirRuntimePermission {
            allocation: 7,
            start_bytes: 8,
            end_bytes: 24,
            can_free_when_complete: false,
        },
    )
}

fn limits() -> RuntimeLoanLimits {
    RuntimeLoanLimits {
        active_loans: 8,
        aliases_per_loan: 8,
        reborrow_depth: 8,
    }
}

#[test]
fn returned_permissions_cannot_change_allocation_free_or_escape_parent_range() {
    for kind in [VirLoanKind::Shared, VirLoanKind::Mutable] {
        for projection in [None, Some(crate::VirMemoryAccess::core_u64())] {
            for mutation in 0..6 {
                let (mut shadow, authority, mut permission) = parent(kind);
                match mutation {
                    0 => permission.allocation = 9,
                    1 => permission.can_free_when_complete = true,
                    2 => permission.start_bytes = 25,
                    3 => permission.start_bytes = 0,
                    4 => permission.end_bytes = 32,
                    _ => {
                        permission.start_bytes = 32;
                        permission.end_bytes = 32;
                    }
                }
                let before = shadow.clone();
                assert!(
                    shadow
                        .activate_conditional_return(
                            authority,
                            projection,
                            permission,
                            limits(),
                            ByteSpan::empty()
                        )
                        .is_err()
                );
                assert_eq!(
                    shadow, before,
                    "failed return must not suspend parent or consume IDs"
                );
            }
        }
    }
}

#[test]
fn whole_returns_preserve_range_and_projected_returns_can_select_empty_endpoints() {
    let span = ByteSpan::empty();
    for kind in [VirLoanKind::Shared, VirLoanKind::Mutable] {
        let (mut shadow, authority, mut permission) = parent(kind);
        permission.start_bytes = 16;
        let before = shadow.clone();
        assert!(
            shadow
                .activate_conditional_return(authority, None, permission, limits(), span)
                .is_err()
        );
        assert_eq!(shadow, before);
        let access = crate::VirMemoryAccess::core_u64();
        let returned = shadow
            .activate_conditional_return(authority, Some(access), permission, limits(), span)
            .unwrap();
        assert_eq!(
            shadow.loans[&returned.loan].range,
            VirLoanRange {
                start_bytes: 16,
                end_bytes: 24
            }
        );
        assert_eq!(shadow.loans[&returned.loan].parent, Some(authority.loan));
        assert_eq!(
            shadow.loans[&authority.loan].activity,
            if kind == VirLoanKind::Mutable {
                RuntimeLoanActivity::Suspended
            } else {
                RuntimeLoanActivity::Active
            }
        );

        let (mut empty, authority, mut permission) = parent(kind);
        permission.start_bytes = 24;
        let returned = empty
            .activate_conditional_return(authority, Some(access), permission, limits(), span)
            .unwrap();
        assert_eq!(
            empty.loans[&returned.loan].range,
            VirLoanRange {
                start_bytes: 24,
                end_bytes: 24
            }
        );
    }
}

#[test]
fn conditional_return_budgets_and_identifier_overflow_are_atomic() {
    let span = ByteSpan::empty();
    for mutation in 0..5 {
        let (mut shadow, authority, permission) = parent(VirLoanKind::Mutable);
        let mut budget = limits();
        match mutation {
            0 => budget.active_loans = 1,
            1 => budget.reborrow_depth = 0,
            2 => shadow.next_authority = u64::MAX,
            3 => shadow.next_dynamic_loan = u32::MAX,
            _ => shadow.loans.get_mut(&authority.loan).unwrap().parent = Some(authority.loan),
        }
        let before = shadow.clone();
        assert!(
            shadow
                .activate_conditional_return(authority, None, permission, budget, span)
                .is_err()
        );
        assert_eq!(shadow, before);
    }
    let (mut shadow, authority, permission) = parent(VirLoanKind::Mutable);
    let mut budget = limits();
    budget.reborrow_depth = 1;
    let child = shadow
        .activate_conditional_return(authority, None, permission, budget, span)
        .unwrap();
    let before = shadow.clone();
    assert!(
        shadow
            .activate_conditional_return(child, None, permission, budget, span)
            .is_err()
    );
    assert_eq!(shadow, before);
    budget.reborrow_depth = 2;
    let nested = shadow
        .activate_conditional_return(child, None, permission, budget, span)
        .unwrap();
    assert_eq!(shadow.loans[&nested.loan].parent, Some(child.loan));
}
