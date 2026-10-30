//! Read-only contract observations retain the actual loan carrier and may
//! inspect a suspended parent's unborrowed bytes. This is not a runtime access
//! or a loan restoration: every other live mutable loan must be disjoint.
use super::*;

pub(in crate::verifier::transfer) fn loan_read_status(
    state: &ResourceState,
    loan_id: VirLoanId,
    permission: VirValueId,
    access: LoanAccess,
    limits: DifferenceLimits,
    pairs: &TransferRelations,
) -> ObligationStatus {
    let Some(loan) = state.loan(loan_id) else {
        return ObligationStatus::Unknown;
    };
    if access.required != AccessPermission::Read
        || access.envelope.is_none_or(|range| range.length() == 0)
    {
        return loan_authority_access_status(state, loan_id, permission, access, limits, pairs);
    }
    match loan.activity() {
        LoanActivity::Ended => return ObligationStatus::Refuted,
        LoanActivity::MaybeActive => return ObligationStatus::Unknown,
        LoanActivity::Active | LoanActivity::Suspended => {}
    }
    if !state.loan_precision_losses().is_empty() {
        return ObligationStatus::Unknown;
    }
    let mut status =
        loan_authority_base_access_status(state, loan_id, permission, access, limits, pairs);
    if !status.is_proven() {
        return status;
    }

    // Only real suspended ancestors are exempt from the conflict scan. Never
    // exempt descendants, same-address tokens, or an unresolved parent chain.
    let mut ancestors = BTreeSet::from([loan_id]);
    let mut parent = loan.parent();
    while let Some(id) = parent {
        if !pairs.charge() || !ancestors.insert(id) {
            return ObligationStatus::Unknown;
        }
        let Some(ancestor) = state.loan(id) else {
            return ObligationStatus::Unknown;
        };
        if ancestor.activity() != LoanActivity::Suspended {
            return ObligationStatus::Unknown;
        }
        status = combine_statuses([
            status,
            provenance_equal_status(ancestor.provenance(), access.pointer.provenance()),
            pairs
                .queries
                .contained(state, ancestor.actual_range(), access.range, limits),
        ]);
        parent = ancestor.parent();
    }
    for (&id, other) in state.loans() {
        if !pairs.charge() {
            return ObligationStatus::Unknown;
        }
        if ancestors.contains(&id) || other.activity() == LoanActivity::Ended {
            continue;
        }
        if other.activity() == LoanActivity::Active && other.kind() == VirLoanKind::Shared {
            continue;
        }
        let disjoint = loan_overlap_status(
            state,
            other,
            access.pointer.provenance(),
            access.envelope.expect("nonempty observation"),
            access.range,
            limits,
            pairs,
        );
        status = combine_statuses([status, disjoint]);
    }
    status
}
