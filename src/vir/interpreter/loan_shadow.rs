//! Path-local runtime oracle for validated VIR loan effects.
//!
//! The shadow is intentionally absent from [`super::VirRuntimeValue`].  It
//! follows one concrete execution path, assigns an opaque token to every
//! runtime alias and survives SSA renaming without making loan identity an
//! observable program value.

use std::collections::{BTreeMap, BTreeSet};

mod calls;
mod field_calls;

use super::{
    BlockFrame, VirExecutionError, VirExecutionErrorKind, VirRuntimePermission, VirRuntimePointer,
    VirRuntimeValue, error, pointer_value,
};
use crate::ByteSpan;
use crate::vir::{
    VirLoanAuthorityEffect, VirLoanEffect, VirLoanId, VirLoanKind, VirLoanRange, VirValue,
    VirValueId,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct RuntimeLoanAuthority {
    pub(super) loan: VirLoanId,
    pub(super) token: RuntimeLoanToken,
}

/// An invocation identity is never reused, including after a frame returns.
/// A token cannot be reconstructed from an address or a frame-local loan ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct RuntimeLoanToken {
    invocation: u64,
    ordinal: u64,
}

/// Evidence captured from an actual caller loan, never reconstructed from
/// parameter pointer bits in the callee.
#[derive(Clone, Copy)]
pub(super) struct RuntimeBorrowImport {
    parameter: u32,
    authority: RuntimeLoanAuthority,
    pointer: VirRuntimePointer,
    permission: VirRuntimePermission,
}

pub(super) struct RuntimeBorrowCall {
    pub(super) imports: Vec<RuntimeBorrowImport>,
    pub(super) returns: Vec<RuntimeBorrowReturn>,
}

#[derive(Clone, Copy)]
pub(super) struct RuntimeStoredBorrowReturn {
    source: crate::BoundarySource,
    caller: RuntimeLoanAuthority,
    callee: RuntimeLoanAuthority,
    pointer: VirRuntimePointer,
    permission: VirRuntimePermission,
    reference: crate::VirMemoryAccess,
}

impl RuntimeStoredBorrowReturn {
    fn binding(
        &self,
    ) -> crate::BoundaryBinding<RuntimeLoanAuthority, (VirRuntimePointer, VirRuntimePermission)>
    {
        crate::BoundaryBinding {
            source: self.source,
            authority: self.caller,
            view: (self.pointer, self.permission),
        }
    }
}

/// A candidate SSA destination derived from the canonical field-result ABI.
/// It is only admitted after checking the callee's actual unique token.
pub(super) struct RuntimeStoredValueExit {
    pub(super) source: crate::BoundarySource,
    pub(super) pointer: VirValueId,
    pub(super) permission: VirValueId,
    pub(super) caller_result: VirValueId,
}

pub(super) struct RuntimeBorrowReturn {
    pub(super) value: VirValueId,
    pub(super) authority: RuntimeLoanAuthority,
    pub(super) permission: VirRuntimePermission,
    /// The callee interface loan which must actually own this result.  `None`
    /// denotes an unconditional restoration.
    pub(super) callee_loan: Option<VirLoanId>,
    /// A projected result creates a caller-side child with this narrower
    /// pointee and the permission range returned by the callee.
    pub(super) projected_pointee: Option<crate::VirMemoryAccess>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RuntimeLoanAccess {
    Read,
    Write,
    Move,
    Free,
}

#[derive(Clone, Copy)]
pub(super) struct RuntimeLoanAccessRequest {
    pub(super) permission: VirValueId,
    pub(super) pointer: VirRuntimePointer,
    pub(super) start_bytes: u64,
    pub(super) end_bytes: u64,
    pub(super) kind: RuntimeLoanAccess,
}

#[derive(Clone, Copy)]
pub(super) struct RuntimeLoanLimits {
    pub(super) active_loans: usize,
    pub(super) aliases_per_loan: usize,
    pub(super) reborrow_depth: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RuntimeLoanActivity {
    Active,
    Suspended,
    Ended,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RuntimeLoan {
    allocation: u64,
    range: VirLoanRange,
    envelope: VirLoanRange,
    kind: VirLoanKind,
    region: crate::vir::VirBorrowRegionId,
    parent: Option<VirLoanId>,
    pointee: crate::vir::VirMemoryAccess,
    activity: RuntimeLoanActivity,
    authorities: BTreeSet<RuntimeLoanToken>,
}

impl RuntimeLoan {
    fn metadata_matches(&self, effect: VirLoanEffect, pointer: VirRuntimePointer) -> bool {
        self.allocation == pointer.allocation
            && self.pointee == pointer.access
            && self.envelope == effect.range
            && self.kind == effect.kind
            && self.region == effect.region
            && self.parent == effect.parent
    }
}

/// Concrete loan state for one function invocation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct RuntimeLoanShadow {
    invocation: u64,
    loans: BTreeMap<VirLoanId, RuntimeLoan>,
    next_authority: u64,
    next_dynamic_loan: u32,
}

impl RuntimeLoanShadow {
    pub(super) fn new(invocation: u64) -> Self {
        Self {
            invocation,
            loans: BTreeMap::new(),
            next_authority: 0,
            next_dynamic_loan: 1 << 31,
        }
    }
}

impl RuntimeLoanShadow {
    pub(in crate::vir::interpreter) fn root_loan(
        &self,
        mut loan: VirLoanId,
        span: ByteSpan,
    ) -> Result<VirLoanId, VirExecutionError> {
        let mut seen = BTreeSet::new();
        while seen.insert(loan) {
            let Some(parent) = self.loan(loan, span)?.parent else {
                return Ok(loan);
            };
            loan = parent;
        }
        Err(error(VirExecutionErrorKind::InvalidRuntimeState, span))
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn resolve_reborrow(
        &self,
        frame: &BlockFrame,
        loan: VirLoanId,
        region: crate::VirBorrowRegionId,
        effect: VirLoanAuthorityEffect,
        actual: VirLoanRange,
        runtime: crate::RuntimeVirView<'_>,
        span: ByteSpan,
    ) -> Result<VirLoanEffect, VirExecutionError> {
        let authority = frame
            .loan_authority(effect.source_permission)
            .ok_or_else(|| authority_error(loan, effect.source_permission, span))?;
        let parent = self.loan(authority.loan, span)?;
        if runtime.borrows.includes(region, parent.region, 4096) != Some(true) {
            return Err(error(
                VirExecutionErrorKind::LoanParentMismatch {
                    loan,
                    parent: authority.loan,
                },
                span,
            ));
        }
        let kind = match runtime.memory.kind(effect.reference.ty) {
            Some(crate::VirMemoryTypeKind::Slice {
                mutability: crate::VirMutability::Mutable,
                ..
            })
            | Some(crate::VirMemoryTypeKind::Pointer {
                mutability: crate::VirMutability::Mutable,
                ..
            }) => VirLoanKind::Mutable,
            _ => VirLoanKind::Shared,
        };
        Ok(VirLoanEffect {
            loan,
            kind,
            region,
            parent: Some(authority.loan),
            source_pointer: effect.source_pointer,
            source_permission: effect.source_permission,
            reference: effect.reference,
            range: actual,
            origin: effect.origin,
        })
    }
    pub(super) fn has_live_loans(&self) -> bool {
        self.loans
            .values()
            .any(|loan| loan.activity != RuntimeLoanActivity::Ended)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn begin(
        &mut self,
        frame: &mut BlockFrame,
        effect: VirLoanEffect,
        actual: VirLoanRange,
        reference_result: VirValue,
        permission_result: VirValue,
        limits: RuntimeLoanLimits,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if self
            .loans
            .get(&effect.loan)
            .is_some_and(|loan| loan.activity != RuntimeLoanActivity::Ended)
        {
            return Err(error(
                VirExecutionErrorKind::LoanAlreadyDefined { loan: effect.loan },
                source_span,
            ));
        }
        if self.active_count() >= limits.active_loans {
            return Err(error(
                VirExecutionErrorKind::ActiveLoanLimitExceeded {
                    limit: limits.active_loans,
                },
                source_span,
            ));
        }
        if limits.aliases_per_loan == 0 {
            return Err(error(
                VirExecutionErrorKind::LoanAliasLimitExceeded {
                    loan: effect.loan,
                    limit: limits.aliases_per_loan,
                },
                source_span,
            ));
        }
        if effect.parent.is_some() || frame.loan_authority(effect.source_permission).is_some() {
            return Err(error(
                VirExecutionErrorKind::LoanAuthorityMismatch {
                    loan: effect.loan,
                    permission: effect.source_permission,
                },
                source_span,
            ));
        }

        let pointer = pointer_value(frame, effect.source_pointer, source_span)?;
        let permission = frame.permission(effect.source_permission, source_span)?;
        self.check_selection(effect, actual, source_span)?;
        self.check_source_range(effect.loan, pointer, permission, actual, source_span)?;
        self.check_creation_conflict(
            effect,
            actual,
            pointer.allocation,
            &BTreeSet::new(),
            source_span,
        )?;

        let authority = self.fresh_authority(effect.loan, source_span)?;
        let mut authorities = BTreeSet::new();
        authorities.insert(authority.token);
        self.loans.insert(
            effect.loan,
            RuntimeLoan {
                allocation: pointer.allocation,
                range: actual,
                envelope: effect.range,
                kind: effect.kind,
                region: effect.region,
                parent: None,
                pointee: pointer.access,
                activity: RuntimeLoanActivity::Active,
                authorities,
            },
        );
        define_results(
            frame,
            actual,
            pointer,
            reference_result,
            permission_result,
            authority,
            source_span,
        )
    }

    pub(super) fn alias_shared(
        &mut self,
        frame: &mut BlockFrame,
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
        limits: RuntimeLoanLimits,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let pointer = pointer_value(frame, effect.source_pointer, source_span)?;
        let permission = frame.permission(effect.source_permission, source_span)?;
        let actual = self.loan(effect.loan, source_span)?.range;
        self.check_source_range(effect.loan, pointer, permission, actual, source_span)?;
        let source_authority =
            self.require_authority(frame, effect.loan, effect.source_permission, source_span)?;
        let loan = self.loan(effect.loan, source_span)?;
        if loan.activity != RuntimeLoanActivity::Active {
            return Err(error(
                VirExecutionErrorKind::LoanInactive { loan: effect.loan },
                source_span,
            ));
        }
        if loan.kind != VirLoanKind::Shared || !loan.metadata_matches(effect, pointer) {
            return Err(error(
                VirExecutionErrorKind::LoanMetadataMismatch { loan: effect.loan },
                source_span,
            ));
        }
        if !loan.authorities.contains(&source_authority.token) {
            return Err(authority_error(
                effect.loan,
                effect.source_permission,
                source_span,
            ));
        }
        if loan.authorities.len() >= limits.aliases_per_loan {
            return Err(error(
                VirExecutionErrorKind::LoanAliasLimitExceeded {
                    loan: effect.loan,
                    limit: limits.aliases_per_loan,
                },
                source_span,
            ));
        }

        let authority = self.fresh_authority(effect.loan, source_span)?;
        self.loans
            .get_mut(&effect.loan)
            .expect("checked loan exists")
            .authorities
            .insert(authority.token);
        define_results(
            frame,
            actual,
            pointer,
            reference_result,
            permission_result,
            authority,
            source_span,
        )
    }

    /// Creates the hidden alias stored by a whole-object copy of a shared
    /// reference-bearing aggregate.
    pub(super) fn alias_stored(
        &mut self,
        source: RuntimeLoanAuthority,
        pointer: VirRuntimePointer,
        _reference: crate::vir::VirMemoryAccess,
        limits: RuntimeLoanLimits,
        source_span: ByteSpan,
    ) -> Result<RuntimeLoanAuthority, VirExecutionError> {
        let loan = self.loan(source.loan, source_span)?;
        if loan.activity != RuntimeLoanActivity::Active
            || loan.kind != VirLoanKind::Shared
            || loan.allocation != pointer.allocation
            || loan.pointee != pointer.access
            || !loan.authorities.contains(&source.token)
        {
            return Err(error(
                VirExecutionErrorKind::LoanAuthorityMismatch {
                    loan: source.loan,
                    permission: VirValueId::new(u32::MAX),
                },
                source_span,
            ));
        }
        if loan.authorities.len() >= limits.aliases_per_loan {
            return Err(error(
                VirExecutionErrorKind::LoanAliasLimitExceeded {
                    loan: source.loan,
                    limit: limits.aliases_per_loan,
                },
                source_span,
            ));
        }
        let alias = self.fresh_authority(source.loan, source_span)?;
        self.loans
            .get_mut(&source.loan)
            .expect("checked loan exists")
            .authorities
            .insert(alias.token);
        Ok(alias)
    }

    pub(super) fn alias_authority(
        &mut self,
        frame: &mut BlockFrame,
        effect: VirLoanAuthorityEffect,
        reference_result: VirValue,
        permission_result: VirValue,
        limits: RuntimeLoanLimits,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let source = frame
            .loan_authority(effect.source_permission)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let pointer = pointer_value(frame, effect.source_pointer, source_span)?;
        let permission = frame.permission(effect.source_permission, source_span)?;
        let loan = self.loan(source.loan, source_span)?;
        if loan.activity != RuntimeLoanActivity::Active
            || loan.kind != VirLoanKind::Shared
            || loan.allocation != pointer.allocation
            || loan.pointee != pointer.access
            || permission.start_bytes != loan.range.start_bytes
            || permission.end_bytes != loan.range.end_bytes
            || !loan.authorities.contains(&source.token)
        {
            return Err(error(
                VirExecutionErrorKind::LoanAuthorityMismatch {
                    loan: source.loan,
                    permission: effect.source_permission,
                },
                source_span,
            ));
        }
        if loan.authorities.len() >= limits.aliases_per_loan {
            return Err(error(
                VirExecutionErrorKind::LoanAliasLimitExceeded {
                    loan: source.loan,
                    limit: limits.aliases_per_loan,
                },
                source_span,
            ));
        }
        let alias = self.fresh_authority(source.loan, source_span)?;
        self.loans
            .get_mut(&source.loan)
            .expect("checked loan exists")
            .authorities
            .insert(alias.token);
        frame.insert(
            reference_result,
            VirRuntimeValue::Pointer(pointer),
            source_span,
        )?;
        frame.insert(
            permission_result,
            VirRuntimeValue::Permission(permission),
            source_span,
        )?;
        frame.set_loan_authority(permission_result.id, alias);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn reborrow(
        &mut self,
        frame: &mut BlockFrame,
        effect: VirLoanEffect,
        actual: VirLoanRange,
        reference_result: VirValue,
        permission_result: VirValue,
        limits: RuntimeLoanLimits,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if self
            .loans
            .get(&effect.loan)
            .is_some_and(|loan| loan.activity != RuntimeLoanActivity::Ended)
        {
            return Err(error(
                VirExecutionErrorKind::LoanAlreadyDefined { loan: effect.loan },
                source_span,
            ));
        }
        if self.active_count() >= limits.active_loans {
            return Err(error(
                VirExecutionErrorKind::ActiveLoanLimitExceeded {
                    limit: limits.active_loans,
                },
                source_span,
            ));
        }
        if limits.aliases_per_loan == 0 {
            return Err(error(
                VirExecutionErrorKind::LoanAliasLimitExceeded {
                    loan: effect.loan,
                    limit: limits.aliases_per_loan,
                },
                source_span,
            ));
        }
        let parent_id = effect.parent.ok_or_else(|| {
            error(
                VirExecutionErrorKind::LoanMetadataMismatch { loan: effect.loan },
                source_span,
            )
        })?;
        let source_authority = frame
            .loan_authority(effect.source_permission)
            .ok_or_else(|| authority_error(parent_id, effect.source_permission, source_span))?;
        if source_authority.loan != parent_id {
            return Err(error(
                VirExecutionErrorKind::LoanParentMismatch {
                    loan: effect.loan,
                    parent: parent_id,
                },
                source_span,
            ));
        }
        let pointer = pointer_value(frame, effect.source_pointer, source_span)?;
        let permission = frame.permission(effect.source_permission, source_span)?;
        self.check_selection(effect, actual, source_span)?;
        self.check_source_range(effect.loan, pointer, permission, actual, source_span)?;

        let parent = self.loan(parent_id, source_span)?;
        let shared_child = parent.kind == VirLoanKind::Shared && effect.kind == VirLoanKind::Shared;
        if !matches!(
            parent.activity,
            RuntimeLoanActivity::Active | RuntimeLoanActivity::Suspended
        ) {
            return Err(error(
                VirExecutionErrorKind::LoanInactive { loan: parent_id },
                source_span,
            ));
        }
        if !parent.authorities.contains(&source_authority.token)
            || source_authority.loan != parent_id
        {
            return Err(error(
                VirExecutionErrorKind::LoanParentMismatch {
                    loan: effect.loan,
                    parent: parent_id,
                },
                source_span,
            ));
        }
        if parent.allocation != pointer.allocation
            || !parent.range.contains(actual)
            || (parent.kind == VirLoanKind::Shared && effect.kind != VirLoanKind::Shared)
        {
            return Err(error(
                VirExecutionErrorKind::LoanParentMismatch {
                    loan: effect.loan,
                    parent: parent_id,
                },
                source_span,
            ));
        }
        let depth = self.reborrow_depth(parent_id, source_span)?;
        if depth > limits.reborrow_depth {
            return Err(error(
                VirExecutionErrorKind::LoanReborrowDepthLimitExceeded {
                    loan: effect.loan,
                    limit: limits.reborrow_depth,
                },
                source_span,
            ));
        }
        let mut ancestors = BTreeSet::new();
        let mut ancestor = Some(parent_id);
        while let Some(id) = ancestor {
            ancestors.insert(id);
            ancestor = self.loan(id, source_span)?.parent;
        }
        self.check_creation_conflict(effect, actual, pointer.allocation, &ancestors, source_span)?;

        let authority = self.fresh_authority(effect.loan, source_span)?;
        if !shared_child {
            self.loans
                .get_mut(&parent_id)
                .expect("checked parent exists")
                .activity = RuntimeLoanActivity::Suspended;
        }
        let mut authorities = BTreeSet::new();
        authorities.insert(authority.token);
        self.loans.insert(
            effect.loan,
            RuntimeLoan {
                allocation: pointer.allocation,
                range: actual,
                envelope: effect.range,
                kind: effect.kind,
                region: effect.region,
                parent: Some(parent_id),
                pointee: pointer.access,
                activity: RuntimeLoanActivity::Active,
                authorities,
            },
        );
        define_results(
            frame,
            actual,
            pointer,
            reference_result,
            permission_result,
            authority,
            source_span,
        )
    }

    pub(super) fn end(
        &mut self,
        frame: &mut BlockFrame,
        effect: VirLoanEffect,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let loan = self.loan(effect.loan, source_span)?;
        if loan.activity != RuntimeLoanActivity::Active {
            return Err(error(
                VirExecutionErrorKind::LoanInactive { loan: effect.loan },
                source_span,
            ));
        }
        let pointer = pointer_value(frame, effect.source_pointer, source_span)?;
        let permission = frame.permission(effect.source_permission, source_span)?;
        self.check_source_range(effect.loan, pointer, permission, loan.range, source_span)?;
        let authority =
            self.require_authority(frame, effect.loan, effect.source_permission, source_span)?;
        let loan = self.loan(effect.loan, source_span)?;
        if !loan.metadata_matches(effect, pointer) {
            return Err(error(
                VirExecutionErrorKind::LoanMetadataMismatch { loan: effect.loan },
                source_span,
            ));
        }
        if self.has_active_child(effect.loan) {
            return Err(error(
                VirExecutionErrorKind::LoanHasActiveChild { loan: effect.loan },
                source_span,
            ));
        }
        if !loan.authorities.contains(&authority.token) {
            return Err(authority_error(
                effect.loan,
                effect.source_permission,
                source_span,
            ));
        }

        frame.consume_permission(effect.source_permission, source_span)?;
        let loan = self
            .loans
            .get_mut(&effect.loan)
            .expect("checked loan exists");
        loan.authorities.remove(&authority.token);
        if !loan.authorities.is_empty() {
            return Ok(());
        }
        loan.activity = RuntimeLoanActivity::Ended;
        let parent = loan.parent;
        if let Some(parent) = parent
            && !self.has_active_child(parent)
            && let Some(parent) = self.loans.get_mut(&parent)
            && parent.activity == RuntimeLoanActivity::Suspended
        {
            parent.activity = RuntimeLoanActivity::Active;
        }
        Ok(())
    }

    /// Ends a reference authority owned by an aggregate payload.
    pub(super) fn end_stored(
        &mut self,
        authority: RuntimeLoanAuthority,
        pointer: VirRuntimePointer,
        _reference: crate::vir::VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let loan = self.loan(authority.loan, source_span)?;
        if loan.activity != RuntimeLoanActivity::Active
            || loan.allocation != pointer.allocation
            || loan.pointee != pointer.access
            || !loan.authorities.contains(&authority.token)
            || (loan.authorities.len() == 1 && self.has_active_child(authority.loan))
        {
            return Err(error(
                VirExecutionErrorKind::LoanAuthorityMismatch {
                    loan: authority.loan,
                    permission: VirValueId::new(u32::MAX),
                },
                source_span,
            ));
        }
        let loan = self
            .loans
            .get_mut(&authority.loan)
            .expect("checked loan exists");
        loan.authorities.remove(&authority.token);
        if !loan.authorities.is_empty() {
            return Ok(());
        }
        loan.activity = RuntimeLoanActivity::Ended;
        let parent = loan.parent;
        if let Some(parent) = parent
            && !self.has_active_child(parent)
            && let Some(parent) = self.loans.get_mut(&parent)
            && parent.activity == RuntimeLoanActivity::Suspended
        {
            parent.activity = RuntimeLoanActivity::Active;
        }
        Ok(())
    }

    pub(super) fn end_authority(
        &mut self,
        frame: &mut BlockFrame,
        effect: VirLoanAuthorityEffect,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let authority = frame
            .loan_authority(effect.source_permission)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let pointer = pointer_value(frame, effect.source_pointer, source_span)?;
        let permission = frame.permission(effect.source_permission, source_span)?;
        let loan = self.loan(authority.loan, source_span)?;
        if permission.start_bytes != loan.range.start_bytes
            || permission.end_bytes != loan.range.end_bytes
            || loan.pointee != pointer.access
        {
            return Err(error(
                VirExecutionErrorKind::LoanAuthorityMismatch {
                    loan: authority.loan,
                    permission: effect.source_permission,
                },
                source_span,
            ));
        }
        self.end_stored(authority, pointer, effect.reference, source_span)?;
        frame.consume_permission(effect.source_permission, source_span)?;
        Ok(())
    }

    pub(super) fn check_access(
        &self,
        frame: &BlockFrame,
        request: RuntimeLoanAccessRequest,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if let Some(authority) = frame.loan_authority(request.permission) {
            let loan = self.loan(authority.loan, source_span)?;
            let compatible = loan.activity == RuntimeLoanActivity::Active
                && loan.authorities.contains(&authority.token)
                && loan.allocation == request.pointer.allocation
                && loan.range.start_bytes <= request.start_bytes
                && request.end_bytes <= loan.range.end_bytes
                && matches!(
                    (loan.kind, request.kind),
                    (VirLoanKind::Shared, RuntimeLoanAccess::Read)
                        | (
                            VirLoanKind::Mutable,
                            RuntimeLoanAccess::Read
                                | RuntimeLoanAccess::Write
                                | RuntimeLoanAccess::Move
                        )
                );
            if compatible {
                return Ok(());
            }
            return Err(error(
                VirExecutionErrorKind::LoanAccessConflict {
                    loan: authority.loan,
                    permission: request.permission,
                },
                source_span,
            ));
        }

        for (&loan_id, loan) in &self.loans {
            if loan.activity == RuntimeLoanActivity::Ended
                || loan.allocation != request.pointer.allocation
                || !ranges_overlap(request.start_bytes, request.end_bytes, loan.range)
            {
                continue;
            }
            if request.kind == RuntimeLoanAccess::Read && loan.kind == VirLoanKind::Shared {
                continue;
            }
            return Err(error(
                VirExecutionErrorKind::LoanAccessConflict {
                    loan: loan_id,
                    permission: request.permission,
                },
                source_span,
            ));
        }
        Ok(())
    }

    pub(super) fn reject_permission_transform(
        &self,
        frame: &BlockFrame,
        permission: VirValueId,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if let Some(authority) = frame.loan_authority(permission) {
            return Err(error(
                VirExecutionErrorKind::LoanAccessConflict {
                    loan: authority.loan,
                    permission,
                },
                source_span,
            ));
        }
        Ok(())
    }

    pub(super) fn finish(&self, source_span: ByteSpan) -> Result<(), VirExecutionError> {
        if let Some((&loan, _)) = self
            .loans
            .iter()
            .find(|(_, loan)| loan.activity != RuntimeLoanActivity::Ended)
        {
            return Err(error(
                VirExecutionErrorKind::LoanNotEnded { loan },
                source_span,
            ));
        }
        Ok(())
    }

    fn active_count(&self) -> usize {
        self.loans
            .values()
            .filter(|loan| loan.activity != RuntimeLoanActivity::Ended)
            .count()
    }

    fn loan(
        &self,
        id: VirLoanId,
        source_span: ByteSpan,
    ) -> Result<&RuntimeLoan, VirExecutionError> {
        self.loans
            .get(&id)
            .ok_or_else(|| error(VirExecutionErrorKind::MissingLoan { loan: id }, source_span))
    }

    fn fresh_authority(
        &mut self,
        loan: VirLoanId,
        source_span: ByteSpan,
    ) -> Result<RuntimeLoanAuthority, VirExecutionError> {
        let token = RuntimeLoanToken {
            invocation: self.invocation,
            ordinal: self.next_authority,
        };
        self.next_authority = self.next_authority.checked_add(1).ok_or_else(|| {
            error(
                VirExecutionErrorKind::ActiveLoanLimitExceeded { limit: usize::MAX },
                source_span,
            )
        })?;
        Ok(RuntimeLoanAuthority { loan, token })
    }

    fn require_authority(
        &self,
        frame: &BlockFrame,
        loan: VirLoanId,
        permission: VirValueId,
        source_span: ByteSpan,
    ) -> Result<RuntimeLoanAuthority, VirExecutionError> {
        frame
            .loan_authority(permission)
            .filter(|authority| {
                authority.loan == loan
                    && self
                        .loans
                        .get(&loan)
                        .is_some_and(|state| state.authorities.contains(&authority.token))
            })
            .ok_or_else(|| authority_error(loan, permission, source_span))
    }

    fn check_source_range(
        &self,
        loan: VirLoanId,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        range: VirLoanRange,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let pointer_in_range = if range.start_bytes == range.end_bytes {
            pointer.offset_bytes == range.start_bytes
        } else {
            range.start_bytes <= pointer.offset_bytes && pointer.offset_bytes < range.end_bytes
        };
        let valid = range.start_bytes <= range.end_bytes
            && pointer_in_range
            && pointer.allocation == permission.allocation
            && permission.start_bytes <= range.start_bytes
            && range.end_bytes <= permission.end_bytes;
        if !valid {
            return Err(error(
                VirExecutionErrorKind::LoanRangeViolation { loan },
                source_span,
            ));
        }
        Ok(())
    }

    fn check_selection(
        &self,
        effect: VirLoanEffect,
        actual: VirLoanRange,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if actual.start_bytes > actual.end_bytes || !effect.range.contains(actual) {
            return Err(error(
                VirExecutionErrorKind::LoanRangeViolation { loan: effect.loan },
                span,
            ));
        }
        Ok(())
    }

    fn check_creation_conflict(
        &self,
        effect: VirLoanEffect,
        actual: VirLoanRange,
        allocation: u64,
        ignored: &BTreeSet<VirLoanId>,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let conflicts = self.loans.iter().any(|(&id, loan)| {
            !ignored.contains(&id)
                && loan.activity != RuntimeLoanActivity::Ended
                && loan.allocation == allocation
                && ranges_overlap(actual.start_bytes, actual.end_bytes, loan.range)
                && !(loan.kind == VirLoanKind::Shared && effect.kind == VirLoanKind::Shared)
        });
        if conflicts {
            return Err(error(
                VirExecutionErrorKind::LoanConflict { loan: effect.loan },
                source_span,
            ));
        }
        Ok(())
    }

    fn has_active_child(&self, parent: VirLoanId) -> bool {
        self.loans
            .values()
            .any(|loan| loan.parent == Some(parent) && loan.activity != RuntimeLoanActivity::Ended)
    }

    fn reborrow_depth(
        &self,
        parent: VirLoanId,
        source_span: ByteSpan,
    ) -> Result<usize, VirExecutionError> {
        let mut depth = 1_usize;
        let mut current = self.loan(parent, source_span)?.parent;
        let mut seen = BTreeSet::from([parent]);
        while let Some(id) = current {
            if !seen.insert(id) {
                return Err(error(
                    VirExecutionErrorKind::LoanParentMismatch {
                        loan: parent,
                        parent: id,
                    },
                    source_span,
                ));
            }
            depth = depth.saturating_add(1);
            current = self.loan(id, source_span)?.parent;
        }
        Ok(depth)
    }
}

fn define_results(
    frame: &mut BlockFrame,
    actual: VirLoanRange,
    pointer: VirRuntimePointer,
    reference_result: VirValue,
    permission_result: VirValue,
    authority: RuntimeLoanAuthority,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    frame.insert(
        reference_result,
        VirRuntimeValue::Pointer(pointer),
        source_span,
    )?;
    frame.insert(
        permission_result,
        VirRuntimeValue::Permission(VirRuntimePermission {
            allocation: pointer.allocation,
            start_bytes: actual.start_bytes,
            end_bytes: actual.end_bytes,
            can_free_when_complete: false,
        }),
        source_span,
    )?;
    frame.set_loan_authority(permission_result.id, authority);
    Ok(())
}

fn ranges_overlap(start: u64, end: u64, other: VirLoanRange) -> bool {
    start < other.end_bytes && other.start_bytes < end
}

fn authority_error(
    loan: VirLoanId,
    permission: VirValueId,
    source_span: ByteSpan,
) -> VirExecutionError {
    error(
        VirExecutionErrorKind::LoanAuthorityMismatch { loan, permission },
        source_span,
    )
}

#[cfg(test)]
mod frame_identity_tests {
    use super::*;

    #[test]
    fn stored_authorities_cannot_cross_or_reenter_invocations_with_reused_loan_ids() {
        let span = ByteSpan::empty();
        let mut interpreter =
            super::super::Interpreter::new(super::super::VirInterpreterConfig::default());
        let id = VirLoanId::new(0);
        let access = crate::VirMemoryAccess::core_u64();
        let range = VirLoanRange {
            start_bytes: 0,
            end_bytes: 8,
        };
        let pointer = VirRuntimePointer {
            allocation: 0,
            offset_bytes: 0,
            access,
            paths: crate::VirPointerPaths::default(),
            view_range: Some(range),
            domain: crate::VirPointerDomain::Restricted(range),
        };
        let permission = VirRuntimePermission {
            allocation: 0,
            start_bytes: 0,
            end_bytes: 8,
            can_free_when_complete: false,
        };
        let limits = RuntimeLoanLimits {
            active_loans: 8,
            aliases_per_loan: 8,
            reborrow_depth: 8,
        };
        let permission_id = VirValueId::new(1);
        let mut retired = Vec::new();
        for _ in 0..16 {
            let invocation = interpreter.fresh_loan_frame(span).unwrap();
            let mut shadow = RuntimeLoanShadow::new(invocation);
            let local = shadow.fresh_authority(id, span).unwrap();
            assert_eq!(local.token.ordinal, 0);
            shadow.loans.insert(
                id,
                RuntimeLoan {
                    allocation: 0,
                    range,
                    envelope: range,
                    kind: VirLoanKind::Shared,
                    region: crate::VirBorrowRegionId::new(0),
                    parent: None,
                    pointee: access,
                    activity: RuntimeLoanActivity::Active,
                    authorities: BTreeSet::from([local.token]),
                },
            );
            for foreign in &retired {
                assert_ne!(*foreign, local);
                let frame = BlockFrame {
                    values: BTreeMap::from([(
                        permission_id,
                        VirRuntimeValue::Permission(permission),
                    )]),
                    consumed_permissions: BTreeSet::new(),
                    loan_authorities: BTreeMap::from([(permission_id, *foreign)]),
                };
                assert!(
                    shadow
                        .require_authority(&frame, id, permission_id, span)
                        .is_err()
                );
                assert!(
                    shadow
                        .check_access(
                            &frame,
                            RuntimeLoanAccessRequest {
                                permission: permission_id,
                                pointer,
                                start_bytes: 0,
                                end_bytes: 8,
                                kind: RuntimeLoanAccess::Read,
                            },
                            span
                        )
                        .is_err()
                );
                assert!(
                    shadow
                        .alias_stored(*foreign, pointer, access, limits, span)
                        .is_err()
                );
                assert!(shadow.end_stored(*foreign, pointer, access, span).is_err());
                assert!(
                    shadow
                        .activate_conditional_return(*foreign, None, permission, limits, span)
                        .is_err()
                );
                assert_eq!(shadow.loans[&id].authorities, BTreeSet::from([local.token]));
                assert_eq!(shadow.loans[&id].activity, RuntimeLoanActivity::Active);
                assert_eq!(shadow.next_authority, 1);
            }
            let alias = shadow
                .alias_stored(local, pointer, access, limits, span)
                .unwrap();
            shadow.end_stored(alias, pointer, access, span).unwrap();
            shadow.end_stored(local, pointer, access, span).unwrap();
            shadow.finish(span).unwrap();
            retired.push(local);
        }
    }
}
