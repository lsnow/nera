//! Stable loop resources come from the real entry, never from a clause.
use super::*;

impl ResourceState {
    pub(in crate::verifier) fn inherit_loop_scalar_frame(
        &mut self,
        entry: &Self,
        retained: &BTreeSet<VirValueId>,
    ) {
        let renames: Vec<_> = retained.iter().map(|id| (*id, *id)).collect();
        let frame = entry.project_cfg_edge(&renames);
        self.path_condition = frame.path_condition;
        self.relations = frame.relations;
        self.word_expressions = frame.word_expressions;
    }
    pub(in crate::verifier) fn inherit_loop_resources(
        &mut self,
        entry: &Self,
        modified: &BTreeSet<AbstractAllocationId>,
    ) -> bool {
        if entry.allocations.values().any(|a| {
            !a.object_state().resource_payloads().is_empty()
                || !a.object_state().active_variants().is_empty()
        }) {
            return false;
        }
        if entry.loans.values().any(|loan| {
            loan.footprint()
                .is_some_and(|f| matches!(f.range, AbstractByteRange::Symbolic { .. }))
        }) {
            return false;
        }
        self.allocations = entry.allocations.clone();
        self.loans = entry.loans.clone();
        self.loan_precision_losses = entry.loan_precision_losses.clone();
        // A first-entry fact mentioning i must not grow when the loop head
        // havocs i. Concrete byte initialization/validity remains monotone.
        for allocation in self.allocations.values_mut() {
            allocation.initialization_prefixes = Default::default();
        }
        for id in modified {
            let Some(allocation) = self.allocations.get_mut(id) else {
                return false;
            };
            let extent = ByteRange::new(0, allocation.size_bytes()).expect("allocation extent");
            // Only valid scalar writes are admitted in this loop profile.
            // They preserve initialized bytes, not values or uninitializedness.
            allocation
                .forget_uninitialized(extent)
                .expect("allocation extent");
        }
        true
    }

    pub(in crate::verifier) fn stable_loop_value(value: AbstractValue) -> bool {
        let stable_range = |r| !matches!(r, AbstractByteRange::Symbolic { .. });
        match value {
            AbstractValue::Pointer(p) => {
                p.offset_bytes().exact_value().is_some()
                    && p.offset_expression().is_none_or(|e| e.is_constant())
                    && p.slice_footprint().is_none_or(|f| stable_range(f.range))
                    && match p.domain() {
                        crate::VirPointerDomain::Restricted(r) => stable_range(r),
                        _ => true,
                    }
            }
            AbstractValue::Permission(p) => stable_range(p.range()),
            _ => false,
        }
    }

    pub(in crate::verifier) fn loop_resources_match(
        &self,
        expected: &Self,
        values: &[VirValueId],
    ) -> bool {
        self.allocations.len() == expected.allocations.len()
            && expected
                .loans
                .iter()
                .all(|(id, before)| self.loans.get(id) == Some(before))
            && self.loans.iter().all(|(id, loan)| {
                expected.loans.contains_key(id)
                    || (loan.activity() == LoanActivity::Ended && loan.authorities().is_empty())
            })
            && self.loan_precision_losses == expected.loan_precision_losses
            && values
                .iter()
                .all(|id| self.value(*id) == expected.value(*id))
            && expected.allocations.iter().all(|(id, before)| {
                self.allocations.get(id).is_some_and(|after| {
                    before.region == after.region
                        && before.size_bytes == after.size_bytes
                        && before.alignment == after.alignment
                        && before.liveness == after.liveness
                        && before.ownership == after.ownership
                        && before.object_state == after.object_state
                })
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const ID: AbstractAllocationId = AbstractAllocationId::new(0);
    const PERMISSION: VirValueId = VirValueId::new(0);

    fn entry() -> ResourceState {
        let mut s = ResourceState::new();
        s.define_allocation(
            ID,
            AbstractAllocation::new(VirRegionId::new(0), 16, 8).unwrap(),
        )
        .unwrap();
        s.define_value(
            PERMISSION,
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(ID),
                AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .unwrap();
        s.define_loan(
            VirLoanId::new(0),
            AbstractLoan::new(
                AbstractProvenance::Known(ID),
                ByteRange::new(0, 8).unwrap(),
                crate::VirLoanKind::Shared,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            ),
        )
        .unwrap();
        s
    }

    #[test]
    fn backedge_cannot_lose_permission_range_instance_or_loan_state() {
        let original = entry();
        assert!(original.loop_resources_match(&original, &[PERMISSION]));
        for mutation in 0..5 {
            let mut s = original.clone();
            match mutation {
                0 => s.allocations.get_mut(&ID).unwrap().mark_dead(),
                1 => {
                    let AbstractValue::Permission(p) = s.values.get_mut(&PERMISSION).unwrap()
                    else {
                        unreachable!()
                    };
                    p.mark_consumed();
                }
                2 => {
                    let AbstractValue::Permission(p) = s.values.get_mut(&PERMISSION).unwrap()
                    else {
                        unreachable!()
                    };
                    p.range = AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap());
                }
                3 => s
                    .loans
                    .get_mut(&VirLoanId::new(0))
                    .unwrap()
                    .set_activity(LoanActivity::Ended),
                _ => {
                    s.allocations.remove(&ID);
                }
            }
            assert!(
                !s.loop_resources_match(&original, &[PERMISSION]),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn only_ended_authority_free_iteration_loans_can_be_forgotten() {
        let original = entry();
        for (activity, authority, expected) in [
            (LoanActivity::Active, false, false),
            (LoanActivity::Ended, true, false),
            (LoanActivity::Ended, false, true),
        ] {
            let mut state = original.clone();
            let mut loan = AbstractLoan::new(
                AbstractProvenance::Known(ID),
                ByteRange::new(0, 8).unwrap(),
                crate::VirLoanKind::Shared,
                crate::VirBorrowRegionId::new(1),
                None,
                activity,
            );
            if authority {
                loan.add_authority(VirValueId::new(1));
            }
            state.define_loan(VirLoanId::new(1), loan).unwrap();
            assert_eq!(
                state.loop_resources_match(&original, &[PERMISSION]),
                expected
            );
        }
    }

    #[test]
    fn head_copies_existing_ledger_without_reviving_or_manufacturing_authority() {
        let mut original = entry();
        original.allocations.get_mut(&ID).unwrap().mark_dead();
        let AbstractValue::Permission(p) = original.values.get_mut(&PERMISSION).unwrap() else {
            unreachable!()
        };
        p.mark_consumed();
        let mut head = ResourceState::new();
        assert!(head.inherit_loop_resources(&original, &BTreeSet::new()));
        assert_eq!(head.allocations, original.allocations);
        assert_eq!(head.loans, original.loans);
        assert!(
            head.values.is_empty(),
            "clauses cannot manufacture SSA authority"
        );
    }
}
