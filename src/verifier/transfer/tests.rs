use super::*;

#[test]
fn sibling_creation_does_not_turn_joined_or_ended_parent_into_active_authority() {
    let source = "fn main() -> u64 { let mut a=[20,22]; let p=&mut a[..];
        let l=&mut p[..1]; let r=&mut p[1..]; return l[0]+r[0]; }";
    let output = crate::analyze(&crate::SourceFile::from_text("sibling-join.nera", source));
    let unit = output.vir().unwrap().as_unit();
    for activity in [LoanActivity::MaybeActive, LoanActivity::Ended] {
        let context = LoanTransferContext {
            borrows: &unit.borrows,
            function: VirFunctionId::new(0),
            limits: LoanTransferLimits {
                max_region_pairs: 256,
                max_active_loans: 256,
                max_aliases_per_loan: 256,
                max_region_constraints: 4096,
                max_reborrow_depth: 64,
            },
        };
        let mut transfer = TransferBuilder::new(
            ResourceState::new(),
            ByteSpan::new(0, source.len()).unwrap(),
            &unit.memory,
            None,
            Some(context),
        );
        let mut tested = false;
        for instruction in &unit.runtime.functions[0].blocks[0].instructions {
            if let VirInstruction::LoanReborrow {
                effect,
                permission_result,
                ..
            } = instruction.instruction
                && effect.loan == VirLoanId::new(2)
            {
                assert_eq!(
                    transfer.state.loan(VirLoanId::new(0)).unwrap().activity(),
                    LoanActivity::Suspended
                );
                transfer
                    .state
                    .loan_mut(VirLoanId::new(0))
                    .unwrap()
                    .set_activity(activity);
                transfer.obligations.clear();
                transfer.apply(&instruction.instruction).unwrap();
                assert_eq!(
                    permission_fact(&transfer.state, permission_result.id)
                        .unwrap()
                        .authority(),
                    PermissionAuthority::Unknown
                );
                assert!(transfer.obligations.iter().any(|o| matches!(
                    o.kind,
                    ResourceObligationKind::LoanParentActive { .. }
                ) && !o.status.is_proven()));
                tested = true;
                break;
            }
            transfer.apply(&instruction.instruction).unwrap();
        }
        assert!(tested);
    }
}

#[test]
fn reborrow_and_alias_recheck_value_state_before_granting_authority() {
    for source in [
        "fn main() -> u64 { let mut value = 42; let parent = &mut value;
         let child = &mut *parent; return *child; }",
        "fn main() -> u64 { let value = 42; let parent = &value;
         let child = parent; return *child + *parent; }",
    ] {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "borrow-transition.nera",
            source,
        ));
        let unit = output.vir().unwrap().as_unit();
        let context = LoanTransferContext {
            borrows: &unit.borrows,
            function: VirFunctionId::new(0),
            limits: LoanTransferLimits {
                max_region_pairs: 256,
                max_active_loans: 256,
                max_aliases_per_loan: 256,
                max_region_constraints: 4096,
                max_reborrow_depth: 64,
            },
        };
        let mut transfer = TransferBuilder::new(
            ResourceState::new(),
            ByteSpan::new(0, source.len()).unwrap(),
            &unit.memory,
            None,
            Some(context),
        );
        let mut checked = false;
        for instruction in &unit.runtime.functions[0].blocks[0].instructions {
            if let VirInstruction::LoanReborrow {
                effect,
                permission_result,
                ..
            }
            | VirInstruction::LoanAliasShared {
                effect,
                permission_result,
                ..
            } = instruction.instruction
            {
                assert!(
                    transfer
                        .obligations
                        .iter()
                        .all(|obligation| obligation.status.is_proven())
                );
                let pointer = pointer_fact(&transfer.state, effect.source_pointer).unwrap();
                let AbstractProvenance::Known(id) = pointer.provenance() else {
                    panic!("known local allocation")
                };
                transfer
                    .state
                    .allocation_mut(id)
                    .unwrap()
                    .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                    .unwrap();
                transfer.obligations.clear();
                transfer.apply(&instruction.instruction).unwrap();
                assert!(transfer.obligations.iter().any(|obligation| matches!(
                    obligation.kind,
                    ResourceObligationKind::ObjectValueBytesInitialized { .. }
                ) && obligation.status
                    == ObligationStatus::Refuted));
                let permission = permission_fact(&transfer.state, permission_result.id).unwrap();
                assert_eq!(permission.authority(), PermissionAuthority::Unknown);
                checked = true;
                break;
            }
            transfer.apply(&instruction.instruction).unwrap();
        }
        assert!(
            checked,
            "fixture must reach the reborrow/alias formation boundary"
        );
    }
}

#[test]
fn borrow_formation_does_not_invent_validity_or_payload_from_initialized_bytes() {
    for source in [
        "fn main() -> u64 { let value = true; let reference = &value; return 0; }",
        "struct Holder { owner: Own<u64>, } fn main() -> u64 {
         let owner = alloc<u64>(1); *owner = 1; let value = Holder { owner: owner };
         let reference = &value; return 0; }",
    ] {
        let output = crate::analyze(&crate::SourceFile::from_text("borrow-facts.nera", source));
        let unit = output.vir().unwrap().as_unit();
        let effect = unit.runtime.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .find_map(|instruction| match instruction.instruction {
                VirInstruction::LoanBegin { effect, .. } => Some(effect),
                _ => None,
            })
            .unwrap();
        let access = reference_pointee(&unit.memory, effect.reference).unwrap();
        let size = unit.memory.layout(access.layout).unwrap().size_bytes;
        let alignment = unit.memory.layout(access.layout).unwrap().alignment;
        let range = ByteRange::new(0, size).unwrap();
        let id = AbstractAllocationId::new(0);
        let pointer = AbstractPointer::new(
            AbstractProvenance::Known(id),
            U64Interval::exact(0),
            GuaranteedAlignment::new(alignment).unwrap(),
        )
        .with_memory_access(Some(access));
        let mut allocation = AbstractAllocation::new_local(size, alignment).unwrap();
        allocation.mark_initialized(range).unwrap();
        let mut state = ResourceState::new();
        state.define_allocation(id, allocation).unwrap();
        state
            .define_value(
                effect.source_permission,
                AbstractValue::Permission(AbstractPermission::new(
                    AbstractProvenance::Known(id),
                    AbstractByteRange::Exact(range),
                    AccessPermission::Write,
                    FreeCapability::No,
                )),
            )
            .unwrap();
        let mut transfer = TransferBuilder::new(
            state,
            ByteSpan::new(0, source.len()).unwrap(),
            &unit.memory,
            None,
            None,
        );
        assert!(
            !transfer
                .require_loan_value(effect, pointer, range)
                .unwrap()
                .is_proven()
        );
        assert!(transfer.obligations.iter().any(|obligation| matches!(
            obligation.kind,
            ResourceObligationKind::ObjectRepresentationValid { .. }
        ) && !obligation.status.is_proven()));
        transfer
            .state
            .allocation_mut(id)
            .unwrap()
            .mark_valid(range)
            .unwrap();
        transfer.obligations.clear();
        let result = transfer.require_loan_value(effect, pointer, range).unwrap();
        if unit
            .memory
            .object_shape(access)
            .unwrap()
            .resource_leaves()
            .is_empty()
        {
            assert!(result.is_proven());
        } else {
            assert!(!result.is_proven());
            assert!(transfer.obligations.iter().any(|obligation| matches!(
                obligation.kind,
                ResourceObligationKind::ResourcePayloadAvailable { .. }
            )
                && !obligation.status.is_proven()));
        }
    }
}

#[test]
fn permission_coverage_status_matches_small_concrete_offset_sets() {
    const WIDTH: u64 = 2;
    for permission_start in 0..=5 {
        for permission_end in permission_start..=6 {
            let permission = AbstractByteRange::Exact(
                ByteRange::new(permission_start, permission_end).expect("valid range"),
            );
            for offset_lower in 0..=5 {
                for offset_upper in offset_lower..=5 {
                    let offset =
                        U64Interval::new(offset_lower, offset_upper).expect("valid interval");
                    let concrete = (offset_lower..=offset_upper).map(|candidate| {
                        candidate >= permission_start
                            && candidate
                                .checked_add(WIDTH)
                                .is_some_and(|end| end <= permission_end)
                    });
                    let outcomes: Vec<_> = concrete.collect();
                    let expected = if outcomes.iter().all(|covered| *covered) {
                        ObligationStatus::Proven
                    } else if outcomes.iter().all(|covered| !*covered) {
                        ObligationStatus::Refuted
                    } else {
                        ObligationStatus::Unknown
                    };
                    assert_eq!(
                        permission_coverage_status(
                            permission,
                            AbstractPointer::new(
                                AbstractProvenance::Unknown,
                                offset,
                                GuaranteedAlignment::one(),
                            ),
                            WIDTH,
                        ),
                        expected,
                        "permission [{permission_start}, {permission_end}), offsets \
                         [{offset_lower}, {offset_upper}]"
                    );
                }
            }
        }
    }
}

#[test]
fn writability_status_preserves_unknown_capability() {
    assert_eq!(
        permission_writable_status(AccessPermission::Write),
        ObligationStatus::Proven
    );
    assert_eq!(
        permission_writable_status(AccessPermission::Read),
        ObligationStatus::Refuted
    );
    assert_eq!(
        permission_writable_status(AccessPermission::MaybeWrite),
        ObligationStatus::Unknown
    );
}

#[test]
fn object_non_overlap_uses_allocation_identity_and_affine_correlation() {
    let allocation = AbstractAllocationId::new(0);
    let alignment = GuaranteedAlignment::new(8).unwrap();
    let root = VirValueId::new(7);
    let left = AbstractPointer::new(
        AbstractProvenance::Known(allocation),
        U64Interval::new(0, 80).unwrap(),
        alignment,
    )
    .with_offset_expression(Some(AffineExpression::identity(root)));
    let right = AbstractPointer::new(
        AbstractProvenance::Known(allocation),
        U64Interval::new(40, 120).unwrap(),
        alignment,
    )
    .with_offset_expression(Some(
        AffineExpression::identity(root)
            .checked_add_constant(40)
            .unwrap(),
    ));
    assert_eq!(
        object_non_overlap_status(left, right, 40),
        ObligationStatus::Proven
    );

    let overlap = AbstractPointer::new(
        AbstractProvenance::Known(allocation),
        U64Interval::exact(8),
        alignment,
    );
    let base = AbstractPointer::new(
        AbstractProvenance::Known(allocation),
        U64Interval::exact(0),
        alignment,
    );
    assert_eq!(
        object_non_overlap_status(base, overlap, 40),
        ObligationStatus::Refuted
    );
    assert_eq!(
        object_non_overlap_status(
            base,
            AbstractPointer::new(
                AbstractProvenance::Unknown,
                U64Interval::unknown(),
                alignment,
            ),
            40,
        ),
        ObligationStatus::Unknown
    );
}
