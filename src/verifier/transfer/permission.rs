use super::*;

impl<'environment> TransferBuilder<'environment> {
    pub(super) fn permission_split(
        &mut self,
        left_result: VirValue,
        right_result: VirValue,
        source_id: VirValueId,
        split_id: VirValueId,
    ) -> Result<(), TransferError> {
        let source = permission_fact(&self.state, source_id)?;
        let split_at = word_fact(&self.state, split_id)?;
        let split_expression = word_expression(&self.state, split_id, split_at);
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: source_id,
            },
            permission_availability_status(source.availability()),
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: match source.authority() {
                    PermissionAuthority::Loan(loan) => Some(loan),
                    PermissionAuthority::Owner | PermissionAuthority::Unknown => None,
                },
                permission: source_id,
                access: exact_abstract_range(source.range()),
                required: AccessPermission::Read,
            },
            owner_authority_status(source.authority()),
        );
        self.require(
            ResourceObligationKind::PermissionSplitPointInRange {
                permission: source_id,
                split_at,
            },
            split_status(source.range(), split_at, split_expression),
        );

        let (left_range, right_range) = split_ranges(source.range(), split_at, split_expression)?;
        mark_permission_consumed(&mut self.state, source_id)?;
        self.define(
            left_result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    source.provenance(),
                    left_range,
                    source.access(),
                    source.free_capability(),
                )
                .with_authority(source.authority()),
            ),
        )?;
        self.define(
            right_result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    source.provenance(),
                    right_range,
                    source.access(),
                    source.free_capability(),
                )
                .with_authority(source.authority()),
            ),
        )
    }

    pub(super) fn permission_join(
        &mut self,
        result: VirValue,
        left_id: VirValueId,
        right_id: VirValueId,
    ) -> Result<(), TransferError> {
        let left = permission_fact(&self.state, left_id)?;
        let right = permission_fact(&self.state, right_id)?;
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: left_id,
            },
            permission_availability_status(left.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: right_id,
            },
            permission_availability_status(right.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionOperandsDistinct {
                left: left_id,
                right: right_id,
            },
            if left_id == right_id {
                ObligationStatus::Refuted
            } else {
                ObligationStatus::Proven
            },
        );
        let (compatibility, joined_range) = permission_join_status(left, right)?;
        self.require(
            ResourceObligationKind::PermissionJoinCompatible {
                left: left_id,
                right: right_id,
            },
            compatibility,
        );

        mark_permission_consumed(&mut self.state, left_id)?;
        if right_id != left_id {
            mark_permission_consumed(&mut self.state, right_id)?;
        }
        self.define(
            result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    left.provenance().join(right.provenance()),
                    joined_range,
                    left.access().join(right.access()),
                    left.free_capability().join(right.free_capability()),
                )
                .with_authority(left.authority().join(right.authority())),
            ),
        )
    }

    pub(super) fn permission_move(
        &mut self,
        result: VirValue,
        source_id: VirValueId,
    ) -> Result<(), TransferError> {
        let source = permission_fact(&self.state, source_id)?;
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: source_id,
            },
            permission_availability_status(source.availability()),
        );
        mark_permission_consumed(&mut self.state, source_id)?;
        self.move_loan_authority(source.authority(), source_id, result.id);
        self.define(
            result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    source.provenance(),
                    source.range(),
                    source.access(),
                    source.free_capability(),
                )
                .with_authority(source.authority()),
            ),
        )
    }
}
