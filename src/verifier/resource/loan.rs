use super::*;

/// Access strength guaranteed by a permission token.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AccessPermission {
    /// The permission is definitely read-only.
    Read,
    /// The permission is definitely writable (and therefore readable).
    Write,
    /// Every represented permission is readable, but writability differs or
    /// is not known precisely enough.
    MaybeWrite,
}

impl AccessPermission {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Read, Self::Read)
                | (Self::Write, Self::Write)
                | (Self::MaybeWrite, Self::MaybeWrite)
        ) {
            self
        } else {
            Self::MaybeWrite
        }
    }
}

/// Whether a complete permission can release its allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FreeCapability {
    Yes,
    No,
    Maybe,
}

impl FreeCapability {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!((self, other), (Self::Yes, Self::Yes) | (Self::No, Self::No)) {
            self
        } else {
            Self::Maybe
        }
    }
}

/// Linear availability of one permission SSA value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PermissionAvailability {
    Available,
    Consumed,
    MaybeConsumed,
}

/// Semantic authority carried by one permission SSA value.
///
/// Authority is never reconstructed from pointer bits, provenance or range.
/// `Unknown` is the conservative join/budget result and grants no access by
/// itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PermissionAuthority {
    Owner,
    Loan(VirLoanId),
    Unknown,
}

impl PermissionAuthority {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Owner, Self::Owner) | (Self::Unknown, Self::Unknown)
        ) {
            self
        } else {
            match (self, other) {
                (Self::Loan(left), Self::Loan(right)) if left.get() == right.get() => self,
                _ => Self::Unknown,
            }
        }
    }
}

impl PermissionAvailability {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Available, Self::Available) | (Self::Consumed, Self::Consumed)
        ) {
            self
        } else {
            Self::MaybeConsumed
        }
    }
}

/// Abstract linear permission carried by a VIR `permission` value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AbstractPermission {
    pub(super) provenance: AbstractProvenance,
    pub(super) range: AbstractByteRange,
    pub(super) access: AccessPermission,
    pub(super) free: FreeCapability,
    pub(super) availability: PermissionAvailability,
    pub(super) authority: PermissionAuthority,
}

impl AbstractPermission {
    #[must_use]
    pub const fn new(
        provenance: AbstractProvenance,
        range: AbstractByteRange,
        access: AccessPermission,
        free: FreeCapability,
    ) -> Self {
        Self {
            provenance,
            range,
            access,
            free,
            availability: PermissionAvailability::Available,
            authority: PermissionAuthority::Owner,
        }
    }

    #[must_use]
    pub const fn provenance(self) -> AbstractProvenance {
        self.provenance
    }

    #[must_use]
    pub const fn range(self) -> AbstractByteRange {
        self.range
    }

    #[must_use]
    pub const fn access(self) -> AccessPermission {
        self.access
    }

    #[must_use]
    pub const fn free_capability(self) -> FreeCapability {
        self.free
    }

    #[must_use]
    pub const fn availability(self) -> PermissionAvailability {
        self.availability
    }

    #[must_use]
    pub const fn authority(self) -> PermissionAuthority {
        self.authority
    }

    #[must_use]
    pub const fn with_availability(mut self, availability: PermissionAvailability) -> Self {
        self.availability = availability;
        self
    }

    #[must_use]
    pub const fn with_authority(mut self, authority: PermissionAuthority) -> Self {
        self.authority = authority;
        self
    }

    pub fn mark_consumed(&mut self) {
        self.availability = PermissionAvailability::Consumed;
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        Self {
            provenance: self.provenance.join(other.provenance),
            range: self.range.join(other.range),
            access: self.access.join(other.access),
            free: self.free.join(other.free),
            availability: self.availability.join(other.availability),
            authority: self.authority.join(other.authority),
        }
    }
}

/// Path-local lifecycle of one canonical loan instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LoanActivity {
    Active,
    Suspended,
    Ended,
    /// At least one joined/budgeted alternative may still be active.
    MaybeActive,
}

impl LoanActivity {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Active, Self::Active)
                | (Self::Suspended, Self::Suspended)
                | (Self::Ended, Self::Ended)
                | (Self::MaybeActive, Self::MaybeActive)
        ) {
            self
        } else {
            Self::MaybeActive
        }
    }
}

/// Conservative precision losses specific to the loan domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LoanPrecisionLoss {
    ActiveLoanBudget,
    LoanAliasBudget,
    RegionConstraintBudget,
    ReborrowDepthBudget,
    LoanJoin,
    LoanLoopWidening,
}

/// One concrete carrier of a loan authority in the abstract state.
///
/// References normally travel in SSA permission values.  A reference-bearing
/// aggregate instead owns the authority at an exact typed payload location;
/// keeping both forms in the same set prevents an object move/copy from
/// manufacturing or losing an alias behind the verifier's back.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbstractLoanAuthority {
    Value(VirValueId),
    Stored {
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    },
}

impl AbstractLoanAuthority {
    #[must_use]
    pub const fn value(value: VirValueId) -> Self {
        Self::Value(value)
    }

    #[must_use]
    pub const fn stored(allocation: AbstractAllocationId, payload: ResourcePayloadKey) -> Self {
        Self::Stored {
            allocation,
            payload,
        }
    }
}

/// Canonical abstract loan fact stored atomically with all resource facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbstractLoan {
    pub(super) provenance: AbstractProvenance,
    pub(super) range: ByteRange,
    pub(super) footprint: Option<MemoryFootprint>,
    pub(super) kind: VirLoanKind,
    pub(super) region: VirBorrowRegionId,
    pub(super) parent: Option<VirLoanId>,
    pub(super) activity: LoanActivity,
    pub(super) authorities: BTreeSet<AbstractLoanAuthority>,
}

impl AbstractLoan {
    #[must_use]
    pub const fn new(
        provenance: AbstractProvenance,
        range: ByteRange,
        kind: VirLoanKind,
        region: VirBorrowRegionId,
        parent: Option<VirLoanId>,
        activity: LoanActivity,
    ) -> Self {
        Self {
            provenance,
            range,
            footprint: None,
            kind,
            region,
            parent,
            activity,
            authorities: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn provenance(&self) -> AbstractProvenance {
        self.provenance
    }

    #[must_use]
    pub const fn range(&self) -> ByteRange {
        self.range
    }

    pub const fn footprint(&self) -> Option<MemoryFootprint> {
        self.footprint
    }
    pub const fn with_footprint(mut self, footprint: Option<MemoryFootprint>) -> Self {
        self.footprint = footprint;
        self
    }
    pub fn actual_range(&self) -> AbstractByteRange {
        self.footprint
            .map_or(AbstractByteRange::Unknown, |f| f.range)
    }

    #[must_use]
    pub const fn kind(&self) -> VirLoanKind {
        self.kind
    }

    #[must_use]
    pub const fn region(&self) -> VirBorrowRegionId {
        self.region
    }

    #[must_use]
    pub const fn parent(&self) -> Option<VirLoanId> {
        self.parent
    }

    #[must_use]
    pub const fn activity(&self) -> LoanActivity {
        self.activity
    }

    pub fn set_activity(&mut self, activity: LoanActivity) {
        self.activity = activity;
    }

    #[must_use]
    pub const fn authorities(&self) -> &BTreeSet<AbstractLoanAuthority> {
        &self.authorities
    }

    #[must_use]
    pub fn with_authority(mut self, authority: VirValueId) -> Self {
        self.authorities
            .insert(AbstractLoanAuthority::value(authority));
        self
    }

    pub fn add_authority(&mut self, authority: VirValueId) {
        self.authorities
            .insert(AbstractLoanAuthority::value(authority));
    }

    pub fn remove_authority(&mut self, authority: VirValueId) -> bool {
        self.authorities
            .remove(&AbstractLoanAuthority::value(authority))
    }

    pub fn move_authority(&mut self, source: VirValueId, result: VirValueId) -> bool {
        if !self
            .authorities
            .remove(&AbstractLoanAuthority::value(source))
        {
            return false;
        }
        self.authorities
            .insert(AbstractLoanAuthority::value(result));
        true
    }

    #[must_use]
    pub fn has_value_authority(&self, authority: VirValueId) -> bool {
        self.authorities
            .contains(&AbstractLoanAuthority::value(authority))
    }

    pub fn move_authority_to_storage(
        &mut self,
        source: VirValueId,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) -> bool {
        if !self
            .authorities
            .remove(&AbstractLoanAuthority::value(source))
        {
            return false;
        }
        self.authorities
            .insert(AbstractLoanAuthority::stored(allocation, payload));
        true
    }

    pub fn move_authority_from_storage(
        &mut self,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
        result: VirValueId,
    ) -> bool {
        if !self
            .authorities
            .remove(&AbstractLoanAuthority::stored(allocation, payload))
        {
            return false;
        }
        self.authorities
            .insert(AbstractLoanAuthority::value(result));
        true
    }

    pub fn add_stored_authority(
        &mut self,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) {
        self.authorities
            .insert(AbstractLoanAuthority::stored(allocation, payload));
    }

    pub fn remove_stored_authority(
        &mut self,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) -> bool {
        self.authorities
            .remove(&AbstractLoanAuthority::stored(allocation, payload))
    }

    pub fn move_stored_authority(
        &mut self,
        source_allocation: AbstractAllocationId,
        source_payload: ResourcePayloadKey,
        destination_allocation: AbstractAllocationId,
        destination_payload: ResourcePayloadKey,
    ) -> bool {
        if !self.authorities.remove(&AbstractLoanAuthority::stored(
            source_allocation,
            source_payload,
        )) {
            return false;
        }
        self.authorities.insert(AbstractLoanAuthority::stored(
            destination_allocation,
            destination_payload,
        ));
        true
    }

    pub(super) fn join(&self, other: &Self, loan: VirLoanId) -> Result<Self, ResourceJoinError> {
        if self.range != other.range
            || self.kind != other.kind
            || self.region != other.region
            || self.parent != other.parent
        {
            return Err(ResourceJoinError::LoanMetadataMismatch { loan });
        }
        let mut authorities = self.authorities.clone();
        authorities.extend(other.authorities.iter().copied());
        Ok(Self {
            provenance: self.provenance.join(other.provenance),
            footprint: match (self.footprint, other.footprint) {
                (Some(a), Some(b)) => a.join(b),
                _ => None,
            },
            activity: self.activity.join(other.activity),
            authorities,
            ..self.clone()
        })
    }

    pub(super) fn join_absent(&self) -> Self {
        let mut joined = self.clone();
        if !matches!(joined.activity, LoanActivity::Ended) {
            joined.activity = LoanActivity::MaybeActive;
        }
        joined
    }

    pub(in crate::verifier) fn project_cfg_edge(&self, remapper: &ExpressionRemapper) -> Self {
        let renames = &remapper.roots;
        let authorities = self
            .authorities
            .iter()
            .map(|authority| match authority {
                AbstractLoanAuthority::Value(value) => {
                    AbstractLoanAuthority::Value(renames.get(value).copied().unwrap_or(*value))
                }
                AbstractLoanAuthority::Stored { .. } => *authority,
            })
            .collect();
        Self {
            authorities,
            footprint: self.footprint.map(|f| f.project(remapper)),
            ..self.clone()
        }
    }
}
