use super::*;

/// Function-analysis-local allocation slot (not a concrete execution instance).
///
/// Transfer assigns these identities; they are never reconstructed from a
/// runtime integer address. Reusing a slot must go through the fresh-instance
/// transition, which forgets every old alias and preserves outstanding owners.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbstractAllocationId {
    /// Identity introduced by an entry environment, contract or test fixture.
    External(u32),
    /// Identity of one allocation instruction in the current VIR function.
    VirAllocationSite(VirValueId),
    /// Identity of one function-local storage site. This namespace is
    /// deliberately disjoint from heap allocation sites even when the result
    /// value IDs are numerically equal.
    VirLocalStorageSite(VirValueId),
    /// Static slot for an existential resource produced by one call site.
    ///
    /// Distinct static call sites get distinct slots. Repeated execution at
    /// one site must use the fresh-instance transition, never blind replacement.
    ContractInstance { call_site: u64, resource: u32 },
    /// Fresh existential introduced by a closed body summary, not a contract slot.
    SummaryInstance { call_site: u64, resource: u32 },
    /// Symbolic owner stored in an ownership-bearing aggregate parameter.
    AbiEntryPayload {
        function: u32,
        parameter: u32,
        leaf: u32,
    },
    /// Existential owner produced in an ownership-bearing aggregate result.
    AbiCallPayload {
        call_site: u64,
        result: u32,
        leaf: u32,
    },
}

impl AbstractAllocationId {
    /// Creates an identity outside the local VIR allocation-site namespace.
    #[must_use]
    pub const fn new(raw: u32) -> Self {
        Self::External(raw)
    }

    #[must_use]
    pub const fn vir_allocation_site(value: VirValueId) -> Self {
        Self::VirAllocationSite(value)
    }

    #[must_use]
    pub const fn vir_local_storage_site(value: VirValueId) -> Self {
        Self::VirLocalStorageSite(value)
    }

    #[must_use]
    pub const fn contract_instance(call_site: u64, resource: u32) -> Self {
        Self::ContractInstance {
            call_site,
            resource,
        }
    }

    #[must_use]
    pub const fn abi_entry_payload(function: u32, parameter: u32, leaf: u32) -> Self {
        Self::AbiEntryPayload {
            function,
            parameter,
            leaf,
        }
    }

    #[must_use]
    pub const fn abi_call_payload(call_site: u64, result: u32, leaf: u32) -> Self {
        Self::AbiCallPayload {
            call_site,
            result,
            leaf,
        }
    }

    /// Returns the underlying external ID or VIR value ID.
    ///
    /// The namespace remains part of equality; equal raw values from different
    /// namespaces are deliberately distinct.
    #[must_use]
    pub const fn get(self) -> u32 {
        match self {
            Self::External(raw) => raw,
            Self::VirAllocationSite(value) => value.get(),
            Self::VirLocalStorageSite(value) => value.get(),
            Self::ContractInstance { resource, .. } => resource,
            Self::SummaryInstance { resource, .. } => resource,
            Self::AbiEntryPayload { leaf, .. } | Self::AbiCallPayload { leaf, .. } => leaf,
        }
    }

    pub(super) const fn same_identity(self, other: Self) -> bool {
        match (self, other) {
            (
                Self::SummaryInstance {
                    call_site: a,
                    resource: x,
                },
                Self::SummaryInstance {
                    call_site: b,
                    resource: y,
                },
            ) => a == b && x == y,
            (Self::External(left), Self::External(right)) => left == right,
            (Self::VirAllocationSite(left), Self::VirAllocationSite(right)) => {
                left.get() == right.get()
            }
            (Self::VirLocalStorageSite(left), Self::VirLocalStorageSite(right)) => {
                left.get() == right.get()
            }
            (
                Self::ContractInstance {
                    call_site: left_site,
                    resource: left_resource,
                },
                Self::ContractInstance {
                    call_site: right_site,
                    resource: right_resource,
                },
            ) => left_site == right_site && left_resource == right_resource,
            (
                Self::AbiEntryPayload {
                    function: left_function,
                    parameter: left_parameter,
                    leaf: left_leaf,
                },
                Self::AbiEntryPayload {
                    function: right_function,
                    parameter: right_parameter,
                    leaf: right_leaf,
                },
            ) => {
                left_function == right_function
                    && left_parameter == right_parameter
                    && left_leaf == right_leaf
            }
            (
                Self::AbiCallPayload {
                    call_site: left_site,
                    result: left_result,
                    leaf: left_leaf,
                },
                Self::AbiCallPayload {
                    call_site: right_site,
                    result: right_result,
                    leaf: right_leaf,
                },
            ) => left_site == right_site && left_result == right_result && left_leaf == right_leaf,
            _ => false,
        }
    }
}

impl fmt::Display for AbstractAllocationId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::External(raw) => write!(formatter, "external:{raw}"),
            Self::SummaryInstance {
                call_site,
                resource,
            } => write!(formatter, "body-summary:{call_site}:{resource}"),
            Self::VirAllocationSite(value) => write!(formatter, "site:%{}", value.get()),
            Self::VirLocalStorageSite(value) => {
                write!(formatter, "local-storage:%{}", value.get())
            }
            Self::ContractInstance {
                call_site,
                resource,
            } => write!(formatter, "summary:{call_site}:{resource}"),
            Self::AbiEntryPayload {
                function,
                parameter,
                leaf,
            } => write!(formatter, "abi-entry:{function}:{parameter}:{leaf}"),
            Self::AbiCallPayload {
                call_site,
                result,
                leaf,
            } => write!(formatter, "abi-call:{call_site}:{result}:{leaf}"),
        }
    }
}

/// Liveness fact known at one program point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LivenessState {
    Live,
    Dead,
    MaybeLive,
}

impl LivenessState {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Live, Self::Live) | (Self::Dead, Self::Dead)
        ) {
            self
        } else {
            Self::MaybeLive
        }
    }
}

/// Whether this abstract state definitely holds the allocation's free authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OwnershipState {
    Owned,
    Unowned,
    MaybeOwned,
}

impl OwnershipState {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Owned, Self::Owned) | (Self::Unowned, Self::Unowned)
        ) {
            self
        } else {
            Self::MaybeOwned
        }
    }
}

/// Classification of one complete byte range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InitializationClass {
    Initialized,
    Uninitialized,
    MaybeInitialized,
}

/// Definite initialized and definite uninitialized byte facts.
///
/// Bytes in neither set are unknown. The sets are always disjoint. Join uses
/// intersection for both sets, retaining only facts true on every path.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct InitializationState {
    initialized: ByteSet,
    uninitialized: ByteSet,
}

impl InitializationState {
    #[must_use]
    pub fn all_uninitialized(size_bytes: u64) -> Self {
        Self {
            initialized: ByteSet::new(),
            uninitialized: ByteSet::single(ByteRange {
                start: 0,
                end: size_bytes,
            }),
        }
    }

    #[must_use]
    pub const fn unknown() -> Self {
        Self {
            initialized: ByteSet::new(),
            uninitialized: ByteSet::new(),
        }
    }

    #[must_use]
    pub const fn initialized(&self) -> &ByteSet {
        &self.initialized
    }

    #[must_use]
    pub const fn uninitialized(&self) -> &ByteSet {
        &self.uninitialized
    }

    #[must_use]
    pub fn classify(&self, range: ByteRange) -> InitializationClass {
        if self.initialized.contains(range) {
            InitializationClass::Initialized
        } else if self.uninitialized.contains(range) {
            InitializationClass::Uninitialized
        } else {
            InitializationClass::MaybeInitialized
        }
    }

    pub(super) fn mark_initialized(&mut self, range: ByteRange) {
        self.uninitialized.remove(range);
        self.initialized.insert(range);
    }

    fn mark_uninitialized(&mut self, range: ByteRange) {
        self.initialized.remove(range);
        self.uninitialized.insert(range);
    }

    fn forget(&mut self, range: ByteRange) {
        self.initialized.remove(range);
        self.uninitialized.remove(range);
    }

    fn forget_uninitialized(&mut self, range: ByteRange) {
        self.uninitialized.remove(range);
    }

    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            initialized: self.initialized.intersection(&other.initialized),
            uninitialized: self.uninitialized.intersection(&other.uninitialized),
        }
    }
}

/// Exact location of one enum subobject inside an abstract allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObjectStateKey {
    offset_bytes: u64,
    access: VirMemoryAccess,
}

/// Allocation-relative identity of one canonical resource leaf.
///
/// The physical byte offset makes the identity stable when the same leaf is
/// reached through a whole-object shape or through a projected field place.
/// `access` prevents overlapping enum representations with different pointer
/// types from being confused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResourcePayloadKey {
    offset_bytes: u64,
    access: VirMemoryAccess,
}

impl ResourcePayloadKey {
    #[must_use]
    pub const fn new(offset_bytes: u64, access: VirMemoryAccess) -> Self {
        Self {
            offset_bytes,
            access,
        }
    }

    #[must_use]
    pub const fn offset_bytes(self) -> u64 {
        self.offset_bytes
    }

    #[must_use]
    pub const fn access(self) -> VirMemoryAccess {
        self.access
    }
}

/// Unforgeable logical value stored in one `Own<T>` memory leaf.
///
/// Pointer and permission facts form one atomic payload. They are never joined
/// independently because doing so could synthesize an owner that occurred on
/// no concrete path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypedResourcePayload {
    pub(super) pointer: AbstractPointer,
    pub(super) permission: AbstractPermission,
}

impl TypedResourcePayload {
    #[must_use]
    pub const fn new(pointer: AbstractPointer, permission: AbstractPermission) -> Self {
        Self {
            pointer,
            permission,
        }
    }

    #[must_use]
    pub const fn pointer(&self) -> AbstractPointer {
        self.pointer
    }

    #[must_use]
    pub const fn permission(&self) -> AbstractPermission {
        self.permission
    }
}

/// Availability of one canonical resource move path.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MovePathState {
    Available(Box<TypedResourcePayload>),
    Moved,
    Unknown,
}

impl MovePathState {
    #[must_use]
    pub fn available(payload: TypedResourcePayload) -> Self {
        Self::Available(Box::new(payload))
    }

    /// Atomic least upper bound. In particular, payload axes are not mixed.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Available(left), Self::Available(right)) if left == right => {
                Self::Available(left.clone())
            }
            (Self::Moved, Self::Moved) => Self::Moved,
            _ => Self::Unknown,
        }
    }
}

impl ObjectStateKey {
    #[must_use]
    pub const fn new(offset_bytes: u64, access: VirMemoryAccess) -> Self {
        Self {
            offset_bytes,
            access,
        }
    }

    #[must_use]
    pub const fn offset_bytes(self) -> u64 {
        self.offset_bytes
    }

    #[must_use]
    pub const fn access(self) -> VirMemoryAccess {
        self.access
    }
}

/// Path-sensitive knowledge of an enum subobject's active representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ActiveVariantState {
    Exact(VirVariantId),
    Alternatives(BTreeSet<VirVariantId>),
    Unknown,
}

impl ActiveVariantState {
    #[must_use]
    pub fn alternatives(&self) -> Option<BTreeSet<VirVariantId>> {
        match self {
            Self::Exact(variant) => Some(BTreeSet::from([*variant])),
            Self::Alternatives(variants) => Some(variants.clone()),
            Self::Unknown => None,
        }
    }

    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let (Some(mut variants), Some(other)) = (self.alternatives(), other.alternatives()) else {
            return Self::Unknown;
        };
        variants.extend(other);
        if variants.len() > VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES {
            Self::Unknown
        } else if variants.len() == 1 {
            Self::Exact(*variants.first().expect("one active variant"))
        } else {
            Self::Alternatives(variants)
        }
    }
}

/// Exact enum facts for subobjects whose allocation-relative address is known.
/// Missing entries have `Unknown` state.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ObjectState {
    pub(super) active_variants: BTreeMap<ObjectStateKey, ActiveVariantState>,
    pub(super) resource_payloads: BTreeMap<ResourcePayloadKey, MovePathState>,
    pub(super) precision_lost: bool,
}

impl ObjectState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            active_variants: BTreeMap::new(),
            resource_payloads: BTreeMap::new(),
            precision_lost: false,
        }
    }

    #[must_use]
    pub const fn active_variants(&self) -> &BTreeMap<ObjectStateKey, ActiveVariantState> {
        &self.active_variants
    }

    #[must_use]
    pub const fn resource_payloads(&self) -> &BTreeMap<ResourcePayloadKey, MovePathState> {
        &self.resource_payloads
    }

    #[must_use]
    pub const fn is_precise(&self) -> bool {
        !self.precision_lost
    }

    #[must_use]
    pub fn active_variant(&self, key: ObjectStateKey) -> ActiveVariantState {
        self.active_variants
            .get(&key)
            .cloned()
            .unwrap_or(ActiveVariantState::Unknown)
    }

    /// Records an exact fact. `false` means the fixed precision budget was
    /// exhausted and the requested subobject remains unknown.
    pub fn set_active_variant(&mut self, key: ObjectStateKey, state: ActiveVariantState) -> bool {
        if !self.active_variants.contains_key(&key)
            && self.active_variants.len() >= VERIFIER_OBJECT_STATE_MAX_ENTRIES
        {
            self.precision_lost = true;
            return false;
        }
        self.active_variants.insert(key, state);
        true
    }

    #[must_use]
    pub fn resource_payload(&self, key: ResourcePayloadKey) -> MovePathState {
        self.resource_payloads
            .get(&key)
            .cloned()
            .unwrap_or(MovePathState::Unknown)
    }

    /// Records one move path. `false` means the fixed precision budget was
    /// exhausted and the path remains conservatively unknown.
    pub fn set_resource_payload(&mut self, key: ResourcePayloadKey, state: MovePathState) -> bool {
        if !self.resource_payloads.contains_key(&key)
            && self.resource_payloads.len() >= VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES
        {
            self.precision_lost = true;
            return false;
        }
        self.resource_payloads.insert(key, state);
        true
    }

    pub fn forget_range(&mut self, range: ByteRange) {
        for (key, state) in &mut self.active_variants {
            if range.contains(ByteRange {
                start: key.offset_bytes,
                end: key.offset_bytes.saturating_add(1),
            }) {
                *state = ActiveVariantState::Unknown;
            }
        }
        for (key, state) in &mut self.resource_payloads {
            if range.contains(ByteRange {
                start: key.offset_bytes,
                end: key.offset_bytes.saturating_add(1),
            }) {
                *state = MovePathState::Unknown;
            }
        }
    }

    pub fn mark_resource_paths_moved(&mut self, range: ByteRange) {
        for (key, state) in &mut self.resource_payloads {
            if range.contains(ByteRange {
                start: key.offset_bytes,
                end: key.offset_bytes.saturating_add(1),
            }) {
                *state = MovePathState::Moved;
            }
        }
    }

    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let mut joined = Self::new();
        joined.precision_lost = self.precision_lost || other.precision_lost;
        for (key, left) in &self.active_variants {
            let Some(right) = other.active_variants.get(key) else {
                continue;
            };
            let state = left.join(right);
            let inserted = joined.set_active_variant(*key, state);
            debug_assert!(inserted, "join cannot exceed either input's entry budget");
        }
        let resource_keys = self
            .resource_payloads
            .keys()
            .chain(other.resource_payloads.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        for key in resource_keys {
            let left = self.resource_payload(key);
            let right = other.resource_payload(key);
            let inserted = joined.set_resource_payload(key, left.join(&right));
            debug_assert!(inserted, "join cannot exceed the resource payload budget");
        }
        joined
    }

    pub(in crate::verifier) fn project_cfg_edge(&self, remapper: &ExpressionRemapper) -> Self {
        let mut projected = self.clone();
        for state in projected.resource_payloads.values_mut() {
            if let MovePathState::Available(payload) = state {
                **payload = TypedResourcePayload::new(
                    remapper.pointer(payload.pointer()),
                    remapper.permission(payload.permission()),
                );
            }
        }
        projected
    }
}

/// An allocation's immutable shape and path-sensitive resource facts.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AbstractAllocation {
    pub(super) scalar_contents: super::contents::ScalarContents,
    pub(super) region: Option<VirRegionId>,
    pub(super) size_bytes: u64,
    pub(super) alignment: GuaranteedAlignment,
    pub(super) liveness: LivenessState,
    pub(super) ownership: OwnershipState,
    pub(super) initialization: InitializationState,
    pub(super) valid_value_bytes: ByteSet,
    pub(super) object_state: ObjectState,
    pub(super) initialization_prefixes: InitializationPrefixes,
}

impl AbstractAllocation {
    pub fn new(
        region: VirRegionId,
        size_bytes: u64,
        alignment: u64,
    ) -> Result<Self, AbstractAllocationError> {
        Self::with_region(Some(region), size_bytes, alignment, OwnershipState::Owned)
    }

    /// Creates function-frame storage. It has no heap/contract region and no
    /// authority to outlive or free the current invocation.
    pub fn new_local(size_bytes: u64, alignment: u64) -> Result<Self, AbstractAllocationError> {
        Self::with_region(None, size_bytes, alignment, OwnershipState::Unowned)
    }

    fn with_region(
        region: Option<VirRegionId>,
        size_bytes: u64,
        alignment: u64,
        ownership: OwnershipState,
    ) -> Result<Self, AbstractAllocationError> {
        if size_bytes == 0 {
            return Err(AbstractAllocationError::ZeroSize);
        }
        let alignment = GuaranteedAlignment::new(alignment)
            .map_err(|error| AbstractAllocationError::InvalidAlignment(error.bytes))?;
        Ok(Self {
            region,
            scalar_contents: Default::default(),
            size_bytes,
            alignment,
            liveness: LivenessState::Live,
            ownership,
            initialization: InitializationState::all_uninitialized(size_bytes),
            valid_value_bytes: ByteSet::new(),
            object_state: ObjectState::new(),
            initialization_prefixes: InitializationPrefixes::default(),
        })
    }

    #[must_use]
    pub const fn region(&self) -> Option<VirRegionId> {
        self.region
    }

    #[must_use]
    pub const fn size_bytes(&self) -> u64 {
        self.size_bytes
    }

    #[must_use]
    pub const fn alignment(&self) -> GuaranteedAlignment {
        self.alignment
    }

    #[must_use]
    pub const fn liveness(&self) -> LivenessState {
        self.liveness
    }

    #[must_use]
    pub const fn ownership(&self) -> OwnershipState {
        self.ownership
    }

    #[must_use]
    pub const fn initialization(&self) -> &InitializationState {
        &self.initialization
    }

    #[must_use]
    pub const fn valid_value_bytes(&self) -> &ByteSet {
        &self.valid_value_bytes
    }

    #[must_use]
    pub const fn object_state(&self) -> &ObjectState {
        &self.object_state
    }

    pub fn mark_dead(&mut self) {
        self.scalar_contents.clear();
        self.liveness = LivenessState::Dead;
        self.ownership = OwnershipState::Unowned;
    }

    pub fn set_liveness(&mut self, liveness: LivenessState) {
        if liveness != LivenessState::Live {
            self.scalar_contents.clear();
        }
        self.liveness = liveness;
    }

    pub fn set_ownership(&mut self, ownership: OwnershipState) {
        self.ownership = ownership;
    }

    pub fn mark_initialized(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.scalar_contents.forget(range);
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.initialization.mark_initialized(range);
        Ok(())
    }

    pub fn mark_valid(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.valid_value_bytes.insert(range);
        Ok(())
    }

    pub fn mark_uninitialized(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.scalar_contents.forget(range);
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.initialization.mark_uninitialized(range);
        self.valid_value_bytes.remove(range);
        self.object_state.forget_range(range);
        self.object_state.mark_resource_paths_moved(range);
        Ok(())
    }

    pub fn forget_initialization(
        &mut self,
        range: ByteRange,
    ) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.scalar_contents.forget(range);
        self.initialization_prefixes.invalidate(range);
        self.initialization.forget(range);
        self.valid_value_bytes.remove(range);
        self.object_state.forget_range(range);
        Ok(())
    }

    pub fn forget_validity(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.scalar_contents.forget(range);
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.valid_value_bytes.remove(range);
        Ok(())
    }

    #[must_use]
    pub fn active_variant(&self, key: ObjectStateKey) -> ActiveVariantState {
        self.object_state.active_variant(key)
    }

    pub fn set_active_variant(
        &mut self,
        key: ObjectStateKey,
        state: ActiveVariantState,
    ) -> Result<bool, AbstractAllocationError> {
        self.scalar_contents.clear();
        let range = ByteRange::from_start_and_length(key.offset_bytes(), 1).map_err(|_| {
            AbstractAllocationError::RangeOutOfBounds {
                range: ByteRange {
                    start: key.offset_bytes(),
                    end: u64::MAX,
                },
                size_bytes: self.size_bytes,
            }
        })?;
        self.check_range(range)?;
        Ok(self.object_state.set_active_variant(key, state))
    }

    #[must_use]
    pub fn resource_payload(&self, key: ResourcePayloadKey) -> MovePathState {
        self.object_state.resource_payload(key)
    }

    pub fn set_resource_payload(
        &mut self,
        key: ResourcePayloadKey,
        state: MovePathState,
    ) -> Result<bool, AbstractAllocationError> {
        let range = ByteRange::from_start_and_length(key.offset_bytes(), 1).map_err(|_| {
            AbstractAllocationError::RangeOutOfBounds {
                range: ByteRange {
                    start: key.offset_bytes(),
                    end: u64::MAX,
                },
                size_bytes: self.size_bytes,
            }
        })?;
        self.check_range(range)?;
        Ok(self.object_state.set_resource_payload(key, state))
    }

    pub fn forget_object_state(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.scalar_contents.forget(range);
        self.check_range(range)?;
        self.object_state.forget_range(range);
        Ok(())
    }

    /// Drops only the fact that bytes are definitely uninitialized.
    ///
    /// A write through an interval pointer may initialize any byte in its
    /// access envelope while preserving already-initialized bytes.
    pub fn forget_uninitialized(
        &mut self,
        range: ByteRange,
    ) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.scalar_contents.forget(range);
        self.initialization_prefixes.invalidate(range);
        self.initialization.forget_uninitialized(range);
        Ok(())
    }

    fn check_range(&self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        if range.end() > self.size_bytes {
            return Err(AbstractAllocationError::RangeOutOfBounds {
                range,
                size_bytes: self.size_bytes,
            });
        }
        Ok(())
    }

    pub(super) fn join(
        &self,
        id: AbstractAllocationId,
        other: &Self,
    ) -> Result<Self, ResourceJoinError> {
        if self.region != other.region {
            return Err(ResourceJoinError::AllocationRegionMismatch { allocation: id });
        }
        if self.size_bytes != other.size_bytes {
            return Err(ResourceJoinError::AllocationSizeMismatch { allocation: id });
        }
        if self.alignment != other.alignment {
            return Err(ResourceJoinError::AllocationAlignmentMismatch { allocation: id });
        }
        Ok(Self {
            region: self.region,
            scalar_contents: self.scalar_contents.join(&other.scalar_contents),
            size_bytes: self.size_bytes,
            alignment: self.alignment,
            liveness: self.liveness.join(other.liveness),
            ownership: self.ownership.join(other.ownership),
            initialization: self.initialization.join(&other.initialization),
            valid_value_bytes: self
                .valid_value_bytes
                .intersection(&other.valid_value_bytes),
            object_state: self.object_state.join(&other.object_state),
            initialization_prefixes: self
                .initialization_prefixes
                .join(&other.initialization_prefixes),
        })
    }

    pub(in crate::verifier) fn project_cfg_edge(
        &self,
        remapper: &ExpressionRemapper,
        values: &BTreeMap<VirValueId, AbstractValue>,
    ) -> Self {
        let mut projected = self.clone();
        projected.reduce_initialization_prefixes(values);
        projected.object_state = self.object_state.project_cfg_edge(remapper);
        projected.initialization_prefixes = self.initialization_prefixes.project(remapper, values);
        projected
    }
}

/// Invalid facts used to construct or update an abstract allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbstractAllocationError {
    ZeroSize,
    InvalidAlignment(u64),
    RangeOutOfBounds { range: ByteRange, size_bytes: u64 },
}

impl fmt::Display for AbstractAllocationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroSize => formatter.write_str("abstract allocation size must be nonzero"),
            Self::InvalidAlignment(alignment) => write!(
                formatter,
                "abstract allocation alignment {alignment} is not a nonzero power of two"
            ),
            Self::RangeOutOfBounds { range, size_bytes } => write!(
                formatter,
                "byte range [{}, {}) is outside allocation of {size_bytes} bytes",
                range.start(),
                range.end()
            ),
        }
    }
}

impl Error for AbstractAllocationError {}
