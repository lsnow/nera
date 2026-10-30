//! Linear, non-recursive predicate instances. Addresses never identify holders.
//!
//! The initial internal calculus seals whole allocations with exclusive owner
//! authority. Typed owner fields retain sealed tokens; recursive bodies are gated.
use super::*;
use crate::VirPredicateId;
mod borrow;
mod call;
mod cleanup;
mod handoff;
mod join;
mod logic;
mod loop_parameters;
mod loops;
pub(in crate::verifier) use loop_parameters::LoopPredicateParameters;
mod fields;
mod matching;
mod memory_observation;
mod observation_frame;
mod parameter_join;
mod representation;
mod storage;
pub use call::{
    PredicateCallBinding, PredicateCallFrame, PredicateScalarCallBinding, enter_predicate_call,
    enter_predicate_call_with_scalars,
};

pub const MAX_PREDICATE_INSTANCES: usize = 256;
pub const MAX_PREDICATE_RESOURCES: usize = 32;
const MAX_PREDICATE_LOCAL_ALIASES: usize = 256;

/// A ghost carrier, distinct from all runtime pointer/value identities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PredicateHolder(pub u32);

/// Pure operands used by the specification adapter; none denotes authority.
#[derive(Clone, Copy)]
pub(in crate::verifier) enum OpenedSpecOperand {
    Opened {
        action: u32,
        holder: u32,
        binder: u32,
    },
    Value(VirValueId),
    Word(u64),
    Bool(bool),
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::verifier) enum OpenedSpecComparison {
    Equal,
    Less,
    LessEqual,
}

pub(in crate::verifier) type OpenedSpecTerm =
    crate::predicate_logic::query::Term<OpenedSpecOperand>;

/// Declaration and witness names are qualified by their defining module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateDefinition {
    id: VirPredicateId,
    module: u32,
    resources: Vec<PredicateResourceShape>,
    scalar_constraints: Vec<PredicateScalarConstraint>,
    initialized_prefixes: Vec<(usize, HeapInitializationPrefix)>,
    logical_prefixes: Vec<crate::PredicateInitializedPrefix<VirMemoryAccess>>,
    logic: crate::predicate_logic::PredicateLogic<VirMemoryAccess>,
    logic_observations:
        BTreeMap<(u32, u64, VirMemoryAccess), crate::predicate_logic::LogicType<VirMemoryAccess>>,
    projected_witnesses: BTreeSet<u32>,
    resource_fields: Vec<Vec<crate::vir::PredicateResourceField>>,
}

/// A pure invariant over one stored u64 cell. The value is an existential
/// witness hidden by fold; bounds must be re-established after every update.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PredicateScalarConstraint {
    pub resource: usize,
    pub offset_bytes: u64,
    pub access: VirMemoryAccess,
    pub lower: u64,
    pub upper: u64,
}

/// A bounded non-recursive representation. Each entry owns a whole allocation;
/// initialized ranges need not cover uninitialized backing storage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateResourceShape {
    pub size_bytes: u64,
    pub initialized: Vec<ByteRange>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicateError {
    InvalidDefinition,
    Budget,
    PrivateRepresentation,
    HolderOccupied,
    MissingHolder,
    WrongDeclaration,
    AlreadyFolded,
    AlreadyUnfolded,
    InvalidBinding,
    MissingAuthority,
    AliasedAuthority,
    Borrowed,
    UnprovedRepresentation,
    OpenBoundary,
    OutstandingCleanup,
    UnsupportedStorage,
    InvalidEvidence,
}

impl fmt::Display for PredicateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "predicate resource transition failed: {self:?}")
    }
}
impl Error for PredicateError {}

impl PredicateDefinition {
    pub(in crate::verifier) fn from_vir(
        memory: &crate::VirMemorySchema,
        predicate: &crate::VirPredicate,
        module: u32,
    ) -> Result<Self, PredicateError> {
        let body = predicate
            .representation
            .as_ref()
            .ok_or(PredicateError::InvalidDefinition)?;
        if !body.has_valid_projected_witnesses() {
            return Err(PredicateError::InvalidDefinition);
        }
        let resources = body
            .resources
            .iter()
            .map(|r| {
                Ok(PredicateResourceShape {
                    size_bytes: memory
                        .object_shape(r.pointee)
                        .map_err(|_| PredicateError::InvalidDefinition)?
                        .size_bytes(),
                    initialized: r
                        .initialized
                        .iter()
                        .map(|(start, end)| {
                            ByteRange::new(*start, *end)
                                .map_err(|_| PredicateError::InvalidDefinition)
                        })
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, PredicateError>>()?;
        let mut definition = Self::new(predicate.id, module, resources)?.with_scalar_constraints(
            body.bounds
                .iter()
                .map(|b| {
                    let resource = body
                        .resources
                        .get(b.resource as usize)
                        .ok_or(PredicateError::InvalidDefinition)?;
                    let access =
                        crate::vir::predicate_word_access(memory, resource.pointee, b.offset)
                            .ok_or(PredicateError::InvalidDefinition)?;
                    Ok(PredicateScalarConstraint {
                        resource: b.resource as usize,
                        offset_bytes: b.offset,
                        access,
                        lower: b.lower,
                        upper: b.upper,
                    })
                })
                .collect::<Result<_, PredicateError>>()?,
        )?;
        for p in &body.prefixes {
            let crate::PredicatePrefixCount::Stored {
                offset: count_offset,
            } = &p.count
            else {
                definition.logical_prefixes.push(p.clone());
                continue;
            };
            let resource = body
                .resources
                .get(p.resource as usize)
                .ok_or(PredicateError::InvalidDefinition)?;
            let count_access =
                crate::vir::predicate_word_access(memory, resource.pointee, *count_offset)
                    .ok_or(PredicateError::InvalidDefinition)?;
            definition.initialized_prefixes.push((
                p.resource as usize,
                HeapInitializationPrefix {
                    array_offset: p.array_offset,
                    element: p.element,
                    length: p.length,
                    stride: p.stride,
                    count_offset: *count_offset,
                    count_access,
                },
            ));
        }
        crate::vir::validate_predicate_logic(memory, body)
            .map_err(|_| PredicateError::InvalidDefinition)?;
        for (index, resource) in body.resources.iter().enumerate() {
            for leaf in memory
                .object_shape(resource.pointee)
                .map_err(|_| PredicateError::InvalidDefinition)?
                .leaves()
            {
                let ty = match memory.kind(leaf.access().ty) {
                    Some(crate::VirMemoryTypeKind::Bool) => crate::predicate_logic::LogicType::Bool,
                    Some(crate::VirMemoryTypeKind::Integer(crate::VirIntegerType::U64)) => {
                        crate::predicate_logic::LogicType::U64
                    }
                    Some(crate::VirMemoryTypeKind::Integer(crate::VirIntegerType::Usize)) => {
                        crate::predicate_logic::LogicType::Usize
                    }
                    _ => continue,
                };
                definition.logic_observations.insert(
                    (index as u32, leaf.bytes().start_bytes(), leaf.access()),
                    ty,
                );
            }
        }
        definition.projected_witnesses = body
            .logic
            .existentials
            .iter()
            .enumerate()
            .filter(|(_, w)| body.witnesses.iter().any(|p| p.name == w.name))
            .map(|(i, _)| i as u32)
            .collect();
        definition.logic = body.logic.clone();
        definition.resource_fields = body
            .resources
            .iter()
            .map(|r| {
                crate::vir::predicate_resource_fields(memory, r.pointee)
                    .ok_or(PredicateError::InvalidDefinition)
            })
            .collect::<Result<_, _>>()?;
        for (shape, fields) in definition
            .resources
            .iter_mut()
            .zip(&definition.resource_fields)
        {
            for field in fields {
                let cell = ByteRange::from_start_and_length(field.offset, 8)
                    .map_err(|_| PredicateError::InvalidDefinition)?;
                if !shape.initialized.contains(&cell) {
                    shape.initialized.push(cell);
                }
            }
        }
        Ok(definition)
    }
    /// Validates the finite body independently of any instance or transfer.
    pub fn new(
        id: VirPredicateId,
        module: u32,
        resources: Vec<PredicateResourceShape>,
    ) -> Result<Self, PredicateError> {
        if resources.is_empty() || resources.len() > MAX_PREDICATE_RESOURCES {
            return Err(PredicateError::InvalidDefinition);
        }
        for resource in &resources {
            if resource.size_bytes == 0
                || resource.size_bytes > 4096
                || resource.initialized.len() > MAX_PREDICATE_RESOURCES
                || resource
                    .initialized
                    .iter()
                    .any(|r| r.start() >= r.end() || r.end() > resource.size_bytes)
            {
                return Err(PredicateError::InvalidDefinition);
            }
        }
        let resource_fields = vec![Vec::new(); resources.len()];
        Ok(Self {
            id,
            module,
            resources,
            scalar_constraints: Vec::new(),
            initialized_prefixes: Vec::new(),
            logical_prefixes: Vec::new(),
            logic: Default::default(),
            logic_observations: BTreeMap::new(),
            projected_witnesses: BTreeSet::new(),
            resource_fields,
        })
    }
    pub fn with_scalar_constraints(
        mut self,
        constraints: Vec<PredicateScalarConstraint>,
    ) -> Result<Self, PredicateError> {
        if constraints.len() > MAX_PREDICATE_RESOURCES
            || constraints.iter().any(|c| {
                c.lower > c.upper
                    || c.offset_bytes % 8 != 0
                    || c.offset_bytes.checked_add(8).is_none_or(|end| {
                        self.resources
                            .get(c.resource)
                            .is_none_or(|r| end > r.size_bytes)
                    })
            })
        {
            return Err(PredicateError::InvalidDefinition);
        }
        self.scalar_constraints = constraints;
        Ok(self)
    }
    pub const fn id(&self) -> VirPredicateId {
        self.id
    }
    pub const fn module(&self) -> u32 {
        self.module
    }
}

/// Runtime SSA bindings supplied to a fold. Neither pointer alone nor equality
/// with another pointer suffices: the exact owner permission is also required.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PredicateBinding {
    pub pointer: VirValueId,
    pub permission: VirValueId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SealedResource {
    allocation: AbstractAllocationId,
    // The unique SSA permission carrier, never inferred from equal addresses.
    // None preserves cleanup when a CFG edge does not carry the token.
    carrier: Option<VirValueId>,
    storage: Option<(AbstractAllocationId, ResourcePayloadKey)>,
    pointer: AbstractPointer,
    permission: AbstractPermission,
}

/// Private representation and existential allocation witnesses. An open
/// instance remains a cleanup obligation until refolded or explicitly retired.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateInstance {
    definition: PredicateDefinition,
    resources: Vec<SealedResource>,
    folded: bool,
    // Destruction retains the entire responsibility group until all members end.
    dropping: bool,
    // A suspended owner retains cleanup and restoration responsibility, not
    // access or a second copy of the borrowed representation.
    borrowed_by: BTreeMap<usize, crate::VirLoanId>,
    logic_scope: Option<crate::predicate_logic::InstanceScope>,
    logical_witnesses: Vec<logic::PredicateLogicValue>,
    logical_parameters: Vec<logic::PredicateLogicValue>,
    logical_facts: Vec<logic::PredicateConstraintFact>,
    logical_initialization: Vec<logic::LogicalInitialization>,
    // Current CFG value -> immutable observation, possibly from an earlier fold.
    logical_local_aliases: BTreeMap<VirValueId, logic::LocalSnapshot>,
    opening_action: Option<u32>,
}

impl PredicateInstance {
    pub const fn declaration(&self) -> VirPredicateId {
        self.definition.id
    }
    pub const fn is_folded(&self) -> bool {
        self.folded
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicateEffect {
    /// Match logical arguments against the actual instance before opening or retiring it.
    WithArguments {
        holder: PredicateHolder,
        arguments: crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
        effect: Box<PredicateEffect>,
    },
    FoldWithWitnesses {
        holder: PredicateHolder,
        bindings: Vec<PredicateBinding>,
        witnesses: crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
    },
    Fold {
        holder: PredicateHolder,
        bindings: Vec<PredicateBinding>,
    },
    Unfold {
        holder: PredicateHolder,
        outputs: Vec<PredicateBinding>,
    },
    UnfoldNamed {
        holder: PredicateHolder,
        bindings: Vec<PredicateBinding>,
        action: u32,
    },
    UnfoldInPlace {
        holder: PredicateHolder,
        bindings: Vec<PredicateBinding>,
    },
    Move {
        source: PredicateHolder,
        destination: PredicateHolder,
    },
    /// Retire an open instance only after its allocations have actually died.
    Finish { holder: PredicateHolder },
}

/// Canonical evidence can be replayed against the original state; its fields
/// are deliberately not interpreted as premises or trusted assumptions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateEvidence {
    pub definition: PredicateDefinition,
    pub module: u32,
    pub effect: PredicateEffect,
    pub output: ResourceState,
}

impl ResourceState {
    pub(in crate::verifier) fn predicate_references_loan(&self, id: crate::VirLoanId) -> bool {
        self.predicates.values().any(|p| {
            p.borrowed_by.values().any(|loan| *loan == id)
                || p.resources
                    .iter()
                    .any(|r| r.permission.authority() == PermissionAuthority::Loan(id))
        })
    }

    pub(in crate::verifier) fn predicate_references_allocation(
        &self,
        id: AbstractAllocationId,
    ) -> bool {
        self.predicates.values().any(|p| {
            p.resources
                .iter()
                .any(|r| r.allocation == id || r.storage.is_some_and(|(storage, _)| storage == id))
        })
    }

    pub(super) fn forget_predicate_local_alias(&mut self, id: VirValueId) {
        for instance in self.predicates.values_mut() {
            instance.logical_local_aliases.remove(&id);
        }
    }

    pub(super) fn project_predicates(
        &self,
        remapper: &ExpressionRemapper,
        renames: &[(VirValueId, VirValueId)],
    ) -> BTreeMap<PredicateHolder, PredicateInstance> {
        let mut result = self.predicates.clone();
        for instance in result.values_mut() {
            let mut aliases = BTreeMap::new();
            // A numeric input may be passed to several block parameters.
            // Inspect all actual edge arguments, including sources with no
            // known alias: an unknown source must defeat a conflicting fact.
            for (source, target) in renames {
                let original = instance.logical_local_aliases.get(source).copied();
                aliases
                    .entry(*target)
                    .and_modify(|known| {
                        if *known != original {
                            *known = None;
                        }
                    })
                    .or_insert(original);
                if aliases.len() > MAX_PREDICATE_LOCAL_ALIASES {
                    aliases.clear();
                    break;
                }
            }
            instance.logical_local_aliases = aliases
                .into_iter()
                .filter_map(|(target, original)| original.map(|original| (target, original)))
                .collect();
            for resource in &mut instance.resources {
                resource.pointer = remapper.pointer(resource.pointer);
                resource.carrier = resource
                    .carrier
                    .and_then(|id| remapper.roots.get(&id).copied());
            }
        }
        result
    }

    pub(super) fn inherit_predicate_scalar_aliases(&mut self, frame: &Self) {
        for (holder, instance) in &mut self.predicates {
            if let Some(before) = frame.predicates.get(holder) {
                instance.logical_local_aliases = before.logical_local_aliases.clone();
            }
        }
    }

    /// Transfer the sealed token along an ordinary runtime permission move.
    /// The destination remains consumed for reads, writes, loans and free.
    pub(in crate::verifier) fn move_predicate_carrier(
        &mut self,
        source: VirValueId,
        destination: VirValueId,
    ) -> Result<bool, PredicateError> {
        let matches: Vec<_> = self
            .predicates
            .iter()
            .flat_map(|(holder, instance)| {
                instance
                    .resources
                    .iter()
                    .enumerate()
                    .filter_map(move |(index, resource)| {
                        (resource.carrier == Some(source)).then_some((*holder, index))
                    })
            })
            .collect();
        let [(holder, index)] = matches.as_slice() else {
            return if matches.is_empty() {
                Ok(false)
            } else {
                Err(PredicateError::AliasedAuthority)
            };
        };
        let instance = &self.predicates[holder];
        if !instance.borrowed_by.is_empty() {
            return Err(PredicateError::Borrowed);
        }
        if !instance.folded {
            return Err(PredicateError::OpenBoundary);
        }
        if source == destination || self.values.contains_key(&destination) {
            return Err(PredicateError::HolderOccupied);
        }
        let permission = instance.resources[*index]
            .permission
            .with_availability(PermissionAvailability::Consumed);
        if self.value(source) != Some(&AbstractValue::Permission(permission)) {
            return Err(PredicateError::MissingAuthority);
        }
        self.predicates.get_mut(holder).unwrap().resources[*index].carrier = Some(destination);
        Ok(true)
    }

    fn carried_predicate_holder(
        &self,
        definition: &PredicateDefinition,
        bindings: &[PredicateBinding],
    ) -> Result<PredicateHolder, PredicateError> {
        self.predicates
            .iter()
            .find_map(|(holder, instance)| {
                (instance.definition == *definition
                    && instance.folded
                    && bindings.len() == instance.resources.len()
                    && bindings
                        .iter()
                        .zip(&instance.resources)
                        .all(|(b, r)| r.carrier == Some(b.permission)))
                .then_some(*holder)
            })
            .ok_or(PredicateError::MissingHolder)
    }

    fn unfold_carried_predicate(
        &mut self,
        definition: &PredicateDefinition,
        module: u32,
        destination: PredicateHolder,
        bindings: &[PredicateBinding],
    ) -> Result<(), PredicateError> {
        let source = self.carried_predicate_holder(definition, bindings)?;
        if source != destination && self.predicates.contains_key(&destination) {
            return Err(PredicateError::HolderOccupied);
        }
        self.predicate_unfold(definition, module, source, bindings, true)?;
        if source != destination {
            let instance = self.predicates.remove(&source).unwrap();
            self.predicates.insert(destination, instance);
        }
        Ok(())
    }

    /// Erase one CLOSED interface ownership token into a temporary owner ABI
    /// view. Used only inside canonical call/return transfer, never as a source
    /// unfold. The actual runtime owner and its unique carrier must match.
    pub(in crate::verifier) fn export_predicate_interface(
        &mut self,
        definition: &PredicateDefinition,
        bindings: &[PredicateBinding],
    ) -> Result<(), PredicateError> {
        let holder = self
            .predicates
            .iter()
            .find_map(|(holder, instance)| {
                (instance.definition == *definition
                    && instance.folded
                    && bindings.len() == instance.resources.len()
                    && bindings
                        .iter()
                        .zip(&instance.resources)
                        .all(|(b, r)| r.carrier == Some(b.permission)))
                .then_some(*holder)
            })
            .ok_or(PredicateError::MissingHolder)?;
        // Reuse the canonical unique-carrier, pointer and outstanding-loan checks.
        let mut next = self.clone();
        next.predicate_unfold(definition, definition.module, holder, bindings, true)?;
        next.predicates.remove(&holder);
        *self = next;
        Ok(())
    }

    /// Normalize an in-place postcondition to a temporary return ABI view.
    /// The closed carrier must still belong to the original parameter loan.
    /// Pointer values are observed in the current SSA state, never synthesized
    /// from the declaration or from an entry value discarded by a CFG edge.
    #[cfg(test)]
    pub(in crate::verifier) fn export_predicate_parameters(
        &mut self,
        definition: &PredicateDefinition,
        parameters: &[(crate::VirLoanId, VirValueId)],
    ) -> Result<(), PredicateError> {
        self.export_predicate_parameters_with_arguments(definition, parameters, &Default::default())
    }

    pub(in crate::verifier) fn export_predicate_parameters_with_arguments(
        &mut self,
        definition: &PredicateDefinition,
        parameters: &[(crate::VirLoanId, VirValueId)],
        arguments: &crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
    ) -> Result<(), PredicateError> {
        let (holder, _) = self
            .predicates
            .iter()
            .find(|(_, instance)| {
                instance.folded
                    && instance.definition == *definition
                    && instance.resources.len() == parameters.len()
                    && instance.resources.iter().zip(parameters).all(
                        |(resource, (loan, permission))| {
                            resource.carrier == Some(*permission)
                                && resource.permission.authority()
                                    == PermissionAuthority::Loan(*loan)
                        },
                    )
            })
            .ok_or(PredicateError::MissingHolder)?;
        self.check_predicate_arguments(definition, *holder, arguments)?;
        self.expose_closed_predicate_carriers(*holder)
    }

    /// Temporary observation/ABI view of an existing closed token. This is
    /// deliberately separate from source unfold: children and suspended parent
    /// loans remain unchanged, so ordinary access checks still apply.
    fn expose_closed_predicate_carriers(
        &mut self,
        holder: PredicateHolder,
    ) -> Result<(), PredicateError> {
        let instance = self
            .predicates
            .get(&holder)
            .ok_or(PredicateError::MissingHolder)?;
        if !instance.folded
            || !instance.borrowed_by.is_empty()
            || !self.predicate_representation_valid(instance)
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        let mut destinations = BTreeSet::new();
        for resource in &instance.resources {
            let permission = resource.carrier.ok_or(PredicateError::MissingAuthority)?;
            let pointer = self
                .values
                .iter()
                .find_map(|(id, value)| {
                    (*value == AbstractValue::Pointer(resource.pointer)).then_some(*id)
                })
                .ok_or(PredicateError::InvalidBinding)?;
            if resource.storage.is_some()
                || !destinations.insert(pointer)
                || !destinations.insert(permission)
                || self.value(permission)
                    != Some(&AbstractValue::Permission(
                        resource
                            .permission
                            .with_availability(PermissionAvailability::Consumed),
                    ))
                || matches!(resource.permission.authority(), PermissionAuthority::Loan(loan)
                    if self.loan(loan).is_none_or(|loan| !loan.has_value_authority(permission)))
            {
                return Err(PredicateError::InvalidBinding);
            }
        }
        // Validate the whole package before exposing any of its carriers.
        let resources = instance.resources.clone();
        for resource in resources {
            self.values.insert(
                resource.carrier.unwrap(),
                AbstractValue::Permission(resource.permission),
            );
        }
        self.predicates.remove(&holder);
        Ok(())
    }

    pub(in crate::verifier) fn available_predicate_holder(
        &self,
    ) -> Result<PredicateHolder, PredicateError> {
        (0..=MAX_PREDICATE_INSTANCES as u32)
            .map(|n| PredicateHolder(u32::MAX - n))
            .find(|h| !self.predicates.contains_key(h))
            .ok_or(PredicateError::Budget)
    }

    /// Import the minimum representation guaranteed by a checked requires or
    /// a closed callee's checked ensures. Callers must never invoke this from an
    /// unproved declaration or a failed/unknown call summary.
    #[cfg(test)]
    pub(in crate::verifier) fn import_predicate_interface(
        &mut self,
        definition: &PredicateDefinition,
        bindings: &[PredicateBinding],
        holder: PredicateHolder,
    ) -> Result<(), PredicateError> {
        self.import_predicate_interface_with_arguments(
            definition,
            bindings,
            holder,
            &Default::default(),
            false,
        )
    }

    // `entry` is supplied only by the fresh function-entry ABI adapter. Call
    // returns must use false: current addresses do not establish entry identity.
    pub(in crate::verifier) fn import_predicate_interface_with_arguments(
        &mut self,
        definition: &PredicateDefinition,
        bindings: &[PredicateBinding],
        holder: PredicateHolder,
        arguments: &crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
        entry: bool,
    ) -> Result<(), PredicateError> {
        if self.predicates.contains_key(&holder) {
            return Err(PredicateError::HolderOccupied);
        }
        if !arguments.values.is_empty() {
            return Err(PredicateError::InvalidBinding);
        }
        if bindings.len() != definition.resources.len() {
            return Err(PredicateError::InvalidBinding);
        }
        let mut candidate = self.clone();
        let mut allocations = Vec::new();
        for (binding, shape) in bindings.iter().zip(&definition.resources) {
            let Some(AbstractValue::Pointer(pointer)) = candidate.value(binding.pointer).copied()
            else {
                return Err(PredicateError::InvalidBinding);
            };
            let AbstractProvenance::Known(id) = pointer.provenance() else {
                return Err(PredicateError::InvalidBinding);
            };
            let allocation = candidate
                .allocations
                .get_mut(&id)
                .ok_or(PredicateError::MissingAuthority)?;
            for range in &shape.initialized {
                if allocation.initialization().classify(*range) != InitializationClass::Initialized
                {
                    allocation
                        .mark_initialized(*range)
                        .map_err(|_| PredicateError::UnprovedRepresentation)?;
                }
                allocation
                    .mark_valid(*range)
                    .map_err(|_| PredicateError::UnprovedRepresentation)?;
            }
            allocations.push(id);
        }
        for bound in &definition.scalar_constraints {
            let range = ByteRange::from_start_and_length(bound.offset_bytes, 8)
                .map_err(|_| PredicateError::InvalidDefinition)?;
            let allocation = candidate
                .allocations
                .get_mut(&allocations[bound.resource])
                .unwrap();
            if allocation.initialization().classify(range) != InitializationClass::Initialized {
                allocation
                    .mark_initialized(range)
                    .map_err(|_| PredicateError::UnprovedRepresentation)?;
            }
            allocation
                .mark_valid(range)
                .map_err(|_| PredicateError::UnprovedRepresentation)?;
        }
        candidate.assume_predicate_scalar_bounds(definition, &allocations)?;
        for (index, prefix) in &definition.initialized_prefixes {
            candidate
                .allocations
                .get_mut(&allocations[*index])
                .ok_or(PredicateError::InvalidBinding)?
                .certify_heap_prefix(*prefix);
        }
        if entry {
            // These are typed, initialized cells in a fresh function-entry
            // representation, not observations of a caller after a call. Give
            // them an entry coordinate before fold captures immutable binders.
            for (&(resource, offset, access), &ty) in &definition.logic_observations {
                use crate::predicate_logic::LogicType;
                let (width, unknown) = match ty {
                    LogicType::Bool => (1, AbstractValue::Bool(AbstractBool::Unknown)),
                    LogicType::U64 | LogicType::Usize => (
                        8,
                        AbstractValue::U64(U64Interval::new(0, u64::MAX).unwrap()),
                    ),
                    _ => return Err(PredicateError::InvalidDefinition),
                };
                let id = *allocations
                    .get(resource as usize)
                    .ok_or(PredicateError::InvalidDefinition)?;
                let range = ByteRange::from_start_and_length(offset, width)
                    .map_err(|_| PredicateError::InvalidDefinition)?;
                let allocation = candidate.allocations.get_mut(&id).unwrap();
                if allocation.liveness() != LivenessState::Live
                    || allocation.initialization().classify(range)
                        != InitializationClass::Initialized
                    || !allocation.valid_value_bytes().contains(range)
                {
                    // The catalog lists legal typed locations, including
                    // uninitialized fields that this contract never observes.
                    // Actual observations still check initialization at capture.
                    continue;
                }
                if allocation.scalar_content(range, access).is_none() {
                    allocation.record_scalar_content(range, access, unknown);
                }
            }
            for id in &allocations {
                candidate
                    .allocations
                    .get_mut(id)
                    .unwrap()
                    .seed_scalar_origins(*id);
            }
        }
        candidate.predicate_fold_impl(
            definition,
            definition.module,
            holder,
            bindings,
            arguments,
            true,
            None,
        )?;
        if !candidate.predicates[&holder]
            .logical_initialization
            .is_empty()
            && !candidate.predicate_representation_valid(&candidate.predicates[&holder])
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        *self = candidate;
        Ok(())
    }

    pub fn predicate_instances(&self) -> &BTreeMap<PredicateHolder, PredicateInstance> {
        &self.predicates
    }

    /// Every observable module/call boundary must restore open invariants.
    /// A boundary can transfer closed holders, but cannot silently discard one.
    pub fn check_predicate_boundary(
        &self,
        transferred: &[PredicateHolder],
    ) -> Result<(), PredicateError> {
        if self.predicates.values().any(|p| !p.borrowed_by.is_empty()) {
            return Err(PredicateError::Borrowed);
        }
        let selected: BTreeSet<_> = transferred.iter().copied().collect();
        if selected.len() != transferred.len()
            || selected.iter().any(|h| !self.predicates.contains_key(h))
        {
            return Err(PredicateError::InvalidBinding);
        }
        if self.predicates.values().any(|p| !p.folded) {
            return Err(PredicateError::OpenBoundary);
        }
        if self
            .predicates
            .values()
            .any(|p| !self.predicate_representation_valid(p))
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        if self.predicates.keys().any(|h| !selected.contains(h)) {
            return Err(PredicateError::OutstandingCleanup);
        }
        Ok(())
    }

    fn predicate_fold(
        &mut self,
        definition: &PredicateDefinition,
        module: u32,
        holder: PredicateHolder,
        bindings: &[PredicateBinding],
    ) -> Result<(), PredicateError> {
        self.predicate_fold_with_witnesses(
            definition,
            module,
            holder,
            bindings,
            &Default::default(),
        )
    }

    fn predicate_fold_with_witnesses(
        &mut self,
        definition: &PredicateDefinition,
        module: u32,
        holder: PredicateHolder,
        bindings: &[PredicateBinding],
        witnesses: &crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
    ) -> Result<(), PredicateError> {
        self.predicate_fold_impl(definition, module, holder, bindings, witnesses, false, None)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Keep boundary identities, state, evidence and shared budget explicit at the resource adapter"
    )]
    fn predicate_fold_impl(
        &mut self,
        definition: &PredicateDefinition,
        module: u32,
        holder: PredicateHolder,
        bindings: &[PredicateBinding],
        witnesses: &crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
        imported: bool,
        inherited: Option<&PredicateInstance>,
    ) -> Result<(), PredicateError> {
        if module != definition.module {
            return Err(PredicateError::PrivateRepresentation);
        }
        if let Some(old) = self.predicates.get(&holder) {
            if old.definition != *definition {
                return Err(PredicateError::WrongDeclaration);
            }
            if old.dropping {
                return Err(PredicateError::OutstandingCleanup);
            }
            if old.folded {
                return Err(PredicateError::AlreadyFolded);
            }
        } else if self.predicates.len() >= MAX_PREDICATE_INSTANCES {
            return Err(PredicateError::Budget);
        }
        if bindings.len() != definition.resources.len() {
            return Err(PredicateError::InvalidBinding);
        }
        let mut resources = Vec::new();
        let mut seen = BTreeSet::new();
        for (resource_index, (binding, shape)) in
            bindings.iter().zip(&definition.resources).enumerate()
        {
            let Some(AbstractValue::Pointer(pointer)) = self.value(binding.pointer).copied() else {
                return Err(PredicateError::InvalidBinding);
            };
            let Some(AbstractValue::Permission(permission)) =
                self.value(binding.permission).copied()
            else {
                return Err(PredicateError::MissingAuthority);
            };
            let AbstractProvenance::Known(id) = pointer.provenance() else {
                return Err(PredicateError::InvalidBinding);
            };
            let whole = ByteRange::new(0, shape.size_bytes)
                .map_err(|_| PredicateError::InvalidDefinition)?;
            let borrowed = match permission.authority() {
                PermissionAuthority::Loan(id)
                    if self.predicate_loan_alias(binding.permission, permission)
                        && permission.access() == AccessPermission::Write =>
                {
                    Some(id)
                }
                _ => None,
            };
            if !Self::stable_loop_value(AbstractValue::Pointer(pointer))
                || pointer.offset_bytes().exact_value() != Some(0)
                || permission.provenance() != pointer.provenance()
                || permission.range() != AbstractByteRange::Exact(whole)
                || permission.availability() != PermissionAvailability::Available
                || (permission.authority() != PermissionAuthority::Owner && borrowed.is_none())
                || permission.access() != AccessPermission::Write
                || (borrowed.is_none() && permission.free_capability() != FreeCapability::Yes)
            {
                return Err(PredicateError::MissingAuthority);
            }
            if !seen.insert(id) {
                return Err(PredicateError::AliasedAuthority);
            }
            if self.predicates.iter().any(|(h, p)| {
                *h != holder
                    && p.resources.iter().any(|r| {
                        r.allocation == id || r.storage.is_some_and(|(storage, _)| storage == id)
                    })
                    && !borrowed.is_some_and(|loan| {
                        self.predicate_handoff_ancestor(p, loan, definition, id)
                    })
            }) {
                return Err(PredicateError::AliasedAuthority);
            }
            let allocation = self
                .allocation(id)
                .ok_or(PredicateError::UnprovedRepresentation)?;
            if allocation.size_bytes() != shape.size_bytes
                || allocation.liveness() != LivenessState::Live
                || (borrowed.is_none() && allocation.ownership() != OwnershipState::Owned)
                || shape.initialized.iter().any(|r| {
                    allocation.initialization().classify(*r) != InitializationClass::Initialized
                        || !allocation.valid_value_bytes().contains(*r)
                })
            {
                return Err(PredicateError::UnprovedRepresentation);
            }
            // A stored alias of this allocation cannot supply a second owner.
            // Independent stored resources remain framed.
            self.predicate_fields_valid(definition, resource_index, id)?;
            if self.allocations.iter().any(|(storage, a)| {
                a.object_state()
                    .resource_payloads()
                    .values()
                    .any(|p| match p {
                        MovePathState::Moved => false,
                        MovePathState::Unknown => true,
                        MovePathState::Available(payload) => {
                            (*storage == id
                                && definition.resource_fields[resource_index].is_empty())
                                || matches!(
                                    payload.pointer().provenance(),
                                    AbstractProvenance::Unknown
                                )
                                || payload.pointer().provenance() == pointer.provenance()
                        }
                    })
            }) {
                return Err(PredicateError::UnsupportedStorage);
            }
            self.predicate_loans_compatible(
                definition,
                resource_index,
                pointer.provenance(),
                borrowed,
            )?;
            if self.values.iter().any(|(v, value)| *v != binding.permission && matches!(value,
                AbstractValue::Permission(p) if p.availability() != PermissionAvailability::Consumed
                    && (p.provenance() == pointer.provenance() || p.provenance() == AbstractProvenance::Unknown)
                    && !self.predicate_loan_alias(*v, *p)
                    && !(borrowed.is_some() && p.authority() == PermissionAuthority::Owner && p.provenance() == pointer.provenance()))) {
                return Err(PredicateError::AliasedAuthority);
            }
            resources.push(SealedResource {
                allocation: id,
                carrier: Some(binding.permission),
                storage: None,
                pointer,
                permission,
            });
        }
        for constraint in &definition.scalar_constraints {
            let resource = &resources[constraint.resource];
            let range = ByteRange::from_start_and_length(constraint.offset_bytes, 8)
                .map_err(|_| PredicateError::InvalidDefinition)?;
            let Some(AbstractValue::U64(value)) = self
                .allocation(resource.allocation)
                .and_then(|a| a.scalar_content(range, constraint.access))
            else {
                return Err(PredicateError::UnprovedRepresentation);
            };
            if value.lower() < constraint.lower || value.upper() > constraint.upper {
                return Err(PredicateError::UnprovedRepresentation);
            }
        }
        for (index, prefix) in &definition.initialized_prefixes {
            if !self
                .allocation(resources[*index].allocation)
                .is_some_and(|a| a.heap_prefix_valid(*prefix))
            {
                return Err(PredicateError::UnprovedRepresentation);
            }
        }
        if let Some(old) = self.predicates.get(&holder)
            && old
                .resources
                .iter()
                .map(|r| r.allocation)
                .collect::<Vec<_>>()
                != resources.iter().map(|r| r.allocation).collect::<Vec<_>>()
        {
            return Err(PredicateError::OutstandingCleanup);
        }
        // Refolding discharges the obligation opened by this instance. Equal
        // allocations do not make owner and loan capabilities interchangeable,
        // nor do they identify distinct loans. A scoped handoff must preserve
        // a separate restoration obligation; Fold cannot perform that handoff.
        if let Some(old) = self.predicates.get(&holder)
            && old
                .resources
                .iter()
                .zip(&resources)
                .any(|(old, new)| old.permission.authority() != new.permission.authority())
        {
            return Err(PredicateError::MissingAuthority);
        }
        let mut inherited_initialization = Vec::new();
        let captured = if let Some(instance) = inherited {
            if imported || instance.definition != *definition || instance.resources != resources {
                return Err(PredicateError::InvalidBinding);
            }
            let mut instance = instance.clone();
            let mut next = self.next_predicate_scope;
            logic::freshen_local_instance(&mut instance, &mut next)?;
            if !self.predicate_logic_valid(&instance) {
                return Err(PredicateError::UnprovedRepresentation);
            }
            self.next_predicate_scope = next;
            inherited_initialization = instance.logical_initialization;
            logic::CapturedPredicateLogic {
                scope: instance.logic_scope,
                witnesses: instance.logical_witnesses,
                parameters: instance.logical_parameters,
                local_aliases: instance.logical_local_aliases,
                facts: instance.logical_facts,
            }
        } else {
            self.capture_predicate_logic(definition, holder, &resources, witnesses, imported)?
        };
        let logical_initialization = self.establish_predicate_logical_prefixes(
            definition,
            &resources,
            &captured,
            imported,
            &inherited_initialization,
        )?;
        for (index, prefix) in &definition.initialized_prefixes {
            self.allocations
                .get_mut(&resources[*index].allocation)
                .unwrap()
                .certify_heap_prefix(*prefix);
        }
        for binding in bindings {
            let Some(AbstractValue::Permission(p)) = self.value_mut(binding.permission) else {
                unreachable!()
            };
            p.mark_consumed();
        }
        self.predicates.insert(
            holder,
            PredicateInstance {
                definition: definition.clone(),
                resources,
                folded: true,
                dropping: false,
                borrowed_by: BTreeMap::new(),
                logic_scope: captured.scope,
                logical_witnesses: captured.witnesses,
                logical_parameters: captured.parameters,
                logical_facts: captured.facts,
                logical_initialization,
                logical_local_aliases: captured.local_aliases,
                opening_action: None,
            },
        );
        Ok(())
    }

    fn predicate_unfold(
        &mut self,
        definition: &PredicateDefinition,
        module: u32,
        holder: PredicateHolder,
        outputs: &[PredicateBinding],
        in_place: bool,
    ) -> Result<(), PredicateError> {
        if module != definition.module {
            return Err(PredicateError::PrivateRepresentation);
        }
        let instance = self
            .predicates
            .get(&holder)
            .ok_or(PredicateError::MissingHolder)?;
        if instance.definition != *definition {
            return Err(PredicateError::WrongDeclaration);
        }
        if !instance.borrowed_by.is_empty() {
            return Err(PredicateError::Borrowed);
        }
        if !instance.folded {
            return Err(PredicateError::AlreadyUnfolded);
        }
        if outputs.len() != instance.resources.len() {
            return Err(PredicateError::InvalidBinding);
        }
        let opened_scope = instance
            .logic_scope
            .map(|mut scope| -> Result<_, PredicateError> {
                scope.opening = scope.opening.checked_add(1).ok_or(PredicateError::Budget)?;
                Ok(scope)
            })
            .transpose()?;
        let mut destinations = BTreeSet::new();
        for (binding, resource) in outputs.iter().zip(&instance.resources) {
            if resource.storage.is_some() {
                return Err(PredicateError::MissingAuthority);
            }
            // The legacy fresh-output calculus has no SSA loan-authority move.
            // Source and ABI adapters reopen the unique carrier in place.
            if !in_place
                && matches!(
                    resource.permission.authority(),
                    PermissionAuthority::Loan(_)
                )
            {
                return Err(PredicateError::InvalidBinding);
            }
            if in_place
                && (resource.carrier != Some(binding.permission)
                    || self.value(binding.pointer)
                        != Some(&AbstractValue::Pointer(resource.pointer))
                    || self.value(binding.permission)
                        != Some(&AbstractValue::Permission(
                            resource
                                .permission
                                .with_availability(PermissionAvailability::Consumed),
                        )))
            {
                return Err(PredicateError::InvalidBinding);
            }
            for id in [binding.pointer, binding.permission] {
                if !destinations.insert(id) || (!in_place && self.values.contains_key(&id)) {
                    return Err(PredicateError::HolderOccupied);
                }
            }
        }
        for (binding, resource) in outputs.iter().zip(instance.resources.clone()) {
            let allocation = self
                .allocation(resource.allocation)
                .ok_or(PredicateError::UnprovedRepresentation)?;
            if allocation.liveness() != LivenessState::Live
                || (resource.permission.authority() == PermissionAuthority::Owner
                    && allocation.ownership() != OwnershipState::Owned)
            {
                return Err(PredicateError::UnprovedRepresentation);
            }
            if self.loans.iter().any(|(id, l)| {
                resource.permission.authority() != PermissionAuthority::Loan(*id)
                    && l.activity() != LoanActivity::Ended
                    && !self.predicate_suspended_ancestor(
                        *id,
                        resource.permission.authority(),
                        definition,
                        resource.allocation,
                    )
                    && (l.provenance() == resource.pointer.provenance()
                        || l.provenance() == AbstractProvenance::Unknown)
            }) {
                return Err(PredicateError::Borrowed);
            }
            self.values
                .insert(binding.pointer, AbstractValue::Pointer(resource.pointer));
            self.values.insert(
                binding.permission,
                AbstractValue::Permission(resource.permission),
            );
        }
        if !self.predicate_representation_valid(&self.predicates[&holder]) {
            return Err(PredicateError::UnprovedRepresentation);
        }
        let instance = self.predicates.get_mut(&holder).unwrap();
        instance.folded = false;
        instance.opening_action = None;
        instance.logic_scope = opened_scope;
        for (resource, binding) in instance.resources.iter_mut().zip(outputs) {
            resource.carrier = Some(binding.permission);
        }
        Ok(())
    }
}

/// Atomic transfer: rejected operations leave the caller's state unchanged.
/// This is the same ResourceState used by instruction, CFG and loan transfer.
pub fn transfer_predicate(
    input: &ResourceState,
    definition: &PredicateDefinition,
    module: u32,
    effect: &PredicateEffect,
) -> Result<PredicateEvidence, PredicateError> {
    let mut output = input.clone();
    if !input.path_condition().is_reachable() {
        return Ok(PredicateEvidence {
            definition: definition.clone(),
            module,
            effect: effect.clone(),
            output,
        });
    }
    // Only one wrapper is admitted. Reject nesting before recursive replay.
    if let PredicateEffect::WithArguments {
        holder,
        arguments,
        effect,
    } = effect
    {
        let target = match effect.as_ref() {
            PredicateEffect::Unfold { holder, .. }
            | PredicateEffect::UnfoldInPlace { holder, .. }
            | PredicateEffect::UnfoldNamed { holder, .. }
            | PredicateEffect::Finish { holder } => holder,
            _ => return Err(PredicateError::InvalidBinding),
        };
        if target != holder {
            return Err(PredicateError::InvalidBinding);
        }
        let source = match effect.as_ref() {
            PredicateEffect::UnfoldInPlace { bindings, .. }
            | PredicateEffect::UnfoldNamed { bindings, .. } => {
                input.carried_predicate_holder(definition, bindings)?
            }
            _ => *holder,
        };
        input.check_predicate_arguments(definition, source, arguments)?;
        let inner = transfer_predicate(input, definition, module, effect)?;
        return Ok(PredicateEvidence {
            definition: definition.clone(),
            module,
            effect: PredicateEffect::WithArguments {
                holder: *holder,
                arguments: arguments.clone(),
                effect: effect.clone(),
            },
            output: inner.output,
        });
    }
    match effect {
        PredicateEffect::WithArguments { .. } => unreachable!(),
        PredicateEffect::FoldWithWitnesses {
            holder,
            bindings,
            witnesses,
        } => output
            .predicate_fold_with_witnesses(definition, module, *holder, bindings, witnesses)?,
        PredicateEffect::Fold { holder, bindings } => {
            output.predicate_fold(definition, module, *holder, bindings)?
        }
        PredicateEffect::Unfold { holder, outputs } => {
            output.predicate_unfold(definition, module, *holder, outputs, false)?
        }
        PredicateEffect::UnfoldNamed {
            holder,
            bindings,
            action,
        } => {
            output.unfold_carried_predicate(definition, module, *holder, bindings)?;
            output
                .predicates
                .get_mut(holder)
                .ok_or(PredicateError::MissingHolder)?
                .opening_action = Some(*action);
        }
        PredicateEffect::UnfoldInPlace { holder, bindings } => {
            output.unfold_carried_predicate(definition, module, *holder, bindings)?
        }
        PredicateEffect::Move {
            source,
            destination,
        } => {
            if output.predicates.contains_key(destination) {
                return Err(PredicateError::HolderOccupied);
            }
            let instance = output
                .predicates
                .get(source)
                .ok_or(PredicateError::MissingHolder)?;
            if instance.definition != *definition {
                return Err(PredicateError::WrongDeclaration);
            }
            if !instance.folded {
                return Err(PredicateError::OpenBoundary);
            }
            if !instance.borrowed_by.is_empty() {
                return Err(PredicateError::Borrowed);
            }
            let instance = output.predicates.remove(source).unwrap();
            output.predicates.insert(*destination, instance);
        }
        PredicateEffect::Finish { holder } => {
            if module != definition.module {
                return Err(PredicateError::PrivateRepresentation);
            }
            let instance = output
                .predicates
                .get(holder)
                .ok_or(PredicateError::MissingHolder)?;
            if instance.definition != *definition {
                return Err(PredicateError::WrongDeclaration);
            }
            let borrowed = instance
                .resources
                .iter()
                .all(|r| matches!(r.permission.authority(), PermissionAuthority::Loan(_)));
            if instance.folded
                || instance.dropping
                || if borrowed {
                    !output.predicate_representation_valid_for_release(instance, true)
                } else {
                    instance.resources.iter().any(|r| {
                        r.permission.authority() != PermissionAuthority::Owner
                            || output
                                .allocation(r.allocation)
                                .is_none_or(|a| a.liveness() != LivenessState::Dead)
                    })
                }
            {
                return Err(PredicateError::OutstandingCleanup);
            }
            output.predicates.remove(holder);
        }
    }
    Ok(PredicateEvidence {
        definition: definition.clone(),
        module,
        effect: effect.clone(),
        output,
    })
}

pub fn check_predicate_evidence(
    input: &ResourceState,
    evidence: &PredicateEvidence,
) -> Result<(), PredicateError> {
    let replay = transfer_predicate(
        input,
        &evidence.definition,
        evidence.module,
        &evidence.effect,
    )?;
    if replay == *evidence {
        Ok(())
    } else {
        Err(PredicateError::InvalidEvidence)
    }
}

#[cfg(test)]
mod tests;
