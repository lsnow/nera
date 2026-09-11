//! Canonical logical-to-physical ABI classification for aggregate values.

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use super::{
    VirFunction, VirFunctionId, VirMemoryAccess, VirMemorySchema, VirMemoryTypeKind, VirMutability,
    VirPointerKind, VirSignature, VirType,
};
use crate::ValueCapability;
use crate::{BorrowAccess, BorrowProjection, BorrowResultRelation};

/// Largest object that may cross a function boundary as scalar leaves.
pub const VIR_AGGREGATE_ABI_MAX_DIRECT_BYTES: u64 = 16;
/// Largest canonical leaf count admitted by direct aggregate scalarization.
pub const VIR_AGGREGATE_ABI_MAX_DIRECT_LEAVES: usize = 2;

/// One scalar leaf retained in canonical byte/path order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirAbiLeaf {
    access: VirMemoryAccess,
    offset_bytes: u64,
    ty: VirType,
}

impl VirAbiLeaf {
    #[must_use]
    pub const fn access(self) -> VirMemoryAccess {
        self.access
    }

    #[must_use]
    pub const fn offset_bytes(self) -> u64 {
        self.offset_bytes
    }

    #[must_use]
    pub const fn ty(self) -> VirType {
        self.ty
    }
}

/// Canonical representation selected for one logical source value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VirAbiValue {
    /// Compatibility representation for hand-authored scalar VIR fixtures.
    Opaque(VirType),
    Unit {
        access: VirMemoryAccess,
    },
    Scalar {
        access: VirMemoryAccess,
        ty: VirType,
    },
    Pointer {
        access: VirMemoryAccess,
        pointee: VirMemoryAccess,
    },
    Slice {
        access: VirMemoryAccess,
        element: VirMemoryAccess,
    },
    DirectAggregate {
        access: VirMemoryAccess,
        leaves: Vec<VirAbiLeaf>,
    },
    IndirectAggregate {
        access: VirMemoryAccess,
    },
}

/// Mandatory ownership/borrow transfer implied by one logical interface value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirInterfaceTransfer {
    /// Compatibility marker for hand-authored physical-only VIR fixtures.
    Opaque,
    Ignore,
    Copy,
    Move,
    BorrowShared,
    BorrowMutable,
}

/// Storage convention required for a logical interface value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirInterfaceStorage {
    Opaque,
    None,
    Direct,
    Indirect,
}

/// Non-optional compiler type semantics attached to each ABI binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirInterfaceEffect {
    pub transfer: VirInterfaceTransfer,
    pub storage: VirInterfaceStorage,
}

impl VirAbiValue {
    #[must_use]
    pub const fn access(&self) -> Option<VirMemoryAccess> {
        match self {
            Self::Opaque(_) => None,
            Self::Unit { access }
            | Self::Scalar { access, .. }
            | Self::Pointer { access, .. }
            | Self::Slice { access, .. }
            | Self::DirectAggregate { access, .. }
            | Self::IndirectAggregate { access } => Some(*access),
        }
    }

    #[must_use]
    pub const fn is_indirect_aggregate(&self) -> bool {
        matches!(self, Self::IndirectAggregate { .. })
    }

    #[must_use]
    pub fn leaves(&self) -> &[VirAbiLeaf] {
        match self {
            Self::DirectAggregate { leaves, .. } => leaves,
            _ => &[],
        }
    }
}

/// Reversible physical slot assignment for one logical value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirAbiBinding {
    value: VirAbiValue,
    interface: VirInterfaceEffect,
    parameter_slots: Vec<u32>,
    result_slots: Vec<u32>,
}

impl VirAbiBinding {
    #[must_use]
    pub const fn value(&self) -> &VirAbiValue {
        &self.value
    }

    #[must_use]
    pub const fn interface(&self) -> VirInterfaceEffect {
        self.interface
    }

    #[must_use]
    pub fn parameter_slots(&self) -> &[u32] {
        &self.parameter_slots
    }

    #[must_use]
    pub fn result_slots(&self) -> &[u32] {
        &self.result_slots
    }
}

/// Logical parameter/result map paired with its exact physical VIR signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirAbiSignature {
    parameters: Vec<VirAbiBinding>,
    results: Vec<VirAbiBinding>,
    physical: VirSignature,
    borrow_result: Option<BorrowResultRelation>,
    borrow_result_alternatives: Vec<crate::BorrowResultAlternative>,
}

impl VirAbiSignature {
    /// Produces a compatibility identity map for existing hand-authored VIR.
    #[must_use]
    pub fn identity(physical: &VirSignature) -> Self {
        let parameters = physical
            .parameters
            .iter()
            .copied()
            .enumerate()
            .map(|(index, ty)| VirAbiBinding {
                value: VirAbiValue::Opaque(ty),
                interface: VirInterfaceEffect {
                    transfer: VirInterfaceTransfer::Opaque,
                    storage: VirInterfaceStorage::Opaque,
                },
                parameter_slots: vec![u32::try_from(index).expect("VIR slot index fits u32")],
                result_slots: Vec::new(),
            })
            .collect();
        let results = physical
            .results
            .iter()
            .copied()
            .enumerate()
            .map(|(index, ty)| VirAbiBinding {
                value: VirAbiValue::Opaque(ty),
                interface: VirInterfaceEffect {
                    transfer: VirInterfaceTransfer::Opaque,
                    storage: VirInterfaceStorage::Opaque,
                },
                parameter_slots: Vec::new(),
                result_slots: vec![u32::try_from(index).expect("VIR slot index fits u32")],
            })
            .collect();
        Self {
            parameters,
            results,
            physical: physical.clone(),
            borrow_result: None,
            borrow_result_alternatives: Vec::new(),
        }
    }

    /// Classifies source-level parameter/result accesses using only the
    /// canonical memory schema.
    pub fn classify(
        memory: &VirMemorySchema,
        parameter_accesses: &[VirMemoryAccess],
        result_accesses: &[VirMemoryAccess],
    ) -> Result<Self, VirAbiError> {
        memory
            .validate()
            .map_err(|_| abi_error(VirAbiErrorKind::InvalidMemorySchema))?;
        Self::classify_validated(memory, parameter_accesses, result_accesses)
    }

    /// Internal fast path for owners that already validated the exact schema.
    pub(crate) fn classify_validated(
        memory: &VirMemorySchema,
        parameter_accesses: &[VirMemoryAccess],
        result_accesses: &[VirMemoryAccess],
    ) -> Result<Self, VirAbiError> {
        let parameters = parameter_accesses
            .iter()
            .copied()
            .map(|access| classify_value(memory, access))
            .collect::<Result<Vec<_>, _>>()?;
        let results = result_accesses
            .iter()
            .copied()
            .map(|access| classify_value(memory, access))
            .collect::<Result<Vec<_>, _>>()?;
        build_signature(memory, parameters, results, BorrowSelection::Legacy)
    }

    /// Classifies slots using an explicit logical interface claim. This does
    /// not verify the body or grant authority to the claim.
    pub fn classify_with_borrow_result(
        memory: &VirMemorySchema,
        parameter_accesses: &[VirMemoryAccess],
        result_accesses: &[VirMemoryAccess],
        borrow_result: Option<BorrowResultRelation>,
    ) -> Result<Self, VirAbiError> {
        memory
            .validate()
            .map_err(|_| abi_error(VirAbiErrorKind::InvalidMemorySchema))?;
        Self::classify_with_borrow_result_validated(
            memory,
            parameter_accesses,
            result_accesses,
            borrow_result,
        )
    }

    /// Classifies slots using bounded guarded logical borrow-result claims.
    /// The claims remain untrusted until VIR validation and body verification.
    pub fn classify_with_borrow_results(
        memory: &VirMemorySchema,
        parameter_accesses: &[VirMemoryAccess],
        result_accesses: &[VirMemoryAccess],
        borrow_result: Option<BorrowResultRelation>,
        alternatives: Vec<crate::BorrowResultAlternative>,
    ) -> Result<Self, VirAbiError> {
        memory
            .validate()
            .map_err(|_| abi_error(VirAbiErrorKind::InvalidMemorySchema))?;
        Self::classify_with_borrow_results_validated(
            memory,
            parameter_accesses,
            result_accesses,
            borrow_result,
            alternatives,
        )
    }

    pub(crate) fn classify_with_borrow_result_validated(
        memory: &VirMemorySchema,
        parameter_accesses: &[VirMemoryAccess],
        result_accesses: &[VirMemoryAccess],
        borrow_result: Option<BorrowResultRelation>,
    ) -> Result<Self, VirAbiError> {
        let parameters = parameter_accesses
            .iter()
            .copied()
            .map(|a| classify_value(memory, a))
            .collect::<Result<Vec<_>, _>>()?;
        let results = result_accesses
            .iter()
            .copied()
            .map(|a| classify_value(memory, a))
            .collect::<Result<Vec<_>, _>>()?;
        build_signature(
            memory,
            parameters,
            results,
            BorrowSelection::Explicit {
                relation: borrow_result,
                alternatives: Vec::new(),
            },
        )
    }

    pub(crate) fn classify_with_borrow_results_validated(
        memory: &VirMemorySchema,
        parameter_accesses: &[VirMemoryAccess],
        result_accesses: &[VirMemoryAccess],
        borrow_result: Option<BorrowResultRelation>,
        alternatives: Vec<crate::BorrowResultAlternative>,
    ) -> Result<Self, VirAbiError> {
        let parameters = parameter_accesses
            .iter()
            .copied()
            .map(|access| classify_value(memory, access))
            .collect::<Result<Vec<_>, _>>()?;
        let results = result_accesses
            .iter()
            .copied()
            .map(|access| classify_value(memory, access))
            .collect::<Result<Vec<_>, _>>()?;
        build_signature(
            memory,
            parameters,
            results,
            BorrowSelection::Explicit {
                relation: borrow_result,
                alternatives,
            },
        )
    }

    #[must_use]
    pub const fn borrow_result(&self) -> Option<BorrowResultRelation> {
        self.borrow_result
    }

    #[must_use]
    pub fn borrow_result_alternatives(&self) -> &[crate::BorrowResultAlternative] {
        &self.borrow_result_alternatives
    }

    #[must_use]
    pub fn borrow_result_parameters(&self) -> BTreeSet<usize> {
        self.borrow_result
            .iter()
            .map(|relation| relation.parameter as usize)
            .chain(
                self.borrow_result_alternatives
                    .iter()
                    .map(|alternative| alternative.relation.parameter as usize),
            )
            .collect()
    }

    #[must_use]
    pub fn parameters(&self) -> &[VirAbiBinding] {
        &self.parameters
    }

    #[must_use]
    pub fn results(&self) -> &[VirAbiBinding] {
        &self.results
    }

    #[must_use]
    pub const fn physical(&self) -> &VirSignature {
        &self.physical
    }

    /// Compatibility accessor for the canonical logical relation. Consumers
    /// never rediscover a source by counting parameters or comparing types.
    pub fn borrow_result_parameter(&self) -> Option<usize> {
        self.borrow_result
            .map(|relation| relation.parameter as usize)
    }

    pub(crate) fn validate(&self, memory: &VirMemorySchema) -> Result<(), VirAbiError> {
        let opaque = self
            .parameters
            .iter()
            .chain(&self.results)
            .any(|binding| matches!(binding.value, VirAbiValue::Opaque(_)));
        if opaque {
            if self != &Self::identity(&self.physical) {
                return Err(abi_error(VirAbiErrorKind::NonCanonicalSlotMap));
            }
            return Ok(());
        }
        let parameter_accesses = self
            .parameters
            .iter()
            .map(|binding| {
                binding
                    .value
                    .access()
                    .ok_or_else(|| abi_error(VirAbiErrorKind::NonCanonicalSlotMap))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result_accesses = self
            .results
            .iter()
            .map(|binding| {
                binding
                    .value
                    .access()
                    .ok_or_else(|| abi_error(VirAbiErrorKind::NonCanonicalSlotMap))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let expected = Self::classify_with_borrow_results_validated(
            memory,
            &parameter_accesses,
            &result_accesses,
            self.borrow_result,
            self.borrow_result_alternatives.clone(),
        )?;
        if &expected != self {
            return Err(abi_error(VirAbiErrorKind::NonCanonicalSlotMap));
        }
        Ok(())
    }
}

/// One dense ABI entry owned by the runtime program.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirFunctionAbi {
    pub function: VirFunctionId,
    pub signature: VirAbiSignature,
}

/// Canonical ABI table for every runtime function.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct VirAbiEnvironment {
    pub functions: Vec<VirFunctionAbi>,
}

impl VirAbiEnvironment {
    #[must_use]
    pub fn identity(functions: &[VirFunction]) -> Self {
        Self {
            functions: functions
                .iter()
                .map(|function| VirFunctionAbi {
                    function: function.id,
                    signature: VirAbiSignature::identity(&function.signature),
                })
                .collect(),
        }
    }

    #[must_use]
    pub fn function(&self, function: VirFunctionId) -> Option<&VirFunctionAbi> {
        self.functions
            .get(function.get() as usize)
            .filter(|entry| entry.function == function)
    }

    pub(crate) fn validate(
        &self,
        memory: &VirMemorySchema,
        functions: &[VirFunction],
    ) -> Result<(), VirAbiError> {
        if self.functions.len() != functions.len() {
            return Err(abi_error(VirAbiErrorKind::FunctionTableMismatch));
        }
        let mut seen = BTreeSet::new();
        for (index, entry) in self.functions.iter().enumerate() {
            let expected = VirFunctionId::new(
                u32::try_from(index)
                    .map_err(|_| abi_error(VirAbiErrorKind::FunctionTableMismatch))?,
            );
            if entry.function != expected || !seen.insert(entry.function) {
                return Err(abi_error(VirAbiErrorKind::FunctionTableMismatch));
            }
            let function = functions
                .iter()
                .find(|function| function.id == entry.function)
                .ok_or_else(|| abi_error(VirAbiErrorKind::FunctionTableMismatch))?;
            entry.signature.validate(memory)?;
            if !super::borrow_interface::preserves_returned_view(function, &entry.signature) {
                return Err(abi_error(VirAbiErrorKind::NonCanonicalSlotMap));
            }
            if entry.signature.physical() != &function.signature {
                return Err(abi_error(VirAbiErrorKind::PhysicalSignatureMismatch {
                    function: entry.function,
                }));
            }
        }
        Ok(())
    }
}

fn classify_value(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
) -> Result<VirAbiValue, VirAbiError> {
    if !memory.resolves_access(access) {
        return Err(abi_error(VirAbiErrorKind::InvalidAccess(access)));
    }
    let kind = memory
        .kind(access.ty)
        .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidAccess(access)))?;
    match kind {
        VirMemoryTypeKind::Unit => Ok(VirAbiValue::Unit { access }),
        VirMemoryTypeKind::Bool => Ok(VirAbiValue::Scalar {
            access,
            ty: VirType::Bool,
        }),
        VirMemoryTypeKind::Integer(super::VirIntegerType::U64 | super::VirIntegerType::Usize) => {
            Ok(VirAbiValue::Scalar {
                access,
                ty: VirType::U64,
            })
        }
        VirMemoryTypeKind::Pointer { pointee, .. } => Ok(VirAbiValue::Pointer {
            access,
            pointee: memory
                .access(*pointee)
                .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidAccess(access)))?,
        }),
        VirMemoryTypeKind::Slice { element, .. } => Ok(VirAbiValue::Slice {
            access,
            element: memory
                .access(*element)
                .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidAccess(access)))?,
        }),
        VirMemoryTypeKind::Array { .. }
        | VirMemoryTypeKind::Tuple(_)
        | VirMemoryTypeKind::Struct { .. }
        | VirMemoryTypeKind::Enum { .. } => classify_aggregate(memory, access),
        VirMemoryTypeKind::Integer(_) | VirMemoryTypeKind::Never => {
            Err(abi_error(VirAbiErrorKind::UnsupportedType(access)))
        }
    }
}

fn classify_aggregate(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
) -> Result<VirAbiValue, VirAbiError> {
    let capabilities = memory
        .type_capabilities(access.ty)
        .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidAccess(access)))?;
    let pointer_free = capabilities.pointer_free_trivial();
    let owning = capabilities.value == ValueCapability::MoveOnly
        && capabilities.drop == crate::DropCapability::BuiltinDrop
        && capabilities.contains_resource
        && capabilities.size == crate::SizeCapability::Sized;
    if !pointer_free && !owning {
        return Err(abi_error(VirAbiErrorKind::OwnershipBearingAggregate(
            access,
        )));
    }
    let shape = memory
        .object_shape(access)
        .map_err(|_| abi_error(VirAbiErrorKind::UnsupportedType(access)))?;
    if shape.size_bytes() == 0 {
        return Err(abi_error(VirAbiErrorKind::UnsupportedType(access)));
    }
    // Resource-bearing values are never scalarized: the caller-owned buffer
    // is the stable carrier for the typed resource payload across the call.
    // Variant-dependent payload transfer needs a conditional interface
    // summary and therefore remains fail-closed until that summary exists.
    if owning {
        if !shape.variants().is_empty()
            || shape.resource_leaves().is_empty()
            || !shape
                .resource_leaves()
                .iter()
                .all(|leaf| leaf.kind() == VirPointerKind::Own)
        {
            return Err(abi_error(VirAbiErrorKind::OwnershipBearingAggregate(
                access,
            )));
        }
        return Ok(VirAbiValue::IndirectAggregate { access });
    }
    let mut leaves = Vec::with_capacity(shape.leaves().len());
    for leaf in shape.leaves() {
        let ty = match memory.kind(leaf.access().ty) {
            Some(VirMemoryTypeKind::Bool) => VirType::Bool,
            Some(VirMemoryTypeKind::Integer(
                super::VirIntegerType::U64 | super::VirIntegerType::Usize,
            )) => VirType::U64,
            Some(VirMemoryTypeKind::Unit) => continue,
            _ => {
                return Err(abi_error(VirAbiErrorKind::OwnershipBearingAggregate(
                    access,
                )));
            }
        };
        leaves.push(VirAbiLeaf {
            access: leaf.access(),
            offset_bytes: leaf.bytes().start_bytes(),
            ty,
        });
    }
    let direct = shape.variants().is_empty()
        && shape.size_bytes() <= VIR_AGGREGATE_ABI_MAX_DIRECT_BYTES
        && leaves.len() <= VIR_AGGREGATE_ABI_MAX_DIRECT_LEAVES;
    if direct {
        Ok(VirAbiValue::DirectAggregate { access, leaves })
    } else {
        Ok(VirAbiValue::IndirectAggregate { access })
    }
}

enum BorrowSelection {
    Legacy,
    Explicit {
        relation: Option<BorrowResultRelation>,
        alternatives: Vec<crate::BorrowResultAlternative>,
    },
}

fn build_signature(
    memory: &VirMemorySchema,
    parameter_values: Vec<VirAbiValue>,
    result_values: Vec<VirAbiValue>,
    selection: BorrowSelection,
) -> Result<VirAbiSignature, VirAbiError> {
    let mut physical_parameters = Vec::new();
    let mut physical_results = Vec::new();
    let mut parameters = parameter_values
        .into_iter()
        .map(|value| {
            let parameter_slots = append_parameter_slots(&value, &mut physical_parameters)?;
            let interface = interface_effect(memory, &value)?;
            Ok(VirAbiBinding {
                value,
                interface,
                parameter_slots,
                result_slots: Vec::new(),
            })
        })
        .collect::<Result<Vec<_>, VirAbiError>>()?;
    let mut results = result_values
        .into_iter()
        .map(|value| {
            let parameter_slots = if matches!(value, VirAbiValue::IndirectAggregate { .. }) {
                append_pointer_permission(&value, &mut physical_parameters)?
            } else {
                Vec::new()
            };
            let interface = interface_effect(memory, &value)?;
            Ok(VirAbiBinding {
                value,
                interface,
                parameter_slots,
                result_slots: Vec::new(),
            })
        })
        .collect::<Result<Vec<_>, VirAbiError>>()?;
    for binding in &mut results {
        binding.result_slots = append_result_slots(&binding.value, &mut physical_results)?;
    }
    // Legacy raw fixtures normalize exactly once. Production HIR passes an
    // explicit relation; slot planning and all consumers use that same value.
    let (borrow_result, borrow_result_alternatives) = match selection {
        BorrowSelection::Explicit {
            relation,
            alternatives,
        } => (relation, alternatives),
        BorrowSelection::Legacy => {
            let mut inputs = parameters
                .iter()
                .enumerate()
                .filter(|(_, p)| p.interface.transfer.is_borrow());
            let relation = match (inputs.next(), inputs.next(), results.first()) {
                (Some((index, input)), None, Some(result))
                    if input.value == result.value && input.interface == result.interface =>
                {
                    Some(BorrowResultRelation::whole(
                        index as u32,
                        if result.interface.transfer == VirInterfaceTransfer::BorrowMutable {
                            BorrowAccess::Mutable
                        } else {
                            BorrowAccess::Shared
                        },
                    ))
                }
                _ => None,
            };
            (relation, Vec::new())
        }
    };
    if borrow_result.is_some() && !borrow_result_alternatives.is_empty() {
        return Err(abi_error(VirAbiErrorKind::InvalidBorrowResult));
    }
    if borrow_result_alternatives.len() > crate::MAX_BORROW_RESULT_ALTERNATIVES {
        return Err(abi_error(VirAbiErrorKind::InvalidBorrowResult));
    }
    let mut alternative_guards = std::collections::BTreeSet::new();
    if let Some(relation) = borrow_result {
        let input = parameters
            .get(relation.parameter as usize)
            .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidBorrowResult))?;
        let result = results
            .get(relation.result as usize)
            .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidBorrowResult))?;
        let transfer = match relation.access {
            BorrowAccess::Shared => VirInterfaceTransfer::BorrowShared,
            BorrowAccess::Mutable => VirInterfaceTransfer::BorrowMutable,
        };
        if relation.result != 0
            || !borrow_projection_compatible(
                memory,
                &parameters,
                &input.value,
                &result.value,
                relation,
            )
            || input.interface != result.interface
            || result.interface.transfer != transfer
            || results
                .iter()
                .skip(1)
                .any(|r| r.interface.transfer.is_borrow())
        {
            return Err(abi_error(VirAbiErrorKind::InvalidBorrowResult));
        }
    }
    for alternative in &borrow_result_alternatives {
        let relation = alternative.relation;
        let input = parameters
            .get(relation.parameter as usize)
            .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidBorrowResult))?;
        let result = results
            .get(relation.result as usize)
            .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidBorrowResult))?;
        let transfer = match relation.access {
            BorrowAccess::Shared => VirInterfaceTransfer::BorrowShared,
            BorrowAccess::Mutable => VirInterfaceTransfer::BorrowMutable,
        };
        if alternative.guard.is_empty()
            || alternative.guard.len() > crate::MAX_BORROW_RESULT_GUARD_ATOMS
            || alternative.guard.windows(2).any(|pair| {
                pair[0] >= pair[1]
                    || matches!(
                        pair,
                        [
                            crate::BorrowGuardAtom::Boolean { parameter: left, .. },
                            crate::BorrowGuardAtom::Boolean { parameter: right, .. }
                        ] if left == right
                    )
            })
            || !alternative_guards.insert(alternative.guard.clone())
            || relation.result != 0
            || !borrow_projection_compatible(
                memory,
                &parameters,
                &input.value,
                &result.value,
                relation,
            )
            || input.interface != result.interface
            || result.interface.transfer != transfer
        {
            return Err(abi_error(VirAbiErrorKind::InvalidBorrowResult));
        }
        for atom in &alternative.guard {
            let crate::BorrowGuardAtom::Boolean { parameter, .. } = atom;
            if !matches!(
                parameters
                    .get(*parameter as usize)
                    .map(VirAbiBinding::value),
                Some(VirAbiValue::Scalar {
                    ty: VirType::Bool,
                    ..
                })
            ) {
                return Err(abi_error(VirAbiErrorKind::InvalidBorrowResult));
            }
        }
    }
    let escaping_mutable = borrow_result
        .filter(|r| r.access == BorrowAccess::Mutable && r.projection == BorrowProjection::Whole)
        .map(|r| r.parameter as usize);
    for (index, binding) in parameters.iter_mut().enumerate() {
        if escaping_mutable == Some(index) {
            continue;
        }
        if matches!(
            binding.value,
            VirAbiValue::Slice { .. } | VirAbiValue::IndirectAggregate { .. }
        ) || binding.interface.transfer.is_borrow()
        {
            binding.result_slots = vec![append_slot(&mut physical_results, VirType::Permission)?];
        }
    }
    Ok(VirAbiSignature {
        parameters,
        results,
        physical: VirSignature {
            parameters: physical_parameters,
            results: physical_results,
        },
        borrow_result,
        borrow_result_alternatives,
    })
}

fn borrow_values_compatible(left: &VirAbiValue, right: &VirAbiValue) -> bool {
    match (left, right) {
        (
            VirAbiValue::Pointer { pointee: left, .. },
            VirAbiValue::Pointer { pointee: right, .. },
        ) => left == right,
        (VirAbiValue::Slice { element: left, .. }, VirAbiValue::Slice { element: right, .. }) => {
            left == right
        }
        _ => left == right,
    }
}

fn borrow_projection_compatible(
    memory: &VirMemorySchema,
    parameters: &[VirAbiBinding],
    input: &VirAbiValue,
    result: &VirAbiValue,
    relation: BorrowResultRelation,
) -> bool {
    match relation.projection {
        BorrowProjection::Whole => borrow_values_compatible(input, result),
        BorrowProjection::Fixed {
            offset_bytes,
            size_bytes,
            alignment,
        } => {
            let (
                VirAbiValue::Pointer { pointee: input, .. },
                VirAbiValue::Pointer {
                    pointee: result, ..
                },
            ) = (input, result)
            else {
                return false;
            };
            let (Some(input_layout), Some(result_layout)) =
                (memory.layout(input.layout), memory.layout(result.layout))
            else {
                return false;
            };
            size_bytes == result_layout.size_bytes
                && alignment == result_layout.alignment
                && alignment.is_power_of_two()
                && offset_bytes % alignment == 0
                && offset_bytes
                    .checked_add(size_bytes)
                    .is_some_and(|end| end <= input_layout.size_bytes)
                && memory.object_shape(*result).is_ok_and(|shape| {
                    shape.resource_leaves().is_empty() && shape.variants().is_empty()
                })
        }
        BorrowProjection::Slice {
            start,
            end,
            stride_bytes,
            alignment,
        } => {
            let (
                VirAbiValue::Slice { element: input, .. },
                VirAbiValue::Slice {
                    element: result, ..
                },
            ) = (input, result)
            else {
                return false;
            };
            let Some(layout) = memory.layout(input.layout) else {
                return false;
            };
            input == result
                && stride_bytes == layout.size_bytes
                && alignment == layout.alignment
                && alignment.is_power_of_two()
                && borrow_bound_compatible(parameters, relation.parameter, start)
                && borrow_bound_compatible(parameters, relation.parameter, end)
                && !matches!((start, end), (crate::BorrowSliceBound::Constant(a), crate::BorrowSliceBound::Constant(b)) if a > b)
                && memory.object_shape(*result).is_ok_and(|shape| {
                    shape.resource_leaves().is_empty() && shape.variants().is_empty()
                })
        }
    }
}

fn borrow_bound_compatible(
    parameters: &[VirAbiBinding],
    source: u32,
    bound: crate::BorrowSliceBound,
) -> bool {
    match bound {
        crate::BorrowSliceBound::Constant(_) => true,
        crate::BorrowSliceBound::Parameter(parameter) => matches!(
            parameters.get(parameter as usize).map(VirAbiBinding::value),
            Some(VirAbiValue::Scalar {
                ty: VirType::U64,
                ..
            })
        ),
        crate::BorrowSliceBound::SourceLength => matches!(
            parameters.get(source as usize).map(VirAbiBinding::value),
            Some(VirAbiValue::Slice { .. })
        ),
    }
}

impl VirInterfaceTransfer {
    #[must_use]
    pub const fn is_borrow(self) -> bool {
        matches!(self, Self::BorrowShared | Self::BorrowMutable)
    }
}

fn interface_effect(
    memory: &VirMemorySchema,
    value: &VirAbiValue,
) -> Result<VirInterfaceEffect, VirAbiError> {
    let Some(access) = value.access() else {
        return Ok(VirInterfaceEffect {
            transfer: VirInterfaceTransfer::Opaque,
            storage: VirInterfaceStorage::Opaque,
        });
    };
    let transfer = match value {
        VirAbiValue::Unit { .. } => VirInterfaceTransfer::Ignore,
        VirAbiValue::Pointer { .. } => match memory.kind(access.ty) {
            Some(VirMemoryTypeKind::Pointer {
                kind: VirPointerKind::Own,
                ..
            }) => VirInterfaceTransfer::Move,
            Some(VirMemoryTypeKind::Pointer {
                kind: VirPointerKind::Raw,
                ..
            }) => VirInterfaceTransfer::Copy,
            Some(VirMemoryTypeKind::Pointer {
                kind: VirPointerKind::Reference,
                mutability: VirMutability::Const,
                ..
            }) => VirInterfaceTransfer::BorrowShared,
            Some(VirMemoryTypeKind::Pointer {
                kind: VirPointerKind::Reference,
                mutability: VirMutability::Mutable,
                ..
            }) => VirInterfaceTransfer::BorrowMutable,
            _ => return Err(abi_error(VirAbiErrorKind::InvalidAccess(access))),
        },
        VirAbiValue::Slice { .. } => match memory.kind(access.ty) {
            Some(VirMemoryTypeKind::Slice {
                mutability: VirMutability::Const,
                ..
            }) => VirInterfaceTransfer::BorrowShared,
            Some(VirMemoryTypeKind::Slice {
                mutability: VirMutability::Mutable,
                ..
            }) => VirInterfaceTransfer::BorrowMutable,
            _ => return Err(abi_error(VirAbiErrorKind::InvalidAccess(access))),
        },
        VirAbiValue::Opaque(_) => VirInterfaceTransfer::Opaque,
        VirAbiValue::Scalar { .. }
        | VirAbiValue::DirectAggregate { .. }
        | VirAbiValue::IndirectAggregate { .. } => {
            match memory
                .type_capabilities(access.ty)
                .ok_or_else(|| abi_error(VirAbiErrorKind::InvalidAccess(access)))?
                .value
            {
                ValueCapability::Copy => VirInterfaceTransfer::Copy,
                ValueCapability::MoveOnly => VirInterfaceTransfer::Move,
            }
        }
    };
    let storage = match value {
        VirAbiValue::Opaque(_) => VirInterfaceStorage::Opaque,
        VirAbiValue::Unit { .. } => VirInterfaceStorage::None,
        VirAbiValue::IndirectAggregate { .. } => VirInterfaceStorage::Indirect,
        _ => VirInterfaceStorage::Direct,
    };
    Ok(VirInterfaceEffect { transfer, storage })
}

fn append_parameter_slots(
    value: &VirAbiValue,
    output: &mut Vec<VirType>,
) -> Result<Vec<u32>, VirAbiError> {
    match value {
        VirAbiValue::Opaque(ty) => Ok(vec![append_slot(output, *ty)?]),
        VirAbiValue::Unit { .. } => Ok(Vec::new()),
        VirAbiValue::Scalar { ty, .. } => Ok(vec![append_slot(output, *ty)?]),
        VirAbiValue::Pointer { .. } | VirAbiValue::IndirectAggregate { .. } => {
            append_pointer_permission(value, output)
        }
        VirAbiValue::Slice { element, .. } => Ok(vec![
            append_slot(output, VirType::Pointer { access: *element })?,
            append_slot(output, VirType::U64)?,
            append_slot(output, VirType::Permission)?,
        ]),
        VirAbiValue::DirectAggregate { leaves, .. } => leaves
            .iter()
            .map(|leaf| append_slot(output, leaf.ty))
            .collect(),
    }
}

fn append_result_slots(
    value: &VirAbiValue,
    output: &mut Vec<VirType>,
) -> Result<Vec<u32>, VirAbiError> {
    match value {
        VirAbiValue::Opaque(ty) => Ok(vec![append_slot(output, *ty)?]),
        VirAbiValue::Unit { .. } => Ok(Vec::new()),
        VirAbiValue::Scalar { ty, .. } => Ok(vec![append_slot(output, *ty)?]),
        VirAbiValue::Pointer { .. } => append_pointer_permission(value, output),
        VirAbiValue::Slice { element, .. } => Ok(vec![
            append_slot(output, VirType::Pointer { access: *element })?,
            append_slot(output, VirType::U64)?,
            append_slot(output, VirType::Permission)?,
        ]),
        VirAbiValue::DirectAggregate { leaves, .. } => leaves
            .iter()
            .map(|leaf| append_slot(output, leaf.ty))
            .collect(),
        VirAbiValue::IndirectAggregate { .. } => {
            Ok(vec![append_slot(output, VirType::Permission)?])
        }
    }
}

fn append_pointer_permission(
    value: &VirAbiValue,
    output: &mut Vec<VirType>,
) -> Result<Vec<u32>, VirAbiError> {
    let access = match value {
        VirAbiValue::Pointer { pointee, .. } => *pointee,
        VirAbiValue::IndirectAggregate { access } => *access,
        _ => return Err(abi_error(VirAbiErrorKind::NonCanonicalSlotMap)),
    };
    Ok(vec![
        append_slot(output, VirType::Pointer { access })?,
        append_slot(output, VirType::Permission)?,
    ])
}

fn append_slot(output: &mut Vec<VirType>, ty: VirType) -> Result<u32, VirAbiError> {
    let slot = u32::try_from(output.len()).map_err(|_| abi_error(VirAbiErrorKind::TooManySlots))?;
    output.push(ty);
    Ok(slot)
}

/// Stable aggregate-ABI classification failures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirAbiErrorKind {
    InvalidMemorySchema,
    InvalidAccess(VirMemoryAccess),
    UnsupportedType(VirMemoryAccess),
    OwnershipBearingAggregate(VirMemoryAccess),
    TooManySlots,
    NonCanonicalSlotMap,
    InvalidBorrowResult,
    FunctionTableMismatch,
    PhysicalSignatureMismatch { function: VirFunctionId },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirAbiError {
    kind: VirAbiErrorKind,
}

impl VirAbiError {
    #[must_use]
    pub const fn kind(&self) -> &VirAbiErrorKind {
        &self.kind
    }
}

impl fmt::Display for VirAbiError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "invalid VIR aggregate ABI: {:?}", self.kind)
    }
}

impl Error for VirAbiError {}

const fn abi_error(kind: VirAbiErrorKind) -> VirAbiError {
    VirAbiError { kind }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn explicit_source_and_slot_mutations_require_independent_validation() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "abi-source.nera",
            "fn main()->u64{return 0;} fn read(a:&u64,b:&u64)->u64{return *a+*b;}",
        ));
        let unit = output.vir().unwrap().as_unit();
        let original = &unit.runtime.abis.functions[1].signature;
        let access = original.parameters()[0].value().access().unwrap();
        let abi = VirAbiSignature::classify_with_borrow_result(
            &unit.memory,
            &[access, access],
            &[access],
            Some(BorrowResultRelation::whole(1, BorrowAccess::Shared)),
        )
        .unwrap();
        abi.validate(&unit.memory).unwrap();
        let mut function = unit.runtime.functions[1].clone();
        function.signature = abi.physical().clone();
        let input: Vec<_> = function.blocks[0].parameters.iter().map(|v| v.id).collect();
        for block in &mut function.blocks {
            if let super::super::VirTerminator::Return { values } = &mut block.terminator.terminator
            {
                *values = vec![input[2], input[3], input[1], input[3]];
            }
        }
        // This checks value origin only, not linear authority conservation.
        assert!(super::super::borrow_interface::preserves_returned_view(
            &function, &abi
        ));
        let mut wrong_source = abi.clone();
        wrong_source.borrow_result.as_mut().unwrap().parameter = 0;
        wrong_source.validate(&unit.memory).unwrap(); // Same shapes/slots.
        assert!(!super::super::borrow_interface::preserves_returned_view(
            &function,
            &wrong_source
        ));
        let mut missing_source = abi.clone();
        missing_source.borrow_result = None;
        assert!(!super::super::borrow_interface::preserves_returned_view(
            &function,
            &missing_source
        ));
        let mut wrong_slot = abi.clone();
        wrong_slot.results[0].result_slots.swap(0, 1);
        assert!(wrong_slot.validate(&unit.memory).is_err());
    }

    #[test]
    fn validation_rejects_a_mutated_interface_effect() {
        let memory = VirMemorySchema::core_u64();
        let access = VirMemoryAccess::core_u64();
        let mut signature =
            VirAbiSignature::classify(&memory, &[access], &[]).expect("u64 ABI classifies");
        signature.parameters[0].interface.transfer = VirInterfaceTransfer::Move;

        assert_eq!(
            signature
                .validate(&memory)
                .expect_err("effect mutation must fail")
                .kind(),
            &VirAbiErrorKind::NonCanonicalSlotMap
        );
    }

    #[test]
    fn guarded_borrow_result_schema_is_bounded_and_complete_for_the_body() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "conditional-abi.nera",
            "fn main()->u64{let a=1;let b=2;let r=choose(true,&a,&b);return *r;}
             fn choose(flag:bool,a:&u64,b:&u64)->&u64{if flag{return a;}else{return b;}}",
        ));
        let unit = output.vir().unwrap().as_unit();
        let function = &unit.runtime.functions[1];
        let original = &unit.runtime.abis.functions[1].signature;
        assert_eq!(original.borrow_result_alternatives().len(), 2);
        original.validate(&unit.memory).unwrap();

        let mut duplicate = original.clone();
        duplicate
            .borrow_result_alternatives
            .push(duplicate.borrow_result_alternatives[0].clone());
        assert_eq!(
            duplicate.validate(&unit.memory).unwrap_err().kind(),
            &VirAbiErrorKind::InvalidBorrowResult
        );

        let mut oversized = original.clone();
        oversized.borrow_result_alternatives[0].guard = vec![
            crate::BorrowGuardAtom::Boolean {
                parameter: 0,
                expected: true,
            };
            crate::MAX_BORROW_RESULT_GUARD_ATOMS
                + 1
        ];
        assert_eq!(
            oversized.validate(&unit.memory).unwrap_err().kind(),
            &VirAbiErrorKind::InvalidBorrowResult
        );

        let mut deleted = original.clone();
        deleted.borrow_result_alternatives.pop();
        deleted.validate(&unit.memory).unwrap();
        assert!(!super::super::borrow_interface::preserves_returned_view(
            function, &deleted
        ));
    }
}
