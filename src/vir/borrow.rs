//! Canonical borrow-region declarations and closed loan-effect metadata.

use super::{
    VirBlockId, VirBorrowRegionConstraintId, VirBorrowRegionId, VirFunctionId, VirLoanId,
    VirMemoryAccess, VirOriginId, VirValueId,
};

/// Frame-local names for interface loans; instruction-defined loans occupy
/// the lower half of the identifier space.
pub(crate) fn interface_loan_id(parameter: u32) -> VirLoanId {
    VirLoanId::new(u32::MAX - parameter)
}

fn parameter_field_loan_id(parameters: usize, field: usize) -> Option<VirLoanId> {
    let ordinal = u32::try_from(parameters.checked_add(field)?).ok()?;
    (ordinal < (1 << 31)).then(|| interface_loan_id(ordinal))
}

/// Derived entry plan for the aggregate reference interface. This
/// is not a borrow declaration and does not admit an ABI or grant authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ParameterReferenceEntry {
    pub parameter: u32,
    pub slot: u32,
    pub pointer_slot: u32,
    pub permission_slot: u32,
    pub offset_bytes: u64,
    pub reference: VirMemoryAccess,
    pub pointee: VirMemoryAccess,
    pub mutability: super::VirMutability,
    pub loan: VirLoanId,
}

/// All direct parameter identities precede field identities. Instruction loans
/// occupy the lower half; dynamic runtime IDs additionally check live tables.
pub(crate) fn plan_parameter_reference_entries(
    memory: &super::VirMemorySchema,
    parameters: &[VirMemoryAccess],
) -> Option<Vec<ParameterReferenceEntry>> {
    let slots = super::plan_reference_parameter_slots(memory, parameters).ok()?;
    let mut entries = Vec::new();
    for (parameter, access) in parameters.iter().copied().enumerate() {
        let access = match memory.kind(access.ty)? {
            super::VirMemoryTypeKind::Pointer {
                pointee,
                kind: super::VirPointerKind::Own | super::VirPointerKind::Reference,
                ..
            } => memory.access(*pointee)?,
            _ => access,
        };
        if !matches!(
            memory.kind(access.ty)?,
            super::VirMemoryTypeKind::Struct { .. }
                | super::VirMemoryTypeKind::Array { .. }
                | super::VirMemoryTypeKind::Tuple(_)
        ) {
            continue;
        }
        let shape = memory.object_shape(access).ok()?;
        let references: Vec<_> = shape
            .resource_leaves()
            .iter()
            .filter(|leaf| leaf.kind() == super::VirPointerKind::Reference)
            .collect();
        if references.is_empty() {
            continue;
        }
        if !shape.variants().is_empty() || references.len() > 256 {
            return None;
        }
        let [pointer_slot, permission_slot] = slots.get(parameter)?.as_slice() else {
            return None;
        };
        for (slot, leaf) in references.into_iter().enumerate() {
            let loan = parameter_field_loan_id(parameters.len(), entries.len())?;
            entries.push(ParameterReferenceEntry {
                parameter: u32::try_from(parameter).ok()?,
                slot: u32::try_from(slot).ok()?,
                pointer_slot: *pointer_slot,
                permission_slot: *permission_slot,
                offset_bytes: leaf.bytes().start_bytes(),
                reference: leaf.access(),
                pointee: leaf.pointee_access(),
                mutability: leaf.mutability(),
                loan,
            });
        }
    }
    Some(entries)
}

/// One canonical source plan. It locates an input carrier but grants no loan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BoundarySourcePlan {
    pub source: crate::BoundarySource,
    pub loan: VirLoanId,
    pub pointer_slot: u32,
    pub permission_slot: u32,
    pub reference: VirMemoryAccess,
    pub pointee: VirMemoryAccess,
    pub mutability: super::VirMutability,
    pub field: Option<ParameterReferenceEntry>,
}

pub(crate) fn plan_boundary_source(
    memory: &super::VirMemorySchema,
    parameters: &[VirMemoryAccess],
    source: crate::BoundarySource,
) -> Option<BoundarySourcePlan> {
    match source {
        crate::BoundarySource::ParameterField { index, field } => {
            let entry = plan_parameter_reference_entries(memory, parameters)?
                .into_iter()
                .find(|e| e.parameter == index && e.slot == field)?;
            Some(BoundarySourcePlan {
                source,
                loan: entry.loan,
                pointer_slot: entry.pointer_slot,
                permission_slot: entry.permission_slot,
                reference: entry.reference,
                pointee: entry.pointee,
                mutability: entry.mutability,
                field: Some(entry),
            })
        }
        crate::BoundarySource::Parameter { index } => {
            let reference = *parameters.get(index as usize)?;
            let (pointee, mutability) = match memory.kind(reference.ty)? {
                super::VirMemoryTypeKind::Pointer {
                    kind: super::VirPointerKind::Reference,
                    pointee,
                    mutability,
                } => (*pointee, *mutability),
                super::VirMemoryTypeKind::Slice {
                    element,
                    mutability,
                } => (*element, *mutability),
                _ => return None,
            };
            let slots = super::plan_reference_parameter_slots(memory, parameters).ok()?;
            let slots = slots.get(index as usize)?;
            Some(BoundarySourcePlan {
                source,
                loan: interface_loan_id(index),
                pointer_slot: *slots.first()?,
                permission_slot: *slots.last()?,
                reference,
                pointee: memory.access(pointee)?,
                mutability,
                field: None,
            })
        }
    }
}

/// Resolve a whole reference-field result using canonical input leaves.
/// The leaf's own pointee and mutability determine the result; an inline
/// referent projection or a same-address owner/raw leaf is not this source.
pub(crate) fn plan_parameter_field_result(
    memory: &super::VirMemorySchema,
    parameters: &[VirMemoryAccess],
    results: &[VirMemoryAccess],
    relation: crate::BorrowResultRelation,
) -> Option<ParameterReferenceEntry> {
    relation.parameter_field?;
    if relation.result != 0
        || results.len() != 1
        || relation.projection != crate::BorrowProjection::Whole
    {
        return None;
    }
    let plan: crate::vir::BoundarySourcePlan =
        crate::vir::plan_boundary_source(memory, parameters, relation.source())?;
    let entry = plan.field?;
    let result = *results.first()?;
    if !memory.resolves_access(result) {
        return None;
    }
    let super::VirMemoryTypeKind::Pointer {
        kind: super::VirPointerKind::Reference,
        pointee,
        mutability,
    } = memory.kind(result.ty)?
    else {
        return None;
    };
    let access = if *mutability == super::VirMutability::Mutable {
        crate::BorrowAccess::Mutable
    } else {
        crate::BorrowAccess::Shared
    };
    (memory.access(*pointee) == Some(entry.pointee)
        && *mutability == entry.mutability
        && relation.access == access)
        .then_some(entry)
}

/// Source/ABI role that introduced one VIR borrow region.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirBorrowRegionOrigin {
    Lexical,
    Parameter {
        index: u32,
    },
    /// One canonical reference leaf in a by-value aggregate parameter.
    ParameterField {
        index: u32,
        slot: u32,
    },
    Result {
        index: u32,
    },
    Inferred,
}

/// Program points at which a reference in one borrow region may be used.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirBorrowRegionScope {
    /// Signature-visible region spanning the complete function.
    Function,
    /// Canonical sorted set of CFG blocks retained after lexical lowering.
    Blocks(Vec<VirBlockId>),
}

/// One canonical borrow region owned by exactly one VIR function.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirBorrowRegion {
    pub id: VirBorrowRegionId,
    pub owner: VirFunctionId,
    pub origin: VirBorrowRegionOrigin,
    pub scope: VirBorrowRegionScope,
    pub source_origin: VirOriginId,
}

/// Canonical `subregion <= superregion` inclusion constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirBorrowRegionConstraint {
    pub id: VirBorrowRegionConstraintId,
    pub owner: VirFunctionId,
    pub subregion: VirBorrowRegionId,
    pub superregion: VirBorrowRegionId,
    pub source_origin: VirOriginId,
}

/// Borrow-region universe shared by validation and verification.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VirBorrowEnvironment {
    regions: Vec<VirBorrowRegion>,
    constraints: Vec<VirBorrowRegionConstraint>,
}

impl VirBorrowEnvironment {
    /// Bounded reachability for an authority-selected parent's actual region.
    /// None means a missing region or exhausted edge-scan budget, never an
    /// implicit inclusion assumption. Edges in other functions are irrelevant.
    pub(crate) fn includes(
        &self,
        sub: VirBorrowRegionId,
        sup: VirBorrowRegionId,
        limit: usize,
    ) -> Option<bool> {
        let owner = self.region(sub)?.owner;
        if self.region(sup)?.owner != owner {
            return Some(false);
        }
        if sub == sup {
            return Some(true);
        }
        let mut seen = std::collections::BTreeSet::new();
        let mut pending = vec![sub];
        let mut visits = 0usize;
        while let Some(current) = pending.pop() {
            if !seen.insert(current) {
                continue;
            }
            for edge in self.constraints.iter().filter(|edge| edge.owner == owner) {
                visits = visits.checked_add(1)?;
                if visits > limit {
                    return None;
                }
                if edge.subregion == current {
                    if edge.superregion == sup {
                        return Some(true);
                    }
                    pending.push(edge.superregion);
                }
            }
        }
        Some(false)
    }
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            regions: Vec::new(),
            constraints: Vec::new(),
        }
    }

    /// Constructs raw tables. [`super::VirUnit::validate`] remains responsible
    /// for density, ownership, origin and scope invariants.
    #[must_use]
    pub const fn from_tables(
        regions: Vec<VirBorrowRegion>,
        constraints: Vec<VirBorrowRegionConstraint>,
    ) -> Self {
        Self {
            regions,
            constraints,
        }
    }

    #[must_use]
    pub fn regions(&self) -> &[VirBorrowRegion] {
        &self.regions
    }

    #[must_use]
    pub fn constraints(&self) -> &[VirBorrowRegionConstraint] {
        &self.constraints
    }

    #[must_use]
    pub fn region(&self, id: VirBorrowRegionId) -> Option<&VirBorrowRegion> {
        self.regions
            .get(id.get() as usize)
            .filter(|region| region.id == id)
    }

    #[must_use]
    pub fn constraint(
        &self,
        id: VirBorrowRegionConstraintId,
    ) -> Option<&VirBorrowRegionConstraint> {
        self.constraints
            .get(id.get() as usize)
            .filter(|constraint| constraint.id == id)
    }
}

/// Access kind granted by one canonical loan.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirLoanKind {
    Shared,
    Mutable,
}

/// Canonical allocation-relative half-open range protected by a loan.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirLoanRange {
    pub start_bytes: u64,
    pub end_bytes: u64,
}

impl VirLoanRange {
    #[must_use]
    pub const fn len_bytes(self) -> Option<u64> {
        self.end_bytes.checked_sub(self.start_bytes)
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.start_bytes <= other.start_bytes && other.end_bytes <= self.end_bytes
    }
}

/// Immutable metadata repeated by every effect for independent validation.
///
/// `reference` is the canonical logical `Reference<T>` memory access. The
/// source/result SSA slots are its physical pointer/permission pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirLoanEffect {
    pub loan: VirLoanId,
    pub kind: VirLoanKind,
    pub region: VirBorrowRegionId,
    pub parent: Option<VirLoanId>,
    pub source_pointer: VirValueId,
    pub source_permission: VirValueId,
    pub reference: VirMemoryAccess,
    pub range: VirLoanRange,
    pub origin: VirOriginId,
}

/// Authority-directed loan effect for interface references, dynamic children,
/// or references moved out of aggregate payloads (alias/end).
///
/// The permission carries the unforgeable loan identity.  Keeping the
/// nominal reference access here still lets the validator reject forged
/// pointer shapes without requiring lowering to predict which guarded loan
/// instance a field or parameter contains. Reborrow additionally declares its
/// fresh child identity and region on the instruction itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirLoanAuthorityEffect {
    pub source_pointer: VirValueId,
    pub source_permission: VirValueId,
    pub reference: VirMemoryAccess,
    pub origin: VirOriginId,
}

#[cfg(test)]
mod parameter_entry_tests {
    use super::*;

    #[test]
    fn field_result_sources_select_real_reference_leaves() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "field-result.nera",
            include_str!("../../spec/cases/aggregate/owning-abi.nera"),
        ));
        let unit = output.vir().unwrap().as_unit();
        let parameters = unit
            .runtime
            .abis
            .functions
            .iter()
            .find(|f| f.signature.parameters().len() == 3)
            .unwrap()
            .signature
            .parameters()
            .iter()
            .map(|b| b.value().access().unwrap())
            .collect::<Vec<_>>();
        for mode in [
            super::super::VirMutability::Const,
            super::super::VirMutability::Mutable,
        ] {
            let mut memory = unit.memory.clone();
            for ty in &mut memory.types {
                if let super::super::VirMemoryTypeKind::Pointer {
                    kind, mutability, ..
                } = &mut ty.kind
                    && *kind == super::super::VirPointerKind::Own
                {
                    *kind = super::super::VirPointerKind::Reference;
                    *mutability = mode;
                }
            }
            memory.assign_canonical_type_capabilities().unwrap();
            memory.validate().unwrap();
            let access = if mode == super::super::VirMutability::Mutable {
                crate::BorrowAccess::Mutable
            } else {
                crate::BorrowAccess::Shared
            };
            let entries = plan_parameter_reference_entries(&memory, &parameters).unwrap();
            assert_eq!(entries.len(), 4);
            for entry in &entries {
                let relation = crate::BorrowResultRelation::from_parameter_field(
                    entry.parameter,
                    entry.slot,
                    access,
                );
                assert_eq!(
                    plan_parameter_field_result(&memory, &parameters, &[entry.reference], relation),
                    Some(*entry)
                );
                for mutation in 0..6 {
                    let mut bad = relation;
                    match mutation {
                        0 => bad.parameter = 0, // bool, not a reference aggregate
                        1 => bad.parameter_field = Some(2),
                        2 => bad.parameter_field = None,
                        3 => bad.result = 1,
                        4 => {
                            bad.access = if access == crate::BorrowAccess::Mutable {
                                crate::BorrowAccess::Shared
                            } else {
                                crate::BorrowAccess::Mutable
                            }
                        }
                        5 => {
                            bad.projection = crate::BorrowProjection::Fixed {
                                offset_bytes: 0,
                                size_bytes: 8,
                                alignment: 8,
                            }
                        }
                        _ => unreachable!(),
                    }
                    assert!(
                        plan_parameter_field_result(&memory, &parameters, &[entry.reference], bad)
                            .is_none()
                    );
                }
                assert!(
                    plan_parameter_field_result(&memory, &parameters, &[entry.pointee], relation)
                        .is_none()
                );
                assert!(plan_parameter_field_result(&memory, &parameters, &[], relation).is_none());
                assert!(
                    plan_parameter_field_result(
                        &memory,
                        &parameters,
                        &[entry.reference, entry.reference],
                        relation
                    )
                    .is_none()
                );
                let direct = plan_boundary_source(
                    &memory,
                    &[entry.reference],
                    crate::BoundarySource::Parameter { index: 0 },
                )
                .unwrap();
                assert_eq!(direct.loan, interface_loan_id(0));
                assert_eq!(direct.pointee, entry.pointee);
                assert_eq!(direct.pointer_slot, 0);
                assert_eq!(direct.permission_slot, 1);
                assert!(direct.field.is_none());
                assert!(
                    plan_boundary_source(
                        &memory,
                        &[entry.reference],
                        crate::BoundarySource::ParameterField { index: 0, field: 0 }
                    )
                    .is_none()
                );
                // Direct-parameter consumers must not ignore the new coordinate.
                assert!(
                    crate::VirAbiSignature::classify_with_borrow_result(
                        &memory,
                        &[entry.reference],
                        &[entry.reference],
                        Some(crate::BorrowResultRelation::from_parameter_field(
                            0, 0, access
                        ))
                    )
                    .is_err()
                );
                assert!(
                    crate::VirAbiSignature::classify_with_borrow_result(
                        &memory,
                        &[entry.reference],
                        &[entry.reference],
                        Some(crate::BorrowResultRelation::whole(0, access))
                    )
                    .is_ok()
                );
            }
            assert_ne!(entries[0].loan, entries[2].loan);
            assert_ne!(entries[0].pointer_slot, entries[2].pointer_slot);
        }
    }

    #[test]
    fn field_loan_names_are_disjoint_and_overflow_fails_closed() {
        for parameters in 0..16 {
            let direct: std::collections::BTreeSet<_> = (0..parameters)
                .map(|index| interface_loan_id(index as u32))
                .collect();
            let mut fields = std::collections::BTreeSet::new();
            for field in 0..256 {
                let id = parameter_field_loan_id(parameters, field).unwrap();
                assert!(id.get() >= 1 << 31);
                assert!(!direct.contains(&id));
                assert!(fields.insert(id));
            }
        }
        assert_eq!(
            parameter_field_loan_id(0, (1 << 31) - 1),
            Some(VirLoanId::new(1 << 31))
        );
        assert_eq!(parameter_field_loan_id(0, 1 << 31), None);
        assert_eq!(parameter_field_loan_id(1 << 31, 0), None);
        assert_eq!(parameter_field_loan_id(usize::MAX, 1), None);
    }
}
