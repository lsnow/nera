//! Resolved HIR source types and target-specific layout results.

use super::ids::{
    HirFieldId, HirGenericParameterId, HirLayoutId, HirRegionId, HirTypeId, HirVariantId,
};

/// Calling convention selected before lowering to VIR/backend-specific IR.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirCallingConvention {
    Nera,
}

/// Mutability carried by references, slices and raw pointers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirMutability {
    Const,
    Mutable,
}

/// All source-level integer families admitted by the HIR data model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirIntegerType {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

/// A fully resolved function type. Generic definitions may refer to generic
/// parameter types, but all executable instances must be concrete before VIR.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HirFunctionType {
    pub parameters: Vec<HirTypeId>,
    pub return_type: HirTypeId,
    pub calling_convention: HirCallingConvention,
}

/// Fully resolved source-type shape. Recursive references use typed IDs and
/// never recursively embed complete definitions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum HirTypeKind {
    Unit,
    Bool,
    Integer(HirIntegerType),
    /// An owning allocation capability retained during the Core0 transition.
    Own {
        pointee: HirTypeId,
    },
    RawPointer {
        pointee: HirTypeId,
        mutability: HirMutability,
    },
    Reference {
        pointee: HirTypeId,
        mutability: HirMutability,
        region: HirRegionId,
    },
    Array {
        element: HirTypeId,
        length: u64,
    },
    Slice {
        element: HirTypeId,
        mutability: HirMutability,
    },
    Tuple(Vec<HirTypeId>),
    Struct {
        fields: Vec<HirFieldId>,
    },
    Enum {
        variants: Vec<HirVariantId>,
    },
    Function(HirFunctionType),
    GenericParameter(HirGenericParameterId),
    Never,
}

impl HirTypeKind {
    #[must_use]
    pub const fn is_pointer_like(&self) -> bool {
        matches!(
            self,
            Self::Own { .. } | Self::RawPointer { .. } | Self::Reference { .. }
        )
    }
}

/// Structural admission for deferred storage. This query
/// grants no initialization facts and is shared by elaboration and validation.
pub(super) fn supports_deferred_local_shape(
    types: &[HirTypeDefinition],
    fields: &[super::program::HirField],
    root: HirTypeId,
) -> bool {
    let mut work = vec![root];
    let mut visited = std::collections::BTreeSet::new();
    while let Some(ty) = work.pop() {
        if !visited.insert(ty) {
            continue;
        }
        if visited.len() > 65_536 {
            return false;
        }
        match types
            .get(ty.index())
            .filter(|definition| definition.id == ty)
            .map(|definition| &definition.kind)
        {
            Some(
                HirTypeKind::Unit
                | HirTypeKind::Bool
                | HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize),
            ) => {}
            Some(HirTypeKind::Array { element, .. }) => work.push(*element),
            Some(HirTypeKind::Tuple(elements)) => work.extend(elements),
            Some(HirTypeKind::Struct { fields: members }) => {
                for id in members {
                    let Some(field) = fields.get(id.index()).filter(|field| field.id == *id) else {
                        return false;
                    };
                    work.push(field.ty);
                }
            }
            Some(HirTypeKind::Own { .. } | HirTypeKind::Reference { .. }) if ty != root => {}
            _ => return false,
        }
    }
    true
}

/// Single-object builtin heap admission, shared by source elaboration and the
/// independent HIR boundary. This says nothing about pointee initialization.
pub(crate) fn supports_builtin_allocation(
    types: &[HirTypeDefinition],
    fields: &[super::program::HirField],
    variants: &[super::program::HirVariant],
    root: HirTypeId,
    count: u64,
) -> bool {
    let kind = |ty: HirTypeId| {
        types
            .get(ty.index())
            .filter(|item| item.id == ty)
            .map(|item| &item.kind)
    };
    if matches!(kind(root), Some(HirTypeKind::Integer(HirIntegerType::U64))) {
        return true;
    }
    if count != 1
        || !matches!(
            kind(root),
            Some(
                HirTypeKind::Tuple(_)
                    | HirTypeKind::Struct { .. }
                    | HirTypeKind::Array { .. }
                    | HirTypeKind::Enum { .. }
            )
        )
    {
        return false;
    }
    let mut work = vec![root];
    let mut visited = std::collections::BTreeSet::new();
    while let Some(ty) = work.pop() {
        if !visited.insert(ty) {
            continue;
        }
        if visited.len() > 65_536 {
            return false;
        }
        let members = match kind(ty) {
            Some(
                HirTypeKind::Unit
                | HirTypeKind::Bool
                | HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize),
            ) => continue,
            Some(HirTypeKind::Own { pointee })
                if matches!(
                    kind(*pointee),
                    Some(HirTypeKind::Integer(HirIntegerType::U64))
                ) =>
            {
                continue;
            }
            Some(HirTypeKind::Reference { .. }) => continue,
            Some(HirTypeKind::Array { element, .. }) => {
                work.push(*element);
                continue;
            }
            Some(HirTypeKind::Tuple(elements)) => {
                work.extend(elements);
                continue;
            }
            Some(HirTypeKind::Struct { fields }) => fields.clone(),
            Some(HirTypeKind::Enum { variants: cases })
                if ty == root && !cases.is_empty() && cases.len() <= 256 =>
            {
                let mut members = Vec::new();
                for id in cases {
                    let Some(case) = variants.get(id.index()).filter(|case| case.id == *id) else {
                        return false;
                    };
                    members.extend(&case.fields);
                }
                members
            }
            _ => return false,
        };
        for id in members {
            let Some(field) = fields.get(id.index()).filter(|field| field.id == id) else {
                return false;
            };
            work.push(field.ty);
        }
    }
    true
}

/// One source-type definition in the deterministic type table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirTypeDefinition {
    pub id: HirTypeId,
    pub name: Option<String>,
    pub kind: HirTypeKind,
    pub generic_parameters: Vec<HirGenericParameterId>,
    /// `None` means unsized or not yet resolved for the selected target.
    pub layout: Option<HirLayoutId>,
}

/// ABI-facing classification, separate from source-type identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirAbiClass {
    Ignore,
    Scalar,
    ScalarPair,
    Aggregate,
}

/// Layout of one field within a resolved aggregate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HirFieldLayout {
    pub field: HirFieldId,
    pub offset_bytes: u64,
}

/// Layout of one variant payload within a resolved enum.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HirVariantCaseLayout {
    pub variant: HirVariantId,
    pub payload_offset_bytes: u64,
    pub fields: Vec<HirFieldLayout>,
}

/// Target layout of a resolved enum representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HirVariantLayout {
    pub tag_size_bytes: u64,
    pub tag_alignment: u64,
    pub cases: Vec<HirVariantCaseLayout>,
}

/// ABI-relevant layout resolved for one source type and one target.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HirLayout {
    pub id: HirLayoutId,
    pub ty: HirTypeId,
    pub size_bytes: u64,
    pub alignment: u64,
    pub abi: HirAbiClass,
    pub fields: Vec<HirFieldLayout>,
    pub variants: Option<HirVariantLayout>,
}

/// Byte order used by the selected target data layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirEndianness {
    Little,
    Big,
}

/// Target facts needed to resolve source types into [`HirLayout`] entries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HirTargetDataLayout {
    pub endianness: HirEndianness,
    pub pointer_size_bytes: u64,
    pub pointer_alignment: u64,
    pub usize_size_bytes: u64,
    pub usize_alignment: u64,
}

impl HirTargetDataLayout {
    /// Current production target profile. It is explicit in HIR so host layout
    /// is never consulted implicitly.
    #[must_use]
    pub const fn x86_64() -> Self {
        Self {
            endianness: HirEndianness::Little,
            pointer_size_bytes: 8,
            pointer_alignment: 8,
            usize_size_bytes: 8,
            usize_alignment: 8,
        }
    }
}
