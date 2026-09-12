//! Canonical target-independent identities and target-specific memory layouts.

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use crate::{DropCapability, SizeCapability, TypeCapabilities, ValueCapability};

macro_rules! memory_id {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u32);

        impl $name {
            #[must_use]
            pub const fn new(raw: u32) -> Self {
                Self(raw)
            }

            #[must_use]
            pub const fn get(self) -> u32 {
                self.0
            }

            #[must_use]
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

memory_id!(VirTypeId);
memory_id!(VirLayoutId);
memory_id!(VirFieldId);
memory_id!(VirVariantId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirEndianness {
    Little,
    Big,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirTargetDataLayout {
    pub endianness: VirEndianness,
    pub pointer_size_bytes: u64,
    pub pointer_alignment: u64,
    pub usize_size_bytes: u64,
    pub usize_alignment: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirMutability {
    Const,
    Mutable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirPointerKind {
    Own,
    Raw,
    Reference,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirIntegerType {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VirMemoryTypeKind {
    Unit,
    Bool,
    Integer(VirIntegerType),
    Pointer {
        pointee: VirTypeId,
        kind: VirPointerKind,
        mutability: VirMutability,
    },
    Array {
        element: VirTypeId,
        length: u64,
    },
    Slice {
        element: VirTypeId,
        mutability: VirMutability,
    },
    Tuple(Vec<VirTypeId>),
    Struct {
        fields: Vec<VirFieldId>,
    },
    Enum {
        variants: Vec<VirVariantId>,
    },
    Never,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirMemoryType {
    pub id: VirTypeId,
    pub kind: VirMemoryTypeKind,
    pub layout: VirLayoutId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirAbiClass {
    Ignore,
    Scalar,
    ScalarPair,
    Aggregate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirFieldLayout {
    pub field: VirFieldId,
    pub offset_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirVariantCaseLayout {
    pub variant: VirVariantId,
    pub payload_offset_bytes: u64,
    pub fields: Vec<VirFieldLayout>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirVariantLayout {
    pub tag_size_bytes: u64,
    pub tag_alignment: u64,
    pub cases: Vec<VirVariantCaseLayout>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirLayout {
    pub id: VirLayoutId,
    pub ty: VirTypeId,
    pub size_bytes: u64,
    pub alignment: u64,
    pub abi: VirAbiClass,
    pub fields: Vec<VirFieldLayout>,
    pub variants: Option<VirVariantLayout>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirField {
    pub id: VirFieldId,
    pub owner: VirTypeId,
    pub ty: VirTypeId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirVariant {
    pub id: VirVariantId,
    pub owner: VirTypeId,
    pub fields: Vec<VirFieldId>,
    pub discriminant: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirMemoryAccess {
    pub ty: VirTypeId,
    pub layout: VirLayoutId,
}

impl VirMemoryAccess {
    #[must_use]
    pub const fn new(ty: VirTypeId, layout: VirLayoutId) -> Self {
        Self { ty, layout }
    }

    /// Access used by hand-authored VIR v0 tests and the frozen Core0 schema.
    #[must_use]
    pub const fn core_u64() -> Self {
        Self::new(VirTypeId::new(0), VirLayoutId::new(0))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirMemorySchema {
    pub target: VirTargetDataLayout,
    pub types: Vec<VirMemoryType>,
    /// Producer-computed canonical capability for each dense type-table slot.
    pub type_capabilities: Vec<TypeCapabilities>,
    pub layouts: Vec<VirLayout>,
    pub fields: Vec<VirField>,
    pub variants: Vec<VirVariant>,
}

impl VirMemorySchema {
    /// Smallest standalone VIR v0 schema: one target-layout-resolved `u64`.
    #[must_use]
    pub fn core_u64() -> Self {
        Self {
            target: VirTargetDataLayout {
                endianness: VirEndianness::Little,
                pointer_size_bytes: 8,
                pointer_alignment: 8,
                usize_size_bytes: 8,
                usize_alignment: 8,
            },
            types: vec![VirMemoryType {
                id: VirTypeId::new(0),
                kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                layout: VirLayoutId::new(0),
            }],
            type_capabilities: vec![TypeCapabilities {
                value: ValueCapability::Copy,
                drop: DropCapability::TrivialDrop,
                contains_resource: false,
                size: SizeCapability::Sized,
            }],
            layouts: vec![VirLayout {
                id: VirLayoutId::new(0),
                ty: VirTypeId::new(0),
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            }],
            fields: Vec::new(),
            variants: Vec::new(),
        }
    }

    pub fn validate(&self) -> Result<(), VirMemorySchemaError> {
        validate_dense("type", &self.types, |item| item.id.get())?;
        validate_dense("layout", &self.layouts, |item| item.id.get())?;
        validate_dense("field", &self.fields, |item| item.id.get())?;
        validate_dense("variant", &self.variants, |item| item.id.get())?;
        if self.target.pointer_size_bytes == 0
            || !self.target.pointer_alignment.is_power_of_two()
            || !self
                .target
                .pointer_size_bytes
                .is_multiple_of(self.target.pointer_alignment)
            || self.target.usize_size_bytes == 0
            || !self.target.usize_alignment.is_power_of_two()
            || !self
                .target
                .usize_size_bytes
                .is_multiple_of(self.target.usize_alignment)
        {
            return Err(schema_error(VirMemorySchemaErrorKind::InvalidTarget));
        }
        for ty in &self.types {
            let layout = self
                .layout(ty.layout)
                .filter(|layout| layout.ty == ty.id)
                .ok_or_else(|| {
                    schema_error(VirMemorySchemaErrorKind::TypeLayoutMismatch { ty: ty.id })
                })?;
            self.validate_type(ty, layout)?;
        }
        for layout in &self.layouts {
            if self.ty(layout.ty).is_none_or(|ty| ty.layout != layout.id)
                || !layout.alignment.is_power_of_two()
                || layout.size_bytes % layout.alignment != 0
            {
                return Err(schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                    layout: layout.id,
                }));
            }
            self.validate_layout_shape(layout)?;
        }
        for field in &self.fields {
            if self.ty(field.owner).is_none()
                || self.ty(field.ty).is_none()
                || !self.owner_contains_field(field.owner, field.id)
            {
                return Err(schema_error(VirMemorySchemaErrorKind::InvalidField {
                    field: field.id,
                }));
            }
        }
        for variant in &self.variants {
            let owned = matches!(self.kind(variant.owner), Some(VirMemoryTypeKind::Enum { variants }) if variants.contains(&variant.id));
            if !owned
                || variant.fields.iter().any(|field| {
                    self.field(*field)
                        .is_none_or(|field| field.owner != variant.owner)
                })
            {
                return Err(schema_error(VirMemorySchemaErrorKind::InvalidVariant {
                    variant: variant.id,
                }));
            }
            if self.variants.iter().any(|other| {
                other.id != variant.id
                    && other.owner == variant.owner
                    && other.discriminant == variant.discriminant
            }) {
                return Err(schema_error(VirMemorySchemaErrorKind::InvalidVariant {
                    variant: variant.id,
                }));
            }
        }
        if self.type_capabilities.len() != self.types.len() {
            return Err(schema_error(
                VirMemorySchemaErrorKind::TypeCapabilityTableMismatch,
            ));
        }
        for ty in &self.types {
            if derive_type_capabilities(self, ty.id)
                != self.type_capabilities.get(ty.id.index()).copied()
            {
                return Err(schema_error(
                    VirMemorySchemaErrorKind::TypeCapabilityMismatch { ty: ty.id },
                ));
            }
        }
        Ok(())
    }

    /// Rebuilds producer-side capabilities from a complete memory type graph.
    /// [`Self::validate`] performs the independent fail-closed comparison.
    pub fn assign_canonical_type_capabilities(&mut self) -> Result<(), VirMemorySchemaError> {
        self.type_capabilities = (0..self.types.len())
            .map(|index| {
                let raw = u32::try_from(index).map_err(|_| {
                    schema_error(VirMemorySchemaErrorKind::TypeCapabilityTableMismatch)
                })?;
                derive_type_capabilities(self, VirTypeId::new(raw)).ok_or_else(|| {
                    schema_error(VirMemorySchemaErrorKind::TypeCapabilityMismatch {
                        ty: VirTypeId::new(raw),
                    })
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(())
    }

    #[must_use]
    pub fn ty(&self, id: VirTypeId) -> Option<&VirMemoryType> {
        self.types.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn kind(&self, id: VirTypeId) -> Option<&VirMemoryTypeKind> {
        self.ty(id).map(|item| &item.kind)
    }

    #[must_use]
    pub fn type_capabilities(&self, id: VirTypeId) -> Option<TypeCapabilities> {
        self.ty(id)
            .and_then(|_| self.type_capabilities.get(id.index()).copied())
    }

    #[must_use]
    pub fn layout(&self, id: VirLayoutId) -> Option<&VirLayout> {
        self.layouts.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn field(&self, id: VirFieldId) -> Option<&VirField> {
        self.fields.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn variant(&self, id: VirVariantId) -> Option<&VirVariant> {
        self.variants.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn access(&self, ty: VirTypeId) -> Option<VirMemoryAccess> {
        self.ty(ty).map(|ty| VirMemoryAccess {
            ty: ty.id,
            layout: ty.layout,
        })
    }

    #[must_use]
    pub fn resolves_access(&self, access: VirMemoryAccess) -> bool {
        self.ty(access.ty)
            .is_some_and(|ty| ty.layout == access.layout)
            && self
                .layout(access.layout)
                .is_some_and(|layout| layout.ty == access.ty)
    }

    /// Returns the canonical typed projection for one tuple element. Tuple
    /// offsets are derived from child layouts, never stored in a parallel
    /// producer-owned table.
    #[must_use]
    pub fn tuple_element_projection(
        &self,
        owner: VirMemoryAccess,
        index: u64,
    ) -> Option<(VirMemoryAccess, u64)> {
        if !self.resolves_access(owner) {
            return None;
        }
        let VirMemoryTypeKind::Tuple(elements) = self.kind(owner.ty)? else {
            return None;
        };
        let target = usize::try_from(index).ok()?;
        let mut cursor = 0_u64;
        for (element_index, element) in elements.iter().copied().enumerate() {
            let access = self.access(element)?;
            let layout = self.layout(access.layout)?;
            cursor = align_up(cursor, layout.alignment)?;
            if element_index == target {
                return Some((access, cursor));
            }
            cursor = cursor.checked_add(layout.size_bytes)?;
        }
        None
    }

    fn validate_type(
        &self,
        ty: &VirMemoryType,
        layout: &VirLayout,
    ) -> Result<(), VirMemorySchemaError> {
        let valid = match &ty.kind {
            VirMemoryTypeKind::Unit => {
                layout.size_bytes == 0 && layout.alignment == 1 && layout.abi == VirAbiClass::Ignore
            }
            VirMemoryTypeKind::Bool => {
                layout.size_bytes == 1 && layout.alignment == 1 && layout.abi == VirAbiClass::Scalar
            }
            VirMemoryTypeKind::Integer(integer) => {
                integer_layout(*integer, self.target) == (layout.size_bytes, layout.alignment)
                    && layout.abi == VirAbiClass::Scalar
            }
            VirMemoryTypeKind::Pointer { pointee, .. } => {
                self.ty(*pointee).is_some()
                    && layout.size_bytes == self.target.pointer_size_bytes
                    && layout.alignment == self.target.pointer_alignment
                    && layout.abi == VirAbiClass::Scalar
            }
            VirMemoryTypeKind::Array { element, length } => self
                .ty(*element)
                .and_then(|element| self.layout(element.layout))
                .filter(|element| layout.alignment >= element.alignment)
                .and_then(|element| {
                    element
                        .size_bytes
                        .checked_mul(*length)
                        .and_then(|size| align_up(size, layout.alignment))
                })
                .is_some_and(|size| {
                    size == layout.size_bytes && layout.abi == VirAbiClass::Aggregate
                }),
            VirMemoryTypeKind::Slice { element, .. } => {
                self.ty(*element).is_some()
                    && self
                        .target
                        .pointer_size_bytes
                        .checked_mul(2)
                        .is_some_and(|size| size == layout.size_bytes)
                    && layout.alignment == self.target.pointer_alignment
                    && layout.abi == VirAbiClass::ScalarPair
            }
            VirMemoryTypeKind::Tuple(elements) => {
                elements.iter().all(|element| self.ty(*element).is_some())
                    && layout.abi == VirAbiClass::Aggregate
            }
            VirMemoryTypeKind::Struct { fields } => {
                fields
                    .iter()
                    .all(|field| self.field(*field).is_some_and(|field| field.owner == ty.id))
                    && layout.abi == VirAbiClass::Aggregate
            }
            VirMemoryTypeKind::Enum { variants } => {
                variants.iter().all(|variant| {
                    self.variant(*variant)
                        .is_some_and(|variant| variant.owner == ty.id)
                }) && layout.abi == VirAbiClass::Aggregate
            }
            VirMemoryTypeKind::Never => layout.size_bytes == 0 && layout.abi == VirAbiClass::Ignore,
        };
        if valid {
            Ok(())
        } else {
            Err(schema_error(VirMemorySchemaErrorKind::InvalidType {
                ty: ty.id,
            }))
        }
    }

    fn validate_layout_shape(&self, layout: &VirLayout) -> Result<(), VirMemorySchemaError> {
        let kind = self.kind(layout.ty).ok_or_else(|| {
            schema_error(VirMemorySchemaErrorKind::InvalidLayout { layout: layout.id })
        })?;
        let shape_matches = match kind {
            VirMemoryTypeKind::Struct { fields } => {
                layout.variants.is_none()
                    && same_ids(fields, layout.fields.iter().map(|field| field.field))
            }
            VirMemoryTypeKind::Enum { variants } => {
                layout.fields.is_empty()
                    && layout.variants.as_ref().is_some_and(|variant_layout| {
                        same_ids(
                            variants,
                            variant_layout.cases.iter().map(|case| case.variant),
                        )
                    })
            }
            _ => layout.fields.is_empty() && layout.variants.is_none(),
        };
        if !shape_matches {
            return Err(schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                layout: layout.id,
            }));
        }

        validate_field_ranges(self, layout, 0, &layout.fields)?;
        if let Some(variants) = &layout.variants {
            if !variants.tag_alignment.is_power_of_two()
                || variants.tag_size_bytes == 0
                || variants.tag_size_bytes % variants.tag_alignment != 0
                || variants.tag_alignment > layout.alignment
                || variants.tag_size_bytes > layout.size_bytes
            {
                return Err(schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                    layout: layout.id,
                }));
            }
            for case in &variants.cases {
                let variant = self
                    .variant(case.variant)
                    .filter(|variant| variant.owner == layout.ty);
                if variant.is_none_or(|variant| {
                    !same_ids(&variant.fields, case.fields.iter().map(|field| field.field))
                        || !discriminant_fits(variant.discriminant, variants.tag_size_bytes)
                }) || case.payload_offset_bytes < variants.tag_size_bytes
                    || case.payload_offset_bytes > layout.size_bytes
                {
                    return Err(schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                        layout: layout.id,
                    }));
                }
                validate_field_ranges(self, layout, case.payload_offset_bytes, &case.fields)?;
            }
        }
        Ok(())
    }

    fn owner_contains_field(&self, owner: VirTypeId, field: VirFieldId) -> bool {
        match self.kind(owner) {
            Some(VirMemoryTypeKind::Struct { fields }) => {
                fields
                    .iter()
                    .filter(|candidate| **candidate == field)
                    .count()
                    == 1
            }
            Some(VirMemoryTypeKind::Enum { variants }) => {
                variants
                    .iter()
                    .filter_map(|variant| self.variant(*variant))
                    .flat_map(|variant| &variant.fields)
                    .filter(|candidate| **candidate == field)
                    .count()
                    == 1
            }
            _ => false,
        }
    }
}

fn validate_field_ranges(
    schema: &VirMemorySchema,
    owner_layout: &VirLayout,
    base_offset: u64,
    fields: &[VirFieldLayout],
) -> Result<(), VirMemorySchemaError> {
    let mut ranges = Vec::with_capacity(fields.len());
    for field_layout in fields {
        let field = schema
            .field(field_layout.field)
            .filter(|field| field.owner == owner_layout.ty)
            .ok_or_else(|| {
                schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                    layout: owner_layout.id,
                })
            })?;
        let layout = schema
            .ty(field.ty)
            .and_then(|ty| schema.layout(ty.layout))
            .ok_or_else(|| {
                schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                    layout: owner_layout.id,
                })
            })?;
        let start = base_offset
            .checked_add(field_layout.offset_bytes)
            .filter(|offset| {
                owner_layout.alignment >= layout.alignment && *offset % layout.alignment == 0
            })
            .ok_or_else(|| {
                schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                    layout: owner_layout.id,
                })
            })?;
        let end = start
            .checked_add(layout.size_bytes)
            .filter(|end| *end <= owner_layout.size_bytes)
            .ok_or_else(|| {
                schema_error(VirMemorySchemaErrorKind::InvalidLayout {
                    layout: owner_layout.id,
                })
            })?;
        if start < end {
            ranges.push((start, end));
        }
    }
    ranges.sort_unstable();
    if ranges.windows(2).any(|pair| pair[0].1 > pair[1].0) {
        return Err(schema_error(VirMemorySchemaErrorKind::InvalidLayout {
            layout: owner_layout.id,
        }));
    }
    Ok(())
}

fn derive_type_capabilities(schema: &VirMemorySchema, root: VirTypeId) -> Option<TypeCapabilities> {
    fn visit(
        schema: &VirMemorySchema,
        ty: VirTypeId,
        stack: &mut BTreeSet<VirTypeId>,
        depth: usize,
    ) -> Option<TypeCapabilities> {
        if depth >= crate::TYPE_CAPABILITY_MAX_DEPTH {
            return None;
        }
        if !stack.insert(ty) {
            return None;
        }
        let definition = schema.ty(ty)?;
        let child_types = match &definition.kind {
            VirMemoryTypeKind::Array { element, .. } => Some(vec![*element]),
            VirMemoryTypeKind::Tuple(elements) => Some(elements.clone()),
            VirMemoryTypeKind::Struct { fields } => Some(
                fields
                    .iter()
                    .map(|id| schema.field(*id).map(|field| field.ty))
                    .collect::<Option<Vec<_>>>()?,
            ),
            VirMemoryTypeKind::Enum { variants } => Some(
                variants
                    .iter()
                    .map(|id| schema.variant(*id))
                    .collect::<Option<Vec<_>>>()?
                    .into_iter()
                    .flat_map(|variant| variant.fields.iter())
                    .map(|id| schema.field(*id).map(|field| field.ty))
                    .collect::<Option<Vec<_>>>()?,
            ),
            _ => None,
        };
        let result = if let Some(children) = child_types {
            let children = children
                .into_iter()
                .map(|child| visit(schema, child, stack, depth + 1))
                .collect::<Option<Vec<_>>>()?;
            TypeCapabilities {
                value: if children
                    .iter()
                    .all(|capability| capability.value == ValueCapability::Copy)
                {
                    ValueCapability::Copy
                } else {
                    ValueCapability::MoveOnly
                },
                drop: children
                    .iter()
                    .map(|capability| capability.drop)
                    .max()
                    .unwrap_or(DropCapability::TrivialDrop),
                contains_resource: children
                    .iter()
                    .any(|capability| capability.contains_resource),
                size: if schema.layout(definition.layout).is_some()
                    && children
                        .iter()
                        .all(|capability| capability.size == SizeCapability::Sized)
                {
                    SizeCapability::Sized
                } else {
                    SizeCapability::Unsized
                },
            }
        } else {
            let sized = if schema.layout(definition.layout).is_some() {
                SizeCapability::Sized
            } else {
                SizeCapability::Unsized
            };
            match &definition.kind {
                VirMemoryTypeKind::Unit
                | VirMemoryTypeKind::Bool
                | VirMemoryTypeKind::Integer(_)
                | VirMemoryTypeKind::Never => TypeCapabilities {
                    value: ValueCapability::Copy,
                    drop: DropCapability::TrivialDrop,
                    contains_resource: false,
                    size: sized,
                },
                VirMemoryTypeKind::Pointer {
                    pointee,
                    kind,
                    mutability,
                } => {
                    schema.ty(*pointee)?;
                    TypeCapabilities {
                        value: match kind {
                            VirPointerKind::Own => ValueCapability::MoveOnly,
                            VirPointerKind::Raw => ValueCapability::Copy,
                            VirPointerKind::Reference => {
                                if *mutability == VirMutability::Const {
                                    ValueCapability::Copy
                                } else {
                                    ValueCapability::MoveOnly
                                }
                            }
                        },
                        drop: if *kind == VirPointerKind::Own {
                            DropCapability::BuiltinDrop
                        } else {
                            DropCapability::TrivialDrop
                        },
                        contains_resource: true,
                        size: sized,
                    }
                }
                VirMemoryTypeKind::Slice {
                    element,
                    mutability,
                } => {
                    schema.ty(*element)?;
                    TypeCapabilities {
                        value: if *mutability == VirMutability::Const {
                            ValueCapability::Copy
                        } else {
                            ValueCapability::MoveOnly
                        },
                        drop: DropCapability::TrivialDrop,
                        contains_resource: true,
                        size: sized,
                    }
                }
                VirMemoryTypeKind::Array { .. }
                | VirMemoryTypeKind::Tuple(_)
                | VirMemoryTypeKind::Struct { .. }
                | VirMemoryTypeKind::Enum { .. } => unreachable!("aggregate handled above"),
            }
        };
        stack.remove(&ty);
        Some(result)
    }

    visit(schema, root, &mut BTreeSet::new(), 0)
}

fn same_ids<T: Copy + Ord>(expected: &[T], actual: impl Iterator<Item = T>) -> bool {
    let expected_len = expected.len();
    let expected: BTreeSet<_> = expected.iter().copied().collect();
    let actual: Vec<_> = actual.collect();
    let actual_set: BTreeSet<_> = actual.iter().copied().collect();
    expected.len() == expected_len
        && expected_len == actual.len()
        && actual_set.len() == actual.len()
        && expected == actual_set
}

fn align_up(value: u64, alignment: u64) -> Option<u64> {
    value
        .checked_add(alignment.checked_sub(1)?)
        .map(|value| value & !(alignment - 1))
}

fn discriminant_fits(discriminant: u64, tag_size_bytes: u64) -> bool {
    match tag_size_bytes.checked_mul(8) {
        Some(bits) if bits >= u64::BITS.into() => true,
        Some(bits) => u32::try_from(bits)
            .ok()
            .and_then(|bits| 1_u64.checked_shl(bits))
            .is_some_and(|limit| discriminant < limit),
        None => true,
    }
}

fn integer_layout(integer: VirIntegerType, target: VirTargetDataLayout) -> (u64, u64) {
    match integer {
        VirIntegerType::U8 | VirIntegerType::I8 => (1, 1),
        VirIntegerType::U16 | VirIntegerType::I16 => (2, 2),
        VirIntegerType::U32 | VirIntegerType::I32 => (4, 4),
        VirIntegerType::U64 | VirIntegerType::I64 => (8, 8),
        VirIntegerType::U128 | VirIntegerType::I128 => (16, 16),
        VirIntegerType::Usize | VirIntegerType::Isize => {
            (target.usize_size_bytes, target.usize_alignment)
        }
    }
}

fn validate_dense<T>(
    table: &'static str,
    items: &[T],
    id: impl Fn(&T) -> u32,
) -> Result<(), VirMemorySchemaError> {
    for (index, item) in items.iter().enumerate() {
        if usize::try_from(id(item)) != Ok(index) {
            return Err(schema_error(VirMemorySchemaErrorKind::NonDenseTable {
                table,
            }));
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirMemorySchemaError {
    kind: VirMemorySchemaErrorKind,
}

impl VirMemorySchemaError {
    #[must_use]
    pub const fn kind(&self) -> &VirMemorySchemaErrorKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirMemorySchemaErrorKind {
    NonDenseTable { table: &'static str },
    InvalidTarget,
    TypeLayoutMismatch { ty: VirTypeId },
    TypeCapabilityTableMismatch,
    TypeCapabilityMismatch { ty: VirTypeId },
    InvalidType { ty: VirTypeId },
    InvalidLayout { layout: VirLayoutId },
    InvalidField { field: VirFieldId },
    InvalidVariant { variant: VirVariantId },
}

impl fmt::Display for VirMemorySchemaError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "invalid VIR memory schema: {:?}", self.kind)
    }
}

impl Error for VirMemorySchemaError {}

const fn schema_error(kind: VirMemorySchemaErrorKind) -> VirMemorySchemaError {
    VirMemorySchemaError { kind }
}
