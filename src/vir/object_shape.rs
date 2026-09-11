//! Canonical, immutable object shapes derived from [`VirMemorySchema`].

use std::error::Error;
use std::fmt;

use super::{
    VirFieldId, VirLayout, VirMemoryAccess, VirMemorySchema, VirMemorySchemaErrorKind,
    VirMemoryTypeKind, VirTypeId, VirVariantId,
};

/// Maximum number of by-value object nodes expanded by one shape query.
///
/// The fixed limit makes malicious or accidentally enormous array schemas fail
/// deterministically instead of allocating an unbounded byte/leaf table.
pub const VIR_OBJECT_SHAPE_MAX_NODES: usize = 65_536;

/// Maximum nesting depth followed through by-value aggregate children.
pub const VIR_OBJECT_SHAPE_MAX_DEPTH: usize = 256;

/// A half-open byte range relative to the root object queried.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirObjectByteRange {
    start_bytes: u64,
    end_bytes: u64,
}

impl VirObjectByteRange {
    #[must_use]
    pub const fn start_bytes(self) -> u64 {
        self.start_bytes
    }

    #[must_use]
    pub const fn end_bytes(self) -> u64 {
        self.end_bytes
    }

    #[must_use]
    pub const fn len_bytes(self) -> u64 {
        self.end_bytes - self.start_bytes
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start_bytes == self.end_bytes
    }

    const fn new(start_bytes: u64, end_bytes: u64) -> Self {
        Self {
            start_bytes,
            end_bytes,
        }
    }
}

/// One canonical step from a root object to a nested object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirObjectPathSegment {
    TupleElement(u64),
    Field(VirFieldId),
    ArrayElement(u64),
    Variant(VirVariantId),
}

/// Canonical nominal/index path of a nested object.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirObjectPath(Vec<VirObjectPathSegment>);

impl VirObjectPath {
    #[must_use]
    pub fn segments(&self) -> &[VirObjectPathSegment] {
        &self.0
    }

    fn child(&self, segment: VirObjectPathSegment) -> Self {
        let mut segments = self.0.clone();
        segments.push(segment);
        Self(segments)
    }
}

/// A scalar leaf that may be active in the root object's representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirObjectLeaf {
    path: VirObjectPath,
    access: VirMemoryAccess,
    bytes: VirObjectByteRange,
}

/// Canonical typed resource leaf derived from an object shape.
///
/// All consumers share this projection; no verifier/backend-owned resource
/// layout table is permitted. The path includes enum variant segments and is
/// therefore also the leaf's active-representation condition.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirObjectResourceLeaf {
    path: VirObjectPath,
    access: VirMemoryAccess,
    pointee_access: VirMemoryAccess,
    kind: super::VirPointerKind,
    mutability: super::VirMutability,
    bytes: VirObjectByteRange,
}

impl VirObjectResourceLeaf {
    #[must_use]
    pub const fn path(&self) -> &VirObjectPath {
        &self.path
    }

    #[must_use]
    pub const fn access(&self) -> VirMemoryAccess {
        self.access
    }

    #[must_use]
    pub const fn pointee_access(&self) -> VirMemoryAccess {
        self.pointee_access
    }

    #[must_use]
    pub const fn kind(&self) -> super::VirPointerKind {
        self.kind
    }

    #[must_use]
    pub const fn mutability(&self) -> super::VirMutability {
        self.mutability
    }

    #[must_use]
    pub const fn bytes(&self) -> VirObjectByteRange {
        self.bytes
    }
}

impl VirObjectLeaf {
    #[must_use]
    pub const fn path(&self) -> &VirObjectPath {
        &self.path
    }

    #[must_use]
    pub const fn access(&self) -> VirMemoryAccess {
        self.access
    }

    #[must_use]
    pub const fn bytes(&self) -> VirObjectByteRange {
        self.bytes
    }
}

/// Canonical stride and physical extent of one fixed array subobject.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirObjectArrayShape {
    path: VirObjectPath,
    access: VirMemoryAccess,
    element_access: VirMemoryAccess,
    stride_bytes: u64,
    length: u64,
    extent: VirObjectByteRange,
}

impl VirObjectArrayShape {
    #[must_use]
    pub const fn path(&self) -> &VirObjectPath {
        &self.path
    }

    #[must_use]
    pub const fn access(&self) -> VirMemoryAccess {
        self.access
    }

    #[must_use]
    pub const fn element_access(&self) -> VirMemoryAccess {
        self.element_access
    }

    #[must_use]
    pub const fn stride_bytes(&self) -> u64 {
        self.stride_bytes
    }

    #[must_use]
    pub const fn length(&self) -> u64 {
        self.length
    }

    #[must_use]
    pub const fn extent(&self) -> VirObjectByteRange {
        self.extent
    }
}

/// The active byte shape of one enum case.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirObjectVariantShape {
    path: VirObjectPath,
    enum_access: VirMemoryAccess,
    variant: VirVariantId,
    discriminant: u64,
    tag: VirObjectByteRange,
    payload: VirObjectByteRange,
    leaves: Vec<VirObjectLeaf>,
    value_bytes: Vec<VirObjectByteRange>,
    padding: Vec<VirObjectByteRange>,
}

impl VirObjectVariantShape {
    #[must_use]
    pub const fn path(&self) -> &VirObjectPath {
        &self.path
    }

    #[must_use]
    pub const fn enum_access(&self) -> VirMemoryAccess {
        self.enum_access
    }

    #[must_use]
    pub const fn variant(&self) -> VirVariantId {
        self.variant
    }

    #[must_use]
    pub const fn discriminant(&self) -> u64 {
        self.discriminant
    }

    #[must_use]
    pub const fn tag(&self) -> VirObjectByteRange {
        self.tag
    }

    #[must_use]
    pub const fn payload(&self) -> VirObjectByteRange {
        self.payload
    }

    #[must_use]
    pub fn leaves(&self) -> &[VirObjectLeaf] {
        &self.leaves
    }

    #[must_use]
    pub fn value_bytes(&self) -> &[VirObjectByteRange] {
        &self.value_bytes
    }

    #[must_use]
    pub fn padding(&self) -> &[VirObjectByteRange] {
        &self.padding
    }
}

/// Canonical shape of one sized, addressable VIR object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirObjectShape {
    access: VirMemoryAccess,
    size_bytes: u64,
    alignment: u64,
    leaves: Vec<VirObjectLeaf>,
    resource_leaves: Vec<VirObjectResourceLeaf>,
    value_bytes: Vec<VirObjectByteRange>,
    padding: Vec<VirObjectByteRange>,
    arrays: Vec<VirObjectArrayShape>,
    variants: Vec<VirObjectVariantShape>,
}

impl VirObjectShape {
    #[must_use]
    pub const fn access(&self) -> VirMemoryAccess {
        self.access
    }

    #[must_use]
    pub const fn size_bytes(&self) -> u64 {
        self.size_bytes
    }

    #[must_use]
    pub const fn alignment(&self) -> u64 {
        self.alignment
    }

    /// All scalar leaves that can be active in some representation.
    ///
    /// Leaves from distinct enum cases may overlap physically. Use
    /// [`VirObjectVariantShape::leaves`] when reasoning about one active case.
    #[must_use]
    pub fn leaves(&self) -> &[VirObjectLeaf] {
        &self.leaves
    }

    /// Pointer/resource leaves in the same canonical order as [`Self::leaves`].
    #[must_use]
    pub fn resource_leaves(&self) -> &[VirObjectResourceLeaf] {
        &self.resource_leaves
    }

    /// Retirement of partial storage must not discard authority or require
    /// reading an active-variant tag to discover which bytes exist.
    #[must_use]
    pub fn supports_storage_reset(&self) -> bool {
        self.resource_leaves.is_empty() && self.variants.is_empty()
    }

    #[must_use]
    pub fn supports_resource_storage_reset(&self) -> bool {
        !self.resource_leaves.is_empty()
            && self.variants.is_empty()
            && self
                .resource_leaves
                .iter()
                .all(|leaf| leaf.kind() != super::VirPointerKind::Raw)
    }

    /// Union of bytes that carry a value in at least one representation.
    #[must_use]
    pub fn value_bytes(&self) -> &[VirObjectByteRange] {
        &self.value_bytes
    }

    /// Bytes that never carry a value in any representation.
    #[must_use]
    pub fn padding(&self) -> &[VirObjectByteRange] {
        &self.padding
    }

    #[must_use]
    pub fn arrays(&self) -> &[VirObjectArrayShape] {
        &self.arrays
    }

    #[must_use]
    pub fn variants(&self) -> &[VirObjectVariantShape] {
        &self.variants
    }
}

impl VirMemorySchema {
    /// Derives the one canonical object shape for `access` without mutating the
    /// schema or storing a parallel layout table.
    pub fn object_shape(
        &self,
        access: VirMemoryAccess,
    ) -> Result<VirObjectShape, VirObjectShapeError> {
        self.validate().map_err(|error| {
            shape_error(VirObjectShapeErrorKind::InvalidSchema(error.kind().clone()))
        })?;
        if !self.resolves_access(access) {
            return Err(shape_error(VirObjectShapeErrorKind::InvalidAccess {
                access,
            }));
        }

        let layout = self.layout(access.layout).expect("validated access layout");
        let mut builder = ObjectShapeBuilder {
            schema: self,
            root_size: layout.size_bytes,
            nodes: 0,
            stack: Vec::new(),
        };
        let mut built = builder.build(access, 0, &VirObjectPath::default())?;
        built.canonicalize();
        let resource_leaves = built
            .leaves
            .iter()
            .filter_map(|leaf| {
                let VirMemoryTypeKind::Pointer {
                    pointee,
                    kind,
                    mutability,
                } = self.kind(leaf.access.ty)?
                else {
                    return None;
                };
                Some(VirObjectResourceLeaf {
                    path: leaf.path.clone(),
                    access: leaf.access,
                    pointee_access: self.access(*pointee)?,
                    kind: *kind,
                    mutability: *mutability,
                    bytes: leaf.bytes,
                })
            })
            .collect();
        let whole = VirObjectByteRange::new(0, layout.size_bytes);
        let padding = built.value_bytes.complement(whole);
        Ok(VirObjectShape {
            access,
            size_bytes: layout.size_bytes,
            alignment: layout.alignment,
            leaves: built.leaves,
            resource_leaves,
            value_bytes: built.value_bytes.into_ranges(),
            padding,
            arrays: built.arrays,
            variants: built.variants,
        })
    }
}

struct ObjectShapeBuilder<'schema> {
    schema: &'schema VirMemorySchema,
    root_size: u64,
    nodes: usize,
    stack: Vec<VirTypeId>,
}

impl ObjectShapeBuilder<'_> {
    fn build(
        &mut self,
        access: VirMemoryAccess,
        base: u64,
        path: &VirObjectPath,
    ) -> Result<BuiltObject, VirObjectShapeError> {
        self.reserve_nodes(access, 1)?;

        let ty = self
            .schema
            .ty(access.ty)
            .filter(|ty| ty.layout == access.layout)
            .expect("root and derived accesses belong to a validated schema");
        let layout = self
            .schema
            .layout(access.layout)
            .filter(|layout| layout.ty == access.ty)
            .expect("root and derived layouts belong to a validated schema");
        let object_end = checked_add(base, layout.size_bytes, access)?;
        if object_end > self.root_size {
            return Err(shape_error(VirObjectShapeErrorKind::OutOfBounds { access }));
        }

        let kind = ty.kind.clone();
        if matches!(kind, VirMemoryTypeKind::Slice { .. }) {
            return Err(shape_error(
                VirObjectShapeErrorKind::UnsupportedObjectType { ty: access.ty },
            ));
        }

        let follows_children = matches!(
            kind,
            VirMemoryTypeKind::Array { .. }
                | VirMemoryTypeKind::Tuple(_)
                | VirMemoryTypeKind::Struct { .. }
                | VirMemoryTypeKind::Enum { .. }
        );
        if follows_children {
            if self.stack.contains(&access.ty) {
                return Err(shape_error(VirObjectShapeErrorKind::RecursiveAggregate {
                    ty: access.ty,
                }));
            }
            if self.stack.len() >= VIR_OBJECT_SHAPE_MAX_DEPTH {
                return Err(shape_error(VirObjectShapeErrorKind::NestingLimitExceeded {
                    access,
                    limit: VIR_OBJECT_SHAPE_MAX_DEPTH,
                }));
            }
            self.stack.push(access.ty);
        }

        let result = match kind {
            VirMemoryTypeKind::Unit | VirMemoryTypeKind::Never => Ok(BuiltObject::default()),
            VirMemoryTypeKind::Bool
            | VirMemoryTypeKind::Integer(_)
            | VirMemoryTypeKind::Pointer { .. } => {
                let bytes = VirObjectByteRange::new(base, object_end);
                Ok(BuiltObject {
                    leaves: vec![VirObjectLeaf {
                        path: path.clone(),
                        access,
                        bytes,
                    }],
                    value_bytes: ByteRangeSet::from_range(bytes),
                    ..BuiltObject::default()
                })
            }
            VirMemoryTypeKind::Array { element, length } => {
                self.build_array(access, layout, element, length, base, path)
            }
            VirMemoryTypeKind::Tuple(elements) => {
                self.build_tuple(access, layout, &elements, base, path)
            }
            VirMemoryTypeKind::Struct { mut fields } => {
                fields.sort_unstable();
                self.build_fields(access, layout, &fields, &layout.fields, base, path)
            }
            VirMemoryTypeKind::Enum { mut variants } => {
                variants.sort_unstable();
                self.build_enum(access, layout, &variants, base, path)
            }
            VirMemoryTypeKind::Slice { .. } => unreachable!("slice rejected above"),
        };

        if follows_children {
            let popped = self.stack.pop();
            debug_assert_eq!(popped, Some(access.ty));
        }
        result
    }

    fn build_array(
        &mut self,
        access: VirMemoryAccess,
        layout: &VirLayout,
        element: VirTypeId,
        length: u64,
        base: u64,
        path: &VirObjectPath,
    ) -> Result<BuiltObject, VirObjectShapeError> {
        let element_access = self.access(element);
        let element_layout = self.layout(element_access);
        let stride_bytes = element_layout.size_bytes;
        let extent_len = checked_mul(stride_bytes, length, access)?;
        let extent_end = checked_add(base, extent_len, access)?;
        if extent_len > layout.size_bytes {
            return Err(shape_error(VirObjectShapeErrorKind::LayoutMismatch {
                access,
            }));
        }
        let remaining = VIR_OBJECT_SHAPE_MAX_NODES.saturating_sub(self.nodes);
        if usize::try_from(length).map_or(true, |length| length > remaining) {
            return Err(shape_error(
                VirObjectShapeErrorKind::ComplexityLimitExceeded {
                    access,
                    limit: VIR_OBJECT_SHAPE_MAX_NODES,
                },
            ));
        }

        let mut built = BuiltObject::default();
        built.arrays.push(VirObjectArrayShape {
            path: path.clone(),
            access,
            element_access,
            stride_bytes,
            length,
            extent: VirObjectByteRange::new(base, extent_end),
        });
        for index in 0..length {
            let offset = checked_mul(stride_bytes, index, access)?;
            let child_base = checked_add(base, offset, access)?;
            let child_path = path.child(VirObjectPathSegment::ArrayElement(index));
            let child = self.build(element_access, child_base, &child_path)?;
            built.absorb(child);
        }
        Ok(built)
    }

    fn build_tuple(
        &mut self,
        access: VirMemoryAccess,
        layout: &VirLayout,
        elements: &[VirTypeId],
        base: u64,
        path: &VirObjectPath,
    ) -> Result<BuiltObject, VirObjectShapeError> {
        let mut built = BuiltObject::default();
        let mut cursor = 0_u64;
        for (index, element) in elements.iter().copied().enumerate() {
            let element_access = self.access(element);
            let element_layout = self.layout(element_access);
            let element_alignment = element_layout.alignment;
            let element_size = element_layout.size_bytes;
            if layout.alignment < element_alignment {
                return Err(shape_error(VirObjectShapeErrorKind::LayoutMismatch {
                    access,
                }));
            }
            cursor = align_up(cursor, element_alignment, access)?;
            let child_base = checked_add(base, cursor, access)?;
            let index = u64::try_from(index)
                .map_err(|_| shape_error(VirObjectShapeErrorKind::ArithmeticOverflow { access }))?;
            let child_path = path.child(VirObjectPathSegment::TupleElement(index));
            let child = self.build(element_access, child_base, &child_path)?;
            built.absorb(child);
            cursor = checked_add(cursor, element_size, access)?;
        }
        let expected_size = align_up(cursor, layout.alignment, access)?;
        if expected_size != layout.size_bytes {
            return Err(shape_error(VirObjectShapeErrorKind::LayoutMismatch {
                access,
            }));
        }
        Ok(built)
    }

    fn build_fields(
        &mut self,
        access: VirMemoryAccess,
        _layout: &VirLayout,
        fields: &[VirFieldId],
        field_layouts: &[super::VirFieldLayout],
        base: u64,
        path: &VirObjectPath,
    ) -> Result<BuiltObject, VirObjectShapeError> {
        let mut built = BuiltObject::default();
        for field_id in fields.iter().copied() {
            let field = self.schema.field(field_id).expect("validated field");
            let field_layout = field_layouts
                .iter()
                .find(|candidate| candidate.field == field_id)
                .expect("validated field layout");
            let child_access = self.access(field.ty);
            let child_base = checked_add(base, field_layout.offset_bytes, access)?;
            let child_path = path.child(VirObjectPathSegment::Field(field_id));
            let child = self.build(child_access, child_base, &child_path)?;
            built.absorb(child);
        }
        Ok(built)
    }

    fn build_enum(
        &mut self,
        access: VirMemoryAccess,
        layout: &VirLayout,
        variants: &[VirVariantId],
        base: u64,
        path: &VirObjectPath,
    ) -> Result<BuiltObject, VirObjectShapeError> {
        let variant_layout = layout.variants.as_ref().expect("validated enum layout");
        self.reserve_nodes(access, variants.len())?;
        let tag_end = checked_add(base, variant_layout.tag_size_bytes, access)?;
        let tag = VirObjectByteRange::new(base, tag_end);
        let whole = VirObjectByteRange::new(base, checked_add(base, layout.size_bytes, access)?);
        let mut built = BuiltObject::default();

        for variant_id in variants.iter().copied() {
            let variant = self.schema.variant(variant_id).expect("validated variant");
            let case_layout = variant_layout
                .cases
                .iter()
                .find(|candidate| candidate.variant == variant_id)
                .expect("validated enum case layout");
            let case_path = path.child(VirObjectPathSegment::Variant(variant_id));
            let mut fields = variant.fields.clone();
            fields.sort_unstable();
            let payload_base = checked_add(base, case_layout.payload_offset_bytes, access)?;
            let mut payload_end = payload_base;
            for field_id in fields.iter().copied() {
                let field = self
                    .schema
                    .field(field_id)
                    .expect("validated variant field");
                let field_layout = case_layout
                    .fields
                    .iter()
                    .find(|candidate| candidate.field == field_id)
                    .expect("validated variant field layout");
                let child_access = self.access(field.ty);
                let child_layout = self.layout(child_access);
                let child_offset = checked_add(
                    case_layout.payload_offset_bytes,
                    field_layout.offset_bytes,
                    access,
                )?;
                let child_base = checked_add(base, child_offset, access)?;
                let child_end = checked_add(child_base, child_layout.size_bytes, access)?;
                payload_end = payload_end.max(child_end);
            }

            let mut case_built = self.build_fields(
                access,
                layout,
                &fields,
                &case_layout.fields,
                payload_base,
                &case_path,
            )?;
            case_built.value_bytes.insert(tag);
            case_built.canonicalize();
            let case_padding = case_built.value_bytes.complement(whole);
            let case_shape = VirObjectVariantShape {
                path: path.clone(),
                enum_access: access,
                variant: variant_id,
                discriminant: variant.discriminant,
                tag,
                payload: VirObjectByteRange::new(payload_base, payload_end),
                leaves: case_built.leaves.clone(),
                value_bytes: case_built.value_bytes.clone().into_ranges(),
                padding: case_padding,
            };

            built.leaves.extend(case_built.leaves);
            built.arrays.extend(case_built.arrays);
            built.variants.push(case_shape);
            built.variants.extend(case_built.variants);
            built.value_bytes.extend(case_built.value_bytes);
        }
        Ok(built)
    }

    fn access(&self, ty: VirTypeId) -> VirMemoryAccess {
        self.schema.access(ty).expect("validated child type")
    }

    fn layout(&self, access: VirMemoryAccess) -> &VirLayout {
        self.schema
            .layout(access.layout)
            .expect("validated child layout")
    }

    fn reserve_nodes(
        &mut self,
        access: VirMemoryAccess,
        additional: usize,
    ) -> Result<(), VirObjectShapeError> {
        self.nodes = self.nodes.checked_add(additional).ok_or_else(|| {
            shape_error(VirObjectShapeErrorKind::ComplexityLimitExceeded {
                access,
                limit: VIR_OBJECT_SHAPE_MAX_NODES,
            })
        })?;
        if self.nodes > VIR_OBJECT_SHAPE_MAX_NODES {
            return Err(shape_error(
                VirObjectShapeErrorKind::ComplexityLimitExceeded {
                    access,
                    limit: VIR_OBJECT_SHAPE_MAX_NODES,
                },
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
struct BuiltObject {
    leaves: Vec<VirObjectLeaf>,
    arrays: Vec<VirObjectArrayShape>,
    variants: Vec<VirObjectVariantShape>,
    value_bytes: ByteRangeSet,
}

impl BuiltObject {
    fn absorb(&mut self, child: Self) {
        self.leaves.extend(child.leaves);
        self.arrays.extend(child.arrays);
        self.variants.extend(child.variants);
        self.value_bytes.extend(child.value_bytes);
    }

    fn canonicalize(&mut self) {
        self.leaves.sort_unstable();
        self.arrays.sort_unstable();
        self.variants.sort_unstable();
        self.value_bytes.normalize();
    }
}

#[derive(Clone, Debug, Default)]
struct ByteRangeSet {
    ranges: Vec<VirObjectByteRange>,
}

impl ByteRangeSet {
    fn from_range(range: VirObjectByteRange) -> Self {
        let mut set = Self::default();
        set.insert(range);
        set
    }

    fn insert(&mut self, range: VirObjectByteRange) {
        if range.is_empty() {
            return;
        }
        self.ranges.push(range);
    }

    fn normalize(&mut self) {
        self.ranges.sort_unstable();
        let mut merged: Vec<VirObjectByteRange> = Vec::with_capacity(self.ranges.len());
        for range in self.ranges.drain(..) {
            if let Some(last) = merged.last_mut()
                && range.start_bytes <= last.end_bytes
            {
                last.end_bytes = last.end_bytes.max(range.end_bytes);
                continue;
            }
            merged.push(range);
        }
        self.ranges = merged;
    }

    fn extend(&mut self, other: Self) {
        self.ranges.extend(other.ranges);
    }

    fn complement(&self, whole: VirObjectByteRange) -> Vec<VirObjectByteRange> {
        let mut cursor = whole.start_bytes;
        let mut complement = Vec::new();
        for range in &self.ranges {
            debug_assert!(range.start_bytes >= whole.start_bytes);
            debug_assert!(range.end_bytes <= whole.end_bytes);
            if cursor < range.start_bytes {
                complement.push(VirObjectByteRange::new(cursor, range.start_bytes));
            }
            cursor = cursor.max(range.end_bytes);
        }
        if cursor < whole.end_bytes {
            complement.push(VirObjectByteRange::new(cursor, whole.end_bytes));
        }
        complement
    }

    fn into_ranges(self) -> Vec<VirObjectByteRange> {
        self.ranges
    }
}

fn checked_add(left: u64, right: u64, access: VirMemoryAccess) -> Result<u64, VirObjectShapeError> {
    left.checked_add(right)
        .ok_or_else(|| shape_error(VirObjectShapeErrorKind::ArithmeticOverflow { access }))
}

fn checked_mul(left: u64, right: u64, access: VirMemoryAccess) -> Result<u64, VirObjectShapeError> {
    left.checked_mul(right)
        .ok_or_else(|| shape_error(VirObjectShapeErrorKind::ArithmeticOverflow { access }))
}

fn align_up(
    value: u64,
    alignment: u64,
    access: VirMemoryAccess,
) -> Result<u64, VirObjectShapeError> {
    checked_add(value, alignment - 1, access).map(|value| value & !(alignment - 1))
}

/// Failure to derive a safe, finite object shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirObjectShapeError {
    kind: VirObjectShapeErrorKind,
}

impl VirObjectShapeError {
    #[must_use]
    pub const fn kind(&self) -> &VirObjectShapeErrorKind {
        &self.kind
    }
}

/// Fail-closed reasons emitted by [`VirMemorySchema::object_shape`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirObjectShapeErrorKind {
    InvalidSchema(VirMemorySchemaErrorKind),
    InvalidAccess {
        access: VirMemoryAccess,
    },
    UnsupportedObjectType {
        ty: VirTypeId,
    },
    RecursiveAggregate {
        ty: VirTypeId,
    },
    ArithmeticOverflow {
        access: VirMemoryAccess,
    },
    OutOfBounds {
        access: VirMemoryAccess,
    },
    LayoutMismatch {
        access: VirMemoryAccess,
    },
    ComplexityLimitExceeded {
        access: VirMemoryAccess,
        limit: usize,
    },
    NestingLimitExceeded {
        access: VirMemoryAccess,
        limit: usize,
    },
}

impl fmt::Display for VirObjectShapeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "cannot derive VIR object shape: {:?}", self.kind)
    }
}

impl Error for VirObjectShapeError {}

const fn shape_error(kind: VirObjectShapeErrorKind) -> VirObjectShapeError {
    VirObjectShapeError { kind }
}
