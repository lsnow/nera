//! Canonical subobject/sequence layouts shared by VIR address consumers.
//!
//! These descriptors establish layout and source structure, never liveness,
//! numeric bounds, allocation-instance identity or access authority.

mod catalog;
pub use catalog::{
    VirAddressStep, VirPointerDescription, VirPointerKey, VirPointerSource, VirProvenanceCatalog,
};

use super::{
    VIR_OBJECT_SHAPE_MAX_DEPTH, VirFieldId, VirIndexBounds, VirMemoryAccess, VirMemorySchema,
    VirMemoryTypeKind, VirObjectPathSegment, VirValueId,
};

/// Arithmetic extent, independent from read/write/free authority. Unknown is
/// never widened back to the enclosing allocation after a join or lost symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirPointerDomain<R> {
    Allocation,
    Restricted(R),
    Unknown,
}

/// Exact bounded nominal path, not a hash. Array ordinals are represented by
/// the separately checked domain endpoints; array nesting itself is retained.
/// Overflow loses comparison precision, never merges two different paths.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirNominalPath {
    root: VirNominalRoot,
    steps: [u32; 8],
    len: u8,
}

/// Parameter roots are local existential anchors, never concrete root layouts.
/// An incoming arithmetic domain need not equal the pointee's object domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum VirNominalRoot {
    Object(VirMemoryAccess),
    Parameter {
        access: VirMemoryAccess,
        function: super::VirFunctionId,
        index: u32,
        role: ParameterPathRole,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ParameterPathRole {
    Object,
    IncomingDomain,
    SelectedDomain,
}

type NominalInterfaceParts<'a> = (VirMemoryAccess, Option<(u32, u8)>, &'a [u32]);

impl VirNominalPath {
    /// Read-only decomposition for signature-relative verifier artifacts. The
    /// function-local anchor is checked here and never exported by summaries.
    pub(crate) fn interface_parts(
        &self,
        function: super::VirFunctionId,
    ) -> Option<NominalInterfaceParts<'_>> {
        let (access, parameter) = match self.root {
            VirNominalRoot::Object(access) => (access, None),
            VirNominalRoot::Parameter {
                access,
                function: owner,
                index,
                role,
            } => {
                if owner != function {
                    return None;
                }
                let role = match role {
                    ParameterPathRole::Object => 0,
                    ParameterPathRole::IncomingDomain => 1,
                    ParameterPathRole::SelectedDomain => 2,
                };
                (access, Some((index, role)))
            }
        };
        Some((access, parameter, &self.steps[..usize::from(self.len)]))
    }

    pub const fn root(root: VirMemoryAccess) -> Self {
        Self {
            root: VirNominalRoot::Object(root),
            steps: [0; 8],
            len: 0,
        }
    }
    pub fn extend(mut self, path: &[VirObjectPathSegment]) -> Option<Self> {
        for step in path {
            let (id, tag) = match step {
                VirObjectPathSegment::Field(id) => (id.get(), 0),
                VirObjectPathSegment::Variant(id) => (id.get(), 1),
                VirObjectPathSegment::TupleElement(index) => (u32::try_from(*index).ok()?, 2),
                VirObjectPathSegment::ArrayElement(_) => (0, 3),
            };
            let encoded = id.checked_mul(4)?.checked_add(tag)?;
            *self.steps.get_mut(usize::from(self.len))? = encoded;
            self.len += 1;
        }
        Some(self)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct VirPointerPaths {
    pub object: Option<VirNominalPath>,
    pub domain: Option<VirNominalPath>,
}

impl VirPointerPaths {
    /// Scoped names for an unknown caller object and its incoming domain.
    /// They establish correlation only among derivations of this parameter.
    pub fn parameter(access: VirMemoryAccess, function: super::VirFunctionId, index: u32) -> Self {
        let path = |role| VirNominalPath {
            root: VirNominalRoot::Parameter {
                access,
                function,
                index,
                role,
            },
            steps: [0; 8],
            len: 0,
        };
        Self {
            object: Some(path(ParameterPathRole::Object)),
            domain: Some(path(ParameterPathRole::IncomingDomain)),
        }
    }

    /// A selected slice has exact endpoints. The input parameter guarantees
    /// only containment in its incoming domain, not equality with that domain.
    pub fn selected(mut self) -> Self {
        if let Some(path) = &mut self.domain
            && let VirNominalRoot::Parameter { role, .. } = &mut path.root
            && *role == ParameterPathRole::IncomingDomain
        {
            *role = ParameterPathRole::SelectedDomain;
        }
        self
    }
    pub const fn root(access: VirMemoryAccess) -> Self {
        Self {
            object: Some(VirNominalPath::root(access)),
            domain: Some(VirNominalPath::root(access)),
        }
    }
    pub fn project(self, object: &VirSubobject) -> Self {
        Self {
            object: self.object.and_then(|p| p.extend(object.path())),
            domain: self.object.and_then(|p| p.extend(object.domain_path())),
        }
    }
    pub fn element(self) -> Self {
        Self {
            object: self
                .object
                .and_then(|p| p.extend(&[VirObjectPathSegment::ArrayElement(0)])),
            domain: self.object,
        }
    }
    pub fn join(self, other: Self) -> Self {
        Self {
            object: (self.object == other.object)
                .then_some(self.object)
                .flatten(),
            domain: (self.domain == other.domain)
                .then_some(self.domain)
                .flatten(),
        }
    }
}

/// Layout-derived subobject and its immediate arithmetic domain. Offsets are
/// relative to the queried object, never machine addresses or permissions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSubobject {
    root: VirMemoryAccess,
    path: Vec<VirObjectPathSegment>,
    access: VirMemoryAccess,
    offset_bytes: u64,
    size_bytes: u64,
    domain_path: Vec<VirObjectPathSegment>,
    domain_offset_bytes: u64,
    domain_size_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VirSequenceExtent {
    Array {
        length: u64,
        size_bytes: u64,
    },
    /// Metadata operand, not a proven allocation extent or permission range.
    Slice {
        length: VirValueId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VirSequence {
    source: VirMemoryAccess,
    element: VirMemoryAccess,
    stride_bytes: u64,
    extent: VirSequenceExtent,
}

impl VirSequence {
    pub const fn source(self) -> VirMemoryAccess {
        self.source
    }
    pub const fn element(self) -> VirMemoryAccess {
        self.element
    }
    pub const fn stride_bytes(self) -> u64 {
        self.stride_bytes
    }
    pub const fn extent(self) -> VirSequenceExtent {
        self.extent
    }
}

impl VirSubobject {
    pub const fn root(&self) -> VirMemoryAccess {
        self.root
    }
    pub fn path(&self) -> &[VirObjectPathSegment] {
        &self.path
    }
    pub const fn access(&self) -> VirMemoryAccess {
        self.access
    }
    pub const fn offset_bytes(&self) -> u64 {
        self.offset_bytes
    }
    pub const fn size_bytes(&self) -> u64 {
        self.size_bytes
    }
    pub fn domain_path(&self) -> &[VirObjectPathSegment] {
        &self.domain_path
    }
    pub const fn domain_offset_bytes(&self) -> u64 {
        self.domain_offset_bytes
    }
    pub const fn domain_size_bytes(&self) -> u64 {
        self.domain_size_bytes
    }
}

impl VirMemorySchema {
    /// Canonical sized pointee and readonly qualifier of a raw-address result.
    #[must_use]
    pub fn raw_address_pointee(
        &self,
        raw: VirMemoryAccess,
    ) -> Option<(VirMemoryAccess, super::VirMutability)> {
        if self.access(raw.ty)? != raw {
            return None;
        }
        let super::VirMemoryTypeKind::Pointer {
            pointee,
            kind: super::VirPointerKind::Raw,
            mutability,
        } = self.kind(raw.ty)?
        else {
            return None;
        };
        let access = self.access(*pointee)?;
        if self.layout(access.layout)?.size_bytes == 0
            || matches!(
                self.kind(access.ty)?,
                super::VirMemoryTypeKind::Slice { .. }
            )
        {
            return None;
        }
        Some((access, *mutability))
    }
    /// Shared schema rule for fixed arrays and dynamic slice views. Numeric
    /// length/index bounds remain verifier/runtime obligations.
    pub fn sequence(&self, source: VirMemoryAccess, bounds: VirIndexBounds) -> Option<VirSequence> {
        if !self.resolves_access(source) {
            return None;
        }
        let (element, length) = match (self.kind(source.ty)?, bounds) {
            (
                VirMemoryTypeKind::Array { element, length },
                VirIndexBounds::Array { length: actual },
            ) if *length == actual => (*element, Some(actual)),
            (VirMemoryTypeKind::Slice { element, .. }, VirIndexBounds::Slice { .. }) => {
                (*element, None)
            }
            _ => return None,
        };
        let element = self.access(element)?;
        let stride_bytes = self.layout(element.layout)?.size_bytes;
        if stride_bytes == 0 {
            return None;
        }
        let extent = match (length, bounds) {
            (Some(length), _) => {
                let size_bytes = stride_bytes.checked_mul(length)?;
                // A valid array layout may have stronger alignment and tail
                // padding. Element arithmetic excludes that trailing padding.
                if self.layout(source.layout)?.size_bytes < size_bytes {
                    return None;
                }
                VirSequenceExtent::Array { length, size_bytes }
            }
            (None, VirIndexBounds::Slice { length }) => VirSequenceExtent::Slice { length },
            _ => return None,
        };
        Some(VirSequence {
            source,
            element,
            stride_bytes,
            extent,
        })
    }

    pub fn slice_sequence(
        &self,
        source: VirMemoryAccess,
        slice: VirMemoryAccess,
        bounds: VirIndexBounds,
    ) -> Option<VirSequence> {
        let sequence = self.sequence(source, bounds)?;
        if !self.resolves_access(slice) {
            return None;
        }
        let VirMemoryTypeKind::Slice {
            element,
            mutability,
        } = self.kind(slice.ty)?
        else {
            return None;
        };
        if *element != sequence.element.ty {
            return None;
        }
        if let Some(VirMemoryTypeKind::Slice {
            mutability: source_mutability,
            ..
        }) = self.kind(source.ty)
        {
            if *mutability == super::VirMutability::Mutable
                && *source_mutability != super::VirMutability::Mutable
            {
                return None;
            }
        }
        Some(sequence)
    }

    /// Resolves only the requested path, in O(path length), without enumerating
    /// array elements. A variant selector must be followed by its actual field.
    /// A valid path/layout establishes neither active variant nor live storage.
    pub fn subobject(
        &self,
        root: VirMemoryAccess,
        path: &[VirObjectPathSegment],
    ) -> Option<VirSubobject> {
        if !self.resolves_access(root) || path.len() > VIR_OBJECT_SHAPE_MAX_DEPTH {
            return None;
        }
        let mut object = VirSubobject {
            root,
            path: Vec::new(),
            access: root,
            offset_bytes: 0,
            size_bytes: self.layout(root.layout)?.size_bytes,
            domain_path: Vec::new(),
            domain_offset_bytes: 0,
            domain_size_bytes: self.layout(root.layout)?.size_bytes,
        };
        let mut variant = None;
        for segment in path {
            let owner = object.access;
            let (access, delta, array_domain_size) = match *segment {
                VirObjectPathSegment::Variant(id) => {
                    if variant.is_some() {
                        return None;
                    }
                    let VirMemoryTypeKind::Enum { variants } = self.kind(owner.ty)? else {
                        return None;
                    };
                    if !variants.contains(&id) || self.variant(id)?.owner != owner.ty {
                        return None;
                    }
                    variant = Some(id);
                    object.path.push(*segment);
                    continue;
                }
                VirObjectPathSegment::Field(id) => {
                    let field = self.field(id)?;
                    if field.owner != owner.ty {
                        return None;
                    }
                    let layout = self.layout(owner.layout)?;
                    let offset = if let Some(id) = variant.take() {
                        if !self.variant(id)?.fields.contains(&field.id) {
                            return None;
                        }
                        let case = layout
                            .variants
                            .as_ref()?
                            .cases
                            .iter()
                            .find(|c| c.variant == id)?;
                        case.payload_offset_bytes.checked_add(
                            case.fields
                                .iter()
                                .find(|f| f.field == field.id)?
                                .offset_bytes,
                        )?
                    } else {
                        let VirMemoryTypeKind::Struct { fields } = self.kind(owner.ty)? else {
                            return None;
                        };
                        if !fields.contains(&id) {
                            return None;
                        }
                        layout.fields.iter().find(|f| f.field == id)?.offset_bytes
                    };
                    (self.access(field.ty)?, offset, None)
                }
                VirObjectPathSegment::TupleElement(index) => {
                    if variant.is_some() {
                        return None;
                    }
                    let (access, offset) = self.tuple_element_projection(owner, index)?;
                    (access, offset, None)
                }
                VirObjectPathSegment::ArrayElement(index) => {
                    if variant.is_some() {
                        return None;
                    }
                    let VirMemoryTypeKind::Array { element, length } = self.kind(owner.ty)? else {
                        return None;
                    };
                    if index >= *length {
                        return None;
                    }
                    let access = self.access(*element)?;
                    (
                        access,
                        index.checked_mul(self.layout(access.layout)?.size_bytes)?,
                        Some(length.checked_mul(self.layout(access.layout)?.size_bytes)?),
                    )
                }
            };
            let size = self.layout(access.layout)?.size_bytes;
            if delta.checked_add(size)? > object.size_bytes {
                return None;
            }
            if let Some(array_size) = array_domain_size {
                object.domain_path = object.path.clone();
                object.domain_offset_bytes = object.offset_bytes;
                object.domain_size_bytes = array_size;
            }
            object.path.push(*segment);
            object.offset_bytes = object.offset_bytes.checked_add(delta)?;
            object.access = access;
            object.size_bytes = size;
            if array_domain_size.is_none() {
                object.domain_path = object.path.clone();
                object.domain_offset_bytes = object.offset_bytes;
                object.domain_size_bytes = size;
            }
        }
        if variant.is_some() {
            return None;
        }
        Some(object)
    }

    pub fn field_subobject(
        &self,
        owner: VirMemoryAccess,
        field: VirFieldId,
    ) -> Option<VirSubobject> {
        let path = match self.kind(owner.ty)? {
            VirMemoryTypeKind::Struct { .. } => vec![VirObjectPathSegment::Field(field)],
            VirMemoryTypeKind::Enum { variants } => {
                let variant = variants.iter().find(|id| {
                    self.variant(**id)
                        .is_some_and(|v| v.fields.contains(&field))
                })?;
                vec![
                    VirObjectPathSegment::Variant(*variant),
                    VirObjectPathSegment::Field(field),
                ]
            }
            _ => return None,
        };
        self.subobject(owner, &path)
    }

    /// ABI leaf addresses have no explicit path. Return a path only when it is
    /// unambiguous; same-address enum alternatives require an unresolved recipe.
    pub fn leaf_subobject(
        &self,
        owner: VirMemoryAccess,
        leaf: VirMemoryAccess,
        offset: u64,
    ) -> Option<VirSubobject> {
        let shape = self.object_shape(owner).ok()?;
        let mut candidates = shape
            .leaves()
            .iter()
            .filter(|l| l.access() == leaf && l.bytes().start_bytes() == offset);
        let candidate = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        self.subobject(owner, candidate.path().segments())
    }
}
