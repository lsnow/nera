//! Concrete type and layout gate for VIR v0 lowering.

use super::invalid_hir;
use crate::ByteSpan;
use crate::frontend::FrontendFailure;
use crate::frontend::hir::{
    HirAbiClass, HirIntegerType, HirLayout, HirMutability, HirProgram, HirTypeId, HirTypeKind,
};
use crate::vir::{VirMemoryAccess, VirType};

/// Matches the current interpreter/native inline object-effect budget. HIR
/// producers fail closed before creating local aggregate storage above it.
pub(super) const HIR_AGGREGATE_MAX_BYTES: u64 = 4_096;

use super::memory::LoweredMemorySchema;

/// Resolves HIR type identities into the closed set of concrete VIR v0 types.
/// Generic definitions may exist elsewhere in the program, but every type
/// crossing this gate must have a target layout and an exact VIR representation.
#[derive(Clone, Copy)]
pub(super) struct ConcreteTypes<'hir> {
    hir: &'hir HirProgram,
}

impl<'hir> ConcreteTypes<'hir> {
    pub(super) const fn new(hir: &'hir HirProgram) -> Self {
        Self { hir }
    }

    pub(super) fn value_type(
        self,
        memory: &LoweredMemorySchema,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<VirType, FrontendFailure> {
        match self.hir.type_kind(ty) {
            Some(HirTypeKind::Bool) => {
                self.require_bool(ty, source_span)?;
                Ok(VirType::Bool)
            }
            Some(HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize)) => {
                self.require_runtime_word(ty, source_span)?;
                Ok(VirType::U64)
            }
            Some(HirTypeKind::Reference { pointee, .. })
                if matches!(
                    self.hir.type_kind(*pointee),
                    Some(HirTypeKind::Slice { .. })
                ) =>
            {
                self.abi_access(memory, ty, source_span)?;
                let Some(HirTypeKind::Slice { element, .. }) = self.hir.type_kind(*pointee) else {
                    unreachable!("guarded slice reference")
                };
                Ok(VirType::Pointer {
                    access: memory.access(*element, source_span)?,
                })
            }
            Some(
                HirTypeKind::Own { pointee }
                | HirTypeKind::RawPointer { pointee, .. }
                | HirTypeKind::Reference { pointee, .. },
            ) => {
                self.require_pointer_layout(ty, source_span)?;
                Ok(VirType::Pointer {
                    access: self.pointee_access(memory, *pointee, source_span)?,
                })
            }
            Some(HirTypeKind::Slice { element, .. }) => {
                self.abi_access(memory, ty, source_span)?;
                Ok(VirType::Pointer {
                    access: memory.access(*element, source_span)?,
                })
            }
            _ => Err(invalid_hir(source_span)),
        }
    }

    /// Runtime representation of a function-local binding. Aggregate values
    /// remain address based and therefore use an exact typed storage pointer;
    /// this does not admit aggregate function ABI slots.
    pub(super) fn local_type(
        self,
        memory: &LoweredMemorySchema,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<VirType, FrontendFailure> {
        if self.supports_aggregate(ty, source_span)? {
            Ok(VirType::Pointer {
                access: memory.access(ty, source_span)?,
            })
        } else {
            self.value_type(memory, ty, source_span)
        }
    }

    pub(super) fn aggregate_access(
        self,
        memory: &LoweredMemorySchema,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<Option<VirMemoryAccess>, FrontendFailure> {
        self.supports_aggregate(ty, source_span)?
            .then(|| memory.access(ty, source_span))
            .transpose()
    }

    pub(super) fn supports_aggregate(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<bool, FrontendFailure> {
        let aggregate = matches!(
            self.hir.type_kind(ty),
            Some(
                HirTypeKind::Array { .. }
                    | HirTypeKind::Tuple(_)
                    | HirTypeKind::Struct { .. }
                    | HirTypeKind::Enum { .. }
            )
        );
        if !aggregate {
            return Ok(false);
        }
        let layout = self.require_addressable(ty, source_span)?;
        if layout.size_bytes == 0 || layout.size_bytes > HIR_AGGREGATE_MAX_BYTES {
            return Err(invalid_hir(source_span));
        }
        Ok(self.hir.type_capabilities(ty).is_some_and(|capabilities| {
            capabilities.pointer_free_trivial()
                || (capabilities.contains_resource
                    && capabilities.size == crate::SizeCapability::Sized
                    && capabilities.drop != crate::DropCapability::UserDropGated
                    && self.supports_storable_value(ty, &mut std::collections::BTreeSet::new(), 0))
        }))
    }

    fn supports_storable_value(
        self,
        ty: HirTypeId,
        visiting: &mut std::collections::BTreeSet<HirTypeId>,
        depth: usize,
    ) -> bool {
        if depth >= crate::TYPE_CAPABILITY_MAX_DEPTH || !visiting.insert(ty) {
            return false;
        }
        let supported = match self.hir.type_kind(ty) {
            Some(
                HirTypeKind::Unit
                | HirTypeKind::Bool
                | HirTypeKind::Integer(_)
                | HirTypeKind::Own { .. }
                | HirTypeKind::Reference { .. },
            ) => true,
            Some(HirTypeKind::Array { element, .. }) => {
                self.supports_storable_value(*element, visiting, depth + 1)
            }
            Some(HirTypeKind::Tuple(elements)) => elements
                .iter()
                .all(|element| self.supports_storable_value(*element, visiting, depth + 1)),
            Some(HirTypeKind::Struct { fields }) => fields.iter().all(|field| {
                self.hir.field(*field).is_some_and(|field| {
                    self.supports_storable_value(field.ty, visiting, depth + 1)
                })
            }),
            Some(HirTypeKind::Enum { variants }) => variants.iter().all(|variant| {
                self.hir.variant(*variant).is_some_and(|variant| {
                    variant.fields.iter().all(|field| {
                        self.hir.field(*field).is_some_and(|field| {
                            self.supports_storable_value(field.ty, visiting, depth + 1)
                        })
                    })
                })
            }),
            Some(
                HirTypeKind::RawPointer { .. }
                | HirTypeKind::Slice { .. }
                | HirTypeKind::Function(_)
                | HirTypeKind::GenericParameter(_)
                | HirTypeKind::Never,
            )
            | None => false,
        };
        visiting.remove(&ty);
        supported
    }

    /// Canonical logical type identity consumed by the shared aggregate ABI
    /// classifier. This validates the HIR capability gate before exposing its
    /// nominal memory access.
    pub(super) fn abi_access(
        self,
        memory: &LoweredMemorySchema,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<VirMemoryAccess, FrontendFailure> {
        match self.hir.type_kind(ty) {
            Some(HirTypeKind::Unit) => self.require_unit_layout(ty, source_span)?,
            Some(HirTypeKind::Bool) => {
                self.require_bool(ty, source_span)?;
            }
            Some(HirTypeKind::Integer(HirIntegerType::U64 | HirIntegerType::Usize)) => {
                self.require_runtime_word(ty, source_span)?;
            }
            Some(HirTypeKind::Own { .. } | HirTypeKind::RawPointer { .. }) => {
                self.require_pointer(ty, source_span)?;
            }
            Some(HirTypeKind::Slice { .. }) => {
                let layout = self.concrete_layout(ty, source_span)?;
                let target = self.hir.data_layout();
                let expected_size = target
                    .pointer_size_bytes
                    .checked_add(target.usize_size_bytes)
                    .ok_or_else(|| invalid_hir(source_span))?;
                if layout.size_bytes != expected_size
                    || layout.alignment != target.pointer_alignment.max(target.usize_alignment)
                    || layout.abi != HirAbiClass::ScalarPair
                {
                    return Err(invalid_hir(source_span));
                }
            }
            Some(HirTypeKind::Reference { pointee, .. })
                if matches!(
                    self.hir.type_kind(*pointee),
                    Some(HirTypeKind::Slice { .. })
                ) =>
            {
                let layout = self.concrete_layout(ty, source_span)?;
                let target = self.hir.data_layout();
                let expected_size = target
                    .pointer_size_bytes
                    .checked_add(target.usize_size_bytes)
                    .ok_or_else(|| invalid_hir(source_span))?;
                if layout.size_bytes != expected_size
                    || layout.alignment != target.pointer_alignment.max(target.usize_alignment)
                    || layout.abi != HirAbiClass::ScalarPair
                {
                    return Err(invalid_hir(source_span));
                }
            }
            Some(
                HirTypeKind::Array { .. }
                | HirTypeKind::Tuple(_)
                | HirTypeKind::Struct { .. }
                | HirTypeKind::Enum { .. },
            ) => {
                if !self.supports_aggregate(ty, source_span)? {
                    return Err(invalid_hir(source_span));
                }
            }
            Some(HirTypeKind::Reference { .. }) => self.require_pointer_layout(ty, source_span)?,
            _ => return Err(invalid_hir(source_span)),
        }
        memory.access(ty, source_span)
    }

    pub(super) fn pointee_access(
        self,
        memory: &LoweredMemorySchema,
        pointee: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<VirMemoryAccess, FrontendFailure> {
        self.require_addressable(pointee, source_span)?;
        memory.access(pointee, source_span)
    }

    pub(super) fn require_runtime_word(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<&'hir HirLayout, FrontendFailure> {
        match self.hir.type_kind(ty) {
            Some(HirTypeKind::Integer(HirIntegerType::U64)) => {
                self.require_integer_layout(ty, 8, 8, source_span)
            }
            Some(HirTypeKind::Integer(HirIntegerType::Usize)) => {
                let target = self.hir.data_layout();
                self.require_integer_layout(
                    ty,
                    target.usize_size_bytes,
                    target.usize_alignment,
                    source_span,
                )
            }
            _ => Err(invalid_hir(source_span)),
        }
    }

    pub(super) fn require_u64(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<&'hir HirLayout, FrontendFailure> {
        if self.hir.type_kind(ty) != Some(&HirTypeKind::Integer(HirIntegerType::U64)) {
            return Err(invalid_hir(source_span));
        }
        self.require_integer_layout(ty, 8, 8, source_span)
    }

    pub(super) fn require_bool(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<&'hir HirLayout, FrontendFailure> {
        let layout = self.concrete_layout(ty, source_span)?;
        if self.hir.type_kind(ty) != Some(&HirTypeKind::Bool)
            || layout.size_bytes != 1
            || layout.alignment != 1
            || layout.abi != HirAbiClass::Scalar
            || !layout.fields.is_empty()
            || layout.variants.is_some()
        {
            return Err(invalid_hir(source_span));
        }
        Ok(layout)
    }

    pub(super) fn require_unit_layout(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let layout = self.concrete_layout(ty, source_span)?;
        if !self.is_unit(ty)
            || layout.size_bytes != 0
            || layout.alignment != 1
            || layout.abi != HirAbiClass::Ignore
            || !layout.fields.is_empty()
            || layout.variants.is_some()
        {
            return Err(invalid_hir(source_span));
        }
        Ok(())
    }

    pub(super) fn require_pointer(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        let pointee = match self.hir.type_kind(ty) {
            Some(
                HirTypeKind::Own { pointee }
                | HirTypeKind::RawPointer { pointee, .. }
                | HirTypeKind::Reference { pointee, .. },
            ) => *pointee,
            _ => return Err(invalid_hir(source_span)),
        };
        self.require_pointer_layout(ty, source_span)?;
        self.require_addressable(pointee, source_span)?;
        Ok(pointee)
    }

    pub(super) fn require_writable_pointer(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        match self.hir.type_kind(ty) {
            Some(HirTypeKind::Own { .. })
            | Some(HirTypeKind::RawPointer {
                mutability: HirMutability::Mutable,
                ..
            })
            | Some(HirTypeKind::Reference {
                mutability: HirMutability::Mutable,
                ..
            }) => self.require_pointer(ty, source_span),
            _ => Err(invalid_hir(source_span)),
        }
    }

    pub(super) fn validate_allocation(
        self,
        result_type: HirTypeId,
        element_type: HirTypeId,
        element_count: u64,
        size_bytes: u64,
        alignment: u64,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let element_layout = self.require_addressable(element_type, source_span)?;
        if !crate::frontend::hir::supports_builtin_allocation(
            self.hir.types(),
            self.hir.fields(),
            self.hir.variants(),
            element_type,
            element_count,
        ) || (!matches!(
            self.hir.type_kind(element_type),
            Some(HirTypeKind::Integer(HirIntegerType::U64))
        ) && !(1..=HIR_AGGREGATE_MAX_BYTES).contains(&element_layout.size_bytes))
            || self.hir.type_kind(result_type)
                != Some(&HirTypeKind::Own {
                    pointee: element_type,
                })
            || element_count.checked_mul(element_layout.size_bytes) != Some(size_bytes)
            || alignment != element_layout.alignment
        {
            return Err(invalid_hir(source_span));
        }
        self.require_pointer_layout(result_type, source_span)
    }

    pub(super) fn require_addressable(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<&'hir HirLayout, FrontendFailure> {
        match self.hir.type_kind(ty) {
            Some(
                HirTypeKind::Unit
                | HirTypeKind::Bool
                | HirTypeKind::Integer(_)
                | HirTypeKind::Own { .. }
                | HirTypeKind::RawPointer { .. }
                | HirTypeKind::Reference { .. }
                | HirTypeKind::Array { .. }
                | HirTypeKind::Tuple(_)
                | HirTypeKind::Struct { .. }
                | HirTypeKind::Enum { .. }
                | HirTypeKind::Never,
            ) => self.concrete_layout(ty, source_span),
            Some(
                HirTypeKind::Slice { .. }
                | HirTypeKind::Function(_)
                | HirTypeKind::GenericParameter(_),
            )
            | None => Err(invalid_hir(source_span)),
        }
    }

    pub(super) fn validate_pointer_offset(
        self,
        result_type: HirTypeId,
        base_type: HirTypeId,
        offset_count: usize,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if offset_count == 0 {
            return Err(invalid_hir(source_span));
        }
        let (pointee, mutability) = match self.hir.type_kind(base_type) {
            Some(HirTypeKind::Own { pointee }) => (*pointee, HirMutability::Mutable),
            Some(HirTypeKind::RawPointer {
                pointee,
                mutability,
            }) => (*pointee, *mutability),
            _ => return Err(invalid_hir(source_span)),
        };
        if self.hir.type_kind(result_type)
            != Some(&HirTypeKind::RawPointer {
                pointee,
                mutability,
            })
        {
            return Err(invalid_hir(source_span));
        }
        self.require_pointer(base_type, source_span)?;
        self.require_pointer(result_type, source_span)?;
        Ok(())
    }

    pub(super) fn matching_raw_pointers(self, left: HirTypeId, right: HirTypeId) -> bool {
        matches!((self.hir.type_kind(left), self.hir.type_kind(right)),
            (Some(HirTypeKind::RawPointer { pointee: a, .. }), Some(HirTypeKind::RawPointer { pointee: b, .. })) if a == b)
    }

    fn concrete_layout(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<&'hir HirLayout, FrontendFailure> {
        let definition = self
            .hir
            .type_definition(ty)
            .ok_or_else(|| invalid_hir(source_span))?;
        let layout_id = definition.layout.ok_or_else(|| invalid_hir(source_span))?;
        self.hir
            .layout(layout_id)
            .filter(|layout| layout.ty == ty)
            .ok_or_else(|| invalid_hir(source_span))
    }

    fn require_integer_layout(
        self,
        ty: HirTypeId,
        size_bytes: u64,
        alignment: u64,
        source_span: ByteSpan,
    ) -> Result<&'hir HirLayout, FrontendFailure> {
        let layout = self.concrete_layout(ty, source_span)?;
        if layout.size_bytes != size_bytes
            || layout.alignment != alignment
            || layout.abi != HirAbiClass::Scalar
            || !layout.fields.is_empty()
            || layout.variants.is_some()
        {
            return Err(invalid_hir(source_span));
        }
        Ok(layout)
    }

    fn require_pointer_layout(
        self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let layout = self.concrete_layout(ty, source_span)?;
        let target = self.hir.data_layout();
        if layout.size_bytes != target.pointer_size_bytes
            || layout.alignment != target.pointer_alignment
            || layout.abi != HirAbiClass::Scalar
            || !layout.fields.is_empty()
            || layout.variants.is_some()
        {
            return Err(invalid_hir(source_span));
        }
        Ok(())
    }

    fn is_unit(self, ty: HirTypeId) -> bool {
        self.hir.type_kind(ty) == Some(&HirTypeKind::Unit)
    }
}
