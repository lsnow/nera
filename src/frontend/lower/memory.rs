//! Deterministic conversion from reachable concrete HIR types to VIR memory tables.

use std::collections::{BTreeMap, BTreeSet};

use super::invalid_hir;
use crate::ByteSpan;
use crate::frontend::FrontendFailure;
use crate::frontend::hir::{
    HirAbiClass, HirBlock, HirEndianness, HirExpression, HirExpressionKind, HirFieldId,
    HirForSource, HirIntegerType, HirMutability, HirPattern, HirPatternKind, HirPlace, HirProgram,
    HirProjectionKind, HirStatement, HirStatementKind, HirTypeId, HirTypeKind, HirVariantId,
};
use crate::vir::{
    VirAbiClass, VirEndianness, VirField, VirFieldId, VirFieldLayout, VirIntegerType, VirLayout,
    VirLayoutId, VirMemoryAccess, VirMemorySchema, VirMemoryType, VirMemoryTypeKind, VirMutability,
    VirPointerKind, VirTargetDataLayout, VirTypeId, VirVariant, VirVariantCaseLayout, VirVariantId,
    VirVariantLayout,
};

#[derive(Clone)]
pub(super) struct LoweredMemorySchema {
    schema: VirMemorySchema,
    types: BTreeMap<HirTypeId, VirTypeId>,
    fields: BTreeMap<HirFieldId, VirFieldId>,
    variants: BTreeMap<HirVariantId, VirVariantId>,
}

impl LoweredMemorySchema {
    pub(super) fn build(hir: &HirProgram, source_span: ByteSpan) -> Result<Self, FrontendFailure> {
        let mut reachable = BTreeSet::new();
        for function in hir
            .functions()
            .iter()
            .filter(|function| function.generic_parameters.is_empty())
        {
            for ty in function
                .signature
                .parameters
                .iter()
                .chain([&function.signature.return_type])
            {
                collect_type(hir, *ty, &mut reachable, source_span)?;
            }
            if let Some(body) = function.body() {
                for local in &body.locals {
                    collect_type(hir, local.ty, &mut reachable, source_span)?;
                }
                collect_block(hir, &body.root, &mut reachable, source_span)?;
            }
        }

        let types: BTreeMap<_, _> = reachable
            .iter()
            .enumerate()
            .map(|(index, hir)| {
                u32::try_from(index)
                    .map(|index| (*hir, VirTypeId::new(index)))
                    .map_err(|_| invalid_hir(source_span))
            })
            .collect::<Result<_, _>>()?;

        let reachable_fields: BTreeSet<_> = reachable
            .iter()
            .flat_map(|ty| fields_of(hir, *ty))
            .collect();
        let fields: BTreeMap<_, _> = reachable_fields
            .iter()
            .enumerate()
            .map(|(index, hir)| {
                u32::try_from(index)
                    .map(|index| (*hir, VirFieldId::new(index)))
                    .map_err(|_| invalid_hir(source_span))
            })
            .collect::<Result<_, _>>()?;

        let reachable_variants: BTreeSet<_> = reachable
            .iter()
            .flat_map(|ty| variants_of(hir, *ty))
            .collect();
        let variants: BTreeMap<_, _> = reachable_variants
            .iter()
            .enumerate()
            .map(|(index, hir)| {
                u32::try_from(index)
                    .map(|index| (*hir, VirVariantId::new(index)))
                    .map_err(|_| invalid_hir(source_span))
            })
            .collect::<Result<_, _>>()?;

        let layouts: BTreeMap<_, _> = reachable
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                let layout = hir
                    .type_definition(*ty)
                    .and_then(|definition| definition.layout)
                    .ok_or_else(|| invalid_hir(source_span))?;
                let index = u32::try_from(index).map_err(|_| invalid_hir(source_span))?;
                Ok((layout, VirLayoutId::new(index)))
            })
            .collect::<Result<_, FrontendFailure>>()?;

        let vir_types = reachable
            .iter()
            .map(|id| {
                let definition = hir
                    .type_definition(*id)
                    .ok_or_else(|| invalid_hir(source_span))?;
                if !definition.generic_parameters.is_empty() {
                    return Err(invalid_hir(source_span));
                }
                let layout = definition.layout.ok_or_else(|| invalid_hir(source_span))?;
                Ok(VirMemoryType {
                    id: map_type(&types, *id, source_span)?,
                    kind: lower_kind(
                        hir,
                        &types,
                        &fields,
                        &variants,
                        &definition.kind,
                        source_span,
                    )?,
                    layout: map_layout(&layouts, layout, source_span)?,
                })
            })
            .collect::<Result<Vec<_>, FrontendFailure>>()?;
        let type_capabilities = reachable
            .iter()
            .map(|id| {
                hir.type_capabilities(*id)
                    .ok_or_else(|| invalid_hir(source_span))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let vir_fields = reachable_fields
            .iter()
            .map(|id| {
                let field = hir.field(*id).ok_or_else(|| invalid_hir(source_span))?;
                Ok(VirField {
                    id: map_field(&fields, *id, source_span)?,
                    owner: map_type(&types, field.owner, source_span)?,
                    ty: map_type(&types, field.ty, source_span)?,
                })
            })
            .collect::<Result<Vec<_>, FrontendFailure>>()?;

        let vir_variants = reachable_variants
            .iter()
            .map(|id| {
                let variant = hir.variant(*id).ok_or_else(|| invalid_hir(source_span))?;
                Ok(VirVariant {
                    id: map_variant(&variants, *id, source_span)?,
                    owner: map_type(&types, variant.owner, source_span)?,
                    fields: variant
                        .fields
                        .iter()
                        .map(|field| map_field(&fields, *field, source_span))
                        .collect::<Result<_, _>>()?,
                    discriminant: variant.discriminant,
                })
            })
            .collect::<Result<Vec<_>, FrontendFailure>>()?;

        let vir_layouts = reachable
            .iter()
            .map(|ty| {
                let layout = hir.layout_of(*ty).ok_or_else(|| invalid_hir(source_span))?;
                Ok(VirLayout {
                    id: map_layout(&layouts, layout.id, source_span)?,
                    ty: map_type(&types, *ty, source_span)?,
                    size_bytes: layout.size_bytes,
                    alignment: layout.alignment,
                    abi: lower_abi(layout.abi),
                    fields: lower_field_layouts(&fields, &layout.fields, source_span)?,
                    variants: layout
                        .variants
                        .as_ref()
                        .map(|layout| {
                            Ok(VirVariantLayout {
                                tag_size_bytes: layout.tag_size_bytes,
                                tag_alignment: layout.tag_alignment,
                                cases: layout
                                    .cases
                                    .iter()
                                    .map(|case| {
                                        Ok(VirVariantCaseLayout {
                                            variant: map_variant(
                                                &variants,
                                                case.variant,
                                                source_span,
                                            )?,
                                            payload_offset_bytes: case.payload_offset_bytes,
                                            fields: lower_field_layouts(
                                                &fields,
                                                &case.fields,
                                                source_span,
                                            )?,
                                        })
                                    })
                                    .collect::<Result<_, FrontendFailure>>()?,
                            })
                        })
                        .transpose()?,
                })
            })
            .collect::<Result<Vec<_>, FrontendFailure>>()?;

        let target = hir.data_layout();
        let schema = VirMemorySchema {
            target: VirTargetDataLayout {
                endianness: match target.endianness {
                    HirEndianness::Little => VirEndianness::Little,
                    HirEndianness::Big => VirEndianness::Big,
                },
                pointer_size_bytes: target.pointer_size_bytes,
                pointer_alignment: target.pointer_alignment,
                usize_size_bytes: target.usize_size_bytes,
                usize_alignment: target.usize_alignment,
            },
            types: vir_types,
            type_capabilities,
            layouts: vir_layouts,
            fields: vir_fields,
            variants: vir_variants,
        };
        schema.validate().map_err(|_| invalid_hir(source_span))?;
        Ok(Self {
            schema,
            types,
            fields,
            variants,
        })
    }

    pub(super) fn access(
        &self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<VirMemoryAccess, FrontendFailure> {
        let ty = map_type(&self.types, ty, source_span)?;
        self.schema
            .access(ty)
            .ok_or_else(|| invalid_hir(source_span))
    }

    pub(super) fn field(
        &self,
        field: HirFieldId,
        source_span: ByteSpan,
    ) -> Result<VirFieldId, FrontendFailure> {
        map_field(&self.fields, field, source_span)
    }

    pub(super) fn variant(
        &self,
        variant: HirVariantId,
        source_span: ByteSpan,
    ) -> Result<VirVariantId, FrontendFailure> {
        map_variant(&self.variants, variant, source_span)
    }

    pub(super) fn into_schema(self) -> VirMemorySchema {
        self.schema
    }

    pub(super) const fn schema(&self) -> &VirMemorySchema {
        &self.schema
    }
}

fn collect_type(
    hir: &HirProgram,
    ty: HirTypeId,
    reachable: &mut BTreeSet<HirTypeId>,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    if !reachable.insert(ty) {
        return Ok(());
    }
    let definition = hir
        .type_definition(ty)
        .ok_or_else(|| invalid_hir(source_span))?;
    if definition.layout.is_none() || !definition.generic_parameters.is_empty() {
        return Err(invalid_hir(source_span));
    }
    match &definition.kind {
        HirTypeKind::Own { pointee }
        | HirTypeKind::RawPointer { pointee, .. }
        | HirTypeKind::Reference { pointee, .. } => {
            collect_type(hir, *pointee, reachable, source_span)?;
        }
        HirTypeKind::Array { element, .. } | HirTypeKind::Slice { element, .. } => {
            collect_type(hir, *element, reachable, source_span)?;
        }
        HirTypeKind::Tuple(elements) => {
            for element in elements {
                collect_type(hir, *element, reachable, source_span)?;
            }
        }
        HirTypeKind::Struct { fields } => {
            for field in fields {
                let field = hir.field(*field).ok_or_else(|| invalid_hir(source_span))?;
                collect_type(hir, field.ty, reachable, source_span)?;
            }
        }
        HirTypeKind::Enum { variants } => {
            for variant in variants {
                let variant = hir
                    .variant(*variant)
                    .ok_or_else(|| invalid_hir(source_span))?;
                for field in &variant.fields {
                    let field = hir.field(*field).ok_or_else(|| invalid_hir(source_span))?;
                    collect_type(hir, field.ty, reachable, source_span)?;
                }
            }
        }
        HirTypeKind::Function(_) | HirTypeKind::GenericParameter(_) => {
            return Err(invalid_hir(source_span));
        }
        HirTypeKind::Unit | HirTypeKind::Bool | HirTypeKind::Integer(_) | HirTypeKind::Never => {}
    }
    Ok(())
}

fn collect_block(
    hir: &HirProgram,
    block: &HirBlock,
    reachable: &mut BTreeSet<HirTypeId>,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    block
        .statements
        .iter()
        .try_for_each(|statement| collect_statement(hir, statement, reachable, source_span))
}

fn collect_statement(
    hir: &HirProgram,
    statement: &HirStatement,
    reachable: &mut BTreeSet<HirTypeId>,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    match &statement.kind {
        HirStatementKind::Prove { .. } => Ok(()),
        HirStatementKind::Let { value, .. } | HirStatementKind::Evaluate { expression: value } => {
            collect_expression(hir, value, reachable, source_span)
        }
        HirStatementKind::Assign { destination, value } => {
            collect_place(hir, destination, reachable, source_span)?;
            collect_expression(hir, value, reachable, source_span)
        }
        HirStatementKind::Declare { .. }
        | HirStatementKind::Free { .. }
        | HirStatementKind::Break { .. }
        | HirStatementKind::Continue { .. } => Ok(()),
        HirStatementKind::Return { value } => value.as_ref().map_or(Ok(()), |value| {
            collect_expression(hir, value, reachable, source_span)
        }),
        HirStatementKind::Block { block } => collect_block(hir, block, reachable, source_span),
        HirStatementKind::If {
            condition,
            then_block,
            else_block,
        } => {
            collect_expression(hir, condition, reachable, source_span)?;
            collect_block(hir, then_block, reachable, source_span)?;
            if let Some(else_block) = else_block {
                collect_block(hir, else_block, reachable, source_span)?;
            }
            Ok(())
        }
        HirStatementKind::While {
            condition, body, ..
        } => {
            collect_expression(hir, condition, reachable, source_span)?;
            collect_block(hir, body, reachable, source_span)
        }
        HirStatementKind::For {
            pattern,
            source,
            body,
            ..
        } => {
            collect_pattern(hir, pattern, reachable, source_span)?;
            match source {
                HirForSource::IntegerRange {
                    start,
                    end,
                    item_type,
                    ..
                } => {
                    collect_type(hir, *item_type, reachable, source_span)?;
                    collect_expression(hir, start, reachable, source_span)?;
                    collect_expression(hir, end, reachable, source_span)?;
                }
            }
            collect_block(hir, body, reachable, source_span)
        }
        HirStatementKind::Match { scrutinee, arms } => {
            collect_expression(hir, scrutinee, reachable, source_span)?;
            for arm in arms {
                collect_pattern(hir, &arm.pattern, reachable, source_span)?;
                if let Some(guard) = &arm.guard {
                    collect_expression(hir, guard, reachable, source_span)?;
                }
                collect_block(hir, &arm.body, reachable, source_span)?;
            }
            Ok(())
        }
    }
}

fn collect_pattern(
    hir: &HirProgram,
    pattern: &HirPattern,
    reachable: &mut BTreeSet<HirTypeId>,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    collect_type(hir, pattern.ty, reachable, source_span)?;
    match &pattern.kind {
        HirPatternKind::Tuple(patterns) => patterns
            .iter()
            .try_for_each(|pattern| collect_pattern(hir, pattern, reachable, source_span)),
        HirPatternKind::Variant { fields, .. } => fields
            .iter()
            .try_for_each(|pattern| collect_pattern(hir, pattern, reachable, source_span)),
        HirPatternKind::Wildcard
        | HirPatternKind::Binding { .. }
        | HirPatternKind::Integer(_)
        | HirPatternKind::Bool(_) => Ok(()),
    }
}

fn collect_expression(
    hir: &HirProgram,
    expression: &HirExpression,
    reachable: &mut BTreeSet<HirTypeId>,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    collect_type(hir, expression.ty, reachable, source_span)?;
    match &expression.kind {
        HirExpressionKind::TupleConstructor { elements }
        | HirExpressionKind::ArrayConstructor { elements } => {
            for element in elements {
                collect_expression(hir, element, reachable, source_span)?;
            }
        }
        HirExpressionKind::ArrayRepeatConstructor { value, .. } => {
            collect_expression(hir, value, reachable, source_span)?;
        }
        HirExpressionKind::StructConstructor { fields }
        | HirExpressionKind::EnumConstructor { fields, .. } => {
            for field in fields {
                collect_expression(hir, &field.value, reachable, source_span)?;
            }
        }
        HirExpressionKind::Compare { left, right, .. }
        | HirExpressionKind::PointerDistance {
            begin: left,
            end: right,
        } => {
            collect_expression(hir, left, reachable, source_span)?;
            collect_expression(hir, right, reachable, source_span)?;
        }
        HirExpressionKind::WordAdd { operands, .. } => {
            for operand in operands {
                collect_expression(hir, operand, reachable, source_span)?;
            }
        }
        HirExpressionKind::PointerOffset { base, .. } => {
            collect_expression(hir, base, reachable, source_span)?;
        }
        HirExpressionKind::Allocate { element_type, .. } => {
            collect_type(hir, *element_type, reachable, source_span)?;
        }
        HirExpressionKind::Read { place, .. }
        | HirExpressionKind::Length { place }
        | HirExpressionKind::OwnerAddress { place }
        | HirExpressionKind::Borrow { place, .. }
        | HirExpressionKind::RawAddress { place, .. } => {
            collect_place(hir, place, reachable, source_span)?;
        }
        HirExpressionKind::Call(call) => {
            for argument in &call.arguments {
                collect_expression(hir, argument, reachable, source_span)?;
            }
        }
        HirExpressionKind::Unit | HirExpressionKind::Integer(_) | HirExpressionKind::Bool(_) => {}
    }
    Ok(())
}

fn collect_place(
    hir: &HirProgram,
    place: &HirPlace,
    reachable: &mut BTreeSet<HirTypeId>,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    collect_type(hir, place.ty, reachable, source_span)?;
    for projection in &place.projections {
        collect_type(hir, projection.result_type, reachable, source_span)?;
        match &projection.kind {
            HirProjectionKind::DynamicIndex { index } => {
                collect_expression(hir, index, reachable, source_span)?;
            }
            HirProjectionKind::Slice { start, end } => {
                for bound in start.iter().chain(end) {
                    collect_expression(hir, bound, reachable, source_span)?;
                }
            }
            HirProjectionKind::Dereference
            | HirProjectionKind::Field { .. }
            | HirProjectionKind::TupleElement { .. }
            | HirProjectionKind::ConstantIndex { .. }
            | HirProjectionKind::Downcast { .. } => {}
        }
    }
    Ok(())
}

fn fields_of(hir: &HirProgram, ty: HirTypeId) -> Vec<HirFieldId> {
    match hir.type_kind(ty) {
        Some(HirTypeKind::Struct { fields }) => fields.clone(),
        Some(HirTypeKind::Enum { variants }) => variants
            .iter()
            .filter_map(|variant| hir.variant(*variant))
            .flat_map(|variant| variant.fields.iter().copied())
            .collect(),
        _ => Vec::new(),
    }
}

fn variants_of(hir: &HirProgram, ty: HirTypeId) -> Vec<HirVariantId> {
    match hir.type_kind(ty) {
        Some(HirTypeKind::Enum { variants }) => variants.clone(),
        _ => Vec::new(),
    }
}

fn lower_kind(
    hir: &HirProgram,
    types: &BTreeMap<HirTypeId, VirTypeId>,
    fields: &BTreeMap<HirFieldId, VirFieldId>,
    variants: &BTreeMap<HirVariantId, VirVariantId>,
    kind: &HirTypeKind,
    span: ByteSpan,
) -> Result<VirMemoryTypeKind, FrontendFailure> {
    Ok(match kind {
        HirTypeKind::Unit => VirMemoryTypeKind::Unit,
        HirTypeKind::Bool => VirMemoryTypeKind::Bool,
        HirTypeKind::Integer(integer) => VirMemoryTypeKind::Integer(lower_integer(*integer)),
        HirTypeKind::Own { pointee } => VirMemoryTypeKind::Pointer {
            pointee: map_type(types, *pointee, span)?,
            kind: VirPointerKind::Own,
            mutability: VirMutability::Mutable,
        },
        HirTypeKind::RawPointer {
            pointee,
            mutability,
        } => VirMemoryTypeKind::Pointer {
            pointee: map_type(types, *pointee, span)?,
            kind: VirPointerKind::Raw,
            mutability: lower_mutability(*mutability),
        },
        HirTypeKind::Reference {
            pointee,
            mutability,
            ..
        } => match hir.type_kind(*pointee) {
            Some(HirTypeKind::Slice { element, .. }) => VirMemoryTypeKind::Slice {
                element: map_type(types, *element, span)?,
                mutability: lower_mutability(*mutability),
            },
            _ => VirMemoryTypeKind::Pointer {
                pointee: map_type(types, *pointee, span)?,
                kind: VirPointerKind::Reference,
                mutability: lower_mutability(*mutability),
            },
        },
        HirTypeKind::Array { element, length } => VirMemoryTypeKind::Array {
            element: map_type(types, *element, span)?,
            length: *length,
        },
        HirTypeKind::Slice {
            element,
            mutability,
        } => VirMemoryTypeKind::Slice {
            element: map_type(types, *element, span)?,
            mutability: lower_mutability(*mutability),
        },
        HirTypeKind::Tuple(elements) => VirMemoryTypeKind::Tuple(
            elements
                .iter()
                .map(|element| map_type(types, *element, span))
                .collect::<Result<_, _>>()?,
        ),
        HirTypeKind::Struct { fields: ids } => VirMemoryTypeKind::Struct {
            fields: ids
                .iter()
                .map(|field| map_field(fields, *field, span))
                .collect::<Result<_, _>>()?,
        },
        HirTypeKind::Enum { variants: ids } => VirMemoryTypeKind::Enum {
            variants: ids
                .iter()
                .map(|variant| map_variant(variants, *variant, span))
                .collect::<Result<_, _>>()?,
        },
        HirTypeKind::Never => VirMemoryTypeKind::Never,
        HirTypeKind::Function(_) | HirTypeKind::GenericParameter(_) => {
            return Err(invalid_hir(span));
        }
    })
}

fn lower_field_layouts(
    fields: &BTreeMap<HirFieldId, VirFieldId>,
    layouts: &[crate::frontend::hir::HirFieldLayout],
    span: ByteSpan,
) -> Result<Vec<VirFieldLayout>, FrontendFailure> {
    layouts
        .iter()
        .map(|layout| {
            Ok(VirFieldLayout {
                field: map_field(fields, layout.field, span)?,
                offset_bytes: layout.offset_bytes,
            })
        })
        .collect()
}

fn map_type(
    map: &BTreeMap<HirTypeId, VirTypeId>,
    id: HirTypeId,
    span: ByteSpan,
) -> Result<VirTypeId, FrontendFailure> {
    map.get(&id).copied().ok_or_else(|| invalid_hir(span))
}

fn map_layout(
    map: &BTreeMap<crate::frontend::hir::HirLayoutId, VirLayoutId>,
    id: crate::frontend::hir::HirLayoutId,
    span: ByteSpan,
) -> Result<VirLayoutId, FrontendFailure> {
    map.get(&id).copied().ok_or_else(|| invalid_hir(span))
}

fn map_field(
    map: &BTreeMap<HirFieldId, VirFieldId>,
    id: HirFieldId,
    span: ByteSpan,
) -> Result<VirFieldId, FrontendFailure> {
    map.get(&id).copied().ok_or_else(|| invalid_hir(span))
}

fn map_variant(
    map: &BTreeMap<HirVariantId, VirVariantId>,
    id: HirVariantId,
    span: ByteSpan,
) -> Result<VirVariantId, FrontendFailure> {
    map.get(&id).copied().ok_or_else(|| invalid_hir(span))
}

const fn lower_mutability(mutability: HirMutability) -> VirMutability {
    match mutability {
        HirMutability::Const => VirMutability::Const,
        HirMutability::Mutable => VirMutability::Mutable,
    }
}

const fn lower_abi(abi: HirAbiClass) -> VirAbiClass {
    match abi {
        HirAbiClass::Ignore => VirAbiClass::Ignore,
        HirAbiClass::Scalar => VirAbiClass::Scalar,
        HirAbiClass::ScalarPair => VirAbiClass::ScalarPair,
        HirAbiClass::Aggregate => VirAbiClass::Aggregate,
    }
}

const fn lower_integer(integer: HirIntegerType) -> VirIntegerType {
    match integer {
        HirIntegerType::U8 => VirIntegerType::U8,
        HirIntegerType::U16 => VirIntegerType::U16,
        HirIntegerType::U32 => VirIntegerType::U32,
        HirIntegerType::U64 => VirIntegerType::U64,
        HirIntegerType::U128 => VirIntegerType::U128,
        HirIntegerType::Usize => VirIntegerType::Usize,
        HirIntegerType::I8 => VirIntegerType::I8,
        HirIntegerType::I16 => VirIntegerType::I16,
        HirIntegerType::I32 => VirIntegerType::I32,
        HirIntegerType::I64 => VirIntegerType::I64,
        HirIntegerType::I128 => VirIntegerType::I128,
        HirIntegerType::Isize => VirIntegerType::Isize,
    }
}
