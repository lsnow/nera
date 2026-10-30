//! Layout and ABI adaptation for predicate contract inputs. This module maps
//! validated typed fields to physical slots; it establishes no logical fact or
//! resource authority. Parameter binding immutability is checked by HIR.
use super::*;
use crate::predicate_logic::{LogicType, ObservationTime, WitnessInput};
use crate::{HirLocalId, VirAbiBinding, VirAbiSignature, VirMemoryAccess};

pub(super) fn lower(
    ty: LogicType<HirTypeId>,
    input: WitnessInput<HirLocalId, HirTypeId>,
    abi: &VirAbiSignature,
    memory: &LoweredMemorySchema,
    ensures: bool,
    span: ByteSpan,
) -> Result<
    (
        LogicType<VirMemoryAccess>,
        WitnessInput<u32, VirMemoryAccess>,
    ),
    FrontendFailure,
> {
    let ty = match ty {
        LogicType::U64 => LogicType::U64,
        LogicType::Usize => LogicType::Usize,
        LogicType::Bool => LogicType::Bool,
        _ => return Err(invalid_hir(span)),
    };
    let input = match input {
        WitnessInput::Memory {
            base,
            offset,
            access,
            time,
        } => {
            if !ensures && time != ObservationTime::Current {
                return Err(invalid_hir(span));
            }
            let binding = abi
                .parameters()
                .get(base.get() as usize)
                .ok_or_else(|| invalid_hir(span))?;
            field(
                binding,
                offset,
                memory.access(access, span)?,
                Some(time),
                span,
            )?
        }
        WitnessInput::ResultField {
            base,
            offset,
            access,
        } if ensures && base.get() == 0 => {
            let binding = abi.results().first().ok_or_else(|| invalid_hir(span))?;
            field(binding, offset, memory.access(access, span)?, None, span)?
        }
        WitnessInput::Scalar(local) => {
            let slots = abi
                .parameters()
                .get(local.get() as usize)
                .ok_or_else(|| invalid_hir(span))?
                .parameter_slots();
            let [slot] = slots else {
                return Err(invalid_hir(span));
            };
            WitnessInput::Scalar(*slot)
        }
        WitnessInput::Result(index) if ensures && index.get() == 0 => {
            let slots = abi
                .results()
                .first()
                .ok_or_else(|| invalid_hir(span))?
                .result_slots();
            let [slot] = slots else {
                return Err(invalid_hir(span));
            };
            WitnessInput::Result(*slot)
        }
        _ => return Err(invalid_hir(span)),
    };
    Ok((ty, input))
}

/// A direct aggregate's scalar leaf is an immutable by-value parameter, so
/// entry and current observations use the same input slot. Pointer referents
/// retain their observation time and require actual memory evidence later.
/// None denotes a result, whose scalar slots and hidden storage have distinct
/// ABI directions and must not be confused with parameter slots.
fn field(
    binding: &VirAbiBinding,
    offset: u64,
    access: VirMemoryAccess,
    parameter: Option<ObservationTime>,
    span: ByteSpan,
) -> Result<WitnessInput<u32, VirMemoryAccess>, FrontendFailure> {
    if let VirAbiValue::DirectAggregate { leaves, .. } = binding.value() {
        let index = leaves
            .iter()
            .position(|leaf| leaf.access() == access && leaf.offset_bytes() == offset)
            .ok_or_else(|| invalid_hir(span))?;
        let slots = if parameter.is_some() {
            binding.parameter_slots()
        } else {
            binding.result_slots()
        };
        let slot = *slots.get(index).ok_or_else(|| invalid_hir(span))?;
        return Ok(if parameter.is_some() {
            WitnessInput::Scalar(slot)
        } else {
            WitnessInput::Result(slot)
        });
    }
    match (binding.value(), parameter) {
        (VirAbiValue::Pointer { .. } | VirAbiValue::IndirectAggregate { .. }, Some(time)) => {
            Ok(WitnessInput::Memory {
                base: *binding
                    .parameter_slots()
                    .first()
                    .ok_or_else(|| invalid_hir(span))?,
                offset,
                access,
                time,
            })
        }
        (VirAbiValue::IndirectAggregate { .. }, None) => Ok(WitnessInput::ResultField {
            base: *binding
                .parameter_slots()
                .first()
                .ok_or_else(|| invalid_hir(span))?,
            offset,
            access,
        }),
        _ => Err(invalid_hir(span)),
    }
}
