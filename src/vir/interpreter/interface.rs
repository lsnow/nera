//! Concrete value checks at call/return boundaries, independent of verifier
//! facts. Keep result-buffer identity across block renames and recursive frames.

use super::*;
use crate::{VirAbiSignature, VirAbiValue, VirLoanRange};

pub(super) struct RuntimeResultBuffer {
    pointer: VirRuntimePointer,
    permission_slot: usize,
}

pub(super) fn capture_result_buffers(
    program: &ResolvedRuntimeVirView<'_>,
    function: VirFunctionId,
    arguments: &[VirRuntimeValue],
    span: ByteSpan,
) -> Result<Vec<RuntimeResultBuffer>, VirExecutionError> {
    let abi = &program
        .abis
        .function(function)
        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
        .signature;
    let mut buffers = Vec::new();
    for binding in abi.results() {
        if let VirAbiValue::IndirectAggregate { access } = binding.value() {
            let [pointer_slot, _] = binding.parameter_slots() else {
                return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
            };
            let [permission_slot] = binding.result_slots() else {
                return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
            };
            let Some(VirRuntimeValue::Pointer(pointer)) = arguments.get(*pointer_slot as usize)
            else {
                return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
            };
            if pointer.access != *access {
                return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
            }
            buffers.push(RuntimeResultBuffer {
                pointer: *pointer,
                permission_slot: *permission_slot as usize,
            });
        }
    }
    Ok(buffers)
}

impl Interpreter {
    pub(super) fn check_interface_inputs(
        &self,
        memory: &VirMemorySchema,
        frame: &BlockFrame,
        arguments: &[VirValueId],
        abi: &VirAbiSignature,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        for binding in abi.parameters() {
            let reference = match binding.value() {
                VirAbiValue::Pointer { access, .. } | VirAbiValue::Slice { access, .. }
                    if binding.interface().transfer.is_borrow() =>
                {
                    Some(*access)
                }
                VirAbiValue::IndirectAggregate { .. } => None,
                _ => continue,
            };
            let pointer = pointer_value(
                frame,
                arguments[binding.parameter_slots()[0] as usize],
                span,
            )?;
            let permission = frame.permission(
                arguments[*binding
                    .parameter_slots()
                    .last()
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                    as usize],
                span,
            )?;
            if let Some(reference) = reference {
                let count = if matches!(binding.value(), VirAbiValue::Slice { .. }) {
                    word_value(
                        frame,
                        arguments[binding.parameter_slots()[1] as usize],
                        span,
                    )?
                } else {
                    1
                };
                let stride = memory
                    .layout(pointer.access.layout)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                    .size_bytes;
                let end = count
                    .checked_mul(stride)
                    .and_then(|bytes| pointer.offset_bytes.checked_add(bytes))
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                let range = VirLoanRange {
                    start_bytes: pointer.offset_bytes,
                    end_bytes: end,
                };
                check_permission_range(pointer, permission, range, span)?;
                self.check_borrow_value(memory, pointer, reference, range, span)?;
            } else {
                self.check_access(
                    pointer,
                    permission,
                    MemoryAccessContext::new(memory, pointer.access, span),
                )?;
                self.check_interface_object(memory, pointer, span)?;
            }
        }
        Ok(())
    }

    pub(super) fn check_interface_outputs(
        &self,
        memory: &VirMemorySchema,
        frame: &FunctionFrame,
        values: &[VirValueId],
        abi: &VirAbiSignature,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        for (index, binding) in abi.parameters().iter().enumerate() {
            if !binding.interface().transfer.is_borrow() {
                continue;
            }
            let Some((pointer, range)) = frame.loan_shadow.parameter_view(index) else {
                continue;
            };
            let reference = match binding.value() {
                VirAbiValue::Pointer { access, .. } | VirAbiValue::Slice { access, .. } => *access,
                _ => return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span)),
            };
            self.check_borrow_value(memory, pointer, reference, range, span)?;
        }
        for buffer in &frame.result_buffers {
            let id = *values
                .get(buffer.permission_slot)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
            let permission = frame.block_frame.permission(id, span)?;
            self.check_access(
                buffer.pointer,
                permission,
                MemoryAccessContext::new(memory, buffer.pointer.access, span),
            )?;
            self.check_interface_object(memory, buffer.pointer, span)?;
        }
        Ok(())
    }

    fn check_interface_object(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        self.check_object_address(memory, pointer, pointer.access, span)?;
        let shape = memory
            .object_shape(pointer.access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        self.check_object_effect_size(shape.size_bytes(), span)?;
        let offsets = self.active_object_offsets(memory, pointer, &shape, span)?;
        self.require_object_value(memory, pointer, &shape, &offsets, span)?;
        self.active_resource_payloads(memory, pointer, &shape, span)?;
        Ok(())
    }
}

fn check_permission_range(
    pointer: VirRuntimePointer,
    permission: VirRuntimePermission,
    range: VirLoanRange,
    span: ByteSpan,
) -> Result<(), VirExecutionError> {
    if pointer.allocation != permission.allocation {
        return Err(error(
            VirExecutionErrorKind::PermissionMismatch {
                allocation: pointer.allocation,
                permission_allocation: permission.allocation,
            },
            span,
        ));
    }
    if range.start_bytes < permission.start_bytes || range.end_bytes > permission.end_bytes {
        return Err(error(
            VirExecutionErrorKind::PermissionOutOfRange {
                start_bytes: permission.start_bytes,
                end_bytes: permission.end_bytes,
                access_start_bytes: range.start_bytes,
                access_end_bytes: range.end_bytes,
            },
            span,
        ));
    }
    Ok(())
}
