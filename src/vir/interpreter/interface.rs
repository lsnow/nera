//! Concrete value checks at call/return boundaries, independent of verifier
//! facts. Keep result-buffer identity across block renames and recursive frames.

use super::*;
use crate::{VirAbiSignature, VirAbiValue, VirLoanRange};

pub(super) struct RuntimeResultBuffer {
    pointer: VirRuntimePointer,
    permission_slot: usize,
    complete_result: bool,
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
                complete_result: true,
            });
        }
    }
    // Reference-bearing parameter buffers also return their storage
    // permissions. Capture their identity before block argument renaming.
    for binding in abi.parameters() {
        let access = match binding.value() {
            VirAbiValue::IndirectAggregate { access } => *access,
            VirAbiValue::Pointer { pointee, .. } if binding.interface().transfer.is_borrow() => {
                *pointee
            }
            _ => continue,
        };
        let shape = program
            .memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        if !shape
            .resource_leaves()
            .iter()
            .any(|leaf| leaf.kind() == crate::VirPointerKind::Reference)
        {
            continue;
        }
        let [pointer_slot, _] = binding.parameter_slots() else {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        };
        let [permission_slot] = binding.result_slots() else {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        };
        let Some(VirRuntimeValue::Pointer(pointer)) = arguments.get(*pointer_slot as usize) else {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        };
        if pointer.access != access {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        }
        buffers.push(RuntimeResultBuffer {
            pointer: *pointer,
            permission_slot: *permission_slot as usize,
            complete_result: false,
        });
    }
    Ok(buffers)
}

pub(super) fn stored_destinations(
    memory: &VirMemorySchema,
    buffers: &[RuntimeResultBuffer],
    abi: &VirAbiSignature,
    frame: &BlockFrame,
    values: &[VirValueId],
    span: ByteSpan,
) -> Result<BTreeSet<(u64, RuntimeResourcePayloadKey)>, VirExecutionError> {
    let mut destinations = BTreeSet::new();
    let mut pointers = buffers
        .iter()
        .map(|buffer| buffer.pointer)
        .collect::<Vec<_>>();
    for binding in abi.results() {
        let VirAbiValue::Pointer { pointee, .. } = binding.value() else {
            continue;
        };
        if binding.interface().transfer != crate::VirInterfaceTransfer::Move {
            continue;
        }
        let [pointer, permission] = binding.result_slots() else {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        };
        let pointer = pointer_value(
            frame,
            *values
                .get(*pointer as usize)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?,
            span,
        )?;
        let permission = frame.permission(
            *values
                .get(*permission as usize)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?,
            span,
        )?;
        let shape = memory
            .object_shape(*pointee)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        if pointer.access != *pointee || !permission.can_free_when_complete {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        }
        check_permission_range(
            pointer,
            permission,
            VirLoanRange {
                start_bytes: pointer.offset_bytes,
                end_bytes: pointer
                    .offset_bytes
                    .checked_add(shape.size_bytes())
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?,
            },
            span,
        )?;
        pointers.push(pointer);
    }
    for pointer in pointers {
        let shape = memory
            .object_shape(pointer.access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        if !shape
            .resource_leaves()
            .iter()
            .any(|l| l.kind() == crate::VirPointerKind::Reference)
        {
            continue;
        }
        if !shape.variants().is_empty() {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        }
        for leaf in shape
            .resource_leaves()
            .iter()
            .filter(|leaf| leaf.kind() == crate::VirPointerKind::Reference)
        {
            destinations.insert((
                pointer.allocation,
                RuntimeResourcePayloadKey {
                    offset_bytes: pointer
                        .offset_bytes
                        .checked_add(leaf.bytes().start_bytes())
                        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?,
                    access: leaf.access(),
                },
            ));
        }
    }
    Ok(destinations)
}

/// Resolve field-result coordinates without granting an authority. The return
/// transaction matches these candidates against the actual callee token.
pub(super) fn stored_value_exits(
    memory: &VirMemorySchema,
    abi: &VirAbiSignature,
    values: &[VirValueId],
    results: &[VirValue],
    span: ByteSpan,
) -> Result<Vec<loan_shadow::RuntimeStoredValueExit>, VirExecutionError> {
    let invalid = || error(VirExecutionErrorKind::InvalidRuntimeState, span);
    if !abi
        .borrow_result()
        .into_iter()
        .chain(abi.borrow_result_alternatives().iter().map(|a| a.relation))
        .any(|r| r.parameter_field.is_some())
    {
        return Ok(Vec::new());
    }
    let parameters = abi
        .parameters()
        .iter()
        .map(|b| b.value().access())
        .collect::<Option<Vec<_>>>()
        .ok_or_else(invalid)?;
    let result_accesses = abi
        .results()
        .iter()
        .map(|b| b.value().access())
        .collect::<Option<Vec<_>>>()
        .ok_or_else(invalid)?;
    let mut exits = Vec::new();
    let mut sources = BTreeSet::new();
    for relation in abi
        .borrow_result()
        .into_iter()
        .chain(abi.borrow_result_alternatives().iter().map(|a| a.relation))
        .filter(|r| r.parameter_field.is_some())
    {
        crate::vir::borrow::plan_parameter_field_result(
            memory,
            &parameters,
            &result_accesses,
            relation,
        )
        .ok_or_else(invalid)?;
        // Several guard alternatives may select the same source.
        if !sources.insert(relation.source()) {
            continue;
        }
        let binding = abi
            .results()
            .get(relation.result as usize)
            .ok_or_else(invalid)?;
        let [pointer, permission] = binding.result_slots() else {
            return Err(invalid());
        };
        exits.push(loan_shadow::RuntimeStoredValueExit {
            source: relation.source(),
            pointer: *values.get(*pointer as usize).ok_or_else(invalid)?,
            permission: *values.get(*permission as usize).ok_or_else(invalid)?,
            caller_result: results.get(*permission as usize).ok_or_else(invalid)?.id,
        });
    }
    Ok(exits)
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
        for binding in abi
            .results()
            .iter()
            .enumerate()
            .filter(|(index, b)| {
                b.interface().transfer.is_borrow()
                    && abi
                        .borrow_result()
                        .into_iter()
                        .chain(abi.borrow_result_alternatives().iter().map(|a| a.relation))
                        .any(|r| r.parameter_field.is_some() && r.result as usize == *index)
            })
            .map(|(_, b)| b)
        {
            let reference = binding
                .value()
                .access()
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
            let slots = binding.result_slots();
            let pointer = pointer_value(&frame.block_frame, values[slots[0] as usize], span)?;
            let permission = frame
                .block_frame
                .permission(values[*slots.last().unwrap() as usize], span)?;
            let count = if matches!(binding.value(), VirAbiValue::Slice { .. }) {
                word_value(&frame.block_frame, values[slots[1] as usize], span)?
            } else {
                1
            };
            let stride = memory
                .layout(pointer.access.layout)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                .size_bytes;
            let end = count
                .checked_mul(stride)
                .and_then(|n| pointer.offset_bytes.checked_add(n))
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
            let range = VirLoanRange {
                start_bytes: pointer.offset_bytes,
                end_bytes: end,
            };
            check_permission_range(pointer, permission, range, span)?;
            self.check_borrow_value(memory, pointer, reference, range, span)?;
            self.check_interface_object(memory, pointer, span)?;
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
            // A moved parameter may have empty fields; its storage permission
            // must still return, while surviving field loans are checked below.
            if buffer.complete_result {
                self.check_interface_object(memory, buffer.pointer, span)?;
            }
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
