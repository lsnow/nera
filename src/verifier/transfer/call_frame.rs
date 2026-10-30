//! Initialization-only frames derived from checked borrowed ABI restoration.
use super::*;
use crate::verifier::resource::HeapInitializationPrefix;

type PrefixFrame = Vec<(AbstractAllocationId, HeapInitializationPrefix)>;

impl TransferBuilder<'_> {
    /// A conservative effect envelope, never a permission or initialized range.
    pub(super) fn call_effect_envelope(range: AbstractByteRange) -> Option<ByteRange> {
        let (start, end) = range.bounds()?;
        ByteRange::new(start.interval().lower(), end.interval().upper()).ok()
    }

    pub(super) fn borrowed_call_prefix_frame(
        &self,
        target: &VirCallTarget,
        arguments: &[VirValueId],
    ) -> PrefixFrame {
        let Some(abi) = &target.abi else {
            return Vec::new();
        };
        // Aggregate payloads can carry additional authority not visible among
        // the physical permission arguments. Admit only scalar values and
        // scalar slices until their nested resource mappings have a frame rule.
        if !abi
            .parameters()
            .iter()
            .chain(abi.results())
            .all(|binding| match binding.value() {
                crate::VirAbiValue::Unit { .. }
                | crate::VirAbiValue::Scalar {
                    ty: VirType::Bool | VirType::U64,
                    ..
                } => true,
                crate::VirAbiValue::Slice { element, .. } => {
                    binding.interface().transfer.is_borrow()
                        && matches!(
                            self.memory.kind(element.ty),
                            Some(
                                crate::VirMemoryTypeKind::Bool
                                    | crate::VirMemoryTypeKind::Integer(
                                        crate::VirIntegerType::U64 | crate::VirIntegerType::Usize
                                    )
                            )
                        )
                }
                _ => false,
            })
        {
            return Vec::new();
        }
        let mut frame = Vec::new();
        for (&id, allocation) in self.state.allocations() {
            for (prefix, _) in allocation.heap_prefixes() {
                if !allocation.heap_prefix_valid(prefix) {
                    continue;
                }
                let Some(extent) = prefix
                    .length
                    .checked_mul(prefix.stride)
                    .and_then(|n| ByteRange::from_start_and_length(prefix.array_offset, n).ok())
                else {
                    continue;
                };
                let preserved = arguments.iter().enumerate().all(|(slot, argument)| {
                    let Some(AbstractValue::Permission(permission)) = self.state.value(*argument)
                    else {
                        return true;
                    };
                    match permission.provenance() {
                        AbstractProvenance::Known(other) if other != id => return true,
                        AbstractProvenance::Unknown => return false,
                        _ => {}
                    }
                    if permission.free_capability() != FreeCapability::No {
                        return false;
                    }
                    if permission.access() == AccessPermission::Read {
                        return true;
                    }
                    let Some(range) = Self::call_effect_envelope(permission.range()) else {
                        return false;
                    };
                    if range.overlaps(prefix.count_range()) {
                        return false;
                    }
                    if !range.overlaps(extent) {
                        return true;
                    }
                    // Every writer of this allocation must satisfy the frame;
                    // one well-behaved slice cannot hide a second writable alias.
                    extent.contains(range) && abi.parameters().iter().any(|binding| {
                        binding.interface().transfer.is_borrow()
                            && binding.parameter_slots().last().copied() == Some(slot as u32)
                            && matches!(binding.value(), crate::VirAbiValue::Slice { element, .. }
                                if *element == prefix.element)
                    })
                });
                if preserved {
                    frame.push((id, prefix));
                }
            }
        }
        frame
    }

    pub(super) fn restore_borrowed_call_prefix_frame(
        state: &mut ResourceState,
        frame: &PrefixFrame,
    ) {
        for &(id, prefix) in frame {
            if let Some(allocation) = state.allocation_mut(id) {
                allocation.certify_heap_prefix(prefix);
            }
        }
    }
}
