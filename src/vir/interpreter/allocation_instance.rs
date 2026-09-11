//! Execution-local, non-recycling logical identities shared by heap and frames.
//! Native addresses are not inputs: the same storage address may be reused but
//! neither pointer provenance nor hidden authority may be recovered from it.

#[derive(Default)]
pub(super) struct RuntimeInstanceSequence {
    next: u64,
}

impl RuntimeInstanceSequence {
    pub(super) fn fresh(&mut self) -> Option<u64> {
        let id = self.next;
        self.next = self.next.checked_add(1)?;
        Some(id)
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::*;

    fn storage(kind: RuntimeAllocationKind) -> Allocation {
        Allocation {
            size_bytes: 8,
            alignment: 8,
            kind,
            live: true,
            bytes: BTreeMap::new(),
            objects: Vec::new(),
            resource_payloads: BTreeMap::new(),
        }
    }

    #[test]
    fn reused_machine_slot_never_revives_old_heap_or_frame_identity() {
        let mut interpreter = Interpreter::new(VirInterpreterConfig::default());
        // Independent deterministic machine-storage oracle. It deliberately
        // returns one address, without depending on malloc's reuse policy.
        let machine_address = 0x1000_u64;
        let mut resident = BTreeMap::new();
        let mut retired = Vec::new();
        let span = ByteSpan::new(0, 1).unwrap();
        for kind in [
            RuntimeAllocationKind::Heap,
            RuntimeAllocationKind::LocalStorage,
        ]
        .into_iter()
        .cycle()
        .take(32)
        {
            let id = interpreter.allocation_instances.fresh().unwrap();
            interpreter.allocations.insert(id, storage(kind));
            assert!(resident.insert(machine_address, id).is_none());
            assert!(interpreter.live_allocation(id, span).is_ok());
            for &(old, old_kind) in &retired {
                assert_ne!(old, resident[&machine_address]);
                let mismatch = interpreter
                    .free(
                        VirRuntimePointer {
                            allocation: id,
                            offset_bytes: 0,
                            access: VirMemoryAccess::core_u64(),
                            paths: crate::VirPointerPaths::root(VirMemoryAccess::core_u64()),
                            view_range: None,
                            domain: crate::VirPointerDomain::Allocation,
                        },
                        VirRuntimePermission {
                            allocation: old,
                            start_bytes: 0,
                            end_bytes: 8,
                            can_free_when_complete: true,
                        },
                        span,
                    )
                    .unwrap_err();
                assert_eq!(
                    mismatch.kind(),
                    &VirExecutionErrorKind::PermissionMismatch {
                        allocation: id,
                        permission_allocation: old,
                    }
                );
                assert!(interpreter.live_allocation(id, span).is_ok());
                let fault = interpreter.live_allocation(old, span).err().unwrap();
                assert_eq!(
                    fault.kind(),
                    &match old_kind {
                        RuntimeAllocationKind::Heap =>
                            VirExecutionErrorKind::UseAfterFree { allocation: old },
                        RuntimeAllocationKind::LocalStorage =>
                            VirExecutionErrorKind::UseAfterLifetimeEnd { allocation: old },
                    }
                );
                let fault = interpreter.ensure_not_freed(old, span).unwrap_err();
                assert_eq!(
                    fault.kind(),
                    &match old_kind {
                        RuntimeAllocationKind::Heap =>
                            VirExecutionErrorKind::DoubleFree { allocation: old },
                        RuntimeAllocationKind::LocalStorage =>
                            VirExecutionErrorKind::UseAfterLifetimeEnd { allocation: old },
                    }
                );
            }
            interpreter.allocations.get_mut(&id).unwrap().live = false;
            resident.remove(&machine_address);
            retired.push((id, kind));
        }
    }

    #[test]
    fn identity_exhaustion_is_sticky_and_never_wraps() {
        let mut ids = RuntimeInstanceSequence { next: u64::MAX - 1 };
        assert_eq!(ids.fresh(), Some(u64::MAX - 1));
        for _ in 0..8 {
            assert_eq!(ids.fresh(), None);
            assert_eq!(ids.next, u64::MAX);
        }
    }
}
