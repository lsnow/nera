//! May events from canonical instruction transfer, accumulated across every
//! evaluation, including faults and provisional loop iterations. No state diff.
use super::*;
use crate::verifier::{
    AbstractByteRange, AbstractPointer, AbstractProvenance, AbstractValue, ResourceState,
};
use crate::{VirInstruction as I, VirMemorySchema, VirValueId};
use std::cell::RefCell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EffectKind {
    Read,
    Write,
    Free,
    Allocate,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EffectEvent {
    pub kind: EffectKind,
    pub pointer: Option<AbstractPointer>,
    pub range: AbstractByteRange,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct EffectJournal {
    pub audit_weight: usize,
    pub audit_overflow: bool,
    pub events: Vec<EffectEvent>,
    pub incomplete: bool,
    pub calls: Vec<CallSummaryUse>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallSummaryUse {
    pub symbol: String,
    pub outcome: CallSummaryOutcome,
    pub observation: audit::CallObservation,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallSummaryOutcome {
    Applied,
    /// Private simultaneous-induction hypothesis, never a published callee proof.
    Inductive,
    NotClosed,
    Preconditions,
    UnsupportedMapping,
    FreshInstanceFailure,
}

#[derive(Clone, Copy)]
pub(crate) struct SummaryTransferContext<'a> {
    pub site: Option<crate::VerifierFinding>,
    pub case_ordinal: usize,
    pub audit_limit: usize,
    pub registry: Option<&'a super::registry::SummaryRegistry>,
    pub journal: &'a RefCell<EffectJournal>,
    pub limit: usize,
}
impl SummaryTransferContext<'_> {
    pub fn record(self, event: EffectEvent) {
        let mut journal = self.journal.borrow_mut();
        if journal.events.contains(&event) {
            return;
        }
        if journal.events.len() >= self.limit {
            journal.incomplete = true;
        } else {
            journal.events.push(event);
        }
    }
    pub fn call(
        self,
        symbol: &str,
        outcome: CallSummaryOutcome,
        observation: audit::CallObservation,
    ) {
        let mut journal = self.journal.borrow_mut();
        let use_ = CallSummaryUse {
            symbol: symbol.into(),
            outcome,
            observation,
        };
        if !journal.calls.contains(&use_) {
            let weight = use_.observation.weight();
            if journal.calls.len() < self.limit
                && journal.audit_weight.saturating_add(weight) <= self.audit_limit
            {
                journal.audit_weight += weight;
                journal.calls.push(use_);
            } else {
                journal.incomplete = true;
                journal.audit_overflow = true;
            }
        }
        if !matches!(
            outcome,
            CallSummaryOutcome::Applied | CallSummaryOutcome::Inductive
        ) {
            journal.incomplete = true;
        }
    }
    pub fn observe(self, state: &ResourceState, instruction: &I, memory: &VirMemorySchema) {
        if !state.path_condition().is_reachable() {
            return;
        }
        if let I::DropOwn { condition, .. } | I::ObjectDrop { condition, .. } = instruction
            && matches!(
                state.value(*condition),
                Some(AbstractValue::Bool(AbstractBool::False))
            )
        {
            return;
        }
        let touch = |kind, id: VirValueId, access: Option<VirMemoryAccess>| {
            let pointer = match state.value(id) {
                Some(AbstractValue::Pointer(p)) => Some(*p),
                _ => None,
            };
            let range = pointer
                .and_then(|p| {
                    let begin = p.offset_bytes().exact_value()?;
                    let size = memory.layout(access?.layout)?.size_bytes;
                    ByteRange::from_start_and_length(begin, size).ok()
                })
                .map(AbstractByteRange::Exact)
                .unwrap_or(AbstractByteRange::Unknown);
            self.record(EffectEvent {
                kind,
                pointer,
                range,
            });
        };
        use EffectKind::*;
        match instruction {
            I::Load {
                pointer, access, ..
            }
            | I::EnumDiscriminant {
                pointer, access, ..
            } => touch(Read, *pointer, Some(*access)),
            I::Initialize {
                pointer, access, ..
            }
            | I::Write {
                pointer, access, ..
            }
            | I::Store {
                pointer, access, ..
            }
            | I::ObjectDeinitialize {
                pointer, access, ..
            }
            | I::StorageReset {
                pointer, access, ..
            }
            | I::ResourceStorageReset {
                pointer, access, ..
            }
            | I::EnumSetDiscriminant {
                pointer, access, ..
            } => touch(Write, *pointer, Some(*access)),
            I::ResourceInitialize {
                destination,
                access,
                ..
            } => touch(Write, *destination, Some(*access)),
            I::ResourceTake { source, access, .. } => {
                touch(Read, *source, Some(*access));
                touch(Write, *source, Some(*access));
            }
            I::ObjectTransfer {
                destination,
                source,
                access,
                source_mode,
                ..
            } => {
                touch(Read, *source, Some(*access));
                touch(Write, *destination, Some(*access));
                if *source_mode == crate::VirObjectSourceMode::Move {
                    touch(Write, *source, Some(*access));
                }
            }
            I::ObjectDrop {
                pointer, access, ..
            } => {
                touch(Read, *pointer, Some(*access));
                touch(Write, *pointer, Some(*access));
                // A may-free walk includes every possible stored owner, not
                // just the payload in a convenient active variant.
                if let Some(AbstractValue::Pointer(p)) = state.value(*pointer)
                    && let AbstractProvenance::Known(id) = p.provenance()
                    && let Some(allocation) = state.allocation(id)
                {
                    for path in allocation.object_state().resource_payloads().values() {
                        match path {
                            crate::verifier::MovePathState::Available(payload)
                                if payload.permission().free_capability()
                                    == FreeCapability::Yes =>
                            {
                                self.record(EffectEvent {
                                    kind: Free,
                                    pointer: Some(payload.pointer()),
                                    range: AbstractByteRange::Unknown,
                                })
                            }
                            crate::verifier::MovePathState::Unknown => {
                                self.journal.borrow_mut().incomplete = true
                            }
                            _ => {}
                        }
                    }
                }
            }
            I::Free { pointer, .. } | I::DropOwn { pointer, .. } => touch(Free, *pointer, None),
            I::Allocate { .. } | I::LocalStorage { .. } => self.record(EffectEvent {
                kind: Allocate,
                pointer: None,
                range: AbstractByteRange::Unknown,
            }),
            I::Call { .. } => {} // The sole call transfer records instantiated callee events.
            I::PointerCompare { .. }
            | I::PointerDistance { .. }
            | I::Constant { .. }
            | I::WordAdd { .. }
            | I::Compare { .. }
            | I::FieldAddress { .. }
            | I::TupleElementAddress { .. }
            | I::ObjectLeafAddress { .. }
            | I::IndexAddress { .. }
            | I::SliceAddress { .. }
            | I::SliceRange { .. }
            | I::RawAddress { .. }
            | I::PointerOffset { .. }
            | I::PermissionSplit { .. }
            | I::PermissionJoin { .. }
            | I::PermissionMove { .. }
            | I::LoanBegin { .. }
            | I::LoanAliasShared { .. }
            | I::LoanReborrow { .. }
            | I::LoanEnd { .. }
            | I::LoanAliasAuthority { .. }
            | I::LoanReborrowAuthority { .. }
            | I::LoanEndAuthority { .. }
            | I::Check { .. } => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn event_budget_loss_never_becomes_a_known_empty_frame() {
        let journal = RefCell::new(EffectJournal::default());
        let context = SummaryTransferContext {
            site: None,
            case_ordinal: 0,
            audit_limit: 0,
            registry: None,
            journal: &journal,
            limit: 0,
        };
        context.record(EffectEvent {
            kind: EffectKind::Write,
            pointer: None,
            range: AbstractByteRange::Unknown,
        });
        assert!(journal.borrow().incomplete);
        assert!(journal.borrow().events.is_empty());
    }
}
