use super::super::{AbstractProvenance, AbstractValue, ResourceObligation, ResourceState};
use super::*;
use crate::VirIndexBounds;

struct Query {
    premises: Vec<RelationPremise>,
}

impl Query {
    fn interval(&mut self, term: RelationTerm, interval: U64Interval) -> RelationTerm {
        let fact = RelationPremise::Interval { term, interval };
        if !self.premises.contains(&fact) {
            self.premises.push(fact);
        }
        term
    }
    fn word(&mut self, value: VirValueId, interval: U64Interval) -> RelationTerm {
        self.interval(
            RelationTerm::Value {
                value,
                ty: VirType::U64,
            },
            interval,
        )
    }
    fn pointer(
        &mut self,
        id: VirValueId,
        state: &ResourceState,
    ) -> Option<(RelationTerm, AbstractPointer)> {
        let AbstractValue::Pointer(fact) = *state.value(id)? else {
            return None;
        };
        let term = RelationTerm::PointerOffset {
            pointer: id,
            access: fact.memory_access()?,
        };
        self.premises.push(RelationPremise::Pointer {
            term,
            fact: Box::new(fact),
        });
        Some((term, fact))
    }
    fn allocation(&mut self, id: AbstractAllocationId, state: &ResourceState) -> Option<()> {
        let a = state.allocation(id)?;
        self.premises.push(RelationPremise::Allocation {
            allocation: id,
            size_bytes: a.size_bytes(),
            alignment: a.alignment().bytes(),
        });
        Some(())
    }
    fn length(
        &mut self,
        instruction: &VirInstruction,
        interval: U64Interval,
    ) -> Option<RelationTerm> {
        match *instruction {
            VirInstruction::SliceAddress {
                bounds: VirIndexBounds::Array { length },
                ..
            } => Some(RelationTerm::Constant(length)),
            VirInstruction::SliceAddress {
                bounds: VirIndexBounds::Slice { length },
                ..
            } => Some(self.word(length, interval)),
            // ABI length is already evaluated. This derived slot records the
            // exact arithmetic premise, not a guessed argument with equal bounds.
            VirInstruction::Call { .. } => Some(self.interval(RelationTerm::Derived(0), interval)),
            _ => None,
        }
    }
}

/// Normalize only audited numeric producers. An absent adapter is not a proof;
/// all original obligations remain in the program verification result.
fn normalize(
    obligation: ResourceObligationKind,
    instruction: &VirInstruction,
    before: &ResourceState,
    after: &ResourceState,
) -> Option<(
    RelationGoal,
    Vec<RelationPremise>,
    RelationRule,
    ObligationStatus,
)> {
    use ResourceObligationKind as K;
    let mut q = Query {
        premises: Vec::new(),
    };
    let (goal, rule, status) = match obligation {
        K::IndexWithinBounds {
            index,
            values,
            length,
        } => (
            RelationGoal::Compare {
                comparison: RelationComparison::LessThan,
                left: q.word(index, values),
                right: RelationTerm::Constant(length),
            },
            RelationRule::IntervalComparison,
            kernel::interval_lt_status(values, U64Interval::exact(length)),
        ),
        K::SliceIndexWithinBounds {
            index,
            values,
            length,
            length_values,
        } => (
            RelationGoal::Compare {
                comparison: RelationComparison::LessThan,
                left: q.word(index, values),
                right: q.word(length, length_values),
            },
            RelationRule::IntervalComparison,
            kernel::interval_lt_status(values, length_values),
        ),
        K::SliceRangeOrdered {
            start,
            start_values,
            end,
            end_values,
        } => (
            RelationGoal::Ordered {
                start: q.word(start, start_values),
                end: q.word(end, end_values),
            },
            RelationRule::IntervalComparison,
            kernel::interval_le_status(start_values, end_values),
        ),
        K::SliceRangeWithinBounds {
            end,
            end_values,
            length_values,
        } => (
            RelationGoal::Compare {
                comparison: RelationComparison::LessOrEqual,
                left: q.word(end, end_values),
                right: q.length(instruction, length_values)?,
            },
            RelationRule::IntervalComparison,
            kernel::interval_le_status(end_values, length_values),
        ),
        K::IndexStrideNoOverflow {
            index,
            values,
            stride_bytes,
        } => (
            RelationGoal::NoOverflow {
                operation: RelationArithmetic::Multiply,
                left: q.word(index, values),
                right: RelationTerm::Constant(stride_bytes),
            },
            RelationRule::CheckedEndpointArithmetic,
            kernel::scale_pointer_interval(values, stride_bytes).1,
        ),
        K::SliceRangeStrideNoOverflow {
            length_values,
            stride_bytes,
        } => (
            RelationGoal::NoOverflow {
                operation: RelationArithmetic::Multiply,
                left: q.length(instruction, length_values)?,
                right: RelationTerm::Constant(stride_bytes),
            },
            RelationRule::CheckedEndpointArithmetic,
            kernel::scale_pointer_interval(length_values, stride_bytes).1,
        ),
        K::AddressCalculationNoOverflow { base, delta }
        | K::PointerOffsetNoOverflow { base, delta } => {
            let (left, pointer) = q.pointer(base, before)?;
            (
                RelationGoal::NoOverflow {
                    operation: RelationArithmetic::Add,
                    left,
                    right: q.interval(RelationTerm::Derived(0), delta),
                },
                RelationRule::CheckedEndpointArithmetic,
                kernel::add_pointer_intervals(pointer.offset_bytes(), delta).1,
            )
        }
        K::AddressObjectWithinBounds {
            allocation,
            offset,
            object_bytes,
            size_bytes,
        } => {
            q.allocation(allocation, before)?;
            (
                RelationGoal::Contained {
                    allocation,
                    start: q.interval(RelationTerm::Derived(0), offset),
                    size_bytes: object_bytes,
                },
                RelationRule::AllocationContainment,
                kernel::object_bounds_status(offset, object_bytes, size_bytes),
            )
        }
        K::AddressObjectAligned {
            pointer,
            required_alignment,
        } => {
            // A derived pointer is defined only at the end of address transfer.
            // On a failing transfer it may not survive; that observation stays
            // solely in the original obligation list, never forged from bits.
            let state = if before.value(pointer).is_some() {
                before
            } else {
                after
            };
            let (term, fact) = q.pointer(pointer, state)?;
            let AbstractProvenance::Known(id) = fact.provenance() else {
                return None;
            };
            q.allocation(id, state)?;
            (
                RelationGoal::Aligned {
                    pointer: term,
                    required_alignment,
                },
                RelationRule::GuaranteedOrExactAlignment,
                kernel::object_alignment_status(fact, state.allocation(id)?, required_alignment),
            )
        }
        K::ObjectNonOverlapping {
            destination,
            source,
            size_bytes,
        } => {
            let (left, destination) = q.pointer(destination, before)?;
            let (right, source) = q.pointer(source, before)?;
            (
                RelationGoal::Disjoint {
                    left,
                    right,
                    size_bytes,
                },
                RelationRule::AllocationOrAffineDisjointness,
                kernel::object_non_overlap_status(destination, source, size_bytes),
            )
        }
        _ => return None,
    };
    Some((goal, q.premises, rule, status))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::verifier) fn capture(
    finding: VerifierFinding,
    config: CfgAnalysisConfig,
    case_ordinal: usize,
    obligation_ordinal: usize,
    instruction: &VirInstruction,
    memory: &crate::VirMemorySchema,
    before: &ResourceState,
    after: &ResourceState,
    obligation: ResourceObligation,
) -> Result<Option<RelationEvidence>, ()> {
    if let ResourceObligationKind::PermissionCoversAccess { permission, .. } = obligation.kind() {
        let operands = match *instruction {
            VirInstruction::Load {
                pointer,
                permission: p,
                access,
                ..
            }
            | VirInstruction::Store {
                pointer,
                permission: p,
                access,
                ..
            }
            | VirInstruction::Initialize {
                pointer,
                permission: p,
                access,
                ..
            }
            | VirInstruction::Write {
                pointer,
                permission: p,
                access,
                ..
            } if p == permission => Some((pointer, access)),
            _ => None,
        };
        if let Some((pointer, access)) = operands {
            let mut q = Query {
                premises: Vec::new(),
            };
            if let (
                Some((start, pointer)),
                Some(AbstractValue::Permission(permission)),
                Ok(shape),
            ) = (
                q.pointer(pointer, before),
                before.value(permission),
                memory.object_shape(access),
            ) {
                if let AbstractProvenance::Known(allocation) = pointer.provenance() {
                    let inner = super::range::access_range(pointer, shape.size_bytes());
                    let (status, bounds) = super::range::covers_access(
                        before,
                        permission.range(),
                        pointer,
                        shape.size_bytes(),
                        config.relation_limits,
                    );
                    if status != obligation.status() {
                        return Err(());
                    }
                    q.premises.push(RelationPremise::Ranges {
                        outer: Box::new(permission.range()),
                        inner: Box::new(inner),
                    });
                    return Ok(Some(RelationEvidence {
                        finding,
                        config,
                        case_ordinal,
                        obligation_ordinal,
                        guard: before.path_condition().clone(),
                        instruction: instruction.clone(),
                        obligation: obligation.kind(),
                        goal: RelationGoal::Contained {
                            allocation,
                            start,
                            size_bytes: shape.size_bytes(),
                        },
                        premises: q.premises,
                        rule: RelationRule::SymbolicPermissionContainment,
                        status,
                        kernel_version: super::RELATION_KERNEL_VERSION,
                        difference: None,
                        bounds,
                        disjoint: None,
                    }));
                }
            }
        }
    }
    let Some((goal, premises, mut rule, mut status)) =
        normalize(obligation.kind(), instruction, before, after)
    else {
        return Ok(None);
    };
    let query = match goal {
        RelationGoal::Compare {
            comparison,
            left,
            right,
        } => Some((comparison, left, right)),
        RelationGoal::Ordered { start, end } => Some((RelationComparison::LessOrEqual, start, end)),
        _ => None,
    };
    let mut difference = None;
    let bounds = Vec::new();
    let mut disjoint = None;
    if let RelationGoal::Disjoint {
        left: RelationTerm::PointerOffset { pointer: left, .. },
        right: RelationTerm::PointerOffset { pointer: right, .. },
        size_bytes,
    } = goal
    {
        if let (Some(AbstractValue::Pointer(left)), Some(AbstractValue::Pointer(right))) =
            (before.value(left), before.value(right))
        {
            let result = super::range::non_overlapping(
                before,
                *left,
                *right,
                size_bytes,
                config.relation_limits,
            );
            status = result.0;
            disjoint = result.1.map(Box::new);
            if disjoint.is_some() {
                rule = RelationRule::BoundedDifference;
            }
        }
    }
    if let Some((comparison, left, right)) = query {
        (status, difference) =
            super::compare(before, comparison, left, right, config.relation_limits);
        if difference.is_some() {
            rule = RelationRule::BoundedDifference;
        }
    }
    if status != obligation.status() {
        return Err(());
    }
    Ok(Some(RelationEvidence {
        finding,
        case_ordinal,
        obligation_ordinal,
        config,
        guard: before.path_condition().clone(),
        instruction: instruction.clone(),
        obligation: obligation.kind(),
        goal,
        premises,
        rule,
        status,
        kernel_version: super::RELATION_KERNEL_VERSION,
        difference,
        bounds,
        disjoint,
    }))
}
