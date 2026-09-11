//! Arithmetic domains reuse the existing bounded range/relation kernel. These
//! are address-formation facts, never permission ranges or initialization.
use super::*;
use crate::VirPointerDomain;

pub(super) use super::super::relation::range::access_range as pointer_range;

impl TransferBuilder<'_> {
    fn pointer_pair(
        &mut self,
        left_id: VirValueId,
        right_id: VirValueId,
    ) -> Result<(AbstractPointer, AbstractPointer, bool), TransferError> {
        let first_obligation = self.obligations.len();
        let left = pointer_fact(&self.state, left_id)?;
        let right = pointer_fact(&self.state, right_id)?;
        // Distinct symbolic IDs do not prove concrete non-aliasing of parameters.
        let same = matches!((left.provenance(), right.provenance()), (AbstractProvenance::Known(a), AbstractProvenance::Known(b)) if a == b);
        self.require(
            ResourceObligationKind::PointerSameInstance {
                left: left_id,
                right: right_id,
            },
            if same {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        for (id, pointer) in [(left_id, left), (right_id, right)] {
            self.require_domain_access(id, pointer, 0);
            if let AbstractProvenance::Known(allocation) = pointer.provenance() {
                if let Some(storage) = self.state.allocation(allocation) {
                    let size_bytes = storage.size_bytes();
                    let offset = pointer.offset_bytes();
                    self.require(
                        ResourceObligationKind::PointerOffsetWithinBounds {
                            allocation,
                            offset,
                            size_bytes,
                        },
                        if offset.upper() <= size_bytes {
                            ObligationStatus::Proven
                        } else if offset.lower() > size_bytes {
                            ObligationStatus::Refuted
                        } else {
                            ObligationStatus::Unknown
                        },
                    );
                }
                let status = self
                    .state
                    .allocation(allocation)
                    .map_or(ObligationStatus::Unknown, |a| liveness_status(a.liveness()));
                self.require(
                    ResourceObligationKind::AllocationLive { allocation },
                    status,
                );
            }
        }
        let nominal = left.paths().domain.is_some() && left.paths().domain == right.paths().domain;
        let compatibility = if nominal {
            let a = self.domain_range(left);
            let b = self.domain_range(right);
            combine_statuses([self.range_contains(a, b), self.range_contains(b, a)])
        } else {
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::PointerCompatibleDomain {
                left: left_id,
                right: right_id,
            },
            compatibility,
        );
        let checked = self.obligations[first_obligation..]
            .iter()
            .all(|o| o.is_proven());
        Ok((left, right, checked))
    }

    fn pointer_order(&self, left: AbstractPointer, right: AbstractPointer) -> ObligationStatus {
        match (
            symbolic_bound(left.offset_bytes(), left.offset_expression()),
            symbolic_bound(right.offset_bytes(), right.offset_expression()),
        ) {
            (Some(a), Some(b)) => {
                self.relations
                    .queries
                    .ordered(&self.state, a, b, self.relation_limits)
            }
            _ => interval_le_status(left.offset_bytes(), right.offset_bytes()),
        }
    }

    pub(super) fn pointer_compare(
        &mut self,
        result: VirValue,
        predicate: VirIntegerPredicate,
        left: VirValueId,
        right: VirValueId,
    ) -> Result<(), TransferError> {
        let (a, b, checked) = self.pointer_pair(left, right)?;
        if !checked {
            return self.define(result, AbstractValue::Bool(AbstractBool::Unknown));
        }
        let le = self.pointer_order(a, b);
        let ge = self.pointer_order(b, a);
        let eq = combine_statuses([le, ge]);
        let (status, negate) = match predicate {
            VirIntegerPredicate::Equal => (eq, false),
            VirIntegerPredicate::NotEqual => (eq, true),
            VirIntegerPredicate::LessOrEqual => (le, false),
            VirIntegerPredicate::GreaterOrEqual => (ge, false),
            VirIntegerPredicate::LessThan => (ge, true),
            VirIntegerPredicate::GreaterThan => (le, true),
        };
        let value = match status {
            ObligationStatus::Unknown => AbstractBool::Unknown,
            ObligationStatus::Proven if !negate => AbstractBool::True,
            ObligationStatus::Refuted if negate => AbstractBool::True,
            _ => AbstractBool::False,
        };
        self.define(result, AbstractValue::Bool(value))
    }

    pub(super) fn pointer_distance(
        &mut self,
        result: VirValue,
        begin: VirValueId,
        end: VirValueId,
    ) -> Result<(), TransferError> {
        let (a, b, checked) = self.pointer_pair(begin, end)?;
        let status = self.pointer_order(a, b);
        self.require(
            ResourceObligationKind::PointerDistanceNonnegative { begin, end },
            status,
        );
        // Nonnegative subtraction of two in-domain u64 offsets is representable
        // in the frozen 64-bit target usize, without wrapping arithmetic.
        let exact = a
            .offset_expression()
            .zip(b.offset_expression())
            .filter(|(a, b)| a.same_terms(*b))
            .and_then(|(a, b)| b.addend().checked_sub(a.addend()));
        let distance = exact.map_or_else(
            || subtract_intervals(b.offset_bytes(), a.offset_bytes()),
            U64Interval::exact,
        );
        self.define(
            result,
            AbstractValue::U64(if checked && status.is_proven() {
                distance
            } else {
                U64Interval::unknown()
            }),
        )
    }
    pub(super) fn set_pointer_paths(
        &mut self,
        id: VirValueId,
        paths: crate::VirPointerPaths,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, id)?;
        if let Some(value) = self.state.value_mut(id) {
            *value = AbstractValue::Pointer(pointer.with_paths(paths));
        }
        Ok(())
    }

    pub(super) fn subobject_address(
        &mut self,
        result: VirValue,
        base: VirValueId,
        object: crate::VirSubobject,
    ) -> Result<(), TransferError> {
        self.typed_address(
            result,
            base,
            AddressAccess {
                source: object.root(),
                result: object.access(),
            },
            U64Interval::exact(object.offset_bytes()),
            Some(AffineExpression::constant(object.offset_bytes())),
        )?;
        self.set_subobject_domain(result.id, base, &object)
    }
    pub(super) fn set_subobject_domain(
        &mut self,
        id: VirValueId,
        base_id: VirValueId,
        object: &crate::VirSubobject,
    ) -> Result<(), TransferError> {
        let base = pointer_fact(&self.state, base_id)?;
        let (offset, overflow) = add_pointer_intervals(
            base.offset_bytes(),
            U64Interval::exact(object.domain_offset_bytes()),
        );
        let expression = base
            .offset_expression()
            .or_else(|| {
                base.offset_bytes()
                    .exact_value()
                    .map(AffineExpression::constant)
            })
            .and_then(|e| e.checked_add_constant(object.domain_offset_bytes()));
        let range = if overflow == ObligationStatus::Proven {
            pointer_range(
                AbstractPointer::new(base.provenance(), offset, base.alignment())
                    .with_offset_expression(expression),
                object.domain_size_bytes(),
            )
        } else {
            AbstractByteRange::Unknown
        };
        self.require_domain_range(base_id, base, range);
        self.set_pointer_paths(id, base.paths().project(object))?;
        self.set_pointer_domain(id, VirPointerDomain::Restricted(range))
    }

    pub(super) fn domain_range(&self, pointer: AbstractPointer) -> AbstractByteRange {
        match pointer.domain() {
            VirPointerDomain::Restricted(range) => range,
            VirPointerDomain::Unknown => AbstractByteRange::Unknown,
            VirPointerDomain::Allocation => {
                let AbstractProvenance::Known(id) = pointer.provenance() else {
                    return AbstractByteRange::Unknown;
                };
                self.state
                    .allocation(id)
                    .and_then(|a| ByteRange::new(0, a.size_bytes()).ok())
                    .map_or(AbstractByteRange::Unknown, AbstractByteRange::Exact)
            }
        }
    }

    pub(super) fn require_domain_range(
        &mut self,
        id: VirValueId,
        pointer: AbstractPointer,
        selection: AbstractByteRange,
    ) -> ObligationStatus {
        let domain = self.domain_range(pointer);
        let status = self.range_contains(domain, selection);
        self.require(
            ResourceObligationKind::PointerDomainContains {
                pointer: id,
                domain,
                selection,
            },
            status,
        );
        status
    }

    pub(super) fn require_domain_access(
        &mut self,
        id: VirValueId,
        pointer: AbstractPointer,
        width: u64,
    ) {
        let domain = self.domain_range(pointer);
        let status = self.relations.queries.covers_access(
            &self.state,
            domain,
            pointer,
            width,
            self.relation_limits,
        );
        self.require(
            ResourceObligationKind::PointerDomainContains {
                pointer: id,
                domain,
                selection: pointer_range(pointer, width),
            },
            status,
        );
    }

    pub(super) fn set_pointer_domain(
        &mut self,
        id: VirValueId,
        domain: VirPointerDomain<AbstractByteRange>,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, id)?;
        if let Some(value) = self.state.value_mut(id) {
            *value = AbstractValue::Pointer(pointer.with_domain(domain));
        }
        Ok(())
    }
}
