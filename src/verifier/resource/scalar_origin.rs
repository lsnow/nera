//! Bounded historical scalar identities. Entry inputs and fresh observations
//! have separate coordinates; current addresses never imply value equality.
use super::*;
mod refinement;
#[cfg(test)]
mod snapshot_tests;
mod transport;
pub(crate) use transport::ScalarOriginTransport;

/// A fresh call-local history name. It has no address or runtime SSA meaning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TransportedOrigin {
    pub epoch: u64,
    pub index: u32,
}

/// A local observation of an actual initialized cell. Epochs are allocated by
/// the enclosing resource adapter and cannot be projected as function inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ScalarCellSnapshot {
    pub epoch: u64,
    pub allocation: AbstractAllocationId,
    pub bytes: ByteRange,
    pub access: VirMemoryAccess,
}

/// Immutable Boolean history. This is an identity, not a numeric
/// interval or a claim that the Boolean is true.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum BoolOrigin {
    Transported(TransportedOrigin),
    Snapshot(ScalarCellSnapshot),
    Parameter {
        function: crate::VirFunctionId,
        value: VirValueId,
    },
    Cell {
        allocation: AbstractAllocationId,
        bytes: ByteRange,
        access: VirMemoryAccess,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ScalarOriginRoot {
    Transported(TransportedOrigin),
    Snapshot(ScalarCellSnapshot),
    Cell {
        allocation: AbstractAllocationId,
        bytes: ByteRange,
        access: VirMemoryAccess,
    },
    Parameter {
        function: crate::VirFunctionId,
        value: VirValueId,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ScalarOriginCell {
    pub root: ScalarOriginRoot,
    pub initial_lower: u64,
    pub initial_upper: u64,
}
/// A nonnegative affine sum of at most two distinct historical inputs. Repeated
/// identities merge coefficients; interval equality is never cell identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ScalarOrigin {
    pub first: ScalarOriginCell,
    pub scale: u64,
    pub second: Option<(ScalarOriginCell, u64)>,
    pub addend: u64,
}
/// A subtraction is admitted only when every historical coefficient and the
/// constant cancel to nonnegative values; general signed arithmetic is absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScalarOriginDifference {
    Constant(u64),
    Origin(ScalarOrigin),
}
impl ScalarOrigin {
    pub(crate) fn difference(self, other: Self) -> Option<ScalarOriginDifference> {
        let addend = self.addend.checked_sub(other.addend)?;
        let mut terms = self.terms().collect::<BTreeMap<_, _>>();
        for (cell, scale) in other.terms() {
            let coefficient = terms.get_mut(&cell)?;
            *coefficient = coefficient.checked_sub(scale)?;
        }
        let mut terms = terms.into_iter().filter(|(_, scale)| *scale != 0);
        let Some((first, scale)) = terms.next() else {
            return Some(ScalarOriginDifference::Constant(addend));
        };
        Some(ScalarOriginDifference::Origin(Self {
            first,
            scale,
            second: terms.next(),
            addend,
        }))
    }

    pub(crate) fn initial_interval(self) -> Option<U64Interval> {
        let mut lower = self.addend;
        let mut upper = self.addend;
        for (cell, scale) in self.terms() {
            lower = lower.checked_add(cell.initial_lower.checked_mul(scale)?)?;
            upper = upper.saturating_add(cell.initial_upper.saturating_mul(scale));
        }
        U64Interval::new(lower, upper).ok()
    }
    pub(crate) fn add(self, n: u64) -> Option<Self> {
        Some(Self {
            addend: self.addend.checked_add(n)?,
            ..self
        })
    }
    pub(crate) fn terms(self) -> impl Iterator<Item = (ScalarOriginCell, u64)> {
        std::iter::once((self.first, self.scale)).chain(self.second)
    }
    pub(crate) fn scale(self, factor: u64) -> Option<Self> {
        if factor == 0 {
            return None;
        }
        Some(Self {
            scale: self.scale.checked_mul(factor)?,
            second: match self.second {
                Some((cell, scale)) => Some((cell, scale.checked_mul(factor)?)),
                None => None,
            },
            addend: self.addend.checked_mul(factor)?,
            ..self
        })
    }
    pub(crate) fn sum(self, other: Self) -> Option<Self> {
        let mut terms = BTreeMap::<ScalarOriginCell, u64>::new();
        for (cell, scale) in self.terms().chain(other.terms()) {
            let coefficient = terms.entry(cell).or_default();
            *coefficient = coefficient.checked_add(scale)?;
            if terms.len() > 2 {
                return None;
            }
        }
        let mut terms = terms.into_iter();
        let (first, scale) = terms.next()?;
        Some(Self {
            first,
            scale,
            second: terms.next(),
            addend: self.addend.checked_add(other.addend)?,
        })
    }
}
impl AbstractAllocation {
    /// Give an existing valid cell a local identity. This neither initializes
    /// bytes nor discards an already surviving origin. Normal writes, joins,
    /// copies and retirement use the same origin rules as entry observations.
    pub(in crate::verifier) fn seed_cell_snapshot(&mut self, snapshot: ScalarCellSnapshot) -> bool {
        let ScalarCellSnapshot { bytes, access, .. } = snapshot;
        if self.liveness() != LivenessState::Live
            || self.initialization().classify(bytes) != InitializationClass::Initialized
            || !self.valid_value_bytes().contains(bytes)
        {
            return false;
        }
        match self.scalar_content(bytes, access) {
            Some(AbstractValue::U64(value)) if bytes.end() - bytes.start() == 8 => {
                if self.scalar_origin(bytes, access).is_none() {
                    self.set_scalar_origin(
                        bytes,
                        access,
                        ScalarOrigin {
                            first: ScalarOriginCell {
                                root: ScalarOriginRoot::Snapshot(snapshot),
                                initial_lower: value.lower(),
                                initial_upper: value.upper(),
                            },
                            scale: 1,
                            second: None,
                            addend: 0,
                        },
                    );
                }
                self.scalar_origin(bytes, access).is_some()
            }
            Some(AbstractValue::Bool(_)) if bytes.end() - bytes.start() == 1 => {
                if self.bool_origin(bytes, access).is_none() {
                    self.set_bool_origin(bytes, access, BoolOrigin::Snapshot(snapshot));
                }
                self.bool_origin(bytes, access).is_some()
            }
            _ => false,
        }
    }

    pub(crate) fn bool_origin(
        &self,
        bytes: ByteRange,
        access: VirMemoryAccess,
    ) -> Option<BoolOrigin> {
        matches!(
            self.scalar_content(bytes, access),
            Some(AbstractValue::Bool(_))
        )
        .then(|| self.scalar_contents.3.get(&(bytes, access)).copied())
        .flatten()
    }
    pub(crate) fn set_bool_origin(
        &mut self,
        bytes: ByteRange,
        access: VirMemoryAccess,
        origin: BoolOrigin,
    ) {
        if bytes.end() - bytes.start() == 1
            && matches!(
                self.scalar_content(bytes, access),
                Some(AbstractValue::Bool(_))
            )
            && (self.scalar_contents.3.len() < 64
                || self.scalar_contents.3.contains_key(&(bytes, access)))
        {
            self.scalar_contents.3.insert((bytes, access), origin);
        }
    }
    pub(crate) fn scalar_origin(
        &self,
        bytes: ByteRange,
        access: VirMemoryAccess,
    ) -> Option<ScalarOrigin> {
        matches!(
            self.scalar_content(bytes, access),
            Some(AbstractValue::U64(_))
        )
        .then(|| self.scalar_contents.2.get(&(bytes, access)).copied())
        .flatten()
    }
    pub(crate) fn set_scalar_origin(
        &mut self,
        bytes: ByteRange,
        access: VirMemoryAccess,
        origin: ScalarOrigin,
    ) {
        if matches!(
            self.scalar_content(bytes, access),
            Some(AbstractValue::U64(_))
        ) && (self.scalar_contents.2.len() < 64
            || self.scalar_contents.2.contains_key(&(bytes, access)))
        {
            self.scalar_contents.2.insert((bytes, access), origin);
        }
    }
}
impl AbstractAllocation {
    /// Called only while constructing function entry. Preserve coordinates
    /// captured by an earlier predicate import or copied from another cell.
    pub(super) fn seed_scalar_origins(&mut self, id: AbstractAllocationId) {
        for (bytes, access, value) in self.scalar_contents() {
            if matches!(value, AbstractValue::Bool(_))
                && bytes.end() - bytes.start() == 1
                && self.bool_origin(bytes, access).is_none()
            {
                self.set_bool_origin(
                    bytes,
                    access,
                    BoolOrigin::Cell {
                        allocation: id,
                        bytes,
                        access,
                    },
                );
            }
            if let AbstractValue::U64(value) = value
                && bytes.end() - bytes.start() == 8
                && self.scalar_origin(bytes, access).is_none()
            {
                self.set_scalar_origin(
                    bytes,
                    access,
                    ScalarOrigin {
                        first: ScalarOriginCell {
                            root: ScalarOriginRoot::Cell {
                                allocation: id,
                                bytes,
                                access,
                            },
                            initial_lower: value.lower(),
                            initial_upper: value.upper(),
                        },
                        scale: 1,
                        second: None,
                        addend: 0,
                    },
                );
            }
        }
    }
}
impl ResourceState {
    pub(crate) fn seed_scalar_origins(&mut self) {
        for (id, allocation) in &mut self.allocations {
            allocation.seed_scalar_origins(*id);
        }
    }
    pub(crate) fn seed_parameter_origins(
        &mut self,
        function: crate::VirFunctionId,
        parameters: &[VirValueId],
    ) {
        for &id in parameters {
            if matches!(self.value(id), Some(AbstractValue::Bool(_))) {
                self.set_bool_origin(
                    id,
                    BoolOrigin::Parameter {
                        function,
                        value: id,
                    },
                );
            }
            if let Some(AbstractValue::U64(value)) = self.value(id) {
                let origin = ScalarOrigin {
                    first: ScalarOriginCell {
                        root: ScalarOriginRoot::Parameter {
                            function,
                            value: id,
                        },
                        initial_lower: value.lower(),
                        initial_upper: value.upper(),
                    },
                    scale: 1,
                    second: None,
                    addend: 0,
                };
                self.set_word_origin(id, origin);
            }
        }
    }
    pub(crate) fn bool_origin(&self, value: VirValueId) -> Option<BoolOrigin> {
        self.bool_origins.get(&value).copied()
    }
    pub(crate) fn set_bool_origin(&mut self, value: VirValueId, origin: BoolOrigin) {
        if matches!(self.value(value), Some(AbstractValue::Bool(_)))
            && (self.bool_origins.len() < 256 || self.bool_origins.contains_key(&value))
        {
            self.bool_origins.insert(value, origin);
        }
    }
    pub(crate) fn word_origin(&self, value: VirValueId) -> Option<ScalarOrigin> {
        self.word_origins.get(&value).copied()
    }
    pub(crate) fn set_word_origin(&mut self, value: VirValueId, origin: ScalarOrigin) {
        if self.word_origins.len() < 256 || self.word_origins.contains_key(&value) {
            self.word_origins.insert(value, origin);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn state() -> ResourceState {
        let mut state = ResourceState::new();
        let mut allocation = AbstractAllocation::new(VirRegionId::new(0), 24, 8).unwrap();
        let all = ByteRange::new(0, 24).unwrap();
        allocation.mark_initialized(all).unwrap();
        allocation.mark_valid(all).unwrap();
        for offset in [0, 8, 16] {
            allocation.record_scalar_content(
                ByteRange::new(offset, offset + 8).unwrap(),
                VirMemoryAccess::core_u64(),
                AbstractValue::U64(U64Interval::new(0, 7).unwrap()),
            );
        }
        state
            .define_allocation(AbstractAllocationId::new(0), allocation)
            .unwrap();
        state.seed_scalar_origins();
        state
    }
    #[test]
    fn historical_origins_are_invalidated_by_writes_free_and_disagreeing_joins() {
        let state = state();
        let id = AbstractAllocationId::new(0);
        let cell = ByteRange::new(0, 8).unwrap();
        let other = ByteRange::new(8, 16).unwrap();
        let access = VirMemoryAccess::core_u64();
        let original = state.allocation(id).unwrap();
        let origin = original.scalar_origin(cell, access).unwrap();
        assert_ne!(origin, original.scalar_origin(other, access).unwrap());
        let mut changed = original.clone();
        changed.record_scalar_content(
            cell,
            access,
            AbstractValue::U64(U64Interval::new(0, 7).unwrap()),
        );
        assert_eq!(changed.scalar_origin(cell, access), None);
        assert!(changed.scalar_origin(other, access).is_some());
        assert_eq!(
            original
                .join(id, &changed)
                .unwrap()
                .scalar_origin(cell, access),
            None
        );
        changed.set_scalar_origin(cell, access, origin.add(1).unwrap());
        assert_eq!(
            original
                .join(id, &changed)
                .unwrap()
                .scalar_origin(cell, access),
            None
        );
        changed.mark_dead();
        assert_eq!(changed.scalar_origin(cell, access), None);
        let mut copied = original.clone();
        copied.copy_scalar_contents(original, cell, 8);
        assert_eq!(copied.scalar_origin(other, access), Some(origin));
        assert_eq!(origin.add(u64::MAX).unwrap().add(1), None);
    }
    #[test]
    fn cfg_edges_rename_carriers_but_never_rebase_historical_cells() {
        let mut state = state();
        let cell = ByteRange::new(0, 8).unwrap();
        let access = VirMemoryAccess::core_u64();
        let origin = state
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .scalar_origin(cell, access)
            .unwrap();
        let source = VirValueId::new(0);
        let target = VirValueId::new(1);
        state
            .define_value(source, AbstractValue::U64(U64Interval::new(1, 8).unwrap()))
            .unwrap();
        state.set_word_origin(source, origin.add(1).unwrap());
        let projected = state.project_cfg_edge(&[(source, target)]);
        assert_eq!(projected.word_origin(source), None);
        assert_eq!(projected.word_origin(target), origin.add(1));
        assert_eq!(
            projected.word_origin(target).unwrap().first.initial_upper,
            7
        );
        assert_eq!(state.project_cfg_edge(&[]).word_origin(target), None);
        let many = (1..=300)
            .map(|n| (source, VirValueId::new(n)))
            .collect::<Vec<_>>();
        let bounded = state.project_cfg_edge(&many);
        assert_eq!(bounded.word_origins.len(), 256);
        assert_eq!(bounded.word_origin(VirValueId::new(257)), None);
        assert_eq!(bounded.word_origin(target), origin.add(1));
    }
    #[test]
    fn difference_cancels_identities_without_signed_coefficients() {
        let state = state();
        let allocation = state.allocation(AbstractAllocationId::new(0)).unwrap();
        let a = allocation
            .scalar_origin(ByteRange::new(0, 8).unwrap(), VirMemoryAccess::core_u64())
            .unwrap();
        let b = allocation
            .scalar_origin(ByteRange::new(8, 16).unwrap(), VirMemoryAccess::core_u64())
            .unwrap();
        assert_eq!(
            a.sum(b).unwrap().difference(a),
            Some(ScalarOriginDifference::Origin(b))
        );
        assert_eq!(
            a.sum(b).unwrap().difference(b),
            Some(ScalarOriginDifference::Origin(a))
        );
        assert_eq!(
            a.add(3).unwrap().difference(a),
            Some(ScalarOriginDifference::Constant(3))
        );
        assert_eq!(a.difference(a), Some(ScalarOriginDifference::Constant(0)));
        assert_eq!(a.difference(b), None);
        assert_eq!(a.difference(a.scale(2).unwrap()), None);
        assert_eq!(a.difference(a.add(1).unwrap()), None);
        assert_eq!(
            a.scale(2).unwrap().sum(b).unwrap().difference(a),
            Some(ScalarOriginDifference::Origin(a.sum(b).unwrap()))
        );
        assert_eq!(
            a.sum(b).unwrap().initial_interval(),
            Some(U64Interval::new(0, 14).unwrap())
        );
        let mut parameter = a;
        parameter.first.root = ScalarOriginRoot::Parameter {
            function: crate::VirFunctionId::new(0),
            value: VirValueId::new(0),
        };
        let mut another_call_scope = parameter;
        another_call_scope.first.root = ScalarOriginRoot::Parameter {
            function: crate::VirFunctionId::new(1),
            value: VirValueId::new(0),
        };
        assert_eq!(parameter.difference(another_call_scope), None);
    }

    #[test]
    fn sums_are_canonical_bounded_and_keep_immutable_cell_identity() {
        let state = state();
        let allocation = state.allocation(AbstractAllocationId::new(0)).unwrap();
        let a = allocation
            .scalar_origin(ByteRange::new(0, 8).unwrap(), VirMemoryAccess::core_u64())
            .unwrap();
        let b = allocation
            .scalar_origin(ByteRange::new(8, 16).unwrap(), VirMemoryAccess::core_u64())
            .unwrap();
        let sum = a.sum(b).unwrap();
        assert_eq!(Some(sum), b.sum(a));
        assert_ne!(sum, a.sum(a).unwrap());
        assert_eq!(a.add(1).unwrap().sum(b.add(2).unwrap()), sum.add(3));
        let c = allocation
            .scalar_origin(ByteRange::new(16, 24).unwrap(), VirMemoryAccess::core_u64())
            .unwrap();
        assert_eq!(sum.sum(c), None);
        assert_eq!(c.sum(sum), None);
        assert_eq!(sum.sum(a), a.sum(sum));
        assert_eq!(sum.sum(a), a.scale(2).unwrap().sum(b));
        assert_eq!(sum.sum(sum), sum.scale(2));
        assert_eq!(a.sum(a), a.scale(2));
        assert_eq!(a.scale(u64::MAX).unwrap().sum(a), None);
        assert_eq!(a.scale(u64::MAX).unwrap().scale(2), None);
        assert_eq!(a.add(1).unwrap().scale(u64::MAX).unwrap().add(1), None);
        assert_eq!(a.scale(0), None);
        assert_eq!(a.add(u64::MAX).unwrap().sum(b.add(1).unwrap()), None);
        assert_eq!(sum.first.initial_upper, 7);
        assert_eq!(sum.second.unwrap().0.initial_upper, 7);
    }
    #[test]
    fn boolean_entry_origins_follow_projection_intersection_and_mutation() {
        let mut state = ResourceState::new();
        let ids = [VirValueId::new(0), VirValueId::new(1)];
        for id in ids {
            state
                .define_value(id, AbstractValue::Bool(AbstractBool::Unknown))
                .unwrap();
        }
        state.seed_parameter_origins(crate::VirFunctionId::new(1), &ids);
        let origin = state.bool_origin(ids[0]).unwrap();
        assert_ne!(Some(origin), state.bool_origin(ids[1]));
        let target = VirValueId::new(10);
        let projected = state.project_cfg_edge(&[(ids[0], target)]);
        assert_eq!(projected.bool_origin(target), Some(origin));
        assert_eq!(projected.bool_origin(ids[0]), None);
        assert_eq!(
            state
                .project_cfg_edge(&[(ids[0], target), (ids[1], target)])
                .bool_origin(target),
            None
        );
        assert_eq!(
            state.join(&state).unwrap().bool_origin(ids[0]),
            Some(origin)
        );
        assert_eq!(
            state.widen(&state).unwrap().bool_origin(ids[0]),
            Some(origin)
        );
        let mut foreign = state.clone();
        foreign.seed_parameter_origins(crate::VirFunctionId::new(2), &ids);
        assert_eq!(state.join(&foreign).unwrap().bool_origin(ids[0]), None);
        assert_eq!(state.widen(&foreign).unwrap().bool_origin(ids[0]), None);
        let mut loop_state = state.clone();
        loop_state.inherit_loop_scalar_frame(&state, &[ids[0]].into_iter().collect());
        assert_eq!(loop_state.bool_origin(ids[0]), Some(origin));
        assert_eq!(loop_state.bool_origin(ids[1]), None);
        *loop_state.value_mut(ids[0]).unwrap() = AbstractValue::Bool(AbstractBool::Unknown);
        assert_eq!(loop_state.bool_origin(ids[0]), None);
        let mut bounded = ResourceState::new();
        for n in 0..257 {
            let id = VirValueId::new(n);
            bounded
                .define_value(id, AbstractValue::Bool(AbstractBool::Unknown))
                .unwrap();
            bounded.seed_parameter_origins(crate::VirFunctionId::new(1), &[id]);
        }
        assert_eq!(bounded.bool_origins.len(), 256);
        assert_eq!(bounded.bool_origin(VirValueId::new(256)), None);
    }
    #[test]
    fn boolean_cell_origins_follow_copy_and_disappear_on_forgetting_or_free() {
        let access = VirMemoryAccess {
            ty: crate::VirTypeId::new(90),
            layout: crate::VirLayoutId::new(90),
        };
        let first = ByteRange::new(0, 1).unwrap();
        let second = ByteRange::new(1, 2).unwrap();
        let mut state = state();
        let id = AbstractAllocationId::new(0);
        let allocation = state.allocation_mut(id).unwrap();
        for cell in [first, second] {
            allocation.record_scalar_content(
                cell,
                access,
                AbstractValue::Bool(AbstractBool::Unknown),
            );
        }
        state.seed_scalar_origins();
        let allocation = state.allocation(id).unwrap();
        let origin = allocation.bool_origin(first, access).unwrap();
        assert_ne!(Some(origin), allocation.bool_origin(second, access));
        let mut copied = allocation.clone();
        copied.copy_scalar_contents(allocation, first, 1);
        assert_eq!(copied.bool_origin(second, access), Some(origin));
        assert_eq!(
            allocation
                .join(id, &copied)
                .unwrap()
                .bool_origin(second, access),
            None
        );
        copied.record_scalar_content(second, access, AbstractValue::Bool(AbstractBool::Unknown));
        assert_eq!(copied.bool_origin(second, access), None);
        assert_eq!(copied.bool_origin(first, access), Some(origin));
        copied.set_bool_origin(second, access, origin);
        assert_eq!(copied.bool_origin(second, access), Some(origin));
        copied.forget_scalar_contents(first);
        assert_eq!(copied.bool_origin(first, access), None);
        assert_eq!(copied.bool_origin(second, access), Some(origin));
        copied.mark_dead();
        assert_eq!(copied.bool_origin(second, access), None);
        assert!(copied.scalar_contents.3.is_empty());
    }
}
