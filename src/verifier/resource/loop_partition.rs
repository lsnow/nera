//! Discrete phase identity, NOT a resource equality or entailment rule.
//! Numeric ranges, contents and initialization prefixes stay inside each
//! whole case and are merged by the existing conservative resource domain.
use super::*;

impl ResourceState {
    pub(in crate::verifier) fn same_loop_predicates(&self, other: &Self, cuts: &[u64]) -> bool {
        cuts.is_empty()
            || self
                .values
                .iter()
                .filter_map(|(id, v)| match v {
                    AbstractValue::U64(v) => Some((id, cell(*v, cuts))),
                    _ => None,
                })
                .eq(other.values.iter().filter_map(|(id, v)| match v {
                    AbstractValue::U64(v) => Some((id, cell(*v, cuts))),
                    _ => None,
                }))
    }

    pub(in crate::verifier) fn widen_loop_predicates(
        &self,
        next: &Self,
        cuts: &[u64],
    ) -> Result<Self, ResourceJoinError> {
        let mut widened = self.widen(next)?;
        for (id, value) in &mut widened.values {
            if let (AbstractValue::U64(wide), Some(AbstractValue::U64(next))) =
                (value, next.values.get(id))
                && let Some(index) = cell(*next, cuts)
            {
                // Both operands must imply the fixed cell. Do not rely on
                // the caller's grouping to make clipping a sound widening.
                if !matches!(self.values.get(id), Some(AbstractValue::U64(old)) if cell(*old, cuts) == Some(index))
                {
                    continue;
                }
                let lower = if index == 0 { 0 } else { cuts[index - 1] };
                let upper = cuts.get(index).map_or(u64::MAX, |cut| cut - 1);
                *wide = U64Interval::new(wide.lower().max(lower), wide.upper().min(upper))
                    .expect("cell contains next interval");
            }
        }
        Ok(widened)
    }

    pub(in crate::verifier) fn same_loop_partition(&self, other: &Self) -> bool {
        self.allocations.len() == other.allocations.len()
            && self.allocations.iter().all(|(id, a)| {
                other.allocations.get(id).is_some_and(|b| {
                    a.region() == b.region()
                        && a.size_bytes() == b.size_bytes()
                        && a.alignment() == b.alignment()
                        && a.liveness() == b.liveness()
                        && a.ownership() == b.ownership()
                        && a.object_state() == b.object_state()
                })
            })
            && self.loans.len() == other.loans.len()
            && self.loans.iter().all(|(id, a)| {
                other.loans.get(id).is_some_and(|b| {
                    a.provenance() == b.provenance()
                        && a.range() == b.range()
                        && a.kind() == b.kind()
                        && a.region() == b.region()
                        && a.parent() == b.parent()
                        && a.activity() == b.activity()
                        && a.authorities() == b.authorities()
                })
            })
            && phase_values(&self.values).eq(phase_values(&other.values))
    }
}

fn cell(interval: U64Interval, cuts: &[u64]) -> Option<usize> {
    let lower = cuts.partition_point(|cut| *cut <= interval.lower());
    (lower == cuts.partition_point(|cut| *cut <= interval.upper())).then_some(lower)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValuePhase {
    Bool(AbstractBool),
    Pointer(AbstractProvenance),
    Permission(
        AbstractProvenance,
        PermissionAvailability,
        PermissionAuthority,
        AccessPermission,
        FreeCapability,
    ),
    Tag(AbstractProvenance, VirMemoryAccess, U64Interval),
}

fn phase_values(
    values: &BTreeMap<VirValueId, AbstractValue>,
) -> impl Iterator<Item = (VirValueId, ValuePhase)> + '_ {
    values.iter().filter_map(|(&id, value)| {
        Some((
            id,
            match *value {
                AbstractValue::U64(_) => return None,
                AbstractValue::Bool(value) => ValuePhase::Bool(value),
                AbstractValue::Pointer(pointer) => ValuePhase::Pointer(pointer.provenance()),
                AbstractValue::Permission(p) => ValuePhase::Permission(
                    p.provenance(),
                    p.availability(),
                    p.authority(),
                    p.access(),
                    p.free_capability(),
                ),
                AbstractValue::EnumDiscriminant(tag) => {
                    ValuePhase::Tag(tag.pointer().provenance(), tag.access(), tag.interval())
                }
            },
        ))
    })
}
