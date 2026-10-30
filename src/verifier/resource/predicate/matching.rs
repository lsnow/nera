//! Bounded matching of actual sealed resource groups. Coordinates index
//! candidates only; complete typed descriptors must still compare exactly.
//! This module neither proves logical equivalence nor restores authority.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct MemberCoordinate {
    allocation: AbstractAllocationId,
    carrier: Option<VirValueId>,
    storage: Option<(AbstractAllocationId, ResourcePayloadKey)>,
}

fn coordinates(instance: &PredicateInstance) -> Vec<MemberCoordinate> {
    instance
        .resources
        .iter()
        .map(|r| MemberCoordinate {
            allocation: r.allocation,
            carrier: r.carrier,
            storage: r.storage,
        })
        .collect()
}

fn has_carriers(instance: &PredicateInstance) -> bool {
    !instance.resources.is_empty()
        && instance.resources.len() <= MAX_PREDICATE_RESOURCES
        && instance
            .resources
            .iter()
            .all(|r| matches!((r.carrier, r.storage), (Some(_), None) | (None, Some(_))))
}

impl ResourceState {
    /// Map each left package to exactly one right package. Only selected,
    /// closed, unsuspended packages may change holder; all others remain pinned.
    pub(super) fn match_predicate_groups(
        &self,
        other: &Self,
        flexible: &BTreeSet<PredicateHolder>,
    ) -> Result<BTreeMap<PredicateHolder, PredicateHolder>, PredicateError> {
        if self.predicates.len() > MAX_PREDICATE_INSTANCES
            || flexible.len() > MAX_PREDICATE_INSTANCES
            || self.predicates.len() != other.predicates.len()
            || self
                .predicates
                .values()
                .chain(other.predicates.values())
                .any(|p| p.resources.len() > MAX_PREDICATE_RESOURCES)
        {
            return Err(PredicateError::InvalidBinding);
        }
        let mut index = BTreeMap::new();
        if !flexible.is_empty() {
            for (holder, instance) in &other.predicates {
                if instance.folded
                    && instance.opening_action.is_none()
                    && instance.borrowed_by.is_empty()
                    && has_carriers(instance)
                    && index.insert(coordinates(instance), *holder).is_some()
                {
                    return Err(PredicateError::AliasedAuthority);
                }
            }
        }
        let mut matches = BTreeMap::new();
        let mut used = BTreeSet::new();
        for (holder, instance) in &self.predicates {
            let target = if flexible.contains(holder) {
                if !instance.folded
                    || instance.opening_action.is_some()
                    || !instance.borrowed_by.is_empty()
                    || !has_carriers(instance)
                {
                    return Err(PredicateError::InvalidBinding);
                }
                let target = *index
                    .get(&coordinates(instance))
                    .ok_or(PredicateError::MissingHolder)?;
                let candidate = &other.predicates[&target];
                // Allocation/SSA/storage coordinates locate a candidate. They
                // do not identify a declaration, pointer type, range or loan.
                if candidate.definition != instance.definition
                    || candidate.resources != instance.resources
                {
                    return Err(PredicateError::InvalidBinding);
                }
                target
            } else {
                if !other.predicates.contains_key(holder) {
                    return Err(PredicateError::MissingHolder);
                }
                *holder
            };
            if !used.insert(target) {
                return Err(PredicateError::AliasedAuthority);
            }
            matches.insert(*holder, target);
        }
        Ok(matches)
    }

    /// Choose one entire existing labeling. Taking per-package minima can
    /// assign the same holder twice when predecessors exchange two packages.
    /// Include the binder scopes in the same choice: taking separate minima
    /// could identify two independent binders after reordered calls. A total
    /// order on whole labelings is symmetric and stable under rejoin.
    /// Call only after establishing a complete resource-group bijection.
    pub(super) fn prefer_predicate_labels(&self, other: &Self) -> bool {
        self.predicates
            .iter()
            .map(|(h, p)| (*h, coordinates(p), p.logic_scope))
            .cmp(
                other
                    .predicates
                    .iter()
                    .map(|(h, p)| (*h, coordinates(p), p.logic_scope)),
            )
            != std::cmp::Ordering::Greater
    }
}
