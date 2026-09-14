//! Shared syntax only. These claims neither allocate nor supply authority.

/// Bounded, entry-bound index in a contract memory observation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecMemoryIndex {
    Constant(u64),
    Parameter(u32),
}

/// One canonical projection; nested pointer chasing is deliberately absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecMemoryProjection<F> {
    Cell,
    Field(F),
    Index(SpecMemoryIndex),
}

/// Requested access, to be matched against existing runtime authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SpecAccess {
    Read,
    Write,
}

/// Half-open byte range relative to the observed pointer. `authority` names
/// an existing HIR owner/reference or VIR permission snapshot, never a newly
/// minted permission. Lowering resolves the owner's physical permission slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecMemoryClaim<S, T, L> {
    pub pointer: S,
    pub authority: S,
    pub start_bytes: T,
    pub end_bytes: T,
    pub layout: L,
    pub access: SpecAccess,
}

/// Geometry only; this descriptor carries no access authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecMemoryRange<S, T, L> {
    pub pointer: S,
    pub start_bytes: T,
    pub end_bytes: T,
    pub layout: L,
}

/// Assertion syntax is separate from Bool terms. Separation edges are ordered
/// occurrences: `[a, a]` must remain two uses even when the node is shared.
/// Exists binds one clause-owned scalar binder in `body`, never in `witness`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecAssertionKind<T, A, B, S, L> {
    /// Entry-bound public effect upper bound, never an access capability.
    Footprint {
        write: bool,
        range: Option<SpecMemoryRange<S, T, L>>,
    },
    Disjoint {
        left: SpecMemoryRange<S, T, L>,
        right: SpecMemoryRange<S, T, L>,
    },
    Pure(T),
    /// State observations, not authority. Identity includes allocation instance.
    Alive(S),
    SameAllocation {
        left: S,
        right: S,
    },
    Initialized {
        pointer: S,
        start_bytes: T,
        end_bytes: T,
        layout: L,
    },
    Permission(SpecMemoryClaim<S, T, L>),
    PointsTo {
        memory: SpecMemoryClaim<S, T, L>,
        /// None matches a valid initialized scalar without claiming its value.
        value: Option<T>,
    },
    Separation(Vec<A>),
    Exists {
        binder: B,
        body: A,
        witness: Option<T>,
    },
}

impl<T, A, B, S, L> SpecAssertionKind<T, A, B, S, L> {
    /// Direct runtime observations; child assertions are visited separately.
    pub(crate) fn snapshots(&self) -> impl Iterator<Item = &S> {
        let snapshots = match self {
            Self::Footprint { range, .. } => [range.as_ref().map(|r| &r.pointer), None],
            Self::Disjoint { left, right } => [Some(&left.pointer), Some(&right.pointer)],
            Self::Alive(pointer) | Self::Initialized { pointer, .. } => [Some(pointer), None],
            Self::SameAllocation { left, right } => [Some(left), Some(right)],
            Self::Permission(memory) | Self::PointsTo { memory, .. } => {
                [Some(&memory.pointer), Some(&memory.authority)]
            }
            _ => [None, None],
        };
        snapshots.into_iter().flatten()
    }
}

use std::collections::BTreeSet;

/// Validation-only graph, never a second resource state.
pub(crate) struct ScopeNode {
    pub terms: Vec<usize>,
    pub children: Vec<usize>,
    pub binder: Option<u32>,
}

/// Child-first DAG free-variable analysis. A binder is removed from the body,
/// then witness dependencies are added in the enclosing scope. Work is bounded
/// even for heavily shared terms and assertions. No occurrence is deduplicated
/// in the public syntax; only free-variable sets are deduplicated here.
pub(crate) fn valid_scopes(
    terms: &[BTreeSet<u32>],
    nodes: &[ScopeNode],
    roots: &[ScopeNode],
) -> bool {
    let mut bound = BTreeSet::new();
    let mut free: Vec<BTreeSet<u32>> = Vec::new();
    let mut depths: Vec<usize> = Vec::new();
    let mut budget = 1_000_000usize;
    for (index, node) in nodes.iter().enumerate() {
        if node.binder.is_some_and(|binder| !bound.insert(binder)) {
            return false;
        }
        let mut vars = BTreeSet::new();
        let mut depth = 1;
        for &child in &node.children {
            if child >= index {
                return false;
            }
            depth = depth.max(depths[child] + 1);
            if depth > 256 || !extend(&mut vars, &free[child], &mut budget) {
                return false;
            }
        }
        if let Some(binder) = node.binder {
            vars.remove(&binder);
        }
        for &term in &node.terms {
            let Some(deps) = terms.get(term) else {
                return false;
            };
            if !extend(&mut vars, deps, &mut budget) {
                return false;
            }
        }
        free.push(vars);
        depths.push(depth);
    }
    roots.iter().all(|root| {
        root.terms
            .iter()
            .all(|&term| terms.get(term).is_some_and(|vars| vars.is_disjoint(&bound)))
            && root
                .children
                .iter()
                .all(|&child| free.get(child).is_some_and(|vars| vars.is_disjoint(&bound)))
    })
}

pub(crate) fn extend(
    target: &mut BTreeSet<u32>,
    source: &BTreeSet<u32>,
    budget: &mut usize,
) -> bool {
    let Some(left) = budget.checked_sub(source.len().saturating_add(1)) else {
        return false;
    };
    *budget = left;
    target.extend(source);
    true
}
