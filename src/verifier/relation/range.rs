//! Bounded queries over already evaluated, non-wrapping affine byte endpoints.
//! Numeric evidence never installs permission, liveness or initialized bytes.
use super::kernel::{bound_le_status, interval_le_status};
use super::{
    RelationComparison,
    difference::{
        DifferenceEvidence, DifferenceGoal, DifferenceLimits, DifferenceStop, solve_difference,
        word,
    },
    kernel, local,
};
use crate::{
    AbstractByteRange, AbstractPointer, ObligationStatus as S, ResourceState, SymbolicRangeBound,
    U64Interval,
};

pub(in crate::verifier) fn interval_coverage(
    permission: AbstractByteRange,
    pointer: AbstractPointer,
    width: u64,
) -> S {
    if let AbstractByteRange::Exact(permission) = permission {
        if permission.length() < width {
            return S::Refuted;
        }
        let safe_start = permission.start();
        let safe_end = permission.end() - width;
        let offset = pointer.offset_bytes();
        return if offset.lower() >= safe_start && offset.upper() <= safe_end {
            S::Proven
        } else if offset.upper() < safe_start || offset.lower() > safe_end {
            S::Refuted
        } else {
            S::Unknown
        };
    }
    let Some((permission_start, permission_end)) = permission.bounds() else {
        return S::Unknown;
    };
    let pointer_start = pointer
        .offset_expression()
        .map(|expression| SymbolicRangeBound::new(expression, pointer.offset_bytes()));
    let pointer_end_interval = match (
        pointer.offset_bytes().lower().checked_add(width),
        pointer.offset_bytes().upper().checked_add(width),
    ) {
        (Some(lower), Some(upper)) => {
            U64Interval::new(lower, upper).unwrap_or_else(|_| U64Interval::unknown())
        }
        (None, _) => return S::Refuted,
        (Some(_), None) => return S::Unknown,
    };
    let pointer_end = pointer_start.and_then(|start| start.checked_add_constant(width));
    combine([
        pointer_start.map_or_else(
            || interval_le_status(permission_start.interval(), pointer.offset_bytes()),
            |pointer| bound_le_status(permission_start, pointer),
        ),
        pointer_end.map_or_else(
            || interval_le_status(pointer_end_interval, permission_end.interval()),
            |pointer| bound_le_status(pointer, permission_end),
        ),
    ])
}

fn combine(statuses: [S; 2]) -> S {
    if statuses.contains(&S::Refuted) {
        S::Refuted
    } else if statuses == [S::Proven; 2] {
        S::Proven
    } else {
        S::Unknown
    }
}

pub fn covers_access(
    state: &ResourceState,
    outer: AbstractByteRange,
    pointer: AbstractPointer,
    width: u64,
    limits: DifferenceLimits,
) -> (S, Vec<BoundEvidence>) {
    let fast = interval_coverage(outer, pointer, width);
    if fast != S::Unknown {
        return (fast, Vec::new());
    }
    contained(state, outer, access_range(pointer, width), limits)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundEvidence {
    /// Projection/theory failure, separate from an inconclusive closure.
    pub stop: Option<DifferenceStop>,
    pub left: SymbolicRangeBound,
    pub right: SymbolicRangeBound,
    pub threshold: Option<i128>,
    pub difference: Option<DifferenceEvidence>,
    pub status: S,
    /// Equal terms were subtracted from both sides before a difference query.
    pub cancelled: Option<(crate::AffineExpression, crate::AffineExpression)>,
}

pub fn ordered(
    state: &ResourceState,
    left: SymbolicRangeBound,
    right: SymbolicRangeBound,
    limits: DifferenceLimits,
) -> BoundEvidence {
    let mut out = BoundEvidence {
        stop: None,
        left,
        right,
        threshold: None,
        difference: None,
        status: kernel::bound_le_status(left, right),
        cancelled: None,
    };
    if out.status != S::Unknown {
        return out;
    }
    let (a, b) = left.expression().cancel_common(right.expression());
    if (a, b) != (left.expression(), right.expression()) {
        out.cancelled = Some((a, b));
    }
    if (!a.is_constant() && a.root().is_none()) || (!b.is_constant() && b.root().is_none()) {
        out.stop = Some(DifferenceStop::InvalidInput);
        return out;
    }
    if a.is_constant() && b.is_constant() {
        out.status = if a.addend() <= b.addend() {
            S::Proven
        } else {
            S::Refuted
        };
        return out;
    }
    match (a.root(), b.root()) {
        (None, Some(y)) if b.scale() != 0 => {
            let delta = i128::from(a.addend()) - i128::from(b.addend());
            let k = -(-delta).div_euclid(i128::from(b.scale()));
            if let Ok(k) = u64::try_from(k) {
                out.threshold = Some(i128::from(k));
                (out.status, out.difference, out.stop) = local::compare_observed(
                    state,
                    RelationComparison::LessOrEqual,
                    super::RelationTerm::Constant(k),
                    word(y),
                    limits,
                );
            }
            return out;
        }
        (Some(x), None) if a.scale() != 0 => {
            let k =
                (i128::from(b.addend()) - i128::from(a.addend())).div_euclid(i128::from(a.scale()));
            if let Ok(k) = u64::try_from(k) {
                out.threshold = Some(i128::from(k));
                (out.status, out.difference, out.stop) = local::compare_observed(
                    state,
                    RelationComparison::LessOrEqual,
                    word(x),
                    super::RelationTerm::Constant(k),
                    limits,
                );
            }
            return out;
        }
        _ => {}
    }
    let (Some(x), Some(y)) = (a.root(), b.root()) else {
        return out;
    };
    if a.scale() == 0 || a.scale() != b.scale() {
        out.stop = Some(DifferenceStop::InvalidInput);
        return out;
    }
    // a*x+c <= a*y+d iff x-y <= floor((d-c)/a), over integers.
    let threshold =
        (i128::from(b.addend()) - i128::from(a.addend())).div_euclid(i128::from(a.scale()));
    out.threshold = Some(threshold);
    let goal = DifferenceGoal {
        comparison: RelationComparison::LessOrEqual,
        left: word(x),
        right: word(y),
    };
    let premises = match local::project(state, goal, limits) {
        Ok(premises) => premises,
        Err(stop) => {
            out.stop = Some(stop);
            return out;
        }
    };
    let proof = solve_difference(&premises, goal, limits);
    if proof.stop == DifferenceStop::Complete {
        let statuses = proof
            .branches
            .iter()
            .filter(|b| b.contradiction.is_none())
            .map(|branch| {
                if branch.bounds.iter().any(|bound| {
                    bound.left == Some(x) && bound.right == Some(y) && bound.bound <= threshold
                }) {
                    S::Proven
                } else if branch.bounds.iter().any(|bound| {
                    bound.left == Some(y) && bound.right == Some(x) && bound.bound < -threshold
                }) {
                    S::Refuted
                } else {
                    S::Unknown
                }
            })
            .collect::<Vec<_>>();
        if !statuses.is_empty() && statuses.iter().all(|s| *s == S::Proven) {
            out.status = S::Proven;
        } else if !statuses.is_empty() && statuses.iter().all(|s| *s == S::Refuted) {
            out.status = S::Refuted;
        }
    }
    out.difference = Some(proof);
    out
}

pub fn contained(
    state: &ResourceState,
    outer: AbstractByteRange,
    inner: AbstractByteRange,
    limits: DifferenceLimits,
) -> (S, Vec<BoundEvidence>) {
    let (Some((a, b)), Some((x, y))) = (outer.bounds(), inner.bounds()) else {
        return (S::Unknown, Vec::new());
    };
    let evidence = vec![ordered(state, a, x, limits), ordered(state, y, b, limits)];
    let status = if evidence.iter().any(|e| e.status == S::Refuted) {
        S::Refuted
    } else if evidence.iter().all(|e| e.status == S::Proven) {
        S::Proven
    } else {
        S::Unknown
    };
    (status, evidence)
}

pub fn access_range(pointer: AbstractPointer, width: u64) -> AbstractByteRange {
    let Some(start) = kernel::symbolic_bound(pointer.offset_bytes(), pointer.offset_expression())
    else {
        // Failing containment of an envelope is not a refutation of every
        // concrete selection. Preserve the interval fast path separately.
        return AbstractByteRange::Unknown;
    };
    start
        .checked_add_constant(width)
        .map_or(AbstractByteRange::Unknown, |end| {
            AbstractByteRange::from_bounds(start, end)
        })
}

pub fn non_overlapping(
    state: &ResourceState,
    left: AbstractPointer,
    right: AbstractPointer,
    width: u64,
    limits: DifferenceLimits,
) -> (S, Option<DisjointEvidence>) {
    let fast = kernel::object_non_overlap_status(left, right, width);
    if fast != S::Unknown {
        return (fast, None);
    }
    disjoint(
        state,
        left.provenance(),
        access_range(left, width),
        right.provenance(),
        access_range(right, width),
        limits,
    )
}

/// Numeric derivation only: no allocation or loan authority is manufactured.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisjointEvidence {
    pub left: AbstractByteRange,
    pub right: AbstractByteRange,
    pub orders: [BoundEvidence; 2],
    pub index_separation: Option<DifferenceEvidence>,
    pub index_stop: Option<DifferenceStop>,
    pub failed_bands: Vec<RangeReductionEvidence>,
    pub status: S,
    /// Bounded layout reduction; only Proven is transported back. A derived
    /// band is never installed as an actual permission/access range.
    pub bands: Option<RangeReductionEvidence>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeReductionEvidence {
    pub rule: RangeReductionRule,
    pub proof: Box<DisjointEvidence>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeReductionRule {
    CommonTranslation,
    FixedStrideBands {
        left_root: crate::VirValueId,
        right_root: crate::VirValueId,
        stride: u64,
    },
}

pub fn disjoint(
    state: &ResourceState,
    left_provenance: crate::AbstractProvenance,
    left: AbstractByteRange,
    right_provenance: crate::AbstractProvenance,
    right: AbstractByteRange,
    limits: DifferenceLimits,
) -> (S, Option<DisjointEvidence>) {
    use crate::AbstractProvenance::Known;
    match (left_provenance, right_provenance) {
        (Known(a), Known(b)) if a != b => return (S::Proven, None),
        (Known(_), Known(_)) => {}
        _ => return (S::Unknown, None),
    }
    disjoint_same_allocation(state, left, right, limits)
}

fn disjoint_same_allocation(
    state: &ResourceState,
    left: AbstractByteRange,
    right: AbstractByteRange,
    limits: DifferenceLimits,
) -> (S, Option<DisjointEvidence>) {
    let (Some((a, b)), Some((x, y))) = (left.bounds(), right.bounds()) else {
        return (S::Unknown, None);
    };
    if a.expression() == b.expression() || x.expression() == y.expression() {
        return (S::Proven, None);
    }
    let orders = [ordered(state, b, x, limits), ordered(state, y, a, limits)];
    let mut status = if orders.iter().any(|e| e.status == S::Proven) {
        S::Proven
    } else if orders.iter().all(|e| e.status == S::Refuted) {
        S::Refuted
    } else {
        S::Unknown
    };
    let mut index_separation = None;
    let mut index_stop = None;
    // Disjunction matters: i != j permits either order, without choosing one
    // globally. Equal-base slots of positive width <= stride cannot overlap
    // when their integer indices differ. An offset inequality alone is unsafe.
    if status == S::Unknown {
        let (aa, bb, xx, yy) = (
            a.expression(),
            b.expression(),
            x.expression(),
            y.expression(),
        );
        if let (Some(i), Some(j), Some(left_width), Some(right_width)) = (
            aa.root(),
            xx.root(),
            bb.addend().checked_sub(aa.addend()),
            yy.addend().checked_sub(xx.addend()),
        ) {
            if aa.scale() > 0
                && aa.scale() == xx.scale()
                && aa.addend() == xx.addend()
                && aa.root() == bb.root()
                && aa.scale() == bb.scale()
                && xx.root() == yy.root()
                && xx.scale() == yy.scale()
                && (1..=aa.scale()).contains(&left_width)
                && (1..=aa.scale()).contains(&right_width)
            {
                (status, index_separation, index_stop) = local::compare_observed(
                    state,
                    RelationComparison::NotEqual,
                    word(i),
                    word(j),
                    limits,
                );
            }
        }
    }
    let mut bands = None;
    let mut failed_bands = Vec::new();
    if status == S::Unknown {
        // At most 2x2 anchor pairs. Every recursive query has single-root
        // endpoints, so this projection cannot recurse or enumerate offsets.
        if let Some(proof) = band_disjointness(state, left, right, limits, &mut failed_bands) {
            status = S::Proven;
            bands = Some(proof);
        }
    }
    (
        status,
        Some(DisjointEvidence {
            left,
            right,
            orders,
            index_separation,
            index_stop,
            failed_bands,
            status,
            bands,
        }),
    )
}

fn evaluated(
    state: &ResourceState,
    expression: crate::AffineExpression,
) -> Option<SymbolicRangeBound> {
    let interval = expression.interval(|id| match state.value(id)? {
        crate::AbstractValue::U64(value) => Some(*value),
        _ => None,
    })?;
    Some(SymbolicRangeBound::new(expression, interval))
}

fn band(
    state: &ResourceState,
    range: AbstractByteRange,
    root: crate::VirValueId,
    scale: u64,
) -> Option<AbstractByteRange> {
    let (a, b) = range.bounds()?;
    if !a.expression().same_terms(b.expression()) {
        return None;
    }
    let low = evaluated(state, a.expression().without_root(root))?
        .interval()
        .lower();
    let high = evaluated(state, b.expression().without_root(root))?
        .interval()
        .upper();
    let anchor = crate::AffineExpression::identity(root).checked_scale(scale)?;
    Some(AbstractByteRange::from_bounds(
        evaluated(state, anchor.checked_add_constant(low)?)?,
        evaluated(state, anchor.checked_add_constant(high)?)?,
    ))
}

fn band_disjointness(
    state: &ResourceState,
    left: AbstractByteRange,
    right: AbstractByteRange,
    limits: DifferenceLimits,
    failed: &mut Vec<RangeReductionEvidence>,
) -> Option<RangeReductionEvidence> {
    let (a, b) = left.bounds()?;
    let (x, y) = right.bounds()?;
    let multi = |e: crate::AffineExpression| !e.is_constant() && e.root().is_none();
    if ![a, b, x, y].iter().any(|b| multi(b.expression())) {
        return None;
    }
    // First remove a translation shared by both complete accesses. This is
    // what makes same-row column disequality independent of the row index.
    let (aa, xx) = a.expression().cancel_common(x.expression());
    let (bb, yy) = b.expression().cancel_common(y.expression());
    if a.expression().same_terms(b.expression())
        && x.expression().same_terms(y.expression())
        && ![aa, bb, xx, yy].iter().any(|e| multi(*e))
    {
        let l = AbstractByteRange::from_bounds(evaluated(state, aa)?, evaluated(state, bb)?);
        let r = AbstractByteRange::from_bounds(evaluated(state, xx)?, evaluated(state, yy)?);
        let (status, evidence) = disjoint_same_allocation(state, l, r, limits);
        if status == S::Proven {
            return evidence.map(|proof| RangeReductionEvidence {
                rule: RangeReductionRule::CommonTranslation,
                proof: Box::new(proof),
            });
        }
        if let Some(proof) = evidence {
            failed.push(RangeReductionEvidence {
                rule: RangeReductionRule::CommonTranslation,
                proof: Box::new(proof),
            });
        }
    }
    for (i, s) in a.expression().terms().into_iter().flatten() {
        for (j, t) in x.expression().terms().into_iter().flatten() {
            if s != t {
                continue;
            }
            let (Some(l), Some(r)) = (band(state, left, i, s), band(state, right, j, t)) else {
                continue;
            };
            let (status, evidence) = disjoint_same_allocation(state, l, r, limits);
            if status == S::Proven {
                return evidence.map(|proof| RangeReductionEvidence {
                    rule: RangeReductionRule::FixedStrideBands {
                        left_root: i,
                        right_root: j,
                        stride: s,
                    },
                    proof: Box::new(proof),
                });
            }
            if let Some(proof) = evidence {
                failed.push(RangeReductionEvidence {
                    rule: RangeReductionRule::FixedStrideBands {
                        left_root: i,
                        right_root: j,
                        stride: s,
                    },
                    proof: Box::new(proof),
                });
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AbstractAllocationId, AbstractProvenance, AbstractValue, AffineExpression,
        GuaranteedAlignment, PathFact, U64Interval, VirIntegerPredicate, VirMemoryAccess,
        VirValueId,
    };

    #[test]
    fn two_dimensional_band_and_translation_rules_match_independent_integer_oracle() {
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        let mut saw_bands = false;
        for same_row in [true, false] {
            let mut state = ResourceState::new();
            for id in 0..4 {
                state
                    .define_value(
                        VirValueId::new(id),
                        AbstractValue::U64(U64Interval::new(0, 2).unwrap()),
                    )
                    .unwrap();
            }
            let (a, b) = if same_row { (2, 3) } else { (0, 1) };
            state.conjoin_path_fact(PathFact::comparison(
                VirIntegerPredicate::NotEqual,
                VirValueId::new(a),
                VirValueId::new(b),
            ));
            for row_stride in [8, 24, 32] {
                for col_stride in [4, 8] {
                    for width in [1, 8, 16] {
                        let make = |row, col| {
                            let expression = AffineExpression::identity(VirValueId::new(row))
                                .checked_scale(row_stride)
                                .unwrap()
                                .checked_add(
                                    AffineExpression::identity(VirValueId::new(col))
                                        .checked_scale(col_stride)
                                        .unwrap(),
                                )
                                .unwrap();
                            let start = evaluated(&state, expression).unwrap();
                            AbstractByteRange::from_bounds(
                                start,
                                start.checked_add_constant(width).unwrap(),
                            )
                        };
                        let left = make(0, 2);
                        let right = make(if same_row { 0 } else { 1 }, 3);
                        let (status, evidence) = disjoint(
                            &state,
                            provenance,
                            left,
                            provenance,
                            right,
                            Default::default(),
                        );
                        saw_bands |= evidence.as_ref().is_some_and(|e| e.bands.is_some());
                        for r in 0..3 {
                            for s in 0..3 {
                                for c in 0..3 {
                                    for d in 0..3 {
                                        if (same_row && c == d) || (!same_row && r == s) {
                                            continue;
                                        }
                                        let x = row_stride * r + col_stride * c;
                                        let y = row_stride * (if same_row { r } else { s })
                                            + col_stride * d;
                                        let disjoint = x + width <= y || y + width <= x;
                                        if status == S::Proven {
                                            assert!(disjoint, "{evidence:?} / {r},{s},{c},{d}");
                                        }
                                        if status == S::Refuted {
                                            assert!(!disjoint, "{evidence:?}");
                                        }
                                    }
                                }
                            }
                        }
                        if (!same_row && row_stride >= 2 * col_stride + width)
                            || (same_row && width <= col_stride)
                        {
                            assert_eq!(status, S::Proven, "{evidence:?}");
                        }
                    }
                }
            }
        }
        assert!(saw_bands);
    }

    #[test]
    fn ordered_two_root_cancellation_never_treats_a_sum_as_constant() {
        let state = state(VirIntegerPredicate::LessThan);
        let shared = AffineExpression::identity(VirValueId::new(0))
            .checked_scale(32)
            .unwrap();
        let left = shared
            .checked_add(
                AffineExpression::identity(VirValueId::new(1))
                    .checked_scale(8)
                    .unwrap(),
            )
            .unwrap();
        let bound = evaluated(&state, left).unwrap();
        assert_eq!(
            ordered(
                &state,
                bound,
                bound.checked_add_constant(8).unwrap(),
                Default::default()
            )
            .status,
            S::Proven
        );
        // Neither a zero addend nor a missing *single* root denotes zero.
        assert_ne!(
            ordered(
                &state,
                bound,
                SymbolicRangeBound::constant(0),
                Default::default()
            )
            .status,
            S::Proven
        );
    }

    fn state(predicate: VirIntegerPredicate) -> ResourceState {
        let mut state = ResourceState::new();
        for id in [0, 1] {
            state
                .define_value(
                    VirValueId::new(id),
                    AbstractValue::U64(U64Interval::new(0, 3).unwrap()),
                )
                .unwrap();
        }
        state.conjoin_path_fact(PathFact::comparison(
            predicate,
            VirValueId::new(0),
            VirValueId::new(1),
        ));
        state
    }

    fn bound(id: u32, scale: u64, add: u64) -> SymbolicRangeBound {
        SymbolicRangeBound::new(
            AffineExpression::identity(VirValueId::new(id))
                .checked_scale(scale)
                .unwrap()
                .checked_add_constant(add)
                .unwrap(),
            U64Interval::new(add, 3 * scale + add).unwrap(),
        )
    }

    #[test]
    fn scaled_endpoint_query_matches_independent_finite_integer_oracle() {
        for predicate in [
            VirIntegerPredicate::LessThan,
            VirIntegerPredicate::LessOrEqual,
            VirIntegerPredicate::NotEqual,
        ] {
            let state = state(predicate);
            for scale in [1, 4, 8] {
                for a in 0..4 {
                    for b in 0..4 {
                        let proof = ordered(
                            &state,
                            bound(0, scale, a),
                            bound(1, scale, b),
                            DifferenceLimits::default(),
                        );
                        let outcomes = (0..4)
                            .flat_map(|x| (0..4).map(move |y| (x, y)))
                            .filter(|(x, y)| match predicate {
                                VirIntegerPredicate::LessThan => x < y,
                                VirIntegerPredicate::LessOrEqual => x <= y,
                                _ => x != y,
                            })
                            .map(|(x, y)| scale * x + a <= scale * y + b)
                            .collect::<Vec<_>>();
                        assert!(!outcomes.is_empty());
                        if proof.status == S::Proven {
                            assert!(outcomes.iter().all(|v| *v), "{proof:?}");
                        }
                        if proof.status == S::Refuted {
                            assert!(outcomes.iter().all(|v| !*v), "{proof:?}");
                        }
                        // Also independently check ceil/floor normalization
                        // when exactly one endpoint is constant.
                        for constant in 0..=3 * scale + b {
                            for reversed in [false, true] {
                                let mut endpoints =
                                    [bound(0, scale, a), SymbolicRangeBound::constant(constant)];
                                if reversed {
                                    endpoints.swap(0, 1);
                                }
                                let proof = ordered(
                                    &state,
                                    endpoints[0],
                                    endpoints[1],
                                    DifferenceLimits::default(),
                                );
                                for (x, y) in (0..4).flat_map(|x| (0..4).map(move |y| (x, y))) {
                                    let admissible = match predicate {
                                        VirIntegerPredicate::LessThan => x < y,
                                        VirIntegerPredicate::LessOrEqual => x <= y,
                                        _ => x != y,
                                    };
                                    if !admissible {
                                        continue;
                                    }
                                    let holds = if reversed {
                                        constant <= scale * x + a
                                    } else {
                                        scale * x + a <= constant
                                    };
                                    if proof.status == S::Proven {
                                        assert!(holds, "{proof:?}");
                                    }
                                    if proof.status == S::Refuted {
                                        assert!(!holds, "{proof:?}");
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn slot_disjointness_matches_independent_byte_interval_oracle() {
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        for predicate in [
            VirIntegerPredicate::NotEqual,
            VirIntegerPredicate::Equal,
            VirIntegerPredicate::LessOrEqual,
        ] {
            let state = state(predicate);
            for stride in [1, 4, 8] {
                for left_width in [0, 1, stride, stride + 1] {
                    for right_width in [1, stride, stride + 1] {
                        for shift in [0, 1] {
                            let a = bound(0, stride, 0);
                            let b = bound(1, stride, shift);
                            let left = AbstractByteRange::from_bounds(
                                a,
                                a.checked_add_constant(left_width).unwrap(),
                            );
                            let right = AbstractByteRange::from_bounds(
                                b,
                                b.checked_add_constant(right_width).unwrap(),
                            );
                            let (status, evidence) = disjoint(
                                &state,
                                provenance,
                                left,
                                provenance,
                                right,
                                DifferenceLimits::default(),
                            );
                            for (i, j) in (0..4).flat_map(|i| (0..4).map(move |j| (i, j))) {
                                if !match predicate {
                                    VirIntegerPredicate::NotEqual => i != j,
                                    VirIntegerPredicate::Equal => i == j,
                                    _ => i <= j,
                                } {
                                    continue;
                                }
                                let concrete = left_width == 0
                                    || stride * i + left_width <= stride * j + shift
                                    || stride * j + shift + right_width <= stride * i;
                                match status {
                                    S::Proven => assert!(concrete, "{evidence:?}, i={i}, j={j}"),
                                    S::Refuted => assert!(!concrete, "{evidence:?}, i={i}, j={j}"),
                                    S::Unknown => {}
                                }
                            }
                            if left_width == stride
                                && right_width == stride
                                && shift == 0
                                && predicate == VirIntegerPredicate::NotEqual
                            {
                                assert_eq!(status, S::Proven);
                                assert!(evidence.unwrap().index_separation.is_some());
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn relation_non_overlap_needs_provenance_and_respects_budget() {
        let state = state(VirIntegerPredicate::LessThan);
        let pointer = |id, provenance| {
            let b = bound(id, 8, 0);
            AbstractPointer::new(
                provenance,
                b.interval(),
                GuaranteedAlignment::new(8).unwrap(),
            )
            .with_offset_expression(Some(b.expression()))
            .with_memory_access(Some(VirMemoryAccess::core_u64()))
        };
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        let (left, right) = (pointer(0, provenance), pointer(1, provenance));
        assert_eq!(
            non_overlapping(&state, left, right, 8, DifferenceLimits::default()).0,
            S::Proven
        );
        assert_eq!(
            non_overlapping(
                &state,
                left,
                pointer(1, AbstractProvenance::Unknown),
                8,
                DifferenceLimits::default()
            )
            .0,
            S::Unknown
        );
        assert_eq!(
            non_overlapping(
                &state,
                left,
                right,
                8,
                DifferenceLimits {
                    max_steps: 0,
                    ..DifferenceLimits::default()
                }
            )
            .0,
            S::Unknown
        );
        assert_eq!(
            non_overlapping(&state, left, left, 8, DifferenceLimits::default()).0,
            S::Refuted
        );
    }
}
