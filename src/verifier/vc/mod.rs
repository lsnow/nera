//! Bounded, shared representation and evaluation of verification conditions.

mod arena;
mod eval;
mod normalize;

pub(super) use arena::{VcArena, VcLimits, VcTermId};
pub(super) use eval::{SnapshotValues, VcQueryBudget, evaluate_bool};
pub(super) use normalize::VcNormalizer;
