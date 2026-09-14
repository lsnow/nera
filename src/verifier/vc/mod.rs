//! Bounded, shared representation and evaluation of verification conditions.

mod arena;
mod eval;
mod normalize;

pub(super) use arena::VcArena;
pub(super) use arena::{VcLimits, VcTermId};
pub(super) use eval::{
    SnapshotValues, VcQueryBudget, evaluate_bool, evaluate_contract_bool, evaluate_contract_u64,
    evaluate_u64, validate_witness,
};
pub(super) use normalize::VcNormalizer;
