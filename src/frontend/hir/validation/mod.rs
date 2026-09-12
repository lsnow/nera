//! Utilities shared by independent HIR validation passes.

use std::collections::BTreeSet;

mod spec;

pub(super) fn validate_specs(
    program: &super::HirProgram,
) -> Result<(), super::HirProgramValidationError> {
    spec::validate_specs(program)
}

pub(super) fn all_unique<T: Ord>(items: impl IntoIterator<Item = T>) -> bool {
    let mut seen = BTreeSet::new();
    items.into_iter().all(|item| seen.insert(item))
}
