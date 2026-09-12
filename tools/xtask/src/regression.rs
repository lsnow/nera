//! Stage-specific checks and focused test selections. No commands execute here.

mod catalog;
mod checks;

use super::GateStep;
use std::{error::Error, path::Path};

#[derive(Clone, Copy)]
pub(super) struct Regression {
    pub check: fn(&Path) -> Result<(), Box<dyn Error>>,
    pub tests: &'static [&'static str],
    pub library: bool,
    pub snapshots: bool,
    pub native: bool,
}

type RegressionEntry = (GateStep, Regression);

/// Binary unit tests share the same deduplicating scheduler as library and
/// integration tests. Historical stages do not acquire a new binary dependency.
pub(super) fn binaries(step: GateStep) -> &'static [&'static str] {
    catalog::binaries(step)
}

pub(super) fn get(step: GateStep) -> Option<Regression> {
    catalog::get(step)
}
