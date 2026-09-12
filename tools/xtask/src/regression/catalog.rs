mod core;
mod stage7_1;
mod stage7_2;
mod stage7_3;
mod stage7_4;
mod stage7_5;
mod stage7_6;
mod stage7_7;
mod stage7_8;

use super::{Regression, RegressionEntry};
use crate::GateStep;

const CATALOGS: &[&[RegressionEntry]] = &[
    core::ENTRIES,
    stage7_1::ENTRIES,
    stage7_2::ENTRIES,
    stage7_3::ENTRIES,
    stage7_4::ENTRIES,
    stage7_5::ENTRIES,
    stage7_6::ENTRIES,
    stage7_7::ENTRIES,
    stage7_8::ENTRIES,
];

const BINARY_ENTRIES: &[(GateStep, &[&str])] = &[
    (GateStep::Phase773VerifyPreview, &["nera"]),
    (GateStep::Phase774AutoMemoryCorpus, &["nera"]),
    (GateStep::Phase775VerifyFailClosed, &["nera"]),
    (GateStep::Phase776VerifyAcceptance, &["nera"]),
    (GateStep::Phase781CompilationSession, &["nera"]),
    (GateStep::Phase782ModuleProgram, &["nera"]),
    (GateStep::Phase783GenericInstances, &["nera"]),
    (GateStep::Phase783NamedLifetimes, &["nera"]),
];

pub(super) fn get(step: GateStep) -> Option<Regression> {
    CATALOGS
        .iter()
        .flat_map(|entries| entries.iter())
        .find_map(|(candidate, regression)| (*candidate == step).then_some(*regression))
}

pub(super) fn binaries(step: GateStep) -> &'static [&'static str] {
    BINARY_ENTRIES
        .iter()
        .find_map(|(candidate, binaries)| (*candidate == step).then_some(*binaries))
        .unwrap_or(&[])
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{BINARY_ENTRIES, CATALOGS};
    use crate::STAGE7_GATE;

    #[test]
    fn catalog_has_one_entry_per_historical_gate_identity() {
        let mut seen = BTreeSet::new();
        for (step, _) in CATALOGS.iter().flat_map(|entries| entries.iter()) {
            assert!(
                STAGE7_GATE.contains(step),
                "cataloged step is not scheduled: {step:?}"
            );
            assert!(
                seen.insert(*step),
                "duplicate regression entry for {step:?}"
            );
        }
        assert_eq!(seen.len(), 87);
    }

    #[test]
    fn binary_catalog_has_unique_gate_identities() {
        let mut seen = BTreeSet::new();
        for (step, binaries) in BINARY_ENTRIES {
            assert!(seen.insert(*step), "duplicate binary entry for {step:?}");
            assert!(!binaries.is_empty());
        }
    }
}
