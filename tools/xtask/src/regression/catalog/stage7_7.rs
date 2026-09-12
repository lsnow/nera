use crate::GateStep;

use super::{Regression, RegressionEntry};
use crate::regression::checks::*;

pub(super) const ENTRIES: &[RegressionEntry] = &[
    (
        GateStep::Phase773VerifyPreview,
        Regression {
            check: check_phase7_verify_preview,
            tests: &["verify_cli", "verification_text", "verification_report"],
            library: true,
            snapshots: true,
            native: false,
        },
    ),
    (
        GateStep::Phase776VerifyAcceptance,
        Regression {
            check: check_phase7_verify_acceptance,
            tests: &[
                "verification_report",
                "verification_text",
                "verify_cli",
                "auto_memory_corpus",
                "verification_fail_closed",
                "summary_audit",
                "summary_recursive",
                "relation_audit",
                "provenance_audit",
                "ghost_non_interference",
                "native_acceptance",
                "frontend_drop",
                "typed_spec_ir",
                "verifier_contracts",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
    ),
    (
        GateStep::Phase775VerifyFailClosed,
        Regression {
            check: check_phase7_verify_fail_closed,
            tests: &[
                "verification_fail_closed",
                "verification_report",
                "verification_text",
                "verify_cli",
                "summary_audit",
                "summary_recursive",
                "relation_audit",
                "provenance_audit",
                "ghost_non_interference",
                "auto_memory_corpus",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
    ),
    (
        GateStep::Phase774AutoMemoryCorpus,
        Regression {
            check: check_phase7_auto_memory_corpus,
            tests: &[
                "auto_memory_corpus",
                "verify_cli",
                "verification_text",
                "verification_report",
                "frontend_drop",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
    ),
    (
        GateStep::Phase772SourceDiagnostics,
        Regression {
            check: check_phase7_source_diagnostics,
            tests: &[
                "verification_text",
                "verification_report",
                "typed_spec_ir",
                "verifier_contracts",
                "summary_audit",
                "summary_recursive",
            ],
            library: true,
            snapshots: true,
            native: false,
        },
    ),
    (
        GateStep::Phase771VerifyReport,
        Regression {
            check: check_phase7_verify_report,
            tests: &[
                "verification_report",
                "typed_spec_ir",
                "verifier_contracts",
                "summary_audit",
                "summary_recursive",
            ],
            library: true,
            snapshots: true,
            native: false,
        },
    ),
];
