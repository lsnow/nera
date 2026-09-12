use crate::GateStep;

use super::{Regression, RegressionEntry};
use crate::regression::checks::*;

pub(super) const ENTRIES: &[RegressionEntry] = &[
    (
        GateStep::Phase711Identity,
        Regression {
            check: check_phase7_identity_regression,
            tests: &[
                "hir_program",
                "hir_control",
                "hir_place",
                "vir_source_map",
                "typed_spec_ir",
                "verifier_cfg",
                "verifier_contracts",
                "verifier_cases",
            ],
            library: true,
            snapshots: true,
            native: false,
        },
    ),
    (
        GateStep::Phase712Capability,
        Regression {
            check: check_phase7_capability_regression,
            tests: &[
                "hir_program",
                "vir_memory_schema",
                "aggregate_abi",
                "frontend_calls",
                "vir_object_effect",
                "object_effect_runtime",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
    ),
    (
        GateStep::Phase713ResourcePayload,
        Regression {
            check: check_phase7_resource_payload_regression,
            tests: &[
                "vir_object_shape",
                "vir_memory_schema",
                "vir_object_effect",
                "verifier_object_state",
                "verifier_properties",
                "object_effect_runtime",
                "resource_payload",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
    ),
    (
        GateStep::Phase714GuardedResource,
        Regression {
            check: check_phase7_guarded_resource_regression,
            tests: &[
                "verifier_cfg",
                "verifier_guarded",
                "verifier_properties",
                "resource_payload",
            ],
            library: true,
            snapshots: false,
            native: false,
        },
    ),
    (
        GateStep::Phase715CopyMove,
        Regression {
            check: check_phase7_copy_move_regression,
            tests: &[
                "frontend_copy_move",
                "frontend_calls",
                "resource_payload",
                "verifier_object_state",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
    ),
    (
        GateStep::Phase716BuiltinDrop,
        Regression {
            check: check_phase7_builtin_drop_regression,
            tests: &[
                "frontend_drop",
                "frontend_copy_move",
                "frontend_calls",
                "frontend_control_flow",
                "frontend_loops",
                "frontend_for_match",
                "resource_payload",
                "verifier_cfg",
                "verifier_guarded",
                "vir_object_effect",
                "object_effect_runtime",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
    ),
    (
        GateStep::Phase717AggregateTransfer,
        Regression {
            check: check_phase7_aggregate_transfer_regression,
            tests: &[
                "aggregate_abi",
                "frontend_aggregate_transfer",
                "frontend_calls",
                "frontend_copy_move",
                "frontend_drop",
                "resource_payload",
                "verifier_cfg",
                "verifier_guarded",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
    ),
    (
        GateStep::Phase718ResourceAcceptance,
        Regression {
            check: check_phase7_resource_acceptance,
            tests: &[
                "stage7_resource_acceptance",
                "frontend_copy_move",
                "frontend_drop",
                "frontend_aggregate_transfer",
                "resource_payload",
                "verifier_cfg",
                "verifier_guarded",
                "verifier_properties",
                "verifier_object_state",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
    ),
];
