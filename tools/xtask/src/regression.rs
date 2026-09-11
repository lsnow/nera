//! Stage-specific checks and focused test selections. No commands execute here.
use super::GateStep;
use std::{error::Error, fs, path::Path};

pub(super) struct Regression {
    pub check: fn(&Path) -> Result<(), Box<dyn Error>>,
    pub tests: &'static [&'static str],
    pub library: bool,
    pub snapshots: bool,
    pub native: bool,
}

/// Binary unit tests share the same deduplicating scheduler as library and
/// integration tests. Historical stages do not acquire a new binary dependency.
pub(super) fn binaries(step: GateStep) -> &'static [&'static str] {
    match step {
        GateStep::Phase773VerifyPreview
        | GateStep::Phase774AutoMemoryCorpus
        | GateStep::Phase775VerifyFailClosed
        | GateStep::Phase776VerifyAcceptance
        | GateStep::Phase781CompilationSession
        | GateStep::Phase782ModuleProgram
        | GateStep::Phase783GenericInstances
        | GateStep::Phase783NamedLifetimes => &["nera"],
        _ => &[],
    }
}

pub(super) fn get(step: GateStep) -> Option<Regression> {
    Some(match step {
        GateStep::Place => Regression {
            check: check_place_regression,
            tests: &[
                "hir_program",
                "hir_place",
                "hir_public_api",
                "vir_v0",
                "vir_memory_schema",
                "vir_corpus",
                "vir_interpreter",
                "native_abi",
                "native_acceptance",
                "native_assembly",
                "native_codegen",
                "native_memory_codegen",
                "native_plan",
                "verifier_transfer",
                "verifier_cfg",
                "verifier_contracts",
                "verifier_cases",
                "verifier_complex_cases",
                "verifier_properties",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::ControlFlow => Regression {
            check: check_control_flow_regression,
            tests: &[
                "frontend_corpus",
                "frontend_control_flow",
                "frontend_calls",
                "frontend_loops",
                "frontend_for_match",
                "hir_program",
                "hir_control",
                "hir_public_api",
                "vir_v0",
                "vir_corpus",
                "vir_interpreter",
                "verifier_cfg",
                "verifier_contracts",
                "native_abi",
                "native_plan",
                "native_codegen",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::VirUnit => Regression {
            check: check_vir_unit_regression,
            tests: &[
                "frontend_calls",
                "hir_program",
                "hir_public_api",
                "hir_spec",
                "vir_unit_baseline",
                "vir_source_map",
                "vir_contracts",
                "typed_spec_ir",
                "ghost_non_interference",
                "vir_v0",
                "vir_corpus",
                "vir_interpreter",
                "verifier_cfg",
                "verifier_contracts",
                "native_plan",
                "native_codegen",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Aggregate => Regression {
            check: check_aggregate_regression,
            tests: &[
                "hir_program",
                "hir_place",
                "hir_public_api",
                "frontend_aggregates",
                "frontend_enums",
                "aggregate_abi",
                "vir_v0",
                "vir_memory_schema",
                "vir_object_shape",
                "vir_object_effect",
                "vir_slice_range",
                "verifier_object_state",
                "object_effect_runtime",
                "vir_local_storage",
                "vir_corpus",
                "vir_interpreter",
                "verifier_transfer",
                "verifier_cfg",
                "verifier_contracts",
                "verifier_cases",
                "verifier_properties",
                "native_abi",
                "native_plan",
                "native_codegen",
                "native_memory_codegen",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase711Identity => Regression {
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
        GateStep::Phase712Capability => Regression {
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
        GateStep::Phase713ResourcePayload => Regression {
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
        GateStep::Phase714GuardedResource => Regression {
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
        GateStep::Phase715CopyMove => Regression {
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
        GateStep::Phase716BuiltinDrop => Regression {
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
        GateStep::Phase717AggregateTransfer => Regression {
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
        GateStep::Phase718ResourceAcceptance => Regression {
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
        GateStep::Phase721BorrowBaseline => Regression {
            check: check_phase7_borrow_baseline_regression,
            tests: &[
                "borrow_baseline",
                "hir_place",
                "aggregate_abi",
                "vir_slice_range",
            ],
            library: true,
            snapshots: false,
            native: false,
        },
        GateStep::Phase722HirBorrowRegions => Regression {
            check: check_phase7_hir_borrow_regions_regression,
            tests: &["borrow_baseline", "hir_regions", "hir_place", "hir_program"],
            library: true,
            snapshots: false,
            native: false,
        },
        GateStep::Phase723VirLoanSchema => Regression {
            check: check_phase7_vir_loan_schema_regression,
            tests: &[
                "vir_loan_schema",
                "borrow_baseline",
                "hir_regions",
                "vir_source_map",
                "vir_unit_baseline",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase724VerifierLoans => Regression {
            check: check_phase7_verifier_loans_regression,
            tests: &[
                "verifier_loans",
                "vir_loan_schema",
                "borrow_baseline",
                "hir_regions",
                "verifier_cfg",
                "verifier_guarded",
                "verifier_transfer",
            ],
            library: true,
            snapshots: false,
            native: false,
        },
        GateStep::Phase725LoanConsumers => Regression {
            check: check_phase7_loan_consumers_regression,
            tests: &[
                "loan_consumers",
                "vir_loan_schema",
                "verifier_loans",
                "ghost_non_interference",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase726LocalSharedBorrow => Regression {
            check: check_phase7_local_shared_borrow_regression,
            tests: &[
                "frontend_shared_borrow",
                "borrow_baseline",
                "hir_regions",
                "vir_loan_schema",
                "verifier_loans",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase727LocalMutableBorrow => Regression {
            check: check_phase7_local_mutable_borrow_regression,
            tests: &[
                "frontend_mutable_borrow",
                "frontend_shared_borrow",
                "borrow_baseline",
                "hir_regions",
                "vir_loan_schema",
                "verifier_loans",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase728Reborrow => Regression {
            check: check_phase7_reborrow_regression,
            tests: &[
                "frontend_reborrow",
                "frontend_mutable_borrow",
                "frontend_shared_borrow",
                "hir_regions",
                "vir_loan_schema",
                "verifier_loans",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase729LoweringArchitecture => Regression {
            check: check_phase7_lowering_architecture_regression,
            tests: &[
                "runtime_semantics",
                "vir_corpus",
                "vir_source_map",
                "frontend_aggregates",
                "frontend_calls",
                "frontend_reborrow",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7210NllEndPlanning => Regression {
            check: check_phase7_nll_regression,
            tests: &[
                "frontend_nll",
                "frontend_reborrow",
                "frontend_mutable_borrow",
                "frontend_shared_borrow",
                "hir_regions",
                "vir_loan_schema",
                "verifier_loans",
                "vir_source_map",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7211GuardedLoanCfg => Regression {
            check: check_phase7_loan_cfg_regression,
            tests: &[
                "frontend_shared_borrow",
                "frontend_nll",
                "frontend_reborrow",
                "frontend_loops",
                "verifier_loans",
                "verifier_guarded",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7212ReferenceAggregate => Regression {
            check: check_phase7_reference_aggregate_regression,
            tests: &[
                "frontend_reference_aggregate",
                "frontend_shared_borrow",
                "frontend_mutable_borrow",
                "frontend_reborrow",
                "vir_loan_schema",
                "verifier_loans",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7213SafeSlice => Regression {
            check: check_phase7_safe_slice_regression,
            tests: &[
                "frontend_safe_slice",
                "frontend_reborrow",
                "vir_slice_range",
                "vir_loan_schema",
                "verifier_loans",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7214BorrowCalls => Regression {
            check: check_phase7_borrow_calls_regression,
            tests: &[
                "frontend_borrow_calls",
                "frontend_calls",
                "frontend_safe_slice",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7215BorrowAcceptance => Regression {
            check: check_phase7_borrow_acceptance,
            tests: &[
                "stage7_borrow_acceptance",
                "borrow_baseline",
                "hir_regions",
                "vir_loan_schema",
                "verifier_loans",
                "verifier_guarded",
                "frontend_shared_borrow",
                "frontend_mutable_borrow",
                "frontend_reborrow",
                "frontend_nll",
                "frontend_reference_aggregate",
                "frontend_safe_slice",
                "frontend_borrow_calls",
                "loan_consumers",
                "ghost_non_interference",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase731InitializationBaseline => Regression {
            check: check_phase7_initialization_baseline,
            tests: &[
                "initialization_baseline",
                "frontend_deferred_local",
                "verifier_object_state",
                "object_effect_runtime",
                "vir_object_effect",
                "vir_object_shape",
                "resource_payload",
                "frontend_copy_move",
                "frontend_drop",
                "frontend_aggregate_transfer",
                "frontend_reference_aggregate",
                "frontend_borrow_calls",
                "verifier_guarded",
                "stage7_resource_acceptance",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase732InitializationPlanning => Regression {
            check: check_phase7_initialization_planning,
            tests: &[
                "initialization_baseline",
                "frontend_deferred_local",
                "initialization_planning",
                "frontend_drop",
                "frontend_copy_move",
                "frontend_reference_aggregate",
                "frontend_borrow_calls",
                "frontend_safe_slice",
                "verifier_loans",
                "loan_consumers",
                "vir_loan_schema",
                "stage7_borrow_acceptance",
                "object_effect_runtime",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase733DeferredLocal => Regression {
            check: check_phase7_deferred_local,
            tests: &[
                "frontend_deferred_local",
                "initialization_baseline",
                "initialization_planning",
                "hir_program",
                "hir_regions",
                "loan_consumers",
                "verifier_object_state",
                "object_effect_runtime",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase734PartialRefill => Regression {
            check: check_phase7_partial_refill,
            tests: &[
                "frontend_partial_refill",
                "frontend_reference_aggregate",
                "initialization_planning",
                "resource_payload",
                "loan_consumers",
                "verifier_object_state",
                "object_effect_runtime",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase735PartialConstruction => Regression {
            check: check_phase7_partial_construction,
            tests: &[
                "frontend_partial_construction",
                "frontend_partial_refill",
                "frontend_deferred_local",
                "frontend_reference_aggregate",
                "resource_payload",
                "loan_consumers",
                "initialization_planning",
                "verifier_object_state",
                "object_effect_runtime",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase736EnumConstruction => Regression {
            check: check_phase7_enum_construction,
            tests: &[
                "frontend_enum_construction",
                "frontend_enums",
                "frontend_reference_aggregate",
                "frontend_partial_construction",
                "verifier_object_state",
                "object_effect_runtime",
                "loan_consumers",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase737HeapConstruction => Regression {
            check: check_phase7_heap_construction,
            tests: &[
                "frontend_heap_construction",
                "frontend_enum_construction",
                "frontend_partial_construction",
                "verifier_object_state",
                "object_effect_runtime",
                "native_plan",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase738LoopInitialization => Regression {
            check: check_phase7_loop_initialization,
            tests: &[
                "frontend_loop_initialization",
                "frontend_heap_construction",
                "verifier_cfg",
                "verifier_contracts",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase739InitializationInterfaces => Regression {
            check: check_phase7_initialization_interfaces,
            tests: &[
                "frontend_initialization_interfaces",
                "frontend_borrow_calls",
                "frontend_aggregate_transfer",
                "aggregate_abi",
                "verifier_contracts",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7310InitializationAcceptance => Regression {
            check: check_phase7_initialization_acceptance,
            tests: &[
                "stage7_initialization_acceptance",
                "initialization_baseline",
                "initialization_planning",
                "frontend_deferred_local",
                "frontend_partial_refill",
                "frontend_partial_construction",
                "frontend_enum_construction",
                "frontend_heap_construction",
                "frontend_loop_initialization",
                "frontend_initialization_interfaces",
                "vir_object_shape",
                "verifier_object_state",
                "ghost_non_interference",
                "native_acceptance",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase741RelationBaseline => Regression {
            check: check_phase7_relation_baseline,
            tests: &[
                "relation_baseline",
                "verifier_cfg",
                "verifier_object_state",
                "frontend_safe_slice",
                "frontend_reborrow",
                "frontend_borrow_calls",
                "frontend_loop_initialization",
                "frontend_initialization_interfaces",
                "stage7_initialization_acceptance",
                "ghost_non_interference",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase742DifferenceRelations => Regression {
            check: check_phase7_difference_relations,
            tests: &[
                "difference_relations",
                "relation_baseline",
                "verifier_cfg",
                "frontend_safe_slice",
                "frontend_loop_initialization",
                "frontend_reborrow",
                "stage7_initialization_acceptance",
                "ghost_non_interference",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase743RelationCfg => Regression {
            check: check_phase7_relation_cfg,
            tests: &[
                "relation_cfg",
                "difference_relations",
                "relation_baseline",
                "verifier_cfg",
                "verifier_guarded",
                "frontend_loop_initialization",
                "frontend_safe_slice",
                "frontend_borrow_calls",
                "stage7_borrow_acceptance",
                "stage7_initialization_acceptance",
                "ghost_non_interference",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase744SymbolicFootprint => Regression {
            check: check_phase7_symbolic_footprint,
            tests: &[
                "symbolic_footprint",
                "relation_cfg",
                "verifier_loans",
                "loan_consumers",
                "frontend_safe_slice",
                "frontend_reference_aggregate",
                "frontend_reborrow",
                "frontend_borrow_calls",
                "stage7_borrow_acceptance",
                "ghost_non_interference",
                "native_acceptance",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase745RelationBounds => Regression {
            check: check_phase7_relation_bounds,
            tests: &[
                "relation_bounds",
                "relation_baseline",
                "relation_cfg",
                "difference_relations",
                "symbolic_footprint",
                "frontend_safe_slice",
                "frontend_borrow_calls",
                "frontend_reborrow",
                "stage7_borrow_acceptance",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase746DisjointElements => Regression {
            check: check_phase7_disjoint_elements,
            tests: &[
                "disjoint_elements",
                "relation_bounds",
                "relation_baseline",
                "difference_relations",
                "relation_cfg",
                "symbolic_footprint",
                "verifier_loans",
                "loan_consumers",
                "frontend_reference_aggregate",
                "frontend_safe_slice",
                "frontend_reborrow",
                "stage7_borrow_acceptance",
                "object_effect_runtime",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase747SiblingSlices => Regression {
            check: check_phase7_sibling_slices,
            tests: &[
                "sibling_slices",
                "disjoint_elements",
                "relation_bounds",
                "relation_baseline",
                "vir_loan_schema",
                "verifier_loans",
                "loan_consumers",
                "frontend_safe_slice",
                "frontend_reborrow",
                "frontend_nll",
                "frontend_reference_aggregate",
                "frontend_borrow_calls",
                "stage7_borrow_acceptance",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase748StridedRegions => Regression {
            check: check_phase7_strided_regions,
            tests: &[
                "strided_regions",
                "sibling_slices",
                "disjoint_elements",
                "relation_bounds",
                "difference_relations",
                "relation_baseline",
                "relation_cfg",
                "symbolic_footprint",
                "verifier_loans",
                "loan_consumers",
                "object_effect_runtime",
                "frontend_safe_slice",
                "frontend_reborrow",
                "stage7_borrow_acceptance",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase749RelationComposition => Regression {
            check: check_phase7_relation_composition,
            tests: &[
                "relation_composition",
                "frontend_loop_initialization",
                "frontend_initialization_interfaces",
                "stage7_initialization_acceptance",
                "relation_cfg",
                "relation_bounds",
                "symbolic_footprint",
                "strided_regions",
                "sibling_slices",
                "frontend_borrow_calls",
                "frontend_safe_slice",
                "verifier_loans",
                "loan_consumers",
                "stage7_borrow_acceptance",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase7410RelationAudit => Regression {
            check: check_phase7_relation_audit,
            tests: &[
                "relation_audit",
                "relation_baseline",
                "difference_relations",
                "relation_cfg",
                "relation_bounds",
                "strided_regions",
                "relation_composition",
                "sibling_slices",
                "verifier_guarded",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase7411RelationAcceptance => Regression {
            check: check_phase7_relation_acceptance,
            tests: &[
                "stage7_relation_acceptance",
                "relation_audit",
                "relation_baseline",
                "difference_relations",
                "relation_cfg",
                "relation_bounds",
                "disjoint_elements",
                "symbolic_footprint",
                "sibling_slices",
                "strided_regions",
                "relation_composition",
                "vir_loan_schema",
                "vir_memory_schema",
                "verifier_guarded",
                "verifier_loans",
                "loan_consumers",
                "frontend_nll",
                "stage7_borrow_acceptance",
                "stage7_initialization_acceptance",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase751ProvenanceBaseline => Regression {
            check: check_phase7_provenance_baseline,
            tests: &[
                "provenance_baseline",
                "hir_place",
                "verifier_transfer",
                "verifier_cases",
                "verifier_cfg",
                "verifier_guarded",
                "verifier_contracts",
                "vir_memory_schema",
                "loan_consumers",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase755PointerDomain => Regression {
            check: check_phase7_pointer_domain,
            tests: &[
                "pointer_domain",
                "raw_address",
                "provenance_schema",
                "provenance_instance",
                "provenance_baseline",
                "symbolic_footprint",
                "relation_bounds",
                "relation_audit",
                "verifier_transfer",
                "verifier_cfg",
                "verifier_contracts",
                "loan_consumers",
                "frontend_borrow_calls",
                "vir_memory_schema",
                "vir_slice_range",
                "runtime_semantics",
                "vir_unit_baseline",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase756PointerComparison => Regression {
            check: check_phase7_pointer_comparison,
            tests: &[
                "pointer_comparison",
                "pointer_domain",
                "raw_address",
                "provenance_instance",
                "relation_audit",
                "verifier_contracts",
                "vir_unit_baseline",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase758AddressModel => Regression {
            check: check_phase7_address_model,
            tests: &[
                "native_address_model",
                "native_acceptance",
                "native_plan",
                "native_abi",
                "native_codegen",
                "native_memory_codegen",
                "native_assembly",
                "ghost_non_interference",
                "raw_address",
                "pointer_domain",
                "pointer_comparison",
                "provenance_instance",
                "provenance_flow",
                "runtime_semantics",
                "vir_source_map",
                "vir_unit_baseline",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase759ProvenanceAudit => Regression {
            check: check_phase7_provenance_audit,
            tests: &[
                "provenance_audit",
                "relation_audit",
                "provenance_instance",
                "provenance_flow",
                "pointer_comparison",
                "pointer_domain",
                "raw_address",
                "verifier_guarded",
                "verifier_cfg",
                "verifier_cases",
                "native_address_model",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase765ConditionalSummary => Regression {
            check: check_phase7_conditional_summary,
            tests: &[
                "summary_conditional",
                "summary_calls",
                "summary_projection",
                "summary_baseline",
                "frontend_initialization_interfaces",
                "frontend_borrow_calls",
                "verifier_guarded",
                "provenance_instance",
                "provenance_flow",
                "stage7_provenance_acceptance",
                "relation_composition",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase767RecursiveSummary => Regression {
            check: check_phase7_recursive_summary,
            tests: &[
                "summary_recursive",
                "summary_borrows",
                "summary_conditional",
                "summary_calls",
                "summary_projection",
                "summary_baseline",
                "frontend_borrow_calls",
                "frontend_aggregates",
                "verifier_loans",
                "verifier_guarded",
                "provenance_flow",
                "provenance_instance",
                "relation_composition",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase768SummaryAcceptance => Regression {
            check: check_phase7_summary_acceptance,
            tests: &[
                "summary_audit",
                "summary_recursive",
                "summary_borrows",
                "summary_conditional",
                "summary_calls",
                "summary_projection",
                "summary_baseline",
                "provenance_audit",
                "relation_audit",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase773VerifyPreview => Regression {
            check: check_phase7_verify_preview,
            tests: &["verify_cli", "verification_text", "verification_report"],
            library: true,
            snapshots: true,
            native: false,
        },
        GateStep::Phase776VerifyAcceptance => Regression {
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
        GateStep::Phase7832BorrowInterfaceMapping => Regression {
            check: check_phase7_borrow_interface_mapping,
            tests: &[
                "borrow_interface_mapping",
                "hir_regions",
                "aggregate_abi",
                "frontend_borrow_calls",
                "implicit_borrow_baseline",
                "implicit_lifetime_syntax",
                "summary_borrows",
                "summary_recursive",
                "generic_instances",
                "native_abi",
                "loan_consumers",
                "stage7_borrow_acceptance",
                "frontend_copy_move",
                "frontend_deferred_local",
                "frontend_partial_construction",
                "resource_payload",
                "vir_loan_schema",
                "vir_unit_baseline",
                "vir_source_map",
                "vir_v0",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase7833ImplicitBorrowInference => Regression {
            check: check_phase7_implicit_borrow_inference,
            tests: &[
                "implicit_borrow_inference",
                "implicit_borrow_baseline",
                "borrow_interface_mapping",
                "frontend_borrow_calls",
                "frontend_reborrow",
                "implicit_lifetime_syntax",
                "summary_borrows",
                "loan_consumers",
                "generic_instances",
                "module_program",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7834ConditionalBorrowInference => Regression {
            check: check_phase7_conditional_borrow_inference,
            tests: &[
                "conditional_borrow_inference",
                "implicit_borrow_inference",
                "frontend_borrow_calls",
                "summary_borrows",
                "loan_consumers",
                "hir_regions",
                "vir_unit_baseline",
                "vir_source_map",
                "vir_loan_schema",
                "resource_payload",
                "frontend_copy_move",
                "frontend_deferred_local",
                "frontend_partial_construction",
                "vir_v0",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase7835BorrowProjection => Regression {
            check: check_phase7_borrow_projection,
            tests: &[
                "borrow_projection",
                "borrow_interface_mapping",
                "conditional_borrow_inference",
                "frontend_safe_slice",
                "summary_borrows",
                "loan_consumers",
                "hir_regions",
                "vir_unit_baseline",
                "vir_source_map",
                "vir_loan_schema",
                "resource_payload",
                "vir_v0",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase7836BorrowSourceScc => Regression {
            check: check_phase7_borrow_source_scc,
            tests: &[
                "borrow_source_scc",
                "implicit_borrow_inference",
                "conditional_borrow_inference",
                "borrow_projection",
                "summary_recursive",
                "summary_borrows",
                "frontend_loops",
                "hir_regions",
                "vir_loan_schema",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7837ImplicitLifetimeSyntax => Regression {
            check: check_phase7_implicit_lifetime_syntax,
            tests: &[
                "implicit_lifetime_syntax",
                "generic_instances",
                "module_program",
                "implicit_borrow_inference",
                "conditional_borrow_inference",
                "borrow_projection",
                "frontend_properties",
                "hir_regions",
                "summary_borrows",
            ],
            library: true,
            snapshots: false,
            native: true,
        },
        GateStep::Phase7838ImplicitBorrowAcceptance => Regression {
            check: check_phase7_implicit_borrow_acceptance,
            tests: &[
                "implicit_borrow_acceptance",
                "implicit_lifetime_syntax",
                "implicit_borrow_baseline",
                "borrow_interface_mapping",
                "implicit_borrow_inference",
                "conditional_borrow_inference",
                "borrow_projection",
                "borrow_source_scc",
                "verification_text",
                "verification_report",
                "generic_instances",
                "module_program",
                "summary_borrows",
                "summary_audit",
                "frontend_nll",
                "frontend_reference_aggregate",
                "vir_loan_schema",
                "ghost_non_interference",
                "verification_fail_closed",
                "native_acceptance",
                "frontend_properties",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase784CapabilityProfile => Regression {
            check: check_phase7_capability_profile,
            tests: &[
                "capability_profile",
                "compilation_session",
                "implicit_lifetime_syntax",
                "verification_text",
                "verify_cli",
            ],
            library: false,
            snapshots: false,
            native: false,
        },
        GateStep::Phase785InterfaceArtifact => Regression {
            check: check_phase7_interface_artifact,
            tests: &[
                "interface_artifact",
                "capability_profile",
                "compilation_session",
                "generic_instances",
                "module_program",
            ],
            library: false,
            snapshots: false,
            native: false,
        },
        GateStep::Phase786StageAcceptance => Regression {
            check: check_phase7_stage_acceptance,
            tests: &[
                "stage7_8_acceptance",
                "interface_artifact",
                "implicit_borrow_acceptance",
                "generic_instances",
                "module_program",
                "compilation_session",
                "capability_profile",
                "summary_baseline",
                "verification_fail_closed",
            ],
            library: false,
            snapshots: true,
            native: true,
        },
        GateStep::Phase7831ImplicitBorrowBaseline => Regression {
            check: check_phase7_implicit_borrow_baseline,
            tests: &[
                "implicit_borrow_baseline",
                "frontend_borrow_calls",
                "frontend_initialization_interfaces",
                "implicit_lifetime_syntax",
                "summary_baseline",
                "summary_borrows",
                "summary_recursive",
                "generic_instances",
            ],
            library: false,
            snapshots: false,
            native: true,
        },
        GateStep::Phase783GenericInstances => Regression {
            check: check_phase7_generic_instances,
            tests: &[
                "generic_instances",
                "module_program",
                "compilation_session",
                "frontend_properties",
                "frontend_copy_move",
                "verification_text",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase783NamedLifetimes => Regression {
            check: check_phase7_implicit_lifetime_syntax,
            tests: &[
                "implicit_lifetime_syntax",
                "generic_instances",
                "frontend_calls",
                "frontend_reborrow",
                "borrow_baseline",
                "summary_borrows",
                "hir_program",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase782ModuleProgram => Regression {
            check: check_phase7_module_program,
            tests: &[
                "module_program",
                "compilation_session",
                "verification_report",
                "verification_text",
                "verify_cli",
                "hir_program",
                "summary_recursive",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase781CompilationSession => Regression {
            check: check_phase7_compilation_session,
            tests: &[
                "compilation_session",
                "verification_report",
                "verification_text",
                "verification_fail_closed",
                "verify_cli",
                "typed_spec_ir",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase775VerifyFailClosed => Regression {
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
        GateStep::Phase774AutoMemoryCorpus => Regression {
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
        GateStep::Phase772SourceDiagnostics => Regression {
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
        GateStep::Phase771VerifyReport => Regression {
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
        GateStep::Phase766BorrowSummary => Regression {
            check: check_phase7_borrow_summary,
            tests: &[
                "summary_borrows",
                "summary_conditional",
                "summary_calls",
                "summary_projection",
                "frontend_borrow_calls",
                "frontend_reference_aggregate",
                "frontend_reborrow",
                "verifier_loans",
                "loan_consumers",
                "stage7_borrow_acceptance",
                "frontend_initialization_interfaces",
                "provenance_instance",
                "relation_composition",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase764SummaryCalls => Regression {
            check: check_phase7_summary_calls,
            tests: &[
                "summary_calls",
                "summary_projection",
                "summary_baseline",
                "summary_architecture",
                "frontend_borrow_calls",
                "frontend_initialization_interfaces",
                "verifier_contracts",
                "verifier_guarded",
                "provenance_instance",
                "provenance_flow",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase763SummaryProjection => Regression {
            check: check_phase7_summary_projection,
            tests: &[
                "summary_projection",
                "summary_baseline",
                "summary_architecture",
                "verifier_cfg",
                "verifier_guarded",
                "verifier_contracts",
                "frontend_initialization_interfaces",
                "frontend_borrow_calls",
                "provenance_flow",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase762SummaryArchitecture => Regression {
            check: check_phase7_summary_architecture,
            tests: &[
                "summary_architecture",
                "summary_baseline",
                "typed_spec_ir",
                "frontend_nll",
                "frontend_borrow_calls",
                "frontend_aggregate_transfer",
                "frontend_initialization_interfaces",
                "verifier_transfer",
                "verifier_contracts",
                "provenance_audit",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase761SummaryBaseline => Regression {
            check: check_phase7_summary_baseline,
            tests: &[
                "summary_baseline",
                "frontend_borrow_calls",
                "frontend_initialization_interfaces",
                "frontend_aggregate_transfer",
                "provenance_flow",
                "verifier_contracts",
                "runtime_semantics",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: false,
            snapshots: true,
            native: true,
        },
        GateStep::Phase7510ProvenanceAcceptance => Regression {
            check: check_phase7_provenance_acceptance,
            tests: &[
                "stage7_provenance_acceptance",
                "provenance_audit",
                "provenance_flow",
                "provenance_instance",
                "provenance_schema",
                "provenance_baseline",
                "pointer_comparison",
                "pointer_domain",
                "raw_address",
                "native_address_model",
                "native_acceptance",
                "ghost_non_interference",
                "verifier_guarded",
                "verifier_properties",
                "vir_unit_baseline",
                "vir_source_map",
                "frontend_nll",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase757ProvenanceFlow => Regression {
            check: check_phase7_provenance_flow,
            tests: &[
                "provenance_flow",
                "pointer_comparison",
                "pointer_domain",
                "provenance_instance",
                "frontend_borrow_calls",
                "frontend_reference_aggregate",
                "frontend_aggregate_transfer",
                "verifier_guarded",
                "verifier_contracts",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase754RawAddress => Regression {
            check: check_phase7_raw_address,
            tests: &[
                "raw_address",
                "provenance_schema",
                "provenance_instance",
                "provenance_baseline",
                "hir_place",
                "vir_unit_baseline",
                "vir_source_map",
                "loan_consumers",
                "verifier_transfer",
                "verifier_cfg",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase753AllocationInstance => Regression {
            check: check_phase7_allocation_instance,
            tests: &[
                "provenance_instance",
                "provenance_schema",
                "provenance_baseline",
                "verifier_cfg",
                "verifier_contracts",
                "verifier_transfer",
                "verifier_properties",
                "frontend_loop_initialization",
                "loan_consumers",
                "native_acceptance",
                "vir_interpreter",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        GateStep::Phase752ProvenanceSchema => Regression {
            check: check_phase7_provenance_schema,
            tests: &[
                "provenance_schema",
                "provenance_baseline",
                "vir_memory_schema",
                "vir_object_shape",
                "vir_slice_range",
                "vir_source_map",
                "verifier_cases",
                "verifier_transfer",
                "loan_consumers",
                "native_acceptance",
                "ghost_non_interference",
            ],
            library: true,
            snapshots: true,
            native: true,
        },
        _ => return None,
    })
}

fn check_place_regression(_root: &Path) -> Result<(), Box<dyn Error>> {
    Ok(())
}

fn check_control_flow_regression(_root: &Path) -> Result<(), Box<dyn Error>> {
    Ok(())
}

fn check_vir_unit_regression(_root: &Path) -> Result<(), Box<dyn Error>> {
    Ok(())
}

fn check_aggregate_regression(_root: &Path) -> Result<(), Box<dyn Error>> {
    Ok(())
}

fn check_phase7_identity_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    for path in [
        "src/frontend/lower.rs",
        "src/frontend/lower/abi.rs",
        "src/frontend/lower/contract.rs",
    ] {
        if fs::read_to_string(root.join(path))?.contains("std::ptr::eq") {
            return Err("HIR lowering still depends on Rust object address identity".into());
        }
    }
    Ok(())
}

fn check_phase7_capability_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    for (path, forbidden) in [
        ("src/frontend/hir.rs", "type_contains_resource"),
        ("src/verifier/transfer.rs", "trivial_object_status"),
    ] {
        if fs::read_to_string(root.join(path))?.contains(forbidden) {
            return Err(format!("{path} restored duplicate classifier {forbidden}").into());
        }
    }
    for path in [
        "src/frontend/hir/body_validation.rs",
        "src/frontend/lower/concrete.rs",
        "src/verifier/transfer.rs",
        "src/vir/interpreter.rs",
        "src/backend/x86_64_plan.rs",
    ] {
        if !fs::read_to_string(root.join(path))?.contains("type_capabilities(") {
            return Err(format!("{path} does not consume canonical type capabilities").into());
        }
    }
    Ok(())
}

fn check_phase7_resource_payload_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let resource = fs::read_to_string(root.join("src/verifier/resource.rs"))?;
    if !resource.contains("resource_payloads: BTreeMap<ResourcePayloadKey, MovePathState>")
        || !resource.contains("pub type ResourceCase = ResourceState")
    {
        return Err(
            "typed payload is no longer owned by the canonical ResourceCase/ObjectState".into(),
        );
    }
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    if !interpreter.contains("resource_payloads: BTreeMap<RuntimeResourcePayloadKey")
        || interpreter.contains("decode_runtime_pointer")
    {
        return Err(
            "interpreter typed shadow payload is absent or pointer identity is decoded from bytes"
                .into(),
        );
    }
    Ok(())
}

fn check_phase7_guarded_resource_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let guarded = fs::read_to_string(root.join("src/verifier/guarded.rs"))?;
    if !guarded.contains("cases: Vec<ResourceCase>")
        || !guarded.contains("GuardedStatePrecisionLoss")
        || guarded.contains("transfer_instruction")
    {
        return Err(
            "guarded analysis must own bounded ResourceCase sets without a second transfer engine"
                .into(),
        );
    }
    let cfg = fs::read_to_string(root.join("src/verifier/cfg.rs"))?;
    if !cfg.contains("GuardedReduction::PreserveGuards")
        || !cfg.contains("evaluate_conditional_block")
        || !cfg.contains("let evaluated = evaluate_block_step(")
        || !cfg.contains("transfer_instruction_with_contracts_and_memory(")
    {
        return Err(
            "CFG analysis no longer replays guarded cases through canonical instruction transfer"
                .into(),
        );
    }
    Ok(())
}

fn check_phase7_copy_move_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let hir = fs::read_to_string(root.join("src/frontend/hir.rs"))?;
    let validation = fs::read_to_string(root.join("src/frontend/hir/body_validation.rs"))?;
    let assignment = fs::read_to_string(root.join("src/frontend/lower/assignment.rs"))?;
    if !hir.contains("pub enum HirUseMode")
        || !validation.contains("canonical_use_mode")
        || !assignment.contains("source_mode,")
    {
        return Err(
            "Copy/Move must be selected in typed HIR, independently validated, and preserved by assignment refinement"
                .into(),
        );
    }
    Ok(())
}

fn check_phase7_builtin_drop_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    let lowering = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer.rs"))?;
    let cfg = fs::read_to_string(root.join("src/verifier/cfg.rs"))?;
    if !vir.contains("DropOwn {") || !vir.contains("ObjectDrop {") {
        return Err("VIR no longer exposes scalar and object builtin-drop effects".into());
    }
    if !lowering.contains("emit_drops_not_in_environment")
        || !lowering.contains("VirGeneratedReason::ImplicitDrop")
    {
        return Err("lowering no longer uses the unified generated scope-cleanup path".into());
    }
    if !transfer.contains("DropFlagKnown") || !cfg.contains("OwnershipConserved") {
        return Err("verifier no longer checks drop flags and normal-exit conservation".into());
    }
    Ok(())
}

fn check_phase7_aggregate_transfer_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let abi = fs::read_to_string(root.join("src/vir/aggregate_abi.rs"))?;
    let lowering = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    let contract = fs::read_to_string(root.join("src/frontend/lower/contract.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer/call.rs"))?;
    if !abi.contains("return Ok(VirAbiValue::IndirectAggregate { access });")
        || !abi.contains("VirInterfaceTransfer::Move")
    {
        return Err("canonical ABI no longer classifies owning aggregates as indirect Move".into());
    }
    if !contract.contains("result_initialization")
        || !lowering.contains("initial_access_drop_flag(storage.access, false")
    {
        return Err(
            "lowering no longer closes owning aggregate call storage and drop state".into(),
        );
    }
    if !transfer.contains("AggregateAbiPayloadValid")
        || !transfer.contains("install_aggregate_abi_payloads")
    {
        return Err("verifier no longer checks aggregate ABI payload transfer".into());
    }
    Ok(())
}

fn check_phase7_resource_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let guarded = fs::read_to_string(root.join("src/verifier/guarded.rs"))?;
    let cfg = fs::read_to_string(root.join("src/verifier/cfg.rs"))?;
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let fuzz = fs::read_to_string(root.join("src/bin/nera_verifier_fuzz.rs"))?;
    if !guarded.contains("guards_have_exact_conjunctive_union")
        || !guarded.contains("same_resource_facts")
    {
        return Err(
            "guarded normalization no longer preserves resource-distinct alternatives".into(),
        );
    }
    if !cfg.contains("a consumed token may cross") || !interpreter.contains("RuntimeBlockArgument")
    {
        return Err("CFG consumers no longer transport permission tombstone state".into());
    }
    if !fuzz.contains("RESOURCE_CFG_VERIFIER_CASES") || !fuzz.contains("resource_cfg_checked") {
        return Err("verifier fuzz no longer covers resource CFG joins and back edges".into());
    }
    Ok(())
}

fn check_phase7_borrow_baseline_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let baseline = fs::read_to_string(root.join("docs/stage7-borrow-baseline-v1.md"))?;
    for required in [
        "Created --activate--> ActiveShared | ActiveMutable",
        "max_active_loans_per_case` | 256",
        "max_aliases_per_loan` | 256",
        "max_region_constraints_per_function` | 4096",
        "max_reborrow_depth` | 64",
        "ActiveLoanBudget",
        "LoanLoopWidening",
    ] {
        if !baseline.contains(required) {
            return Err(format!("borrow baseline is missing frozen rule '{required}'").into());
        }
    }

    let hir_types = fs::read_to_string(root.join("src/frontend/hir/types.rs"))?;
    let hir = fs::read_to_string(root.join("src/frontend/hir.rs"))?;
    let lowering = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    let memory = fs::read_to_string(root.join("src/vir/memory.rs"))?;
    let abi = fs::read_to_string(root.join("src/vir/aggregate_abi.rs"))?;
    if !hir_types.contains("Reference {") || !hir.contains("Borrow {") {
        return Err("typed HIR no longer exposes the structural Reference/Borrow baseline".into());
    }
    if !lowering.contains("HirExpressionKind::Borrow { .. }") {
        return Err(
            "HIR lowering no longer handles Borrow explicitly and may silently fall through".into(),
        );
    }
    if !memory.contains("Reference,")
        || !abi.contains("VirInterfaceTransfer::BorrowShared")
        || !abi.contains("VirInterfaceTransfer::BorrowMutable")
    {
        return Err("VIR memory/ABI no longer exposes the frozen reference skeleton".into());
    }

    Ok(())
}

fn check_phase7_hir_borrow_regions_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-hir-borrow-regions-v1.md"))?;
    for required in [
        "HirVersion::V4",
        "LexicalScope | Parameter | Result | Inferred",
        "subregion <= superregion",
        "production reference syntax remains gated",
    ] {
        if !acceptance.contains(required) {
            return Err(
                format!("HIR borrow-region acceptance is missing rule '{required}'").into(),
            );
        }
    }

    let regions = fs::read_to_string(root.join("src/frontend/hir/regions.rs"))?;
    let program = fs::read_to_string(root.join("src/frontend/hir/program.rs"))?;
    if !regions.contains("pub enum HirRegionOrigin")
        || !regions.contains("pub struct HirRegionConstraint")
        || !program.contains("version: HirVersion::V12")
        || !program.contains("validate_region_constraints")
    {
        return Err("canonical HIR borrow-region schema or validation is missing".into());
    }

    Ok(())
}

fn check_phase7_vir_loan_schema_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-vir-loan-schema-v1.md"))?;
    for required in [
        "VirUnitVersion::V6",
        "vir-unit-v6",
        "runtime-vir-v5",
        "LoanBegin | LoanAliasShared | LoanReborrow | LoanEnd",
        "production reference syntax remains gated",
    ] {
        if !acceptance.contains(required) {
            return Err(format!("VIR loan-schema acceptance is missing rule '{required}'").into());
        }
    }

    let borrow = fs::read_to_string(root.join("src/vir/borrow.rs"))?;
    let validate = fs::read_to_string(root.join("src/vir/validate.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer.rs"))?;
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let native = fs::read_to_string(root.join("src/backend/x86_64_plan.rs"))?;
    if !borrow.contains("pub struct VirBorrowEnvironment")
        || !borrow.contains("pub struct VirLoanEffect")
        || !validate.contains("validate_loan_instruction")
        || !validate.contains("borrow_region_is_subregion")
    {
        return Err("canonical VIR loan schema or structural validation is missing".into());
    }
    let interpreter_handles_loans = interpreter.contains("RuntimeLoanShadow");
    let native_handles_loans = native.contains("X86_64InstructionPlan::LoanReference");
    if !transfer.contains("fn loan_begin")
        || !transfer.contains("fn loan_end")
        || !interpreter_handles_loans
        || !native_handles_loans
    {
        return Err("a loan consumer neither implements nor explicitly rejects V6 effects".into());
    }

    Ok(())
}

fn check_phase7_verifier_loans_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-verifier-loans-v1.md"))?;
    for required in [
        "PermissionAuthority",
        "LoanRangeContained",
        "LoanCompatible",
        "LoanParentActive",
        "LoanEndedExactlyOnce",
        "production reference syntax remains gated",
    ] {
        if !acceptance.contains(required) {
            return Err(format!("verifier-loan acceptance is missing rule '{required}'").into());
        }
    }

    let resource = fs::read_to_string(root.join("src/verifier/resource.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer.rs"))?;
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let native = fs::read_to_string(root.join("src/backend/x86_64_plan.rs"))?;
    if !resource.contains("pub enum PermissionAuthority")
        || !resource.contains("pub struct AbstractLoan")
        || !transfer.contains("fn loan_alias_shared")
        || !transfer.contains("fn loan_reborrow")
        || !transfer.contains("fn loan_end")
    {
        return Err("canonical verifier loan domain or transfer rules are missing".into());
    }
    if !interpreter.contains("RuntimeLoanShadow") {
        return Err("the interpreter loan consumer is missing".into());
    }
    if !native.contains("X86_64InstructionPlan::LoanReference") {
        return Err("the native loan consumer is missing".into());
    }

    Ok(())
}

fn check_phase7_loan_consumers_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-loan-consumers-v1.md"))?;
    for required in [
        "RuntimeLoanShadow",
        "RuntimeLoanAuthority",
        "LoanReference",
        "ErasedLoan",
        "production reference syntax remains gated",
    ] {
        if !acceptance.contains(required) {
            return Err(format!("loan-consumer acceptance is missing rule '{required}'").into());
        }
    }

    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let shadow = fs::read_to_string(root.join("src/vir/interpreter/loan_shadow.rs"))?;
    let native_plan = fs::read_to_string(root.join("src/backend/x86_64_plan.rs"))?;
    let native_codegen = fs::read_to_string(root.join("src/backend/x86_64_codegen.rs"))?;
    if !interpreter.contains("RuntimeLoanShadow")
        || !shadow.contains("pub(super) struct RuntimeLoanShadow")
        || !shadow.contains("pub(super) fn reborrow")
        || !shadow.contains("pub(super) fn check_access")
    {
        return Err("bounded interpreter loan shadow is missing".into());
    }
    if !native_plan.contains("LoanReference")
        || !native_plan.contains("ErasedLoan")
        || !native_codegen.contains("X86_64InstructionPlan::LoanReference")
        || !native_codegen.contains("X86_64InstructionPlan::ErasedLoan")
    {
        return Err("native loan ghost erasure does not preserve reference pointer values".into());
    }

    Ok(())
}

fn check_phase7_local_shared_borrow_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-local-shared-borrow-v1.md"))?;
    for required in [
        "&place",
        "LoanAliasShared",
        "lexical scope end",
        "dynamic index",
        "stage 7.2.8",
    ] {
        if !acceptance.contains(required) {
            return Err(
                format!("local shared-borrow acceptance is missing rule '{required}'").into(),
            );
        }
    }

    let parser = fs::read_to_string(root.join("src/frontend/parser.rs"))?;
    let hir = fs::read_to_string(root.join("src/frontend/hir.rs"))?;
    let lower = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    if !parser.contains("fn parse_borrow")
        || !hir.contains("fn elaborate_borrow")
        || !lower.contains("fn lower_borrow")
        || !lower.contains("VirInstruction::LoanAliasShared")
        || !lower.contains("VirInstruction::LoanEnd")
    {
        return Err("the production local shared-borrow pipeline is incomplete".into());
    }

    Ok(())
}

fn check_phase7_local_mutable_borrow_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-local-mutable-borrow-v1.md"))?;
    for required in [
        "&mut place",
        "MoveOnly",
        "PermissionMove",
        "LoanBegin",
        "stage 7.2.8",
    ] {
        if !acceptance.contains(required) {
            return Err(
                format!("local mutable-borrow acceptance is missing rule '{required}'").into(),
            );
        }
    }

    let ast = fs::read_to_string(root.join("src/frontend.rs"))?;
    let parser = fs::read_to_string(root.join("src/frontend/parser.rs"))?;
    let hir = fs::read_to_string(root.join("src/frontend/hir.rs"))?;
    let lower = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    let assignment = fs::read_to_string(root.join("src/frontend/lower/assignment.rs"))?;
    let concrete = fs::read_to_string(root.join("src/frontend/lower/concrete.rs"))?;
    if !ast.contains("Reference {\n        pointee: Box<AstType>,\n        mutable: bool,")
        || !parser.contains("fn parse_borrow")
        || !hir.contains("fn elaborate_borrow")
        || !lower.contains("VirLoanKind::Mutable")
        || !lower.contains("VirInstruction::PermissionMove")
        || !assignment.contains("effect.source_pointer")
        || !concrete.contains("HirTypeKind::Reference {")
    {
        return Err("the production local mutable-borrow pipeline is incomplete".into());
    }

    Ok(())
}

fn check_phase7_reborrow_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-reborrow-v1.md"))?;
    for required in [
        "LoanReborrow",
        "child <= parent",
        "parent suspension",
        "explicit dereference",
        "stage7-2-8",
    ] {
        if !acceptance.contains(required) {
            return Err(format!("reborrow acceptance is missing rule '{required}'").into());
        }
    }

    let hir = fs::read_to_string(root.join("src/frontend/hir.rs"))?;
    let validation = fs::read_to_string(root.join("src/frontend/hir/body_validation.rs"))?;
    let lower = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    if !hir.contains("too many inferred borrow-region constraints")
        || !validation.contains("reborrow region is not constrained")
        || !lower.contains("VirInstruction::LoanReborrow")
        || !lower.contains("parent.range.contains(range)")
    {
        return Err("the production reborrow pipeline is incomplete".into());
    }

    Ok(())
}

fn check_phase7_lowering_architecture_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-lowering-architecture-v1.md"))?;
    for required in [
        "Validated HIR → Draft VIR → post-CFG effect planning",
        "InitializationEffects → LoanEndEffects → Seal",
        "RuntimeSemanticsUnsupported",
        "VerificationUnsupported",
        "TargetUnsupported",
        "stage7-2-9",
    ] {
        if !acceptance.contains(required) {
            return Err(
                format!("lowering-architecture acceptance is missing rule '{required}'").into(),
            );
        }
    }

    let lower = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    let draft = fs::read_to_string(root.join("src/frontend/lower/draft.rs"))?;
    let post_cfg = fs::read_to_string(root.join("src/frontend/lower/post_cfg.rs"))?;
    let semantics = fs::read_to_string(root.join("src/vir/semantics.rs"))?;
    let validation = fs::read_to_string(root.join("src/vir/validate.rs"))?;
    if !lower.contains("let mut draft_functions = Vec::new()")
        || !lower.contains("post_cfg::canonicalize_function")
        || !draft.contains("pub(super) enum DraftInstruction")
        || !post_cfg.contains("pub(super) const POST_CFG_PASSES")
        || !post_cfg.contains("seal_blocks")
        || !semantics.contains("pub const VIR_SYSTEM_SEMANTICS_V1")
        || !validation.contains("SemanticProfileMismatch")
    {
        return Err(
            "the production lowering architecture or semantic profile is incomplete".into(),
        );
    }

    Ok(())
}

fn check_phase7_nll_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-nll-v1.md"))?;
    for required in [
        "finite region-inclusion closure",
        "last SSA use",
        "lexical fallback",
        "LoanEndEffects",
        "stage7-2-10",
    ] {
        if !acceptance.contains(required) {
            return Err(format!("NLL acceptance is missing rule '{required}'").into());
        }
    }

    let loan_end = fs::read_to_string(root.join("src/frontend/lower/loan_end.rs"))?;
    let post_cfg = fs::read_to_string(root.join("src/frontend/lower/post_cfg.rs"))?;
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    if !loan_end.contains("RegionSolution::solve")
        || !loan_end.contains("instruction_escapes_authority")
        || !loan_end.contains("remap_source_locations")
        || !post_cfg.contains("loan_end::plan")
        || !vir.contains("pub(crate) fn visit_operands")
    {
        return Err("the production NLL end-planning pipeline is incomplete".into());
    }

    Ok(())
}

fn check_phase7_loan_cfg_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-guarded-loan-cfg-v1.md"))?;
    for required in [
        "ConditionalResourceState",
        "per-block last-use",
        "early return",
        "dynamic instance",
        "stage7-2-11",
    ] {
        if !acceptance.contains(required) {
            return Err(format!("loan-CFG acceptance is missing rule '{required}'").into());
        }
    }

    let lower = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    let loan_end = fs::read_to_string(root.join("src/frontend/lower/loan_end.rs"))?;
    let resource = fs::read_to_string(root.join("src/verifier/resource.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer.rs"))?;
    let shadow = fs::read_to_string(root.join("src/vir/interpreter/loan_shadow.rs"))?;
    if lower.contains("borrows across branch or loop CFG require stage 7.2.11")
        || !loan_end.contains("Each block is planned independently")
        || !resource.contains("define_next_loan_instance")
        || !transfer.contains("require_previous_loan_instance_ended")
        || !shadow.contains("loan.activity != RuntimeLoanActivity::Ended")
    {
        return Err("the guarded loan-CFG or loop-instance pipeline is incomplete".into());
    }

    Ok(())
}

fn check_phase7_reference_aggregate_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-reference-aggregate-v1.md"))?;
    for required in [
        "AggregateErased",
        "Stored",
        "candidate envelope",
        "partial move",
        "HirVersion::V5",
        "VirUnitVersion::V7",
        "stage7-2-12",
    ] {
        if !acceptance.contains(required) {
            return Err(
                format!("reference-aggregate acceptance is missing rule '{required}'").into(),
            );
        }
    }

    let regions = fs::read_to_string(root.join("src/frontend/hir/regions.rs"))?;
    let hir_program = fs::read_to_string(root.join("src/frontend/hir/program.rs"))?;
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    let dump = fs::read_to_string(root.join("src/vir/dump.rs"))?;
    let resource = fs::read_to_string(root.join("src/verifier/resource.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer.rs"))?;
    if !regions.contains("AggregateErased")
        || !vir.contains("LoanAliasAuthority")
        || !vir.contains("LoanEndAuthority")
        || !hir_program.contains("version: HirVersion::V12")
        || !vir.contains("version: VirUnitVersion::V18")
        || !dump.contains("runtime-vir-v17")
        || !resource.contains("Stored {")
        || !transfer.contains("move_authority_to_storage")
        || !transfer.contains("move_authority_from_storage")
    {
        return Err("the reference-bearing aggregate authority pipeline is incomplete".into());
    }

    Ok(())
}

fn check_phase7_safe_slice_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-safe-slice-v1.md"))?;
    for required in [
        "SliceAddress",
        "pointer + length + permission + loan",
        "one-past",
        "conservative envelope",
        "shared subslice",
        "VirUnitVersion::V8",
        "stage7-2-13",
    ] {
        if !acceptance.contains(required) {
            return Err(format!("safe-slice acceptance is missing rule '{required}'").into());
        }
    }

    let parser = fs::read_to_string(root.join("src/frontend/parser.rs"))?;
    let hir = fs::read_to_string(root.join("src/frontend/hir.rs"))?;
    let lower = fs::read_to_string(root.join("src/frontend/lower.rs"))?;
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    let dump = fs::read_to_string(root.join("src/vir/dump.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer.rs"))?;
    let shadow = fs::read_to_string(root.join("src/vir/interpreter/loan_shadow.rs"))?;
    if !parser.contains("AstType::Slice")
        || !hir.contains("intern_slice_type")
        || !lower.contains("lower_slice_borrow")
        || !vir.contains("SliceAddress")
        || !vir.contains("version: VirUnitVersion::V18")
        || !dump.contains("runtime-vir-v17")
        || !transfer.contains("pointer_within_slice_range_status")
        || !shadow.contains("range.start_bytes == range.end_bytes")
    {
        return Err("the safe-slice surface or loan pipeline is incomplete".into());
    }

    Ok(())
}

fn check_phase7_borrow_calls_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-borrow-calls-v1.md"))?;
    for rule in [
        "unconditional skeleton",
        "parameter region",
        "escape",
        "VirUnitVersion::V9",
        "stage7-2-14",
    ] {
        if !acceptance.contains(rule) {
            return Err(format!("borrow-call acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_borrow_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-borrow-acceptance-v1.md"))?;
    for rule in [
        "7.2.15",
        "Proven",
        "ghost non-interference",
        "7.6",
        "lexical fallback",
    ] {
        if !acceptance.contains(rule) {
            return Err(format!("borrow acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_initialization_baseline(root: &Path) -> Result<(), Box<dyn Error>> {
    let baseline = fs::read_to_string(root.join("docs/stage7-initialization-baseline-v1.md"))?;
    for rule in [
        "7.3.1",
        "let mut value: T;",
        "ObjectDeinitialize",
        "Unknown",
        "LoanBegin",
        "7.3.2",
        "stage7-3-1",
    ] {
        if !baseline.contains(rule) {
            return Err(format!("initialization baseline is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_initialization_planning(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-initialization-planning-v1.md"))?;
    for rule in [
        "InitializationEffects",
        "LoanBegin",
        "Unknown",
        "stage7-3-2",
    ] {
        if !plan.contains(rule) {
            return Err(format!("initialization planning acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_deferred_local(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-deferred-local-v1.md"))?;
    for rule in [
        "StorageReset",
        "HirVersion::V6",
        "VirUnitVersion::V10",
        "stage7-3-3",
    ] {
        if !plan.contains(rule) {
            return Err(format!("deferred local acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_partial_refill(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-partial-refill-v1.md"))?;
    for rule in [
        "ResourceInitialize",
        "ObjectDrop",
        "exactly-once",
        "stage7-3-4",
    ] {
        if !plan.contains(rule) {
            return Err(format!("partial refill acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_partial_construction(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-partial-construction-v1.md"))?;
    for rule in [
        "ResourceStorageReset",
        "ObjectDrop",
        "HirVersion::V7",
        "VirUnitVersion::V11",
        "stage7-3-5",
    ] {
        if !plan.contains(rule) {
            return Err(format!("partial construction acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_enum_construction(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-enum-construction-v1.md"))?;
    for rule in [
        "EnumSetDiscriminant",
        "ObjectResourcePayloadEmpty",
        "ObjectDrop",
        "stage7-3-6",
    ] {
        if !plan.contains(rule) {
            return Err(format!("enum construction acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_heap_construction(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-heap-construction-v1.md"))?;
    for rule in [
        "alloc<T>(1)",
        "ObjectDrop",
        "AllocationResourcePayloadEmpty",
        "stage7-3-7",
    ] {
        if !plan.contains(rule) {
            return Err(format!("heap construction acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_loop_initialization(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-loop-initialization-v1.md"))?;
    for rule in ["initialized-prefix", "back-edge", "Unknown", "stage7-3-8"] {
        if !plan.contains(rule) {
            return Err(format!("loop initialization acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_initialization_interfaces(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-initialization-interfaces-v1.md"))?;
    for rule in ["value bytes", "padding", "unconditional", "stage7-3-9"] {
        if !plan.contains(rule) {
            return Err(format!("initialization interface acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_initialization_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-initialization-acceptance-v1.md"))?;
    for rule in ["concretization", "padding", "Unknown", "stage7-3-10", "7.4"] {
        if !plan.contains(rule) {
            return Err(format!("initialization acceptance is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_relation_baseline(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-baseline-v1.md"))?;
    for rule in ["Unknown", "len", "7.4.5", "stage7-4-1", "derivation", "SMT"] {
        if !doc.contains(rule) {
            return Err(format!("relation baseline is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_difference_relations(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-difference-relations-v1.md"))?;
    for rule in [
        "Unknown",
        "wrapping",
        "7.4.3",
        "stage7-4-2",
        "derivation",
        "SMT",
    ] {
        if !doc.contains(rule) {
            return Err(format!("difference relations is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_relation_cfg(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-cfg-v1.md"))?;
    for rule in [
        "Unknown",
        "widening",
        "7.4.4",
        "stage7-4-3",
        "derivation",
        "SSA",
    ] {
        if !doc.contains(rule) {
            return Err(format!("relation CFG is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_symbolic_footprint(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-symbolic-footprint-v1.md"))?;
    for rule in ["Unknown", "envelope", "SSA", "7.4.5", "stage7-4-4"] {
        if !doc.contains(rule) {
            return Err(format!("symbolic footprint is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_relation_bounds(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-bounds-v1.md"))?;
    for rule in ["len(value)", "Unknown", "HIR V8", "stage7-4-5", "7.4.6"] {
        if !doc.contains(rule) {
            return Err(format!("relation bounds is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_disjoint_elements(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-disjoint-elements-v1.md"))?;
    for rule in ["i != j", "Unknown", "stride", "stage7-4-6", "7.4.7"] {
        if !doc.contains(rule) {
            return Err(format!("disjoint elements is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_sibling_slices(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-sibling-slices-v1.md"))?;
    for rule in [
        "Suspended",
        "Unknown",
        "LoanReborrowAuthority",
        "stage7-4-7",
        "7.4.8",
    ] {
        if !doc.contains(rule) {
            return Err(format!("sibling slices is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_strided_regions(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-strided-regions-v1.md"))?;
    for rule in [
        "stage7-4-8",
        "Unknown",
        "stride",
        "max_region_pairs_per_instruction",
        "7.4.9",
    ] {
        if !doc.contains(rule) {
            return Err(format!("strided regions is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_relation_composition(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-composition-v1.md"))?;
    for rule in [
        "stage7-4-9",
        "Unknown",
        "initialized-prefix",
        "7.4.10",
        "7.6",
    ] {
        if !doc.contains(rule) {
            return Err(format!("relation composition is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_relation_audit(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-audit-v1.md"))?;
    for rule in [
        "stage7-4-10",
        "Unknown",
        "RelationReplayCache",
        "Rust",
        "7.4.11",
        "query",
    ] {
        if !doc.contains(rule) {
            return Err(format!("relation audit is missing '{rule}'").into());
        }
    }
    Ok(())
}

fn check_phase7_relation_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-acceptance-v1.md"))?;
    for rule in [
        "stage7-4-11",
        "source accepted",
        "Unknown",
        "native",
        "7.5",
        "7.6",
        "relation-acceptance-limited",
    ] {
        if !doc.contains(rule) {
            return Err(format!("relation acceptance is missing '{rule}'").into());
        }
    }
    for path in [
        "spec/cases/verify/relation-acceptance.nera",
        "spec/cases/verify/relation-acceptance-limited.nera",
        "src/bin/fuzz_support/relation_cases.rs",
    ] {
        fs::read(root.join(path))?;
    }
    Ok(())
}

fn check_phase7_provenance_baseline(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-baseline-v1.md"))?;
    for rule in [
        "stage7-5-1",
        "ptr_byte_distance",
        "one-past",
        "allocation instance",
        "Unknown",
        "10.1/10.3",
        "consumer",
        "unverified",
    ] {
        if !doc.contains(rule) {
            return Err(format!("provenance baseline is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/provenance-baseline.nera"))?;
    Ok(())
}

fn check_phase7_provenance_schema(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-schema-v1.md"))?;
    for rule in [
        "stage7-5-2",
        "VirProvenanceCatalog",
        "VirSubobject",
        "authority",
        "7.5.3",
        "7.5.5",
    ] {
        if !doc.contains(rule) {
            return Err(format!("provenance schema is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/provenance-schema.nera"))?;
    Ok(())
}

fn check_phase7_address_model(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-address-model-v1.md"))?;
    for rule in [
        "stage7-5-8",
        "SystemV2",
        "one-past",
        "PointerDomainViolation",
        "PermissionMismatch",
        "unverified",
        "ABI",
    ] {
        if !doc.contains(rule) {
            return Err(format!("address model audit is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/native-address-model.nera"))?;
    Ok(())
}

fn check_phase7_provenance_audit(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-audit-v1.md"))?;
    for marker in [
        "stage7-5-9",
        "ProvenanceEvidence",
        "accepts_memory_trace",
        "max_relation_evidence",
        "Unknown",
    ] {
        if !doc.contains(marker) {
            return Err(format!("provenance audit is missing '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_summary_projection(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-projection-v1.md"))?;
    for marker in [
        "stage7-6-3",
        "Unknown",
        "ReturnWorld",
        "SummaryBinding",
        "7.6.4",
    ] {
        if !doc.contains(marker) {
            return Err(format!("summary projection is missing '{marker}'").into());
        }
    }
    let transfer = fs::read_to_string(root.join("src/verifier/transfer/call.rs"))?;
    if transfer.contains("validate_structure") || transfer.contains("stable_dump") {
        return Err("call transfer must not treat a structurally valid dump as authority".into());
    }
    Ok(())
}

fn check_phase7_summary_calls(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-calls-v2.md"))?;
    for marker in ["stage7-6-4", "SummaryRegistry", "Unknown", "Frame", "7.6.5"] {
        if !doc.contains(marker) {
            return Err(format!("summary calls document misses '{marker}'").into());
        }
    }
    let registry = fs::read_to_string(root.join("src/verifier/summary/registry.rs"))?;
    if !registry.contains("pub(crate) struct SummaryRegistry")
        || !registry.contains("SummaryState::Candidate")
    {
        return Err("summary publication must remain private and require proved candidates".into());
    }
    Ok(())
}

fn check_phase7_recursive_summary(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-recursive-summary-v5.md"))?;
    for marker in ["stage7-6-7", "Inductive", "SccLimits", "Unknown", "7.6.8"] {
        if !doc.contains(marker) {
            return Err(format!("recursive summary document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_summary_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-acceptance-v6.md"))?;
    for marker in [
        "stage7-6-8",
        "SummaryAudit",
        "max_summary_evidence",
        "Unknown",
        "7.7",
        "峰值",
    ] {
        if !doc.contains(marker) {
            return Err(format!("summary acceptance document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_verify_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verify-acceptance-v1.md"))?;
    for marker in [
        "stage7-7-6",
        "NERA_VERIFY_SCALE",
        "VmHWM",
        "SummaryAudit",
        "7.8.1",
    ] {
        if !doc.contains(marker) {
            return Err(format!("verify acceptance document misses '{marker}'").into());
        }
    }
    let guide = fs::read_to_string(root.join("docs/verify.md"))?;
    for marker in [
        "nera verify",
        "--explain",
        "Unknown",
        "unverified",
        "终止",
        "栈空间",
    ] {
        if !guide.contains(marker) {
            return Err(format!("verify guide misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_compilation_session(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-compilation-session-v1.md"))?;
    for marker in [
        "stage7-8-1",
        "CompilerSession",
        "SourceDatabase",
        "VirSourceId",
        "7.8.2",
        "raw VIR",
    ] {
        if !doc.contains(marker) {
            return Err(format!("session document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_module_program(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-module-program-v1.md"))?;
    for marker in [
        "stage7-8-2",
        "CompilerSession::modules",
        "DAG",
        "private",
        "VirSourceMap",
        "7.8.3",
    ] {
        if !doc.contains(marker) {
            return Err(format!("module program document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_borrow_interface_mapping(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-interface-mapping-v1.md"))?;
    for marker in [
        "BorrowResultRelation",
        "SignatureDraft",
        "V16",
        "V10",
        "check-phase7-borrow-interface-mapping",
        "7.8.3.3",
    ] {
        if !doc.contains(marker) {
            return Err(format!("borrow interface mapping document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_implicit_borrow_inference(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-borrow-inference-v1.md"))?;
    for marker in [
        "infer_borrow_sources",
        "check-phase7-implicit-borrow-inference",
        "BorrowResultRelation",
        "7.8.3.4",
        "非递归",
    ] {
        if !doc.contains(marker) {
            return Err(format!("implicit borrow inference document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_conditional_borrow_inference(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-conditional-borrow-inference-v1.md"))?;
    for marker in [
        "BorrowResultAlternative",
        "BorrowGuardAtom",
        "check-phase7-conditional-borrow-inference",
        "V17",
        "V11",
        "7.8.3.5",
    ] {
        if !doc.contains(marker) {
            return Err(format!("conditional borrow inference document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_borrow_projection(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-projection-v1.md"))?;
    for marker in [
        "BorrowProjection",
        "BorrowSliceBound",
        "caller",
        "HirVersion::V12",
        "VirUnitVersion::V18",
        "runtime-vir-v17",
        "check-phase7-borrow-projection",
        "7.8.3.6",
    ] {
        if !doc.contains(marker) {
            return Err(format!("borrow projection document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_borrow_source_scc(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-source-scc-v1.md"))?;
    for marker in [
        "NoNormalReturn",
        "source_components",
        "MAX_BORROW_SOURCE_SCC_FUNCTIONS",
        "MAX_BORROW_SOURCE_FIXPOINT_ITERATIONS",
        "check-phase7-borrow-source-scc",
        "7.8.3.7",
    ] {
        if !doc.contains(marker) {
            return Err(format!("borrow source SCC document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_implicit_borrow_baseline(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-borrow-baseline-v1.md"))?;
    for marker in [
        "check-phase7-implicit-borrow-baseline",
        "CandidateSources",
        "NoNormalReturn",
        "Unknown",
        "InputLoan",
        "Initialized",
        "7.8.3.2",
    ] {
        if !doc.contains(marker) {
            return Err(format!("implicit borrow baseline document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_generic_instances(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-generic-instances-v1.md"))?;
    for marker in [
        "stage7-8-3",
        "InstanceKey",
        "InstantiationReport",
        "128",
        "7.8.4",
        "未实例化",
    ] {
        if !doc.contains(marker) {
            return Err(format!("generic instance document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_implicit_lifetime_syntax(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-lifetime-syntax-v1.md"))?;
    for marker in [
        "check-phase7-implicit-lifetime-syntax",
        "check-phase7-named-lifetimes",
        "&T",
        "stage 8",
        "TokenKind::Lifetime",
    ] {
        if !doc.contains(marker) {
            return Err(format!("implicit lifetime syntax document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_implicit_borrow_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-borrow-acceptance-v1.md"))?;
    for marker in [
        "check-phase7-implicit-borrow-acceptance",
        "borrow_interfaces",
        "complete result worlds",
        "Unknown",
        "stage 8",
        "7.8.4",
    ] {
        if !doc.contains(marker) {
            return Err(format!("implicit borrow acceptance document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_capability_profile(root: &Path) -> Result<(), Box<dyn Error>> {
    let manifest = fs::read_to_string(root.join("spec/capability-profile-v1.txt"))?;
    let profile = nera::CapabilityProfile::parse(&manifest)?;
    profile.check_implementation()?;

    let doc = fs::read_to_string(root.join("docs/stage7-capability-profile-v1.md"))?;
    for marker in [
        "stage7-8-4",
        "check-phase7-capability-profile",
        profile.profile(),
        profile.language(),
        profile.runtime(),
        profile.verifier(),
        profile.interpreter(),
        profile.target(),
        profile.backend(),
        profile.formal_checker(),
        "schema-only",
        "rejected-with-diagnostic",
        "erased-after-validation",
        "7.8.5",
    ] {
        if !doc.contains(marker) {
            return Err(format!("capability profile document misses '{marker}'").into());
        }
    }
    for feature in profile.features() {
        if !doc.contains(feature.id())
            || !doc.contains(feature.limit())
            || !doc.contains(feature.check())
        {
            return Err(format!(
                "capability profile document does not account for '{}'",
                feature.id()
            )
            .into());
        }
    }
    let config = fs::read_to_string(root.join("src/session/config.rs"))?;
    if !config.contains("current_capability_profile")
        || config.contains("pub const RUNTIME_PROFILE")
        || config.contains("pub const VERIFIER_PROFILE")
    {
        return Err(
            "compilation session does not use the capability profile as its defaults".into(),
        );
    }
    let cli = fs::read_to_string(root.join("src/main.rs"))?;
    let verification_text = fs::read_to_string(root.join("src/verification/text.rs"))?;
    if !cli.contains("current_capability_profile")
        || !cli.contains("capability-profile:")
        || !verification_text.contains("effective capability profile:")
    {
        return Err("frontend/run/build/verify do not report the registered profile".into());
    }
    Ok(())
}

fn check_phase7_interface_artifact(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-interface-artifact-v1.md"))?;
    for marker in [
        "stage7-8-5",
        "check-phase7-interface-artifact",
        "InterfaceArtifactVersion::V1",
        "InterfaceInputIdentity",
        "InterfaceDeclarationIdentity",
        "InterfaceInstanceIdentity",
        "BorrowResultRelation",
        "matches_analysis",
        "schema-only",
        "7.8.6",
    ] {
        if !doc.contains(marker) {
            return Err(format!("interface artifact document misses '{marker}'").into());
        }
    }
    let implementation = fs::read_to_string(root.join("src/module_interface.rs"))?;
    for marker in [
        "InterfaceArtifactVersion::V1",
        "InterfaceInputIdentity::from_input",
        "ConcreteInstance",
        "borrow_result_alternatives",
        "matches_analysis",
        "FrontendNotAccepted",
    ] {
        if !implementation.contains(marker) {
            return Err(format!("interface artifact implementation misses '{marker}'").into());
        }
    }
    if implementation.contains("ProgramVerification")
        || implementation.contains("is_checked: bool")
        || implementation.contains("DefaultHasher")
    {
        return Err("interface artifact contains verdict or hash authorization state".into());
    }
    Ok(())
}

fn check_phase7_stage_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-8-acceptance-v1.md"))?;
    for marker in [
        "stage7-8-6",
        "check-phase7-stage-acceptance",
        "check-rust",
        "stage7_8_acceptance",
        "InterfaceArtifact",
        "20,000",
        "阶段 8.1",
    ] {
        if !doc.contains(marker) {
            return Err(format!("stage 7 acceptance document misses '{marker}'").into());
        }
    }
    for fixture in [
        "spec/cases/modules/stage7-acceptance-app.nera",
        "spec/cases/modules/stage7-acceptance-ownership.nera",
    ] {
        if !root.join(fixture).is_file() {
            return Err(format!("stage 7 acceptance fixture is missing: {fixture}").into());
        }
    }
    Ok(())
}

fn check_phase7_verify_fail_closed(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verify-fail-closed-v1.md"))?;
    for marker in [
        "stage7-7-5",
        "write_report",
        "BudgetAborted",
        "SummaryAudit",
        "7.7.6",
    ] {
        if !doc.contains(marker) {
            return Err(format!("verify fail-closed document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_auto_memory_corpus(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-auto-memory-corpus-v1.md"))?;
    for marker in [
        "stage7-7-4",
        "auto_memory_cases",
        "NotClosed",
        "OwnershipConserved",
        "7.7.5",
    ] {
        if !doc.contains(marker) {
            return Err(format!("ordinary memory corpus document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_verify_preview(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verify-preview-v1.md"))?;
    for marker in ["stage7-7-3", "nera verify", "stdout", "Unknown", "7.7.4"] {
        if !doc.contains(marker) {
            return Err(format!("verify preview document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_source_diagnostics(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-source-diagnostics-v1.md"))?;
    for marker in [
        "stage7-7-2",
        "render_text",
        "TextReportMode",
        "Unknown",
        "7.7.3",
    ] {
        if !doc.contains(marker) {
            return Err(format!("source diagnostic document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_verify_report(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verification-report-v1.md"))?;
    for marker in [
        "stage7-7-1",
        "VerificationPreview",
        "BudgetAborted",
        "Unknown",
        "7.7.2",
    ] {
        if !doc.contains(marker) {
            return Err(format!("verification report document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_borrow_summary(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-summary-v4.md"))?;
    for marker in [
        "stage7-6-6",
        "BorrowRestoration",
        "InputLoan",
        "Unknown",
        "7.6.7",
    ] {
        if !doc.contains(marker) {
            return Err(format!("borrow summary document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_conditional_summary(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-conditional-summary-v3.md"))?;
    for marker in [
        "stage7-6-5",
        "ConditionalResourceState",
        "ReturnWorld",
        "Unknown",
        "7.6.6",
    ] {
        if !doc.contains(marker) {
            return Err(format!("conditional summary document misses '{marker}'").into());
        }
    }
    Ok(())
}

fn check_phase7_summary_architecture(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-architecture-v1.md"))?;
    for marker in [
        "stage7-6-2",
        "Lowerer",
        "TransferBuilder",
        "Draft",
        "NERA_REFACTOR_COMPARE_DIR",
        "7.6.3",
    ] {
        if !doc.contains(marker) {
            return Err(format!("summary architecture is missing '{marker}'").into());
        }
    }
    // Follow the actual implementation owner, never keep dead marker copies in
    // a parent file merely to satisfy an old textual regression check.
    for (parent, owner, markers) in [
        (
            "src/frontend/lower.rs",
            "src/frontend/lower/contract.rs",
            &["fn infer_contracts(", "fn lower_hir_specs("][..],
        ),
        (
            "src/frontend/lower.rs",
            "src/frontend/lower/abi.rs",
            &[
                "fn classify_hir_signature(",
                "fn bind_abi_entry_parameters(",
                "fn lower_return(",
            ][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/call.rs",
            &["fn call(", "fn install_aggregate_abi_payloads("][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/access.rs",
            &[
                "fn require_slice_argument(",
                "fn object_access_facts(",
                "fn permission_access_obligations(",
            ][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/obligation.rs",
            &[
                "struct ResourceObligation {",
                "struct InstructionTransfer {",
            ][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/error.rs",
            &["enum TransferError {"][..],
        ),
    ] {
        let parent_source = fs::read_to_string(root.join(parent))?;
        let owner_source = fs::read_to_string(root.join(owner))?;
        for marker in markers {
            if parent_source.contains(marker) || owner_source.matches(marker).count() != 1 {
                return Err(format!("{marker} must be owned once by {owner}, not {parent}").into());
            }
        }
    }
    for path in [
        "src/frontend/lower/tests.rs",
        "src/verifier/transfer/tests.rs",
    ] {
        fs::read(root.join(path))?;
    }
    check_phase7_identity_regression(root)?;
    check_phase7_builtin_drop_regression(root)?;
    check_phase7_aggregate_transfer_regression(root)?;
    Ok(())
}

fn check_phase7_summary_baseline(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-baseline-v1.md"))?;
    for marker in [
        "stage7-6-1",
        "may-footprint",
        "must-fact",
        "normal return",
        "divergence",
        "Unknown",
        "Invalid",
        "conditional interface summary",
        "SCC",
        "unverified",
    ] {
        if !doc.contains(marker) {
            return Err(format!("summary baseline is missing '{marker}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/summary-baseline.nera"))?;
    Ok(())
}

fn check_phase7_provenance_acceptance(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-acceptance-v1.md"))?;
    for marker in [
        "stage7-5-10",
        "Unknown",
        "gated",
        "7.6",
        "provenance_checked",
        "max_slots",
        "unverified",
    ] {
        if !doc.contains(marker) {
            return Err(format!("provenance acceptance is missing '{marker}'").into());
        }
    }
    fs::read(root.join("src/bin/fuzz_support/provenance_cases.rs"))?;
    Ok(())
}

fn check_phase7_provenance_flow(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-flow-v1.md"))?;
    for rule in [
        "stage7-5-7",
        "MaybeLive",
        "IncomingDomain",
        "SelectedDomain",
        "Unknown",
        "7.6",
        "ABI",
    ] {
        if !doc.contains(rule) {
            return Err(format!("provenance flow design is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/provenance-flow.nera"))?;
    Ok(())
}

fn check_phase7_pointer_comparison(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-pointer-comparison-v1.md"))?;
    for rule in [
        "stage7-5-6",
        "PointerSameInstance",
        "PointerCompatibleDomain",
        "ptr_byte_distance",
        "Unknown",
        "V15",
        "7.5.7",
    ] {
        if !doc.contains(rule) {
            return Err(format!("pointer relation design is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/pointer-comparison.nera"))?;
    Ok(())
}

fn check_phase7_pointer_domain(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-pointer-domain-v1.md"))?;
    for rule in [
        "stage7-5-5",
        "PointerDomainContains",
        "one-past",
        "Unknown",
        "V14",
        "SystemV2",
        "7.5.7",
        "10.1/10.3",
    ] {
        if !doc.contains(rule) {
            return Err(format!("pointer domain design is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/pointer-domain.nera"))?;
    Ok(())
}

fn check_phase7_raw_address(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-raw-address-v1.md"))?;
    for rule in [
        "stage7-5-4",
        "RawAddress",
        "permission",
        "V13",
        "7.5.5",
        "10.1/10.3",
    ] {
        if !doc.contains(rule) {
            return Err(format!("raw address design is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/raw-address.nera"))?;
    Ok(())
}

fn check_phase7_allocation_instance(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-allocation-instance-v1.md"))?;
    for rule in [
        "stage7-5-3",
        "AllocationInstanceFresh",
        "Unknown",
        "4_096",
        "unverified",
        "7.5.5",
    ] {
        if !doc.contains(rule) {
            return Err(format!("allocation instance design is missing '{rule}'").into());
        }
    }
    fs::read(root.join("spec/cases/verify/provenance-instance.nera"))?;
    Ok(())
}
