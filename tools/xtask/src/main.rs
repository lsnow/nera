use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

mod contracts;
mod gate;
mod loops;
mod regression;
mod spec_local;
mod stage4;

const FUZZ_ITERATIONS: &str = "20000";
const FRONTEND_FUZZ_SEED: &str = "5640004548657764954";
const VERIFIER_FUZZ_SEED: &str = "5640004548925149769";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum GateStep {
    VirSnapshots,
    Format,
    WorkspaceTests,
    FrontendFuzz,
    VerifierFuzz,
    Clippy,
    Place,
    Rustdoc,
    ControlFlow,
    VirUnit,
    Aggregate,
    Phase711Identity,
    Phase712Capability,
    Phase713ResourcePayload,
    Phase714GuardedResource,
    Phase715CopyMove,
    Phase716BuiltinDrop,
    Phase717AggregateTransfer,
    Phase718ResourceAcceptance,
    Phase721BorrowBaseline,
    Phase722HirBorrowRegions,
    Phase723VirLoanSchema,
    Phase724VerifierLoans,
    Phase725LoanConsumers,
    Phase726LocalSharedBorrow,
    Phase727LocalMutableBorrow,
    Phase728Reborrow,
    Phase729LoweringArchitecture,
    Phase7210NllEndPlanning,
    Phase7211GuardedLoanCfg,
    Phase7212ReferenceAggregate,
    Phase7213SafeSlice,
    Phase7214BorrowCalls,
    Phase7215BorrowAcceptance,
    Phase731InitializationBaseline,
    Phase732InitializationPlanning,
    Phase733DeferredLocal,
    Phase734PartialRefill,
    Phase735PartialConstruction,
    Phase736EnumConstruction,
    Phase737HeapConstruction,
    Phase738LoopInitialization,
    Phase739InitializationInterfaces,
    Phase7310InitializationAcceptance,
    Phase741RelationBaseline,
    Phase742DifferenceRelations,
    Phase743RelationCfg,
    Phase744SymbolicFootprint,
    Phase745RelationBounds,
    Phase746DisjointElements,
    Phase747SiblingSlices,
    Phase748StridedRegions,
    Phase749RelationComposition,
    Phase7410RelationAudit,
    Phase7411RelationAcceptance,
    Phase751ProvenanceBaseline,
    Phase752ProvenanceSchema,
    Phase753AllocationInstance,
    Phase754RawAddress,
    Phase755PointerDomain,
    Phase756PointerComparison,
    Phase757ProvenanceFlow,
    Phase758AddressModel,
    Phase759ProvenanceAudit,
    Phase7510ProvenanceAcceptance,
    Phase761SummaryBaseline,
    Phase762SummaryArchitecture,
    Phase763SummaryProjection,
    Phase764SummaryCalls,
    Phase765ConditionalSummary,
    Phase766BorrowSummary,
    Phase767RecursiveSummary,
    Phase768SummaryAcceptance,
    Phase771VerifyReport,
    Phase772SourceDiagnostics,
    Phase773VerifyPreview,
    Phase774AutoMemoryCorpus,
    Phase775VerifyFailClosed,
    Phase776VerifyAcceptance,
    Phase781CompilationSession,
    Phase782ModuleProgram,
    Phase783GenericInstances,
    Phase783NamedLifetimes,
    Phase7831ImplicitBorrowBaseline,
    Phase7832BorrowInterfaceMapping,
    Phase7833ImplicitBorrowInference,
    Phase7834ConditionalBorrowInference,
    Phase7835BorrowProjection,
    Phase7836BorrowSourceScc,
    Phase7837ImplicitLifetimeSyntax,
    Phase7838ImplicitBorrowAcceptance,
    Phase784CapabilityProfile,
    Phase785InterfaceArtifact,
    Phase786StageAcceptance,
}

const STAGE7_GATE: &[GateStep] = &[
    GateStep::VirSnapshots,
    GateStep::Format,
    GateStep::WorkspaceTests,
    GateStep::FrontendFuzz,
    GateStep::VerifierFuzz,
    GateStep::Clippy,
    GateStep::Place,
    GateStep::Rustdoc,
    GateStep::ControlFlow,
    GateStep::VirUnit,
    GateStep::Aggregate,
    GateStep::Phase711Identity,
    GateStep::Phase712Capability,
    GateStep::Phase713ResourcePayload,
    GateStep::Phase714GuardedResource,
    GateStep::Phase715CopyMove,
    GateStep::Phase716BuiltinDrop,
    GateStep::Phase717AggregateTransfer,
    GateStep::Phase718ResourceAcceptance,
    GateStep::Phase721BorrowBaseline,
    GateStep::Phase722HirBorrowRegions,
    GateStep::Phase723VirLoanSchema,
    GateStep::Phase724VerifierLoans,
    GateStep::Phase725LoanConsumers,
    GateStep::Phase726LocalSharedBorrow,
    GateStep::Phase727LocalMutableBorrow,
    GateStep::Phase728Reborrow,
    GateStep::Phase729LoweringArchitecture,
    GateStep::Phase7210NllEndPlanning,
    GateStep::Phase7211GuardedLoanCfg,
    GateStep::Phase7212ReferenceAggregate,
    GateStep::Phase7213SafeSlice,
    GateStep::Phase7214BorrowCalls,
    GateStep::Phase7215BorrowAcceptance,
    GateStep::Phase731InitializationBaseline,
    GateStep::Phase732InitializationPlanning,
    GateStep::Phase733DeferredLocal,
    GateStep::Phase734PartialRefill,
    GateStep::Phase735PartialConstruction,
    GateStep::Phase736EnumConstruction,
    GateStep::Phase737HeapConstruction,
    GateStep::Phase738LoopInitialization,
    GateStep::Phase739InitializationInterfaces,
    GateStep::Phase7310InitializationAcceptance,
    GateStep::Phase741RelationBaseline,
    GateStep::Phase742DifferenceRelations,
    GateStep::Phase743RelationCfg,
    GateStep::Phase744SymbolicFootprint,
    GateStep::Phase745RelationBounds,
    GateStep::Phase746DisjointElements,
    GateStep::Phase747SiblingSlices,
    GateStep::Phase748StridedRegions,
    GateStep::Phase749RelationComposition,
    GateStep::Phase7410RelationAudit,
    GateStep::Phase7411RelationAcceptance,
    GateStep::Phase751ProvenanceBaseline,
    GateStep::Phase752ProvenanceSchema,
    GateStep::Phase753AllocationInstance,
    GateStep::Phase754RawAddress,
    GateStep::Phase755PointerDomain,
    GateStep::Phase756PointerComparison,
    GateStep::Phase757ProvenanceFlow,
    GateStep::Phase758AddressModel,
    GateStep::Phase759ProvenanceAudit,
    GateStep::Phase7510ProvenanceAcceptance,
    GateStep::Phase761SummaryBaseline,
    GateStep::Phase762SummaryArchitecture,
    GateStep::Phase763SummaryProjection,
    GateStep::Phase764SummaryCalls,
    GateStep::Phase765ConditionalSummary,
    GateStep::Phase766BorrowSummary,
    GateStep::Phase767RecursiveSummary,
    GateStep::Phase768SummaryAcceptance,
    GateStep::Phase771VerifyReport,
    GateStep::Phase772SourceDiagnostics,
    GateStep::Phase773VerifyPreview,
    GateStep::Phase774AutoMemoryCorpus,
    GateStep::Phase775VerifyFailClosed,
    GateStep::Phase776VerifyAcceptance,
    GateStep::Phase781CompilationSession,
    GateStep::Phase782ModuleProgram,
    GateStep::Phase783GenericInstances,
    GateStep::Phase783NamedLifetimes,
    GateStep::Phase7831ImplicitBorrowBaseline,
    GateStep::Phase7832BorrowInterfaceMapping,
    GateStep::Phase7833ImplicitBorrowInference,
    GateStep::Phase7834ConditionalBorrowInference,
    GateStep::Phase7835BorrowProjection,
    GateStep::Phase7836BorrowSourceScc,
    GateStep::Phase7837ImplicitLifetimeSyntax,
    GateStep::Phase7838ImplicitBorrowAcceptance,
    GateStep::Phase784CapabilityProfile,
    GateStep::Phase785InterfaceArtifact,
    GateStep::Phase786StageAcceptance,
];
const STAGE5_GATE_END: usize = 6;
const STAGE6_2_GATE_END: usize = 8;
const STAGE6_3_GATE_END: usize = 9;
const STAGE6_4_GATE_END: usize = 10;
const STAGE6_5_GATE_END: usize = 11;
const STAGE7_1_1_GATE_END: usize = 12;
const STAGE7_1_2_GATE_END: usize = 13;
const STAGE7_1_3_GATE_END: usize = 14;
const STAGE7_1_4_GATE_END: usize = 15;
const STAGE7_1_5_GATE_END: usize = 16;
const STAGE7_1_6_GATE_END: usize = 17;
const STAGE7_1_7_GATE_END: usize = 18;
const STAGE7_1_8_GATE_END: usize = 19;
const STAGE7_2_1_GATE_END: usize = 20;
const STAGE7_2_2_GATE_END: usize = 21;
const STAGE7_2_3_GATE_END: usize = 22;
const STAGE7_2_4_GATE_END: usize = 23;
const STAGE7_2_5_GATE_END: usize = 24;
const STAGE7_2_6_GATE_END: usize = 25;
const STAGE7_2_7_GATE_END: usize = 26;
const STAGE7_2_8_GATE_END: usize = 27;
const STAGE7_2_9_GATE_END: usize = 28;
const STAGE7_2_10_GATE_END: usize = 29;
const STAGE7_2_11_GATE_END: usize = 30;
const STAGE7_2_12_GATE_END: usize = 31;
const STAGE7_2_13_GATE_END: usize = 32;
const STAGE7_2_14_GATE_END: usize = 33;
const STAGE7_2_15_GATE_END: usize = 34;
const STAGE7_3_1_GATE_END: usize = 35;
const STAGE7_3_2_GATE_END: usize = 36;
const STAGE7_3_3_GATE_END: usize = 37;
const STAGE7_3_4_GATE_END: usize = 38;
const STAGE7_3_5_GATE_END: usize = 39;
const STAGE7_3_6_GATE_END: usize = 40;
const STAGE7_3_7_GATE_END: usize = 41;
const STAGE7_3_8_GATE_END: usize = 42;
const STAGE7_3_9_GATE_END: usize = 43;
const STAGE7_3_10_GATE_END: usize = 44;
const STAGE7_4_1_GATE_END: usize = 45;
const STAGE7_4_2_GATE_END: usize = 46;
const STAGE7_4_3_GATE_END: usize = 47;
const STAGE7_4_4_GATE_END: usize = 48;
const STAGE7_4_5_GATE_END: usize = 49;
const STAGE7_4_6_GATE_END: usize = 50;
const STAGE7_4_7_GATE_END: usize = 51;
const STAGE7_4_8_GATE_END: usize = 52;
const STAGE7_4_9_GATE_END: usize = 53;
const STAGE7_4_10_GATE_END: usize = 54;
const STAGE7_4_11_GATE_END: usize = 55;
const STAGE7_5_1_GATE_END: usize = 56;
const STAGE7_5_2_GATE_END: usize = 57;
const STAGE7_5_3_GATE_END: usize = 58;
const STAGE7_5_4_GATE_END: usize = 59;
const STAGE7_5_5_GATE_END: usize = 60;
const STAGE7_5_6_GATE_END: usize = 61;
const STAGE7_5_7_GATE_END: usize = 62;
const STAGE7_5_8_GATE_END: usize = 63;
const STAGE7_5_9_GATE_END: usize = 64;
const STAGE7_5_10_GATE_END: usize = 65;
const STAGE7_6_1_GATE_END: usize = 66;
const STAGE7_6_2_GATE_END: usize = 67;
const STAGE7_6_3_GATE_END: usize = 68;
const STAGE7_6_4_GATE_END: usize = 69;
const STAGE7_6_5_GATE_END: usize = 70;
const STAGE7_6_6_GATE_END: usize = 71;
const STAGE7_6_7_GATE_END: usize = 72;
const STAGE7_6_8_GATE_END: usize = 73;
const STAGE7_7_1_GATE_END: usize = 74;
const STAGE7_7_2_GATE_END: usize = 75;
const STAGE7_7_3_GATE_END: usize = 76;
const STAGE7_7_4_GATE_END: usize = 77;
const STAGE7_7_5_GATE_END: usize = 78;
const STAGE7_7_6_GATE_END: usize = 79;
const STAGE7_8_1_GATE_END: usize = 80;
const STAGE7_8_2_GATE_END: usize = 81;
const STAGE7_8_3_GATE_END: usize = 83;
const STAGE7_8_4_GATE_END: usize = 92;
const STAGE7_8_5_GATE_END: usize = 93;
const STAGE7_8_6_GATE_END: usize = 94;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let command = parse_command(env::args().skip(1))?;
    let root = workspace_root();

    match command.as_str() {
        "generate-vir" => stage4::generate(&root),
        "check-rust" => run_gate(&root, &gate::rust_steps()),
        "check-vir" => stage4::check(&root),
        "check-spec-local" => spec_local::run(&root),
        "check-contracts" => contracts::run(&root),
        "check-loops" => loops::run(&root),
        "stage4" => {
            stage4::check(&root)?;
            run_frontend_regression(&root)
        }
        "check-verifier" => run_verifier_regression(&root),
        "check-place" => run_gate(&root, &[GateStep::Place]),
        "check-control-flow" => run_gate(&root, &[GateStep::ControlFlow]),
        "check-vir-unit" => run_gate(&root, &[GateStep::VirUnit]),
        "check-aggregate" => run_gate(&root, &[GateStep::Aggregate]),
        "check-phase7-identity" => run_gate(&root, &[GateStep::Phase711Identity]),
        "check-phase7-capability" => run_gate(&root, &[GateStep::Phase712Capability]),
        "check-phase7-resource-payload" => run_gate(&root, &[GateStep::Phase713ResourcePayload]),
        "check-phase7-guarded-resource" => run_gate(&root, &[GateStep::Phase714GuardedResource]),
        "check-phase7-copy-move" => run_gate(&root, &[GateStep::Phase715CopyMove]),
        "check-phase7-builtin-drop" => run_gate(&root, &[GateStep::Phase716BuiltinDrop]),
        "check-phase7-aggregate-transfer" => {
            run_gate(&root, &[GateStep::Phase717AggregateTransfer])
        }
        "check-phase7-resource-acceptance" => {
            run_gate(&root, &[GateStep::Phase718ResourceAcceptance])
        }
        "check-phase7-borrow-baseline" => run_gate(&root, &[GateStep::Phase721BorrowBaseline]),
        "check-phase7-hir-borrow-regions" => run_gate(&root, &[GateStep::Phase722HirBorrowRegions]),
        "check-phase7-vir-loan-schema" => run_gate(&root, &[GateStep::Phase723VirLoanSchema]),
        "check-phase7-verifier-loans" => run_gate(&root, &[GateStep::Phase724VerifierLoans]),
        "check-phase7-loan-consumers" => run_gate(&root, &[GateStep::Phase725LoanConsumers]),
        "check-phase7-local-shared-borrow" => {
            run_gate(&root, &[GateStep::Phase726LocalSharedBorrow])
        }
        "check-phase7-local-mutable-borrow" => {
            run_gate(&root, &[GateStep::Phase727LocalMutableBorrow])
        }
        "check-phase7-reborrow" => run_gate(&root, &[GateStep::Phase728Reborrow]),
        "check-phase7-lowering-architecture" => {
            run_gate(&root, &[GateStep::Phase729LoweringArchitecture])
        }
        "check-phase7-nll" => run_gate(&root, &[GateStep::Phase7210NllEndPlanning]),
        "check-phase7-loan-cfg" => run_gate(&root, &[GateStep::Phase7211GuardedLoanCfg]),
        "check-phase7-reference-aggregate" => {
            run_gate(&root, &[GateStep::Phase7212ReferenceAggregate])
        }
        "check-phase7-safe-slice" => run_gate(&root, &[GateStep::Phase7213SafeSlice]),
        "check-phase7-borrow-calls" => run_gate(&root, &[GateStep::Phase7214BorrowCalls]),
        "check-phase7-borrow-acceptance" => run_gate(&root, &[GateStep::Phase7215BorrowAcceptance]),
        "check-phase7-initialization-baseline" => {
            run_gate(&root, &[GateStep::Phase731InitializationBaseline])
        }
        "check-phase7-initialization-planning" => {
            run_gate(&root, &[GateStep::Phase732InitializationPlanning])
        }
        "check-phase7-deferred-local" => run_gate(&root, &[GateStep::Phase733DeferredLocal]),
        "check-phase7-partial-refill" => run_gate(&root, &[GateStep::Phase734PartialRefill]),
        "check-phase7-partial-construction" => {
            run_gate(&root, &[GateStep::Phase735PartialConstruction])
        }
        "check-phase7-enum-construction" => run_gate(&root, &[GateStep::Phase736EnumConstruction]),
        "check-phase7-heap-construction" => run_gate(&root, &[GateStep::Phase737HeapConstruction]),
        "check-phase7-loop-initialization" => {
            run_gate(&root, &[GateStep::Phase738LoopInitialization])
        }
        "stage5" => run_stage5(&root),
        "stage6-2" => run_stage6_2(&root),
        "stage6-3" => run_stage6_3(&root),
        "stage6-4" => run_stage6_4(&root),
        "stage6-5" => run_stage6_5(&root),
        "stage7-1-1" => run_stage7_1_1(&root),
        "stage7-1-2" => run_stage7_1_2(&root),
        "stage7-1-3" => run_stage7_1_3(&root),
        "stage7-1-4" => run_stage7_1_4(&root),
        "stage7-1-5" => run_stage7_1_5(&root),
        "stage7-1-6" => run_stage7_1_6(&root),
        "stage7-1-7" => run_stage7_1_7(&root),
        "stage7-1-8" => run_stage7_1_8(&root),
        "stage7-2-1" => run_stage7_2_1(&root),
        "stage7-2-2" => run_stage7_2_2(&root),
        "stage7-2-3" => run_stage7_2_3(&root),
        "stage7-2-4" => run_stage7_2_4(&root),
        "stage7-2-5" => run_stage7_2_5(&root),
        "stage7-2-6" => run_stage7_2_6(&root),
        "stage7-2-7" => run_stage7_2_7(&root),
        "stage7-2-8" => run_stage7_2_8(&root),
        "stage7-2-9" => run_stage7_2_9(&root),
        "stage7-2-10" => run_stage7_2_10(&root),
        "stage7-2-11" => run_stage7_2_11(&root),
        "stage7-2-12" => run_stage7_2_12(&root),
        "stage7-2-13" => run_stage7_2_13(&root),
        "stage7-2-14" => run_gate(&root, &STAGE7_GATE[..STAGE7_2_14_GATE_END]),
        "stage7-2-15" => run_gate(&root, &STAGE7_GATE[..STAGE7_2_15_GATE_END]),
        "stage7-3-1" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_1_GATE_END]),
        "stage7-3-2" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_2_GATE_END]),
        "stage7-3-3" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_3_GATE_END]),
        "stage7-3-4" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_4_GATE_END]),
        "stage7-3-5" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_5_GATE_END]),
        "stage7-3-6" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_6_GATE_END]),
        "stage7-3-7" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_7_GATE_END]),
        "stage7-3-8" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_8_GATE_END]),
        "stage7-3-9" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_9_GATE_END]),
        "stage7-3-10" => run_gate(&root, &STAGE7_GATE[..STAGE7_3_10_GATE_END]),
        "stage7-4-1" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_1_GATE_END]),
        "check-phase7-relation-baseline" => run_gate(&root, &[GateStep::Phase741RelationBaseline]),
        "stage7-4-2" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_2_GATE_END]),
        "stage7-4-3" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_3_GATE_END]),
        "stage7-4-4" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_4_GATE_END]),
        "stage7-4-5" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_5_GATE_END]),
        "stage7-4-6" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_6_GATE_END]),
        "stage7-4-7" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_7_GATE_END]),
        "stage7-4-8" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_8_GATE_END]),
        "stage7-4-9" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_9_GATE_END]),
        "stage7-4-10" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_10_GATE_END]),
        "stage7-4-11" => run_gate(&root, &STAGE7_GATE[..STAGE7_4_11_GATE_END]),
        "stage7-5-1" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_1_GATE_END]),
        "stage7-5-2" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_2_GATE_END]),
        "stage7-5-3" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_3_GATE_END]),
        "stage7-5-4" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_4_GATE_END]),
        "stage7-5-5" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_5_GATE_END]),
        "stage7-5-6" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_6_GATE_END]),
        "stage7-5-7" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_7_GATE_END]),
        "check-phase7-provenance-flow" => run_gate(&root, &[GateStep::Phase757ProvenanceFlow]),
        "stage7-5-8" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_8_GATE_END]),
        "check-phase7-address-model" => run_gate(&root, &[GateStep::Phase758AddressModel]),
        "stage7-5-9" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_9_GATE_END]),
        "check-phase7-provenance-audit" => run_gate(&root, &[GateStep::Phase759ProvenanceAudit]),
        "stage7-5-10" => run_gate(&root, &STAGE7_GATE[..STAGE7_5_10_GATE_END]),
        "stage7-6-1" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_1_GATE_END]),
        "stage7-6-2" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_2_GATE_END]),
        "stage7-6-3" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_3_GATE_END]),
        "stage7-6-4" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_4_GATE_END]),
        "stage7-6-5" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_5_GATE_END]),
        "stage7-6-6" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_6_GATE_END]),
        "stage7-6-7" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_7_GATE_END]),
        "stage7-6-8" => run_gate(&root, &STAGE7_GATE[..STAGE7_6_8_GATE_END]),
        "stage7-7-1" => run_gate(&root, &STAGE7_GATE[..STAGE7_7_1_GATE_END]),
        "check-phase7-verify-report" => run_gate(&root, &[GateStep::Phase771VerifyReport]),
        "stage7-7-2" => run_gate(&root, &STAGE7_GATE[..STAGE7_7_2_GATE_END]),
        "stage7-7-3" => run_gate(&root, &STAGE7_GATE[..STAGE7_7_3_GATE_END]),
        "stage7-7-4" => run_gate(&root, &STAGE7_GATE[..STAGE7_7_4_GATE_END]),
        "stage7-7-5" => run_gate(&root, &STAGE7_GATE[..STAGE7_7_5_GATE_END]),
        "stage7-7-6" => run_gate(&root, &STAGE7_GATE[..STAGE7_7_6_GATE_END]),
        "stage7-8-1" => run_gate(&root, &STAGE7_GATE[..STAGE7_8_1_GATE_END]),
        "stage7-8-3" => run_gate(&root, &STAGE7_GATE[..STAGE7_8_3_GATE_END]),
        "check-phase7-implicit-borrow-baseline" => {
            run_gate(&root, &[GateStep::Phase7831ImplicitBorrowBaseline])
        }
        "check-phase7-borrow-interface-mapping" => {
            run_gate(&root, &[GateStep::Phase7832BorrowInterfaceMapping])
        }
        "check-phase7-implicit-borrow-inference" => {
            run_gate(&root, &[GateStep::Phase7833ImplicitBorrowInference])
        }
        "check-phase7-conditional-borrow-inference" => {
            run_gate(&root, &[GateStep::Phase7834ConditionalBorrowInference])
        }
        "check-phase7-borrow-projection" => run_gate(&root, &[GateStep::Phase7835BorrowProjection]),
        "check-phase7-borrow-source-scc" => run_gate(&root, &[GateStep::Phase7836BorrowSourceScc]),
        "check-phase7-implicit-lifetime-syntax" => {
            run_gate(&root, &[GateStep::Phase7837ImplicitLifetimeSyntax])
        }
        "check-phase7-implicit-borrow-acceptance" => {
            run_gate(&root, &[GateStep::Phase7838ImplicitBorrowAcceptance])
        }
        "check-phase7-capability-profile" => {
            run_gate(&root, &[GateStep::Phase784CapabilityProfile])
        }
        "stage7-8-4" => run_gate(&root, &STAGE7_GATE[..STAGE7_8_4_GATE_END]),
        "check-phase7-interface-artifact" => {
            run_gate(&root, &[GateStep::Phase785InterfaceArtifact])
        }
        "stage7-8-5" => run_gate(&root, &STAGE7_GATE[..STAGE7_8_5_GATE_END]),
        "check-phase7-stage-acceptance" => run_gate(&root, &[GateStep::Phase786StageAcceptance]),
        "stage7-8-6" => run_gate(&root, &STAGE7_GATE[..STAGE7_8_6_GATE_END]),
        "check-phase7-generic-instances" => run_gate(&root, &[GateStep::Phase783GenericInstances]),
        "check-phase7-named-lifetimes" => run_gate(&root, &[GateStep::Phase783NamedLifetimes]),
        "stage7-8-2" => run_gate(&root, &STAGE7_GATE[..STAGE7_8_2_GATE_END]),
        "check-phase7-module-program" => run_gate(&root, &[GateStep::Phase782ModuleProgram]),
        "check-phase7-compilation-session" => {
            run_gate(&root, &[GateStep::Phase781CompilationSession])
        }
        "check-phase7-verify-acceptance" => run_gate(&root, &[GateStep::Phase776VerifyAcceptance]),
        "check-phase7-verify-fail-closed" => run_gate(&root, &[GateStep::Phase775VerifyFailClosed]),
        "check-phase7-auto-memory-corpus" => run_gate(&root, &[GateStep::Phase774AutoMemoryCorpus]),
        "check-phase7-verify-preview" => run_gate(&root, &[GateStep::Phase773VerifyPreview]),
        "check-phase7-source-diagnostics" => {
            run_gate(&root, &[GateStep::Phase772SourceDiagnostics])
        }
        "check-phase7-summary-acceptance" => {
            run_gate(&root, &[GateStep::Phase768SummaryAcceptance])
        }
        "check-phase7-recursive-summary" => run_gate(&root, &[GateStep::Phase767RecursiveSummary]),
        "check-phase7-borrow-summary" => run_gate(&root, &[GateStep::Phase766BorrowSummary]),
        "check-phase7-conditional-summary" => {
            run_gate(&root, &[GateStep::Phase765ConditionalSummary])
        }
        "check-phase7-summary-calls" => run_gate(&root, &[GateStep::Phase764SummaryCalls]),
        "check-phase7-summary-projection" => {
            run_gate(&root, &[GateStep::Phase763SummaryProjection])
        }
        "check-phase7-summary-architecture" => {
            run_gate(&root, &[GateStep::Phase762SummaryArchitecture])
        }
        "check-phase7-summary-baseline" => run_gate(&root, &[GateStep::Phase761SummaryBaseline]),
        "check-phase7-provenance-acceptance" => {
            run_gate(&root, &[GateStep::Phase7510ProvenanceAcceptance])
        }
        "check-phase7-pointer-comparison" => {
            run_gate(&root, &[GateStep::Phase756PointerComparison])
        }
        "check-phase7-pointer-domain" => run_gate(&root, &[GateStep::Phase755PointerDomain]),
        "check-phase7-raw-address" => run_gate(&root, &[GateStep::Phase754RawAddress]),
        "check-phase7-allocation-instance" => {
            run_gate(&root, &[GateStep::Phase753AllocationInstance])
        }
        "check-phase7-provenance-schema" => run_gate(&root, &[GateStep::Phase752ProvenanceSchema]),
        "check-phase7-provenance-baseline" => {
            run_gate(&root, &[GateStep::Phase751ProvenanceBaseline])
        }
        "check-phase7-relation-acceptance" => {
            run_gate(&root, &[GateStep::Phase7411RelationAcceptance])
        }
        "check-phase7-relation-audit" => run_gate(&root, &[GateStep::Phase7410RelationAudit]),
        "check-phase7-relation-composition" => {
            run_gate(&root, &[GateStep::Phase749RelationComposition])
        }
        "check-phase7-strided-regions" => run_gate(&root, &[GateStep::Phase748StridedRegions]),
        "check-phase7-sibling-slices" => run_gate(&root, &[GateStep::Phase747SiblingSlices]),
        "check-phase7-disjoint-elements" => run_gate(&root, &[GateStep::Phase746DisjointElements]),
        "check-phase7-relation-bounds" => run_gate(&root, &[GateStep::Phase745RelationBounds]),
        "check-phase7-symbolic-footprint" => {
            run_gate(&root, &[GateStep::Phase744SymbolicFootprint])
        }
        "check-phase7-relation-cfg" => run_gate(&root, &[GateStep::Phase743RelationCfg]),
        "check-phase7-difference-relations" => {
            run_gate(&root, &[GateStep::Phase742DifferenceRelations])
        }
        "check-phase7-initialization-acceptance" => {
            run_gate(&root, &[GateStep::Phase7310InitializationAcceptance])
        }
        "check-phase7-initialization-interfaces" => {
            run_gate(&root, &[GateStep::Phase739InitializationInterfaces])
        }
        "help" | "-h" | "--help" => {
            print_help();
            Ok(())
        }
        other => Err(format!("unknown xtask command '{other}'").into()),
    }
}

fn parse_command(mut arguments: impl Iterator<Item = String>) -> Result<String, Box<dyn Error>> {
    let command = arguments.next().unwrap_or_else(|| "help".to_owned());
    if let Some(argument) = arguments.next() {
        return Err(format!(
            "xtask command '{command}' does not accept extra argument '{argument}'; stage gates do not accept test filters"
        )
        .into());
    }
    Ok(command)
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("xtask must live under tools/xtask")
        .to_owned()
}

fn run_cargo(root: &Path, arguments: &[&str]) -> Result<(), Box<dyn Error>> {
    let status = Command::new("cargo")
        .args(arguments)
        .current_dir(root)
        .status()?;

    if !status.success() {
        return Err(format!("cargo {} failed", arguments.join(" ")).into());
    }

    Ok(())
}

fn run_stage5(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE5_GATE_END])
}

fn run_stage6_2(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE6_2_GATE_END])
}

fn run_stage6_3(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE6_3_GATE_END])
}

/// Runs the complete stage 6.4 acceptance gate.
///
/// `stage6-3` retains every earlier Rust, fuzz, native and documentation
/// baseline. `check-vir-unit` then adds the canonical-unit, cross-table,
/// Check/Prove/trust and ghost non-interference regressions introduced by 6.4.
fn run_stage6_4(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE6_4_GATE_END])
}

/// Runs the complete stage 6.5 aggregate-memory acceptance gate.
///
/// `stage6-4` retains the feature registry, full Rust workspace, two fuzz,
/// and strict Clippy/rustdoc gates. `check-aggregate` then adds
/// every schema, object-state/effect, surface, ABI and native differential
/// regression introduced by 6.5.
fn run_stage6_5(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE6_5_GATE_END])
}

/// Runs stage 6.5 plus the canonical finding and HIR-identity gate.
fn run_stage7_1_1(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_1_GATE_END])
}

/// Runs 7.1.1 plus the canonical type-capability/interface-effect gate.
fn run_stage7_1_2(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_2_GATE_END])
}

/// Runs 7.1.2 plus the typed resource payload/move-path gate.
fn run_stage7_1_3(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_3_GATE_END])
}

/// Runs 7.1.3 plus bounded guarded resource-state and refinement checks.
fn run_stage7_1_4(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_4_GATE_END])
}

/// Runs 7.1.4 plus source-level canonical Copy/Move and pattern bindings.
fn run_stage7_1_5(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_5_GATE_END])
}

/// Runs 7.1.5 plus builtin drop, scope cleanup and exit conservation.
fn run_stage7_1_6(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_6_GATE_END])
}

/// Runs 7.1.6 plus ownership-bearing aggregate call/return transfer.
fn run_stage7_1_7(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_7_GATE_END])
}

/// Runs the complete stage 7.1 ownership/resource acceptance gate.
fn run_stage7_1_8(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_1_8_GATE_END])
}

/// Runs stage 7.1 plus the frozen safe-borrow semantic and regression baseline.
fn run_stage7_2_1(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_1_GATE_END])
}

/// Runs 7.2.1 plus the canonical HIR borrow-region universe and constraints.
fn run_stage7_2_2(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_2_GATE_END])
}

/// Runs 7.2.2 plus the explicit V6 VIR borrow-region and loan-effect schema.
fn run_stage7_2_3(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_3_GATE_END])
}

/// Runs 7.2.3 plus the canonical verifier loan domain and transfer semantics.
fn run_stage7_2_4(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_4_GATE_END])
}

/// Runs 7.2.4 plus interpreter loan shadow and native ghost erasure checks.
fn run_stage7_2_5(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_5_GATE_END])
}

/// Runs 7.2.5 plus the local lexical shared-borrow surface vertical slice.
fn run_stage7_2_6(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_6_GATE_END])
}

/// Runs 7.2.6 plus the local lexical mutable-borrow surface vertical slice.
fn run_stage7_2_7(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_7_GATE_END])
}

/// Runs 7.2.7 plus explicit local reborrow and exact parent restoration.
fn run_stage7_2_8(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_8_GATE_END])
}

/// Runs 7.2.8 plus the private Draft VIR pipeline and frozen runtime semantics.
fn run_stage7_2_9(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_9_GATE_END])
}

/// Runs 7.2.9 plus function-local NLL end planning and finite region solving.
fn run_stage7_2_10(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_10_GATE_END])
}

/// Runs 7.2.10 plus guarded branch/exit loans and bounded loop instances.
fn run_stage7_2_11(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_11_GATE_END])
}

/// Runs 7.2.11 plus subobject loans and reference-bearing aggregate payloads.
fn run_stage7_2_12(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_12_GATE_END])
}

/// Runs 7.2.12 plus safe array/slice views, subslice reborrow and indexing.
fn run_stage7_2_13(root: &Path) -> Result<(), Box<dyn Error>> {
    run_gate(root, &STAGE7_GATE[..STAGE7_2_13_GATE_END])
}

fn run_gate(root: &Path, steps: &[GateStep]) -> Result<(), Box<dyn Error>> {
    gate::run(root, steps)
}

fn run_rustdoc(root: &Path) -> Result<(), Box<dyn Error>> {
    let status = Command::new("cargo")
        .args(["doc", "--workspace", "--all-features", "--no-deps"])
        .env("RUSTDOCFLAGS", "-D warnings")
        .current_dir(root)
        .status()?;

    if !status.success() {
        return Err("strict workspace rustdoc failed".into());
    }

    Ok(())
}

fn run_frontend_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    run_cargo(root, &["test", "--workspace"])?;
    run_frontend_fuzz(root)
}

fn run_frontend_fuzz(root: &Path) -> Result<(), Box<dyn Error>> {
    run_cargo(
        root,
        &[
            "run",
            "--bin",
            "nera-frontend-fuzz",
            "--",
            "--iterations",
            FUZZ_ITERATIONS,
            "--seed",
            FRONTEND_FUZZ_SEED,
        ],
    )
}

fn run_verifier_regression(root: &Path) -> Result<(), Box<dyn Error>> {
    run_cargo(
        root,
        &[
            "test",
            "--lib",
            "--bin",
            "nera-verifier-fuzz",
            "--test",
            "verifier_transfer",
            "--test",
            "verifier_cfg",
            "--test",
            "verifier_contracts",
            "--test",
            "verifier_cases",
            "--test",
            "verifier_complex_cases",
            "--test",
            "verifier_guarded",
            "--test",
            "verifier_properties",
        ],
    )?;
    run_verifier_fuzz(root)
}

fn run_verifier_fuzz(root: &Path) -> Result<(), Box<dyn Error>> {
    run_cargo(
        root,
        &[
            "run",
            "--bin",
            "nera-verifier-fuzz",
            "--",
            "--iterations",
            FUZZ_ITERATIONS,
            "--seed",
            VERIFIER_FUZZ_SEED,
        ],
    )
}

fn require_native_acceptance_host() -> Result<(), Box<dyn Error>> {
    if supports_native_acceptance(env::consts::ARCH, env::consts::OS) {
        Ok(())
    } else {
        Err(format!(
            "native acceptance requires x86_64 Linux so differential tests cannot be silently cfg-filtered (current target: {} {})",
            env::consts::ARCH,
            env::consts::OS
        )
        .into())
    }
}

fn supports_native_acceptance(arch: &str, os: &str) -> bool {
    arch == "x86_64" && os == "linux"
}

fn print_help() {
    println!(
        "Nera repository tasks\n\n\
         Usage: cargo run -p xtask -- <COMMAND>\n\n\
         Commands:\n\
           check-rust Run the current deduplicated Rust gate\n\
           check-vir Check checked-in VIR corpus snapshots\n\
           check-spec-local Run the stage 8.1 focused Spec/VC acceptance union\n\
           check-contracts Run the stage 8.2 contract/frame acceptance union\n\
           check-loops Run the stage 8.3 loop acceptance union\n\
           generate-vir Refresh checked-in VIR corpus snapshots\n\
           stage4    Run VIR regression and frontend fuzz\n\
           check-verifier Run verifier tests and the deterministic verifier fuzz gate\n\
           check-place Run the stage 6.2 Place semantic regression baseline\n\
           check-control-flow Run the stage 6.3 control-flow semantic baseline\n\
           check-vir-unit Run the stage 6.4 VirUnit semantic baseline\n\
           check-aggregate Run the stage 6.5 aggregate-memory semantic baseline\n\
           check-phase7-identity Run the stage 7.1.1 finding/identity regression baseline\n\
           check-phase7-capability Run the stage 7.1.2 capability/effect regression baseline\n\
           check-phase7-resource-payload Run the stage 7.1.3 typed resource payload regression baseline\n\
           check-phase7-guarded-resource Run the stage 7.1.4 guarded resource regression baseline\n\
           check-phase7-copy-move Run the stage 7.1.5 source Copy/Move regression baseline\n\
           check-phase7-builtin-drop Run the stage 7.1.6 builtin drop and conservation regression baseline\n\
           check-phase7-aggregate-transfer Run the stage 7.1.7 owning aggregate ABI regression baseline\n\
           check-phase7-resource-acceptance Run the complete stage 7.1 resource acceptance baseline\n\
           check-phase7-borrow-baseline Run the stage 7.2.1 safe-borrow semantic baseline\n\
           check-phase7-hir-borrow-regions Run the stage 7.2.2 HIR borrow-region regression baseline\n\
           check-phase7-vir-loan-schema Run the stage 7.2.3 VIR loan-schema regression baseline\n\
           check-phase7-verifier-loans Run the stage 7.2.4 verifier loan-state regression baseline\n\
           check-phase7-loan-consumers Run the stage 7.2.5 interpreter/native loan-consumer baseline\n\
           check-phase7-local-shared-borrow Run the stage 7.2.6 local shared-borrow surface baseline\n\
           check-phase7-local-mutable-borrow Run the stage 7.2.7 local mutable-borrow surface baseline\n\
           check-phase7-reborrow Run the stage 7.2.8 reborrow and parent-restoration baseline\n\
           check-phase7-lowering-architecture Run the stage 7.2.9 Draft VIR and semantic-profile baseline\n\
           check-phase7-nll Run the stage 7.2.10 NLL end-planning baseline\n\
           check-phase7-loan-cfg Run the stage 7.2.11 guarded and loop loan-CFG baseline\n\
           check-phase7-reference-aggregate Run the stage 7.2.12 subobject/reference aggregate baseline\n\
           check-phase7-safe-slice Run the stage 7.2.13 safe slice/view baseline\n\
           check-phase7-borrow-calls Run the stage 7.2.14 borrow call and escape baseline\n\
           check-phase7-borrow-acceptance Run the stage 7.2.15 integrated borrow acceptance\n\
           check-phase7-initialization-baseline Run the stage 7.3.1 initialization semantic baseline\n\
           check-phase7-initialization-planning Run the stage 7.3.2 initialization and cleanup planning gate\n\
           check-phase7-deferred-local Run the stage 7.3.3 deferred local gate\n\
           check-phase7-partial-refill Run the stage 7.3.4 partial move/refill gate\n\
           check-phase7-partial-construction Run the stage 7.3.5 partial resource construction gate\n\
           check-phase7-enum-construction Run the stage 7.3.6 tagged construction gate\n\
           stage5    Run formatting, Rust, frontend and verifier stage gates\n\
           stage6-2  Run the complete stage 6.2 gate, including strict rustdoc\n\
           stage6-3  Run stage6-2 plus the complete control-flow acceptance gate\n\
           stage6-4  Run stage6-3 plus the complete VirUnit/Spec acceptance gate\n\
           stage6-5  Run stage6-4 plus the complete aggregate-memory acceptance gate\n\
           stage7-1-1 Run stage6-5 plus the finding/identity acceptance gate\n\
           stage7-1-2 Run stage7-1-1 plus the capability/effect acceptance gate\n\
           stage7-1-3 Run stage7-1-2 plus the typed resource payload acceptance gate\n\
           stage7-1-4 Run stage7-1-3 plus the guarded resource-state acceptance gate\n\
           stage7-1-5 Run stage7-1-4 plus the source Copy/Move acceptance gate\n\
           stage7-1-6 Run stage7-1-5 plus the builtin drop and conservation acceptance gate\n\
           stage7-1-7 Run stage7-1-6 plus the owning aggregate ABI acceptance gate\n\
           stage7-1-8 Run the complete stage 7.1 resource acceptance gate\n\
           stage7-2-1 Run stage7-1-8 plus the safe-borrow semantic baseline\n\
           stage7-2-2 Run stage7-2-1 plus canonical HIR borrow regions and constraints\n\
           stage7-2-3 Run stage7-2-2 plus explicit VIR borrow regions and loan effects\n\
           stage7-2-4 Run stage7-2-3 plus verifier loan state and transfer semantics\n\
           stage7-2-5 Run stage7-2-4 plus interpreter shadow and native loan erasure\n\
           stage7-2-6 Run stage7-2-5 plus the local shared-borrow surface vertical slice\n\
           stage7-2-7 Run stage7-2-6 plus the local mutable-borrow surface vertical slice\n\
           stage7-2-8 Run stage7-2-7 plus reborrow and exact parent restoration\n\
           stage7-2-9 Run stage7-2-8 plus lowering architecture and frozen runtime semantics\n\
           stage7-2-10 Run stage7-2-9 plus NLL end planning and finite region solving\n\
           stage7-2-11 Run stage7-2-10 plus guarded branch, exit and loop loan fixed points\n\
           stage7-2-12 Run stage7-2-11 plus subobject and reference-bearing aggregate support\n\
           stage7-2-13 Run stage7-2-12 plus safe slice/view and range reborrow support\n\
           stage7-2-14 Run stage7-2-13 plus borrowed calls, returns, recursion and escape checks\n\
           stage7-2-15 Run stage7-2-14 plus complete borrow/region acceptance\n\
           stage7-3-1 Run stage7-2-15 plus initialization and active-representation baseline\n\
           stage7-3-2 Run stage7-3-1 plus initialization planning and complete borrow formation\n\
           stage7-3-3 Run stage7-3-2 plus deferred local and partial trivial initialization\n\
           stage7-3-4 Run stage7-3-3 plus partial move/refill and exactly-once cleanup\n\
           stage7-3-5 Run stage7-3-4 plus partial resource construction and conditional cleanup\n\
           stage7-3-6 Run stage7-3-5 plus tagged construction and active payload cleanup\n\
           check-phase7-heap-construction Run the stage 7.3.7 typed heap storage gate\n\
           stage7-3-7 Run stage7-3-6 plus uninitialized aggregate heap construction\n\
           check-phase7-loop-initialization Run the stage 7.3.8 initialized-prefix gate\n\
           stage7-3-8 Run stage7-3-7 plus bounded loop initialization\n\
           check-phase7-initialization-interfaces Run the stage 7.3.9 call/return initialization gate\n\
           stage7-3-9 Run stage7-3-8 plus initialization interface boundaries\n\
           check-phase7-initialization-acceptance Run the stage 7.3.10 initialization acceptance gate\n\
           stage7-3-10 Run stage7-3-9 plus complete initialization acceptance\n\
           check-phase7-relation-baseline Run the stage 7.4.1 relation/evidence baseline\n\
           stage7-4-1 Run stage7-3-10 plus relation/evidence baseline\n\
           check-phase7-difference-relations Run bounded local difference queries\n\
           stage7-4-2 Run stage7-4-1 plus bounded difference relations\n\
           check-phase7-relation-cfg Run relation CFG propagation and fixed-point checks\n\
           stage7-4-3 Run stage7-4-2 plus relation CFG propagation\n\
           check-phase7-symbolic-footprint Run evaluated footprint and consumer checks\n\
           stage7-4-4 Run stage7-4-3 plus canonical symbolic footprints\n\
           check-phase7-relation-bounds Run length and symbolic containment checks\n\
           stage7-4-5 Run stage7-4-4 plus relation-driven bounds\n\
           check-phase7-disjoint-elements Run dynamic element disjointness checks\n\
           stage7-4-6 Run stage7-4-5 plus dynamic disjoint element loans\n\
           check-phase7-sibling-slices Run dynamic split and sibling reborrow checks\n\
           stage7-4-7 Run stage7-4-6 plus dynamic sibling slice loans\n\
           check-phase7-strided-regions Run fixed-stride multidimensional region checks\n\
           stage7-4-8 Run stage7-4-7 plus fixed-stride regions and pair budgets\n\
           check-phase7-relation-composition Run loop/prefix/call composition checks\n\
           stage7-4-9 Run stage7-4-8 plus relation composition\n\
           stage7-4-10 Run stage7-4-9 plus relation evidence audit\n\
           stage7-4-11 Run complete bounds/disjointness acceptance\n\
           stage7-5-1 Run stage7-4-11 plus provenance semantics baseline\n\
           stage7-5-2 Run stage7-5-1 plus canonical provenance schema\n\
           stage7-5-3 Run stage7-5-2 plus allocation instance lifecycle\n\
           stage7-5-4 Run stage7-5-3 plus authority-free raw address formation\n\
           stage7-5-5 Run stage7-5-4 plus subobject offsets and one-past endpoints\n\
           check-phase7-pointer-domain Run arithmetic domain regressions\n\
           stage7-5-6 Run stage7-5-5 plus checked pointer relations\n\
           check-phase7-pointer-comparison Run same-domain pointer relation regressions\n\
           stage7-5-7 Run stage7-5-6 plus provenance flow across CFG and calls\n\
           check-phase7-provenance-flow Run pointer carrier and lifetime regressions\n\
           stage7-5-8 Run stage7-5-7 plus interpreter/native address model checks\n\
           check-phase7-address-model Run address model and erasure regressions\n\
           stage7-5-9 Run stage7-5-8 plus provenance evidence and replay checks\n\
           check-phase7-provenance-audit Run provenance audit and budget regressions\n\
           stage7-5-10 Run complete safe provenance acceptance gate\n\
           check-phase7-provenance-acceptance Run provenance matrix and growth checks\n\
           stage7-6-1 Run internal summary baseline gate\n\
           check-phase7-summary-baseline Run summary semantics and capability baseline checks\n\
           stage7-6-2 Run summary architecture and behavior-preservation gate\n\
           check-phase7-summary-architecture Run lowering and transfer seam regressions\n\
           stage7-6-3 Run signature-relative summary projection gate\n\
           check-phase7-summary-projection Run summary schema and mutation checks\n\
           stage7-6-5 Run conditional summary resource composition gate\n\
           check-phase7-conditional-summary Run conditional summary regressions\n\
           stage7-6-6 Run borrowed summary interface gate\n\
           check-phase7-borrow-summary Run borrowed summary regressions\n\
           stage7-6-7 Run recursive SCC summary closure gate\n\
           stage7-6-8 Run summary audit and acceptance gate\n\
           stage7-7-1 Run verification preview report gate\n\
           check-phase7-verify-report Run preview report regressions\n\
           stage7-7-2 Run source diagnostic and text report gate\n\
           check-phase7-source-diagnostics Run text report regressions\n\
           stage7-7-3 Run single-file verify CLI gate\n\
           stage7-7-4 Run ordinary memory-safe source corpus gate\n\
           stage7-7-5 Run verification fail-closed integration gate\n\
           stage7-7-6 Run complete single-file verification preview gate\n\
           stage7-8-1 Run compilation session and source snapshot gate\n\
           stage7-8-2 Run closed module program acceptance gate\n\
           stage7-8-3 Run generic instances and named lifetime acceptance gate\n\
           stage7-8-6 Run the complete stage 7 Rust acceptance gate\n\
           check-phase7-implicit-borrow-baseline Run implicit borrow baseline regressions only\n\
           check-phase7-borrow-interface-mapping Run logical borrow interface and ABI regressions\n\
           check-phase7-implicit-borrow-inference Run unique borrow-source inference regressions\n\
           check-phase7-conditional-borrow-inference Run guarded borrow-source world regressions\n\
           check-phase7-borrow-projection Run bounded borrow-result projection regressions\n\
           check-phase7-borrow-source-scc Run loop and recursive borrow-source regressions\n\
           check-phase7-implicit-lifetime-syntax Run inferred lifetime syntax and legacy migration regressions\n\
           check-phase7-implicit-borrow-acceptance Run diagnostics and combined implicit-borrow acceptance\n\
           check-phase7-stage-acceptance Run the focused stage 7 transition acceptance\n\
           check-phase7-generic-instances Run concrete type/const instance regressions\n\
           check-phase7-named-lifetimes Compatibility alias for removed lifetime syntax regressions\n\
           check-phase7-module-program Run module ownership, visibility, source and consumer regressions\n\
           check-phase7-compilation-session Run session identity and source mapping regressions\n\
           check-phase7-verify-acceptance Run combined preview acceptance regressions\n\
           check-phase7-verify-fail-closed Run budget/trust/replay report regressions\n\
           check-phase7-auto-memory-corpus Run source composition regressions\n\
           check-phase7-verify-preview Run verify CLI regressions\n\
           check-phase7-summary-acceptance Run summary audit regressions\n\
           check-phase7-recursive-summary Run recursive summary regressions\n\
           stage7-6-4 Run nonrecursive summary call closure gate\n\
           check-phase7-summary-calls Run effects, frame and call regressions\n\
           check-phase7-raw-address Run raw address formation regressions\n\
           check-phase7-allocation-instance Check bounded instance reuse and lifecycle\n\
           check-phase7-provenance-schema Check canonical subobject/source recipes\n\
           check-phase7-provenance-baseline Check pointer surface and safety boundaries\n\
           check-phase7-relation-acceptance Check stage 7.4 acceptance\n\
           check-phase7-relation-audit Check query evidence and replay"
    );
}

#[cfg(test)]
mod tests {
    use super::{
        GateStep, STAGE5_GATE_END, STAGE6_2_GATE_END, STAGE6_3_GATE_END, STAGE6_4_GATE_END,
        STAGE7_2_11_GATE_END, STAGE7_2_12_GATE_END, STAGE7_2_13_GATE_END, STAGE7_2_14_GATE_END,
        STAGE7_GATE, parse_command, supports_native_acceptance,
    };

    #[test]
    fn command_parser_rejects_silent_test_filters() {
        assert_eq!(
            parse_command(["stage6-5".to_owned()].into_iter()).expect("command parses"),
            "stage6-5"
        );
        assert_eq!(
            parse_command(["stage7-1-1".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-1"
        );
        assert_eq!(
            parse_command(["stage7-1-2".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-2"
        );
        assert_eq!(
            parse_command(["stage7-1-3".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-3"
        );
        assert_eq!(
            parse_command(["stage7-1-4".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-4"
        );
        assert_eq!(
            parse_command(["stage7-1-5".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-5"
        );
        assert_eq!(
            parse_command(["stage7-1-6".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-6"
        );
        assert_eq!(
            parse_command(["stage7-1-7".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-7"
        );
        assert_eq!(
            parse_command(["stage7-1-8".to_owned()].into_iter()).expect("command parses"),
            "stage7-1-8"
        );
        assert_eq!(
            parse_command(["stage7-2-1".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-1"
        );
        assert_eq!(
            parse_command(["stage7-2-2".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-2"
        );
        assert_eq!(
            parse_command(["stage7-2-3".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-3"
        );
        assert_eq!(
            parse_command(["stage7-2-4".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-4"
        );
        assert_eq!(
            parse_command(["stage7-2-5".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-5"
        );
        assert_eq!(
            parse_command(["stage7-2-6".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-6"
        );
        assert_eq!(
            parse_command(["stage7-2-7".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-7"
        );
        assert_eq!(
            parse_command(["stage7-2-8".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-8"
        );
        assert_eq!(
            parse_command(["stage7-2-9".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-9"
        );
        assert_eq!(
            parse_command(["stage7-2-10".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-10"
        );
        assert_eq!(
            parse_command(["stage7-2-11".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-11"
        );
        assert_eq!(
            parse_command(["stage7-2-12".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-12"
        );
        assert_eq!(
            parse_command(["stage7-2-13".to_owned()].into_iter()).expect("command parses"),
            "stage7-2-13"
        );
        let error =
            parse_command(["stage6-5".to_owned(), "native_acceptance".to_owned()].into_iter())
                .expect_err("stage gates must reject extra filters");
        assert!(error.to_string().contains("do not accept test filters"));
        for command in [
            "stage7-2-14",
            "stage7-2-15",
            "check-phase7-borrow-acceptance",
            "stage7-3-1",
            "check-phase7-initialization-baseline",
            "stage7-3-2",
            "check-phase7-initialization-planning",
            "stage7-3-3",
            "check-phase7-deferred-local",
            "stage7-3-4",
            "check-phase7-partial-refill",
            "stage7-3-5",
            "check-phase7-partial-construction",
            "stage7-3-6",
            "check-phase7-enum-construction",
            "stage7-3-7",
            "check-phase7-heap-construction",
            "stage7-3-8",
            "check-phase7-loop-initialization",
            "stage7-3-9",
            "check-phase7-initialization-interfaces",
            "stage7-3-10",
            "check-phase7-initialization-acceptance",
            "stage7-4-1",
            "check-phase7-relation-baseline",
            "stage7-4-2",
            "stage7-4-3",
            "stage7-4-4",
            "stage7-4-5",
            "stage7-4-6",
            "check-phase7-disjoint-elements",
            "stage7-4-7",
            "check-phase7-sibling-slices",
            "stage7-4-8",
            "stage7-4-9",
            "stage7-4-10",
            "stage7-4-11",
            "stage7-5-1",
            "stage7-5-2",
            "stage7-5-3",
            "stage7-5-4",
            "stage7-5-5",
            "check-phase7-pointer-domain",
            "stage7-5-6",
            "check-phase7-pointer-comparison",
            "stage7-5-7",
            "check-phase7-provenance-flow",
            "stage7-5-8",
            "check-phase7-address-model",
            "stage7-5-9",
            "check-phase7-provenance-audit",
            "stage7-5-10",
            "check-phase7-provenance-acceptance",
            "stage7-6-1",
            "check-phase7-summary-baseline",
            "stage7-6-2",
            "stage7-6-3",
            "stage7-6-4",
            "stage7-6-5",
            "check-phase7-conditional-summary",
            "stage7-6-6",
            "check-phase7-borrow-summary",
            "stage7-6-7",
            "stage7-6-8",
            "stage7-7-1",
            "check-phase7-verify-report",
            "stage7-7-2",
            "check-phase7-source-diagnostics",
            "stage7-7-3",
            "stage7-7-4",
            "stage7-7-5",
            "stage7-7-6",
            "stage7-8-1",
            "stage7-8-2",
            "stage7-8-3",
            "check-phase7-implicit-borrow-baseline",
            "check-phase7-borrow-interface-mapping",
            "check-phase7-implicit-borrow-inference",
            "check-phase7-conditional-borrow-inference",
            "check-phase7-borrow-projection",
            "check-phase7-borrow-source-scc",
            "check-phase7-implicit-lifetime-syntax",
            "check-phase7-implicit-borrow-acceptance",
            "generate-vir",
            "check-phase7-generic-instances",
            "check-phase7-named-lifetimes",
            "check-phase7-module-program",
            "check-phase7-compilation-session",
            "check-phase7-verify-acceptance",
            "check-phase7-verify-fail-closed",
            "check-phase7-auto-memory-corpus",
            "check-phase7-verify-preview",
            "check-phase7-summary-acceptance",
            "check-phase7-recursive-summary",
            "check-phase7-summary-calls",
            "check-phase7-summary-projection",
            "check-phase7-summary-architecture",
            "check-phase7-raw-address",
            "check-phase7-allocation-instance",
            "check-phase7-provenance-schema",
            "check-phase7-provenance-baseline",
            "check-phase7-relation-acceptance",
            "check-phase7-relation-audit",
            "check-phase7-relation-composition",
            "check-phase7-strided-regions",
            "check-phase7-relation-bounds",
            "check-phase7-symbolic-footprint",
            "check-phase7-relation-cfg",
            "check-phase7-difference-relations",
        ] {
            assert_eq!(
                parse_command([command.to_owned()].into_iter()).unwrap(),
                command
            );
            assert!(parse_command([command.to_owned(), "filter".to_owned()].into_iter()).is_err());
        }
    }

    #[test]
    fn stage_gate_manifests_are_complete_monotonic_extensions() {
        assert_eq!(
            STAGE7_GATE,
            &[
                GateStep::VirSnapshots,
                GateStep::Format,
                GateStep::WorkspaceTests,
                GateStep::FrontendFuzz,
                GateStep::VerifierFuzz,
                GateStep::Clippy,
                GateStep::Place,
                GateStep::Rustdoc,
                GateStep::ControlFlow,
                GateStep::VirUnit,
                GateStep::Aggregate,
                GateStep::Phase711Identity,
                GateStep::Phase712Capability,
                GateStep::Phase713ResourcePayload,
                GateStep::Phase714GuardedResource,
                GateStep::Phase715CopyMove,
                GateStep::Phase716BuiltinDrop,
                GateStep::Phase717AggregateTransfer,
                GateStep::Phase718ResourceAcceptance,
                GateStep::Phase721BorrowBaseline,
                GateStep::Phase722HirBorrowRegions,
                GateStep::Phase723VirLoanSchema,
                GateStep::Phase724VerifierLoans,
                GateStep::Phase725LoanConsumers,
                GateStep::Phase726LocalSharedBorrow,
                GateStep::Phase727LocalMutableBorrow,
                GateStep::Phase728Reborrow,
                GateStep::Phase729LoweringArchitecture,
                GateStep::Phase7210NllEndPlanning,
                GateStep::Phase7211GuardedLoanCfg,
                GateStep::Phase7212ReferenceAggregate,
                GateStep::Phase7213SafeSlice,
                GateStep::Phase7214BorrowCalls,
                GateStep::Phase7215BorrowAcceptance,
                GateStep::Phase731InitializationBaseline,
                GateStep::Phase732InitializationPlanning,
                GateStep::Phase733DeferredLocal,
                GateStep::Phase734PartialRefill,
                GateStep::Phase735PartialConstruction,
                GateStep::Phase736EnumConstruction,
                GateStep::Phase737HeapConstruction,
                GateStep::Phase738LoopInitialization,
                GateStep::Phase739InitializationInterfaces,
                GateStep::Phase7310InitializationAcceptance,
                GateStep::Phase741RelationBaseline,
                GateStep::Phase742DifferenceRelations,
                GateStep::Phase743RelationCfg,
                GateStep::Phase744SymbolicFootprint,
                GateStep::Phase745RelationBounds,
                GateStep::Phase746DisjointElements,
                GateStep::Phase747SiblingSlices,
                GateStep::Phase748StridedRegions,
                GateStep::Phase749RelationComposition,
                GateStep::Phase7410RelationAudit,
                GateStep::Phase7411RelationAcceptance,
                GateStep::Phase751ProvenanceBaseline,
                GateStep::Phase752ProvenanceSchema,
                GateStep::Phase753AllocationInstance,
                GateStep::Phase754RawAddress,
                GateStep::Phase755PointerDomain,
                GateStep::Phase756PointerComparison,
                GateStep::Phase757ProvenanceFlow,
                GateStep::Phase758AddressModel,
                GateStep::Phase759ProvenanceAudit,
                GateStep::Phase7510ProvenanceAcceptance,
                GateStep::Phase761SummaryBaseline,
                GateStep::Phase762SummaryArchitecture,
                GateStep::Phase763SummaryProjection,
                GateStep::Phase764SummaryCalls,
                GateStep::Phase765ConditionalSummary,
                GateStep::Phase766BorrowSummary,
                GateStep::Phase767RecursiveSummary,
                GateStep::Phase768SummaryAcceptance,
                GateStep::Phase771VerifyReport,
                GateStep::Phase772SourceDiagnostics,
                GateStep::Phase773VerifyPreview,
                GateStep::Phase774AutoMemoryCorpus,
                GateStep::Phase775VerifyFailClosed,
                GateStep::Phase776VerifyAcceptance,
                GateStep::Phase781CompilationSession,
                GateStep::Phase782ModuleProgram,
                GateStep::Phase783GenericInstances,
                GateStep::Phase783NamedLifetimes,
                GateStep::Phase7831ImplicitBorrowBaseline,
                GateStep::Phase7832BorrowInterfaceMapping,
                GateStep::Phase7833ImplicitBorrowInference,
                GateStep::Phase7834ConditionalBorrowInference,
                GateStep::Phase7835BorrowProjection,
                GateStep::Phase7836BorrowSourceScc,
                GateStep::Phase7837ImplicitLifetimeSyntax,
                GateStep::Phase7838ImplicitBorrowAcceptance,
                GateStep::Phase784CapabilityProfile,
                GateStep::Phase785InterfaceArtifact,
                GateStep::Phase786StageAcceptance,
            ]
        );
        assert_eq!(STAGE7_GATE[STAGE5_GATE_END], GateStep::Place);
        assert_eq!(STAGE7_GATE[STAGE6_2_GATE_END], GateStep::ControlFlow);
        assert_eq!(STAGE7_GATE[STAGE6_3_GATE_END], GateStep::VirUnit);
        assert_eq!(STAGE7_GATE[STAGE6_4_GATE_END], GateStep::Aggregate);
        assert_eq!(
            STAGE7_GATE[STAGE7_2_11_GATE_END],
            GateStep::Phase7212ReferenceAggregate
        );
        // Frozen adjacent stage prefixes do not depend on the number of future stages.
        let boundaries = [
            STAGE7_2_12_GATE_END,
            STAGE7_2_13_GATE_END,
            STAGE7_2_14_GATE_END,
            super::STAGE7_2_15_GATE_END,
            super::STAGE7_3_1_GATE_END,
            super::STAGE7_3_2_GATE_END,
            super::STAGE7_3_3_GATE_END,
            super::STAGE7_3_4_GATE_END,
            super::STAGE7_3_5_GATE_END,
            super::STAGE7_3_6_GATE_END,
            super::STAGE7_3_7_GATE_END,
            super::STAGE7_3_8_GATE_END,
            super::STAGE7_3_9_GATE_END,
            super::STAGE7_3_10_GATE_END,
            super::STAGE7_4_1_GATE_END,
            super::STAGE7_4_2_GATE_END,
            super::STAGE7_4_3_GATE_END,
            super::STAGE7_4_4_GATE_END,
            super::STAGE7_4_5_GATE_END,
            super::STAGE7_4_6_GATE_END,
            super::STAGE7_4_7_GATE_END,
            super::STAGE7_4_8_GATE_END,
            super::STAGE7_4_9_GATE_END,
            super::STAGE7_4_10_GATE_END,
            super::STAGE7_4_11_GATE_END,
            super::STAGE7_5_1_GATE_END,
            super::STAGE7_5_2_GATE_END,
            super::STAGE7_5_3_GATE_END,
            super::STAGE7_5_4_GATE_END,
            super::STAGE7_5_5_GATE_END,
            super::STAGE7_5_6_GATE_END,
            super::STAGE7_5_7_GATE_END,
            super::STAGE7_5_8_GATE_END,
            super::STAGE7_5_9_GATE_END,
            super::STAGE7_5_10_GATE_END,
            super::STAGE7_6_1_GATE_END,
            super::STAGE7_6_2_GATE_END,
            super::STAGE7_6_3_GATE_END,
            super::STAGE7_6_4_GATE_END,
            super::STAGE7_6_5_GATE_END,
            super::STAGE7_6_6_GATE_END,
            super::STAGE7_6_7_GATE_END,
            super::STAGE7_6_8_GATE_END,
            super::STAGE7_7_1_GATE_END,
            super::STAGE7_7_2_GATE_END,
            super::STAGE7_7_3_GATE_END,
            super::STAGE7_7_4_GATE_END,
            super::STAGE7_7_5_GATE_END,
            super::STAGE7_7_6_GATE_END,
            super::STAGE7_8_1_GATE_END,
            super::STAGE7_8_2_GATE_END,
        ];
        assert!(boundaries.windows(2).all(|pair| pair[1] == pair[0] + 1));
        // The original 7.8.3 prefix freezes its two initial acceptance increments;
        // later implicit-borrow increments remain independently selectable.
        assert_eq!(super::STAGE7_8_3_GATE_END, super::STAGE7_8_2_GATE_END + 2);
        assert_eq!(super::STAGE7_8_4_GATE_END, super::STAGE7_8_3_GATE_END + 9);
        assert_eq!(super::STAGE7_8_5_GATE_END, super::STAGE7_8_4_GATE_END + 1);
        assert_eq!(super::STAGE7_8_6_GATE_END, super::STAGE7_8_5_GATE_END + 1);
        assert_eq!(STAGE7_GATE.len(), super::STAGE7_8_6_GATE_END);
        assert_eq!(
            STAGE7_GATE[super::STAGE7_8_3_GATE_END],
            GateStep::Phase7831ImplicitBorrowBaseline
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_8_2_GATE_END],
            GateStep::Phase783GenericInstances
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_8_2_GATE_END + 1],
            GateStep::Phase783NamedLifetimes
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_5_2_GATE_END],
            GateStep::Phase753AllocationInstance
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_5_1_GATE_END],
            GateStep::Phase752ProvenanceSchema
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_11_GATE_END],
            GateStep::Phase751ProvenanceBaseline
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_4_GATE_END],
            GateStep::Phase745RelationBounds
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_5_GATE_END],
            GateStep::Phase746DisjointElements
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_6_GATE_END],
            GateStep::Phase747SiblingSlices
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_7_GATE_END],
            GateStep::Phase748StridedRegions
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_8_GATE_END],
            GateStep::Phase749RelationComposition
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_3_GATE_END],
            GateStep::Phase744SymbolicFootprint
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_2_GATE_END],
            GateStep::Phase743RelationCfg
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_4_1_GATE_END],
            GateStep::Phase742DifferenceRelations
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_10_GATE_END],
            GateStep::Phase741RelationBaseline
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_9_GATE_END],
            GateStep::Phase7310InitializationAcceptance
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_8_GATE_END],
            GateStep::Phase739InitializationInterfaces
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_7_GATE_END],
            GateStep::Phase738LoopInitialization
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_6_GATE_END],
            GateStep::Phase737HeapConstruction
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_5_GATE_END],
            GateStep::Phase736EnumConstruction
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_4_GATE_END],
            GateStep::Phase735PartialConstruction
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_3_GATE_END],
            GateStep::Phase734PartialRefill
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_2_GATE_END],
            GateStep::Phase733DeferredLocal
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_3_1_GATE_END],
            GateStep::Phase732InitializationPlanning
        );
        assert_eq!(
            STAGE7_GATE[super::STAGE7_2_15_GATE_END],
            GateStep::Phase731InitializationBaseline
        );
        assert_eq!(
            STAGE7_GATE[STAGE7_2_13_GATE_END],
            GateStep::Phase7214BorrowCalls
        );
        assert_eq!(
            STAGE7_GATE[STAGE7_2_14_GATE_END],
            GateStep::Phase7215BorrowAcceptance
        );
        assert_eq!(
            STAGE7_GATE[STAGE7_2_12_GATE_END],
            GateStep::Phase7213SafeSlice
        );
    }

    #[test]
    fn native_acceptance_host_gate_is_explicit() {
        assert!(supports_native_acceptance("x86_64", "linux"));
        assert!(!supports_native_acceptance("aarch64", "linux"));
        assert!(!supports_native_acceptance("x86_64", "macos"));
    }
}
