#[path = "support/core0_oracle.rs"]
mod core0_oracle;

use core0_oracle::{CoreFault, CoreOutcome};
use nera::{
    CfgAnalysisConfig, FrontendOutput, FrontendStatus, SourceFile, VirExecutionErrorKind,
    VirRuntimeValue, analyze, interpret, project_core0_compat, verify_program,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expected {
    Unit,
    Word(u64),
    Fault(FaultClass),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FaultClass {
    AllocationFailure,
    UseAfterFree,
    DoubleFree,
    PointerOffsetOutOfBounds,
    OutOfBounds,
    Misaligned,
    UninitializedRead,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CoreObserved {
    Returned(u64),
    Fault(FaultClass),
}

struct CorpusCase {
    name: &'static str,
    source_path: &'static str,
    source: &'static [u8],
    snapshot: &'static str,
    expected: Expected,
}

const CORPUS: &[CorpusCase] = &[
    CorpusCase {
        name: "memory",
        source_path: "spec/cases/vir/memory.nera",
        source: include_bytes!("../spec/cases/vir/memory.nera"),
        snapshot: include_str!("../spec/cases/vir/memory.vir"),
        expected: Expected::Word(44),
    },
    CorpusCase {
        name: "unit",
        source_path: "spec/cases/vir/unit.nera",
        source: include_bytes!("../spec/cases/vir/unit.nera"),
        snapshot: include_str!("../spec/cases/vir/unit.vir"),
        expected: Expected::Unit,
    },
    CorpusCase {
        name: "uninitialized-read",
        source_path: "spec/cases/vir/uninitialized-read.nera",
        source: include_bytes!("../spec/cases/vir/uninitialized-read.nera"),
        snapshot: include_str!("../spec/cases/vir/uninitialized-read.vir"),
        expected: Expected::Fault(FaultClass::UninitializedRead),
    },
    CorpusCase {
        name: "out-of-bounds-access",
        source_path: "spec/cases/vir/out-of-bounds-access.nera",
        source: include_bytes!("../spec/cases/vir/out-of-bounds-access.nera"),
        snapshot: include_str!("../spec/cases/vir/out-of-bounds-access.vir"),
        expected: Expected::Fault(FaultClass::OutOfBounds),
    },
    CorpusCase {
        name: "pointer-offset-out-of-bounds",
        source_path: "spec/cases/vir/pointer-offset-out-of-bounds.nera",
        source: include_bytes!("../spec/cases/vir/pointer-offset-out-of-bounds.nera"),
        snapshot: include_str!("../spec/cases/vir/pointer-offset-out-of-bounds.vir"),
        expected: Expected::Fault(FaultClass::PointerOffsetOutOfBounds),
    },
    CorpusCase {
        name: "misaligned-access",
        source_path: "spec/cases/vir/misaligned-access.nera",
        source: include_bytes!("../spec/cases/vir/misaligned-access.nera"),
        snapshot: include_str!("../spec/cases/vir/misaligned-access.vir"),
        expected: Expected::Fault(FaultClass::Misaligned),
    },
    CorpusCase {
        name: "double-free",
        source_path: "spec/cases/vir/double-free.nera",
        source: include_bytes!("../spec/cases/vir/double-free.nera"),
        snapshot: include_str!("../spec/cases/vir/double-free.vir"),
        expected: Expected::Fault(FaultClass::DoubleFree),
    },
    CorpusCase {
        name: "allocation-failure",
        source_path: "spec/cases/vir/allocation-failure.nera",
        source: include_bytes!("../spec/cases/vir/allocation-failure.nera"),
        snapshot: include_str!("../spec/cases/vir/allocation-failure.vir"),
        expected: Expected::Fault(FaultClass::AllocationFailure),
    },
    CorpusCase {
        name: "use-after-free",
        source_path: "spec/cases/verify/uaf.nera",
        source: include_bytes!("../spec/cases/verify/uaf.nera"),
        snapshot: include_str!("../spec/cases/vir/uaf.vir"),
        expected: Expected::Fault(FaultClass::UseAfterFree),
    },
];

#[test]
fn vir_corpus_preserves_snapshots_replay_and_independent_oracle() {
    for case in CORPUS {
        let output = lower(case);
        let replay = lower(case);
        assert_eq!(output, replay, "{} frontend output", case.name);
        assert_eq!(
            output.vir().map(ToString::to_string),
            replay.vir().map(ToString::to_string),
            "{} stable dump",
            case.name
        );
        assert_eq!(
            output.vir().expect("accepted corpus has VIR").stable_dump(),
            case.snapshot,
            "{} VIR snapshot is stale; run `cargo run -p xtask -- generate`",
            case.name
        );
        let execution = execute(output.vir().expect("accepted corpus has VIR"));
        assert_eq!(
            execution,
            execute(replay.vir().expect("replay has VIR")),
            "{} interpreter outcome",
            case.name
        );
        let vir = observe_execution(execution);
        let resolved = output
            .vir()
            .expect("accepted corpus has VIR")
            .resolve()
            .expect("corpus VIR resolves");
        let core = project_core0_compat(resolved.runtime())
            .expect("corpus is inside the frozen Core0 compatibility subset");
        let core = observe_core(core0_oracle::execute(&core));
        assert_core_expected(core, case.expected, case.name);
        assert_eq!(vir, case.expected, "{}", case.name);
    }
}

#[test]
fn safe_raw_memory_source_is_verified_before_runtime_consumers() {
    let case = CORPUS
        .iter()
        .find(|case| case.name == "memory")
        .expect("safe raw-memory corpus case");
    let output = lower(case);
    let resolved = output
        .vir()
        .expect("safe raw-memory source has VIR")
        .resolve()
        .expect("safe raw-memory VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("safe raw-memory VIR reaches whole-program verification");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("verified raw-memory source executes")
            .values(),
        &[VirRuntimeValue::U64(44)]
    );
}

#[test]
fn unsafe_raw_memory_source_corpus_never_becomes_memory_checked() {
    for name in [
        "uninitialized-read",
        "out-of-bounds-access",
        "pointer-offset-out-of-bounds",
        "misaligned-access",
        "double-free",
        "use-after-free",
    ] {
        let case = CORPUS
            .iter()
            .find(|case| case.name == name)
            .expect("unsafe raw-memory corpus case");
        let output = lower(case);
        let resolved = output
            .vir()
            .expect("structural raw-memory source has VIR")
            .resolve()
            .expect("structural raw-memory VIR resolves");
        let verification = verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("unsafe raw-memory VIR is reported, not treated as malformed");
        assert!(
            !verification.is_memory_checked_core0(),
            "{name} unexpectedly became memory checked"
        );
        assert!(!verification.diagnostics().is_empty(), "{name}");
    }
}

fn lower(case: &CorpusCase) -> FrontendOutput {
    let output = analyze(&SourceFile::new(case.source_path, case.source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{} frontend issues: {:?}",
        case.name,
        output.issues()
    );
    output
}

fn observe_execution(result: Result<nera::VirExecution, nera::VirExecutionError>) -> Expected {
    match result {
        Ok(execution) => match execution.values() {
            [] => Expected::Unit,
            [VirRuntimeValue::U64(value)] => Expected::Word(*value),
            values => panic!("unexpected VIR return values: {values:?}"),
        },
        Err(error) => Expected::Fault(match error.kind() {
            VirExecutionErrorKind::AllocationFailure { .. } => FaultClass::AllocationFailure,
            VirExecutionErrorKind::UseAfterFree { .. } => FaultClass::UseAfterFree,
            VirExecutionErrorKind::DoubleFree { .. } => FaultClass::DoubleFree,
            VirExecutionErrorKind::PointerOffsetOutOfBounds { .. } => {
                FaultClass::PointerOffsetOutOfBounds
            }
            VirExecutionErrorKind::OutOfBoundsAccess { .. } => FaultClass::OutOfBounds,
            VirExecutionErrorKind::MisalignedAccess { .. } => FaultClass::Misaligned,
            VirExecutionErrorKind::UninitializedRead { .. } => FaultClass::UninitializedRead,
            other => panic!("unexpected VIR fault: {other:?}"),
        }),
    }
}

fn execute(
    program: &nera::ValidatedVirUnit,
) -> Result<nera::VirExecution, nera::VirExecutionError> {
    let resolved = program.resolve().expect("corpus VIR resolves");
    interpret(resolved.runtime())
}

fn observe_core(outcome: CoreOutcome) -> CoreObserved {
    match outcome {
        CoreOutcome::Returned(value) => CoreObserved::Returned(value),
        CoreOutcome::Fault(fault) => CoreObserved::Fault(match fault {
            CoreFault::AllocationFailure => FaultClass::AllocationFailure,
            CoreFault::PointerOffsetOutOfBounds => FaultClass::PointerOffsetOutOfBounds,
            CoreFault::OutOfBounds => FaultClass::OutOfBounds,
            CoreFault::Misaligned => FaultClass::Misaligned,
            CoreFault::UninitializedRead => FaultClass::UninitializedRead,
            CoreFault::DoubleFree => FaultClass::DoubleFree,
            CoreFault::UseAfterFree => FaultClass::UseAfterFree,
            other => panic!("unexpected Core0 fault: {other:?}"),
        }),
    }
}

fn assert_core_expected(observed: CoreObserved, expected: Expected, case: &str) {
    let expected = match expected {
        Expected::Unit => CoreObserved::Returned(0),
        Expected::Word(value) => CoreObserved::Returned(value),
        Expected::Fault(fault) => CoreObserved::Fault(fault),
    };
    assert_eq!(observed, expected, "{case}");
}
