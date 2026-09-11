#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::path::{Path, PathBuf};
#[path = "support/preview_checks.rs"]
mod preview_checks;
use std::process::{Command, ExitStatus};
use std::sync::atomic::{AtomicU64, Ordering};

use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64SystemToolchain};
use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId, VirConstant,
    VirContractId, VirFunction, VirFunctionId, VirInstruction, VirLocation, VirMemorySchema,
    VirSignature, VirSpecClause, VirSpecClauseId, VirSpecClauseKind, VirSpecClauseOrigin,
    VirSpecClauseOwner, VirSpecLocation, VirSpecProve, VirSpecProveId, VirSpecTerm, VirSpecTermId,
    VirSpecTermKind, VirSpecType, VirTerminator, VirTrustEntry, VirTrustEntryId,
    VirTrustPolicyKind, VirTrustScope, VirType, VirUnit, VirValue, VirValueId, interpret,
};

#[test]
fn legal_ghost_tables_cannot_change_runtime_or_native_observations() {
    assert_ghost_observations(returning_unit());
}

#[test]
fn conditional_and_recursive_summary_closure_cannot_change_ghost_erasure() {
    for source in [
        include_str!("../spec/cases/verify/summary-recursive.nera"),
        include_str!("../spec/cases/verify/summary-conditional-payload.nera"),
    ] {
        let output = nera::analyze(&nera::SourceFile::from_text("summary-ghost.nera", source));
        assert_ghost_observations(output.vir().unwrap().as_unit().clone());
    }
}

#[test]
fn provenance_operations_and_borrowed_abi_ignore_ghost_tables() {
    let output = nera::analyze(&nera::SourceFile::from_text(
        "native-address-model.nera",
        include_str!("../spec/cases/verify/native-address-model.nera"),
    ));
    assert_eq!(
        output.status(),
        nera::FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    assert_ghost_observations(output.vir().unwrap().as_unit().clone());
}

fn assert_ghost_observations(raw: VirUnit) {
    let baseline_preview = nera::verification::verify_unit(raw.clone(), Default::default());
    let enriched_preview =
        nera::verification::verify_unit(with_prove_and_trust(raw), Default::default());
    preview_checks::observe(&baseline_preview);
    preview_checks::observe(&enriched_preview);
    let baseline = baseline_preview
        .validated_unit()
        .expect("baseline validates");
    let enriched = enriched_preview
        .validated_unit()
        .expect("ghost-enriched unit validates");

    assert_ne!(baseline.stable_dump(), enriched.stable_dump());
    let baseline = baseline.resolve().expect("baseline resolves");
    let enriched = enriched.resolve().expect("ghost-enriched unit resolves");

    assert_eq!(
        baseline.runtime().as_runtime().stable_dump(),
        enriched.runtime().as_runtime().stable_dump()
    );

    let baseline_execution = interpret(baseline.runtime()).expect("baseline executes");
    let enriched_execution = interpret(enriched.runtime()).expect("enriched unit executes");
    assert_eq!(baseline_execution, enriched_execution);
    assert_eq!(baseline_execution.trace(), enriched_execution.trace());

    let baseline_plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(baseline.runtime())
        .expect("baseline plans");
    let enriched_plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(enriched.runtime())
        .expect("enriched unit plans");
    assert_eq!(baseline_plan, enriched_plan);

    let baseline_machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(baseline.runtime())
        .expect("baseline lowers");
    let enriched_machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(enriched.runtime())
        .expect("enriched unit lowers");
    assert_eq!(baseline_machine, enriched_machine);

    let baseline_assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&baseline_machine)
        .expect("baseline assembly emits");
    let enriched_assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&enriched_machine)
        .expect("enriched assembly emits");
    assert_eq!(baseline_assembly, enriched_assembly);
    assert_eq!(
        execute_assembly("baseline", &baseline_assembly),
        execute_assembly("enriched", &enriched_assembly)
    );

    let baseline_verification = baseline_preview.verification().expect("baseline verifies");
    let enriched_verification = enriched_preview
        .verification()
        .expect("enriched unit verifies");
    assert!(baseline_verification.is_memory_checked_core0());
    assert!(enriched_verification.is_memory_checked_core0());
    assert!(
        baseline_verification.functions()[&VirFunctionId::new(0)]
            .proofs()
            .is_empty()
    );
    assert_eq!(
        enriched_verification.functions()[&VirFunctionId::new(0)]
            .proofs()
            .len(),
        1
    );
    assert!(baseline_verification.trust_report().entries().is_empty());
    assert_eq!(enriched_verification.trust_report().entries().len(), 1);
}

#[test]
fn legal_ghost_tables_cannot_change_fault_or_fault_trace() {
    let raw = faulting_unit();
    let baseline = raw
        .clone()
        .into_validated()
        .expect("baseline unit validates");
    let enriched = with_prove_and_trust(raw)
        .into_validated()
        .expect("ghost-enriched unit validates");
    let baseline = baseline.resolve().expect("baseline resolves");
    let enriched = enriched.resolve().expect("ghost-enriched unit resolves");

    let baseline_fault = interpret(baseline.runtime()).expect_err("runtime Check faults");
    let enriched_fault = interpret(enriched.runtime()).expect_err("runtime Check still faults");
    assert_eq!(baseline_fault, enriched_fault);
    assert_eq!(baseline_fault.trace(), enriched_fault.trace());
}

fn returning_unit() -> VirUnit {
    unit_with_body(
        VirSignature {
            parameters: Vec::new(),
            results: vec![VirType::U64],
        },
        vec![instruction(VirInstruction::Constant {
            result: value(0, VirType::U64),
            value: VirConstant::U64(17),
        })],
        VirTerminator::Return {
            values: vec![VirValueId::new(0)],
        },
    )
}

fn faulting_unit() -> VirUnit {
    unit_with_body(
        VirSignature {
            parameters: Vec::new(),
            results: Vec::new(),
        },
        vec![
            instruction(VirInstruction::Constant {
                result: value(0, VirType::Bool),
                value: VirConstant::Bool(false),
            }),
            instruction(VirInstruction::Check {
                condition: VirValueId::new(0),
            }),
        ],
        VirTerminator::Return { values: Vec::new() },
    )
}

fn unit_with_body(
    signature: VirSignature,
    instructions: Vec<SpannedVirInstruction>,
    terminator: VirTerminator,
) -> VirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "main".to_owned(),
            signature,
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions,
                terminator: SpannedVirTerminator {
                    terminator,
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn with_prove_and_trust(mut unit: VirUnit) -> VirUnit {
    let term_base = unit.specs.terms().len() as u32;
    let clause_base = unit.specs.clauses().len() as u32;
    let trust = VirTrustEntryId::new(unit.specs.trust_entries().len() as u32);
    let prove = VirSpecProveId::new(unit.specs.proves().len() as u32);
    let function = VirFunctionId::new(0);
    let origin = unit
        .source_map
        .origin_at(VirLocation::FunctionEntry { function })
        .expect("function entry has an origin")
        .id;
    unit.specs.terms_mut().extend([
        VirSpecTerm {
            id: VirSpecTermId::new(term_base),
            clause: VirSpecClauseId::new(clause_base),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Bool(true),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(term_base + 1),
            clause: VirSpecClauseId::new(clause_base + 1),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Bool(true),
            origin,
        },
    ]);
    let location = VirSpecLocation::FunctionEntry { function };
    unit.specs.clauses_mut().extend([
        VirSpecClause {
            id: VirSpecClauseId::new(clause_base),
            owner: VirSpecClauseOwner::TrustEntry(trust),
            location,
            origin: VirSpecClauseOrigin::Explicit { origin },
            kind: VirSpecClauseKind::Logic {
                root: VirSpecTermId::new(term_base),
            },
        },
        VirSpecClause {
            id: VirSpecClauseId::new(clause_base + 1),
            owner: VirSpecClauseOwner::Prove(prove),
            location,
            origin: VirSpecClauseOrigin::Explicit { origin },
            kind: VirSpecClauseKind::Logic {
                root: VirSpecTermId::new(term_base + 1),
            },
        },
    ]);
    unit.specs.trust_entries_mut().push(VirTrustEntry {
        id: trust,
        scope: VirTrustScope::FunctionEntry { function },
        policy: VirTrustPolicyKind::EntryPointAssumption,
        clause: VirSpecClauseId::new(clause_base),
        origin,
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: prove,
        function,
        location,
        clause: VirSpecClauseId::new(clause_base + 1),
        origin,
    });
    unit
}

fn execute_assembly(name: &str, assembly: &str) -> ExitStatus {
    let artifact = NativeArtifact::create(name);
    X86_64SystemToolchain::default()
        .build_executable(assembly, artifact.executable())
        .expect("system tools build non-interference fixture");
    Command::new(artifact.executable())
        .status()
        .expect("native non-interference fixture starts")
}

fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

const fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("fixture span")
}

struct NativeArtifact {
    directory: PathBuf,
    executable: PathBuf,
}

impl NativeArtifact {
    fn create(name: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nonce = NEXT.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "nera-ghost-non-interference-{}-{nonce}-{name}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).expect("create native fixture directory");
        let executable = directory.join("program");
        Self {
            directory,
            executable,
        }
    }

    fn executable(&self) -> &Path {
        &self.executable
    }
}

impl Drop for NativeArtifact {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.executable);
        let _ = std::fs::remove_dir(&self.directory);
    }
}
