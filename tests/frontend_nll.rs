use nera::backend::X86_64_UNKNOWN_LINUX_GNU;
use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirInstruction, VirLoanId, VirRuntimeValue,
    analyze, interpret, verify_program,
};

fn accepted(name: &str, source: &str) -> nera::FrontendOutput {
    let output = analyze(&SourceFile::from_text(name, source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:?}",
        output.issues()
    );
    output
}

#[test]
fn last_use_ends_shared_aliases_before_later_owner_access() {
    let source = "fn main() -> u64 {
        let mut value = 1;
        let borrowed = &value;
        let alias = borrowed;
        let first = *borrowed;
        let second = *alias;
        value = 40;
        return first + second + value;
    }";
    let output = accepted("nll-shared-alias.nera", source);
    let instructions = &output
        .vir()
        .expect("NLL source has VIR")
        .runtime()
        .functions[0]
        .blocks[0]
        .instructions;
    let end_positions = instructions
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| match instruction.instruction {
            VirInstruction::LoanEnd { effect } if effect.loan == VirLoanId::new(0) => Some(index),
            _ => None,
        })
        .collect::<Vec<_>>();
    let owner_store = instructions
        .iter()
        .enumerate()
        .rfind(|(_, instruction)| matches!(instruction.instruction, VirInstruction::Store { .. }))
        .map(|(index, _)| index)
        .expect("owner update is a Store");
    assert_eq!(end_positions.len(), 2);
    assert!(end_positions.iter().all(|end| *end < owner_store));

    let resolved = output
        .vir()
        .expect("NLL source has VIR")
        .resolve()
        .expect("NLL VIR resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("NLL verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("NLL source executes")
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn child_last_use_restores_parent_without_a_nested_scope() {
    let output = accepted(
        "nll-reborrow.nera",
        "fn main() -> u64 {
            let mut value = 1;
            let parent = &mut value;
            let child = &mut *parent;
            *child = 7;
            *parent = 9;
            return *parent;
        }",
    );
    let vir = output.vir().expect("NLL reborrow has VIR");
    let instructions = &vir.runtime().functions[0].blocks[0].instructions;
    let child_end = instructions
        .iter()
        .position(|instruction| {
            matches!(
                instruction.instruction,
                VirInstruction::LoanEnd { effect } if effect.loan == VirLoanId::new(1)
            )
        })
        .expect("child has an end");
    let parent_store = instructions
        .iter()
        .enumerate()
        .filter(|(_, instruction)| matches!(instruction.instruction, VirInstruction::Store { .. }))
        .nth(1)
        .map(|(index, _)| index)
        .expect("parent write follows the child write");
    assert!(child_end < parent_store);

    let resolved = vir.resolve().expect("NLL reborrow resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("NLL reborrow verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("NLL reborrow executes")
            .values(),
        [VirRuntimeValue::U64(9)]
    );
}

#[test]
fn unused_borrow_ends_immediately_and_full_fixture_reaches_native() {
    let unused = accepted(
        "nll-unused.nera",
        "fn main() -> u64 {
            let mut value = 1;
            let borrowed = &value;
            value = 2;
            return value;
        }",
    );
    let resolved = unused
        .vir()
        .expect("unused borrow has VIR")
        .resolve()
        .expect("unused-borrow VIR resolves");
    let unused_instructions = &resolved.runtime().functions[0].blocks[0].instructions;
    let begin = unused_instructions
        .iter()
        .position(|instruction| matches!(instruction.instruction, VirInstruction::LoanBegin { .. }))
        .expect("unused borrow begins");
    let end = unused_instructions
        .iter()
        .position(|instruction| matches!(instruction.instruction, VirInstruction::LoanEnd { .. }))
        .expect("unused borrow ends");
    assert_eq!(end, begin + 1, "unused authority ends after its definition");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("unused-borrow verification converges")
            .is_memory_checked_core0()
    );

    let fixture = analyze(&SourceFile::new(
        "local-nll.nera",
        include_bytes!("../spec/cases/verify/local-nll.nera"),
    ));
    assert_eq!(fixture.status(), FrontendStatus::AcceptedProposal);
    let resolved = fixture
        .vir()
        .expect("checked-in NLL fixture has VIR")
        .resolve()
        .expect("checked-in NLL fixture resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("checked-in NLL fixture verifies")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("checked-in NLL fixture executes")
            .values(),
        [VirRuntimeValue::U64(44)]
    );
    X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("verified NLL fixture reaches native planning");

    let repeated = analyze(&SourceFile::new(
        "local-nll.nera",
        include_bytes!("../spec/cases/verify/local-nll.nera"),
    ));
    assert_eq!(
        fixture.vir().expect("first NLL VIR").stable_dump(),
        repeated.vir().expect("repeated NLL VIR").stable_dump(),
        "NLL placement and source-map identity are deterministic"
    );
}

#[test]
fn reference_return_escape_remains_fail_closed() {
    let source = "fn expose() -> &u64 {
        let value = 1;
        return &value;
    }
    fn main() -> u64 { return 0; }";
    let output = analyze(&SourceFile::from_text("nll-result-gated.nera", source));
    assert_eq!(output.status(), FrontendStatus::Invalid);
    assert!(
        output
            .issues()
            .iter()
            .any(|issue| issue.diagnostic().message().contains("local storage"))
    );
    assert!(output.vir().is_none());
}
