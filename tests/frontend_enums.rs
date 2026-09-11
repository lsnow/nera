use nera::{
    CfgAnalysisConfig, FrontendIssueKind, FrontendStatus, HirPatternKind, HirTypeKind, SourceFile,
    VirInstruction, VirRuntimeValue, analyze, interpret, verify_program,
};

fn analyze_text(name: &str, source: &str) -> nera::FrontendOutput {
    analyze(&SourceFile::from_text(name, source))
}

#[test]
fn enum_constructor_match_and_payload_bindings_reach_all_consumers() {
    let source = include_str!("../spec/cases/aggregate/enum-surface.nera");
    let output = analyze_text("enum-surface.nera", source);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "issues: {:?}",
        output.issues()
    );

    let ast = output.ast().expect("enum source has AST");
    assert_eq!(ast.enums().len(), 1);
    assert_eq!(ast.enums()[0].variants.len(), 3);

    let hir = output.hir().expect("enum source has HIR");
    let message = hir
        .types()
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Message"))
        .expect("Message type exists");
    let HirTypeKind::Enum { variants } = &message.kind else {
        panic!("Message is not an enum");
    };
    assert_eq!(variants.len(), 3);
    let layout = hir.layout_of(message.id).expect("Message has a layout");
    let variant_layout = layout
        .variants
        .as_ref()
        .expect("Message has variant layout");
    assert_eq!(variant_layout.tag_size_bytes, 1);
    assert_eq!(variant_layout.cases.len(), 3);
    assert_eq!(variant_layout.cases[2].payload_offset_bytes, 8);
    let function = hir.entry_function();
    let body = function.body().expect("entry function has a body");
    let match_statement = body
        .root
        .statements
        .iter()
        .find_map(|statement| match &statement.kind {
            nera::HirStatementKind::Match { arms, .. } => Some(arms),
            _ => None,
        })
        .expect("enum match remains structured in HIR");
    assert!(matches!(
        match_statement[2].pattern.kind,
        HirPatternKind::Variant { .. }
    ));

    let vir = output.vir().expect("enum source has VIR");
    let calls = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.instruction {
            VirInstruction::Call { target, .. } => Some(target.symbol.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls, ["right_value", "left_value"]);
    assert!(
        vir.runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(
                instruction.instruction,
                VirInstruction::EnumDiscriminant { .. }
            ))
    );
    let resolved = vir.resolve().expect("enum VIR resolves");
    let verification =
        verify_program(&resolved, CfgAnalysisConfig::default()).expect("enum VIR verifies");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("enum source executes")
            .values(),
        [VirRuntimeValue::U64(9)]
    );
    assert_eq!(
        analyze_text("enum-surface.nera", source)
            .vir()
            .expect("repeated enum lowering has VIR")
            .stable_dump(),
        vir.stable_dump()
    );
}

#[test]
fn enum_surface_errors_fail_closed() {
    let cases = [
        (
            "wrong-shape.nera",
            "enum Option { None, Some(u64), }
             fn main() -> u64 {
                 let value = Option::Some { value: 1 };
                 return 0;
             }",
        ),
        (
            "missing-arm.nera",
            "enum Option { None, Some(u64), }
             fn main() -> u64 {
                 let value = Option::None;
                 match value {
                     Option::None => { return 0; },
                 }
             }",
        ),
        (
            "wrong-owner.nera",
            "enum Left { A, }
             enum Right { A, }
             fn main() -> u64 {
                 let value = Left::A;
                 match value {
                     Right::A => { return 0; },
                 }
             }",
        ),
    ];
    for (name, source) in cases {
        let output = analyze_text(name, source);
        assert_ne!(output.status(), FrontendStatus::AcceptedProposal, "{name}");
        assert!(
            output.issues().iter().any(|issue| matches!(
                issue.kind(),
                FrontendIssueKind::Elaboration | FrontendIssueKind::Unsupported
            )),
            "{name}: {:?}",
            output.issues()
        );
    }
}

#[test]
fn trivial_variant_switch_retires_the_old_payload() {
    let source = include_str!("../spec/cases/aggregate/enum-switch.nera");
    let output = analyze_text("enum-switch.nera", source);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "issues: {:?}",
        output.issues()
    );
    let vir = output.vir().expect("variant switch has VIR");
    let resolved = vir.resolve().expect("variant switch VIR resolves");
    let verification =
        verify_program(&resolved, CfgAnalysisConfig::default()).expect("variant switch verifies");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("variant switch executes")
            .values(),
        [VirRuntimeValue::U64(13)]
    );
}

#[test]
fn aggregate_payload_binding_uses_a_typed_object_copy() {
    let output = analyze_text(
        "enum-aggregate-binding.nera",
        "enum Wrapped {
             Empty,
             Pair((u64, u64)),
         }
         fn main() -> u64 {
             let wrapped = Wrapped::Pair((3, 8));
             match wrapped {
                 Wrapped::Empty => { return 0; },
                 Wrapped::Pair(pair) => { return pair.0 + pair.1; },
             }
         }",
    );
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "issues: {:?}",
        output.issues()
    );
    let vir = output.vir().expect("aggregate binding has VIR");
    assert!(
        vir.runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(
                instruction.instruction,
                VirInstruction::ObjectTransfer { .. }
            ))
    );
    let resolved = vir.resolve().expect("aggregate binding resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("aggregate binding verifies")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("aggregate binding executes")
            .values(),
        [VirRuntimeValue::U64(11)]
    );
}
