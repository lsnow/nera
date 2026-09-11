#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, LoanActivity, ResourceObligationKind, VirFunctionId, VirInstruction,
    VirRuntimeValue, analyze_function_cfg, interpret, verify_program,
};

const SOURCE: &str = include_str!("../spec/cases/verify/disjoint-elements.nera");

fn unit(source: &str) -> nera::ValidatedVirUnit {
    frontend_checks::accepted("disjoint-elements.nera", source)
        .vir()
        .unwrap()
        .clone()
}

fn rejected(source: &str) -> nera::ValidatedVirUnit {
    let unit = unit(source);
    let result = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(
        result
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| {
                !o.obligation().status().is_proven()
                    && matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::LoanCompatible { .. }
                            | ResourceObligationKind::IndexWithinBounds { .. }
                            | ResourceObligationKind::LoanParentActive { .. }
                    )
            })
    );
    unit
}

#[test]
fn two_live_dynamic_element_loans_can_both_be_used() {
    frontend_checks::checked("disjoint-elements.nera", SOURCE, 42);
    let unit = unit(SOURCE);
    let resolved = unit.resolve().unwrap();
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(1)).unwrap();
    let mut simultaneous_write = false;
    for block in &unit.runtime().functions[1].blocks {
        for (instruction, state) in block
            .instructions
            .iter()
            .zip(analysis.block(block.id).unwrap().instruction_states())
        {
            if matches!(
                instruction.instruction,
                VirInstruction::Write { .. } | VirInstruction::Store { .. }
            ) {
                let active = state
                    .loans()
                    .values()
                    .filter(|l| l.activity() == LoanActivity::Active)
                    .collect::<Vec<_>>();
                if active.len() == 2 {
                    assert!(active[0].range().overlaps(active[1].range()));
                    assert_ne!(active[0].actual_range(), active[1].actual_range());
                    simultaneous_write = true;
                }
            }
        }
    }
    assert!(
        simultaneous_write,
        "NLL must not hide the overlapping lifetimes"
    );
    assert!(analysis.returns().iter().all(|r| {
        r.state()
            .loans()
            .values()
            .all(|l| l.activity() == LoanActivity::Ended)
    }));
    for i in 0..4 {
        for j in 0..4 {
            let source = SOURCE.replace(
                "update(0usize, 2usize)",
                &format!("update({i}usize, {j}usize)"),
            );
            let unit = self::unit(&source);
            assert_eq!(
                interpret(unit.resolve().unwrap().runtime())
                    .unwrap()
                    .values(),
                [VirRuntimeValue::U64(if i == j { 0 } else { 42 })]
            );
        }
    }
}

#[test]
fn disjoint_owner_access_and_early_cleanup_compose() {
    let source = SOURCE.replace(
        "let right = &mut values[j];\n                *left = 12;\n                *right = 30;\n                return *left + *right;",
        "values[j] = 30; *left = 12; return *left + values[j];",
    );
    assert_ne!(source, SOURCE);
    frontend_checks::checked("owner-access.nera", &source, 42);
    // Both aliases are consumed before the conditional return so losing old
    // index roots across CFG is not mistaken for retaining arbitrary footprints.
    let early = SOURCE.replace(
        "return *left + *right;",
        "let sum = *left + *right; if sum == 42 { return sum; } return 1;",
    );
    frontend_checks::checked("early-exit.nera", &early, 42);
    let shared = SOURCE
        .replace("&mut values", "&values")
        .replace("if i != j", "if true")
        .replace("*left = 12;", "")
        .replace("*right = 30;", "");
    frontend_checks::checked("shared-unknown-overlap.nera", &shared, 40);
}

#[test]
fn missing_or_wrong_guards_and_overlapping_owner_access_fail_closed() {
    for source in [
        SOURCE.replace("if i != j", "if true"),
        SOURCE.replace("if i != j", "if i == j"),
        SOURCE.replace("if j < len(values)", "if true"),
        SOURCE.replace("if i != j {", "if i != j { let unused=0; } {"),
        SOURCE.replace("*left = 12;", "values[i] = 12;"),
    ] {
        rejected(&source);
    }
    let same = SOURCE
        .replace("if i != j", "if true")
        .replace("update(0usize, 2usize)", "update(1usize, 1usize)");
    let bad = rejected(&same);
    assert!(matches!(
        interpret(bad.resolve().unwrap().runtime())
            .unwrap_err()
            .kind(),
        nera::VirExecutionErrorKind::LoanConflict { .. }
    ));
}

#[test]
fn mutable_parent_siblings_use_the_same_numeric_disjointness() {
    let source = SOURCE
        .replace(
            "let left = &mut values[i];",
            "let parent=&mut values; let left=&mut parent[i];",
        )
        .replace("let right = &mut values[j];", "let right=&mut parent[j];");
    frontend_checks::checked("element-siblings.nera", &source, 42);
}

#[test]
fn exhausted_relation_budgets_never_create_two_active_authorities() {
    use nera::verifier::relation::difference::DifferenceLimits;
    let unit = unit(SOURCE);
    let resolved = unit.resolve().unwrap();
    for limits in [
        DifferenceLimits {
            max_branches: 1,
            ..DifferenceLimits::default()
        },
        DifferenceLimits {
            max_steps: 0,
            ..DifferenceLimits::default()
        },
        DifferenceLimits {
            max_variables: 0,
            ..DifferenceLimits::default()
        },
    ] {
        let config = CfgAnalysisConfig {
            relation_limits: limits,
            ..CfgAnalysisConfig::default()
        };
        let result = verify_program(&resolved, config).unwrap();
        assert!(!result.is_memory_checked_core0());
        let analysis =
            nera::analyze_function_cfg_with_config(&resolved, VirFunctionId::new(1), config)
                .unwrap();
        assert!(unit.runtime().functions[1].blocks.iter().all(|b| {
            analysis
                .block(b.id)
                .unwrap()
                .instruction_states()
                .iter()
                .all(|s| {
                    s.loans()
                        .values()
                        .filter(|l| l.activity() == LoanActivity::Active)
                        .count()
                        < 2
                })
        }));
    }
}

#[test]
fn object_transfer_uses_the_same_disjointness_and_replays_its_evidence() {
    let mut unit = unit(SOURCE).as_unit().clone();
    let instructions = unit.runtime.functions[1]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.instructions);
    let mut left = None;
    let mut mutated = 0;
    let mut begins = 0;
    for spanned in instructions {
        if matches!(spanned.instruction, VirInstruction::LoanBegin { .. }) {
            begins += 1;
        }
        if begins < 2 {
            continue;
        }
        if let VirInstruction::Write {
            pointer,
            permission,
            access,
            ..
        }
        | VirInstruction::Store {
            pointer,
            permission,
            access,
            ..
        } = spanned.instruction
        {
            if let Some((source, source_permission)) = left {
                spanned.instruction = VirInstruction::ObjectTransfer {
                    destination: pointer,
                    destination_permission: permission,
                    source,
                    source_permission,
                    access,
                    destination_mode: nera::VirObjectDestinationMode::Replace,
                    source_mode: nera::VirObjectSourceMode::Copy,
                };
                mutated += 1;
                break;
            }
            left = Some((pointer, permission));
        }
    }
    assert_eq!(mutated, 1);
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let result = verify_program(&resolved, config).unwrap();
    assert!(
        result.is_memory_checked_core0(),
        "{:#?}",
        result.diagnostics()
    );
    let evidence = result
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_evidence())
        .find(|e| {
            e.disjoint
                .as_ref()
                .is_some_and(|d| d.index_separation.is_some())
        })
        .unwrap();
    assert!(
        nera::verifier::relation::replay_relation_evidence(&resolved, config, evidence).unwrap()
    );
    let mut forged = evidence.clone();
    forged.disjoint.as_mut().unwrap().index_separation = None;
    assert!(
        !nera::verifier::relation::replay_relation_evidence(&resolved, config, &forged).unwrap()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(24)]
    );
}
