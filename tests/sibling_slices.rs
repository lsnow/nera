#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, LoanActivity, ValidatedVirUnit, VirFunctionId, VirInstruction, VirLoanId,
    analyze_function_cfg, interpret, verify_program,
};

const SOURCE: &str = include_str!("../spec/cases/verify/sibling-slices.nera");
const PARAMETERS: &str = include_str!("../spec/cases/verify/sibling-parameters.nera");

fn unit(source: &str) -> ValidatedVirUnit {
    frontend_checks::accepted("sibling-slices.nera", source)
        .vir()
        .unwrap()
        .clone()
}

fn checked(unit: &ValidatedVirUnit) -> bool {
    verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default())
        .unwrap()
        .is_memory_checked_core0()
}

fn revalidate(mut raw: nera::VirUnit, source: &str) -> ValidatedVirUnit {
    raw.rebuild_source_map_from_runtime("edited-siblings.nera", source.len());
    raw.borrows = nera::VirBorrowEnvironment::from_tables(
        raw.borrows
            .regions()
            .iter()
            .cloned()
            .map(|mut r| {
                r.source_origin = nera::VirOriginId::new(0);
                r
            })
            .collect(),
        raw.borrows
            .constraints()
            .iter()
            .copied()
            .map(|mut c| {
                c.source_origin = nera::VirOriginId::new(0);
                c
            })
            .collect(),
    );
    raw.into_validated().unwrap()
}

#[test]
fn malformed_sibling_end_sequences_fail_in_verifier_and_interpreter() {
    const LOCAL: &str = "fn main() -> u64 { let mut a=[20,22]; let p=&mut a[..];
        let l=&mut p[..1]; let r=&mut p[1..]; return l[0]+r[0]; }";
    for mode in 0..3 {
        let mut raw = unit(LOCAL).as_unit().clone();
        let instructions = &mut raw.runtime.functions[0].blocks[0].instructions;
        let child = instructions.iter().position(|i| matches!(i.instruction, VirInstruction::LoanEnd { effect } if effect.loan == VirLoanId::new(1))).unwrap();
        match mode {
            0 => {
                instructions.remove(child);
            }
            1 => {
                instructions.insert(child + 1, instructions[child].clone());
            }
            _ => {
                let parent = instructions.iter().position(|i| matches!(i.instruction, VirInstruction::LoanEnd { effect } if effect.loan == VirLoanId::new(0))).unwrap();
                let end = instructions.remove(parent);
                instructions.insert(child, end);
            }
        }
        let bad = revalidate(raw, LOCAL);
        assert!(!checked(&bad));
        let error = interpret(bad.resolve().unwrap().runtime()).unwrap_err();
        assert!(
            matches!(
                error.kind(),
                nera::VirExecutionErrorKind::LoanInactive { .. }
                    | nera::VirExecutionErrorKind::LoanHasActiveChild { .. }
                    | nera::VirExecutionErrorKind::PermissionAlreadyConsumed { .. }
            ),
            "{:?}",
            error.kind()
        );
    }
}

#[test]
fn authority_reborrow_schema_rejects_bad_identity_region_types_and_origin() {
    for mode in 0..5 {
        let mut raw = unit(PARAMETERS).as_unit().clone();
        let mut found = false;
        for instruction in raw.runtime.functions[1]
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
        {
            if let VirInstruction::LoanReborrowAuthority {
                loan,
                region,
                effect,
                permission_result,
                ..
            } = &mut instruction.instruction
            {
                match mode {
                    0 => *loan = VirLoanId::new(5),
                    1 => *region = nera::VirBorrowRegionId::new(u32::MAX),
                    2 => permission_result.ty = nera::VirType::U64,
                    3 => effect.origin = nera::VirOriginId::new(u32::MAX),
                    _ => effect.reference.layout = nera::VirLayoutId::new(u32::MAX),
                }
                found = true;
                break;
            }
        }
        assert!(found);
        assert!(raw.into_validated().is_err(), "mutation {mode}");
    }
}

#[test]
fn authority_reborrow_checks_actual_region_inclusion_and_mutability() {
    let mut raw = unit(PARAMETERS).as_unit().clone();
    // Removing the parent's inclusion edge leaves well-typed VIR but no
    // proof that the actual authority's region contains this child region.
    raw.borrows = nera::VirBorrowEnvironment::from_tables(raw.borrows.regions().to_vec(), vec![]);
    let bad = raw.into_validated().unwrap();
    assert!(!checked(&bad));
    assert!(matches!(
        interpret(bad.resolve().unwrap().runtime())
            .unwrap_err()
            .kind(),
        nera::VirExecutionErrorKind::LoanParentMismatch { .. }
    ));
    let source = PARAMETERS.replace("parent: &mut [u64]", "parent: &[u64]");
    assert_eq!(
        nera::analyze(&nera::SourceFile::from_text("upgrade.nera", &source)).status(),
        nera::FrontendStatus::Invalid
    );
}

#[test]
fn empty_children_can_really_coexist_without_nll_hiding_their_lifetimes() {
    for mid in [0, 4] {
        let source = format!(
            "fn main() -> u64 {{ let mut a=[1,2,3,4]; let p=&mut a[..];
            let l=&mut p[..{mid}]; let r=&mut p[{mid}..]; return 42; }}"
        );
        let mut raw = unit(&source).as_unit().clone();
        let instructions = &mut raw.runtime.functions[0].blocks[0].instructions;
        let mut ends = vec![];
        instructions.retain(|i| {
            if matches!(i.instruction, VirInstruction::LoanEnd { .. }) {
                ends.push(i.clone());
                false
            } else {
                true
            }
        });
        // Keep all canonical ends, but force both child creations before any
        // end. No pointer/value/permission is fabricated by this mutation.
        let last = instructions
            .iter()
            .rposition(|i| matches!(i.instruction, VirInstruction::LoanReborrow { .. }))
            .unwrap();
        instructions.splice(last + 1..last + 1, ends);
        let validated = revalidate(raw, &source);
        assert!(checked(&validated));
        assert_eq!(
            interpret(validated.resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [nera::VirRuntimeValue::U64(42)]
        );
        let analysis =
            analyze_function_cfg(&validated.resolve().unwrap(), VirFunctionId::new(0)).unwrap();
        assert!(
            analysis
                .block(nera::VirBlockId::new(0))
                .unwrap()
                .instruction_states()
                .iter()
                .any(|s| s
                    .loan(VirLoanId::new(0))
                    .is_some_and(|l| l.activity() == LoanActivity::Suspended)
                    && s.loans()
                        .values()
                        .filter(|l| l.activity() == LoanActivity::Active)
                        .count()
                        == 2)
        );
    }
}

#[test]
fn sibling_budget_exhaustion_and_branch_cleanup_remain_conservative() {
    let validated = unit(SOURCE);
    for config in [
        CfgAnalysisConfig {
            max_active_loans_per_case: 2,
            ..CfgAnalysisConfig::default()
        },
        CfgAnalysisConfig {
            max_region_constraints_per_function: 0,
            ..CfgAnalysisConfig::default()
        },
        CfgAnalysisConfig {
            max_reborrow_depth: 0,
            ..CfgAnalysisConfig::default()
        },
    ] {
        let result = verify_program(&validated.resolve().unwrap(), config).unwrap();
        assert!(!result.is_memory_checked_core0());
    }
    for flag in ["true", "false"] {
        let source = format!(
            "fn main() -> u64 {{ return edit({flag}); }}
            fn edit(flag: bool) -> u64 {{ let mut a=[20,22]; let p=&mut a[..];
            if flag {{ let l=&mut p[..1]; let r=&mut p[1..]; let sum=l[0]+r[0]; }}
            p[0]=42; return p[0]; }}"
        );
        frontend_checks::checked("branch-cleanup.nera", &source, 42);
    }
}

#[test]
fn dynamic_siblings_restore_the_parent_after_both_end() {
    frontend_checks::checked("sibling-slices.nera", SOURCE, 42);
    let unit = unit(SOURCE);
    let analysis = analyze_function_cfg(&unit.resolve().unwrap(), VirFunctionId::new(1)).unwrap();
    let states = unit.runtime().functions[1]
        .blocks
        .iter()
        .flat_map(|b| analysis.block(b.id).unwrap().instruction_states());
    let mut both = false;
    let mut one = false;
    let mut restored = false;
    for state in states {
        let Some(parent) = state.loan(VirLoanId::new(0)) else {
            continue;
        };
        let children = state
            .loans()
            .values()
            .filter(|l| l.parent() == Some(VirLoanId::new(0)))
            .collect::<Vec<_>>();
        if children.len() != 2 {
            continue;
        }
        let active = children
            .iter()
            .filter(|l| l.activity() == LoanActivity::Active)
            .count();
        let ended = children
            .iter()
            .filter(|l| l.activity() == LoanActivity::Ended)
            .count();
        if active == 2 {
            assert_eq!(parent.activity(), LoanActivity::Suspended);
            both = true;
        }
        if active == 1 && ended == 1 {
            assert_eq!(parent.activity(), LoanActivity::Suspended);
            one = true;
        }
        if ended == 2 && parent.activity() == LoanActivity::Active {
            restored = true;
        }
    }
    assert!(
        both && one && restored,
        "must observe simultaneous children, partial end and full restoration"
    );
}

#[test]
fn parameter_subslice_uses_actual_authority_parent() {
    frontend_checks::checked(
        "parameter-subslice.nera",
        "fn main() -> u64 { let a=[42,1,2]; return prefix(&a[..],2usize); }
    fn prefix(view: &[u64], end: usize) -> u64 {
        if end > 0usize { if end <= len(view) { let part=&view[..end]; return part[0]; } } return 0;
    }",
        42,
    );
}

#[test]
fn mutable_parameter_creates_children_from_actual_authority() {
    frontend_checks::checked("parameter-siblings.nera", PARAMETERS, 42);
    let nested = PARAMETERS.replace("left[0] = 12;", "let nested=&mut left[..1]; nested[0]=12;");
    frontend_checks::checked("parameter-nested.nera", &nested, 42);
    assert!(
        unit(PARAMETERS)
            .runtime()
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i.instruction, VirInstruction::LoanReborrowAuthority { .. }))
    );
}

#[test]
fn owner_splits_and_empty_endpoint_children_keep_authority_without_element_access() {
    let owner = SOURCE
        .replace("let parent = &mut values[..];", "")
        .replace("parent", "values");
    frontend_checks::checked("owner-splits.nera", &owner, 42);
    for mid in 0..=4 {
        let source = format!(
            "fn main() -> u64 {{ return split({mid}usize); }}
            fn split(mid: usize) -> u64 {{ let mut a=[1,2,3,4];
            if mid <= len(a) {{ let parent=&mut a[..]; let left=&mut parent[..mid];
            let right=&mut parent[mid..]; let size=len(left)+len(right);
            parent[0]=42; return parent[0]; }} return 0; }}"
        );
        frontend_checks::checked("endpoint.nera", &source, 42);
    }
}

#[test]
fn three_children_nested_children_and_shared_aliases_restore_in_either_order() {
    for uses in ["let sum=a[0]+b[0]+c[0];", "let sum=c[0]+b[0]+a[0];"] {
        let source = format!(
            "fn main() -> u64 {{ let mut v=[10,20,30,40]; let parent=&mut v[..];
            let a=&mut parent[..1]; let b=&mut parent[1..2]; let c=&mut parent[2..];
            let nested=&mut c[..1]; nested[0]=12; {uses} parent[0]=sum; return parent[0]; }}"
        );
        frontend_checks::checked("three-nested.nera", &source, 42);
    }
    frontend_checks::checked(
        "shared-alias.nera",
        "fn main() -> u64 { let mut v=[20,22];
        let parent=&mut v[..]; let left=&parent[..1]; let alias=left; let right=&mut parent[1..];
        right[0]=22; let sum=alias[0]+right[0]; parent[0]=sum; return parent[0]; }",
        42,
    );
}

#[test]
fn overlap_missing_bounds_and_suspended_parent_access_fail_closed() {
    let cases = [
        SOURCE.replace("&mut parent[mid..]", "&mut parent[..mid]"),
        SOURCE.replace("if mid < len(values)", "if true"),
        SOURCE.replace("left[0] = 12;", "parent[0] = 12;"),
        SOURCE.replace(
            "let sum = left[0] + right[0];",
            "let first=left[0]; parent[0]=first; let sum=first+right[0];",
        ),
    ];
    for source in &cases {
        assert!(!checked(&unit(source)), "{source}");
    }
    for index in [0, 2, 3] {
        let bad = unit(&cases[index]);
        let error = interpret(bad.resolve().unwrap().runtime()).unwrap_err();
        assert!(
            matches!(
                error.kind(),
                nera::VirExecutionErrorKind::LoanConflict { .. }
                    | nera::VirExecutionErrorKind::LoanInactive { .. }
                    | nera::VirExecutionErrorKind::LoanAccessConflict { .. }
            ),
            "{error:?}"
        );
    }
    let out = cases[1].replace("split(2usize)", "split(5usize)");
    assert!(interpret(unit(&out).resolve().unwrap().runtime()).is_err());
}
