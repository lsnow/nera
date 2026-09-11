#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, LoanActivity, ResourceObligationKind, VirFunctionId, VirInstruction,
    VirLoanId, VirRuntimeValue, analyze_function_cfg, interpret, verify_program,
};

const SOURCE: &str = include_str!("../spec/cases/verify/strided-regions.nera");
const CHUNKS: &str = include_str!("../spec/cases/verify/strided-chunks.nera");

#[test]
fn three_live_two_dimensional_elements_use_both_row_and_column_relations() {
    frontend_checks::checked("strided-regions.nera", SOURCE, 42);
    let unit = frontend_checks::accepted("strided-regions.nera", SOURCE)
        .vir()
        .unwrap()
        .clone();
    let resolved = unit.resolve().unwrap();
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(1)).unwrap();
    assert!(unit.runtime().functions[1].blocks.iter().any(|b| {
        analysis
            .block(b.id)
            .unwrap()
            .instruction_states()
            .iter()
            .any(|s| {
                s.loans()
                    .values()
                    .filter(|l| l.activity() == LoanActivity::Active)
                    .count()
                    == 3
            })
    }));
    // Independent concrete grid of row/column selections, including both
    // directions and excluded equal-index branches; no argument specialization.
    for row in 0..3 {
        for other in 0..3 {
            for col in 0..4 {
                for next in 0..4 {
                    let source = SOURCE.replace(
                        "edit(0usize, 1usize, 1usize, 2usize)",
                        &format!("edit({row}usize, {other}usize, {col}usize, {next}usize)"),
                    );
                    let out = frontend_checks::accepted("grid.nera", &source);
                    assert_eq!(
                        interpret(out.vir().unwrap().resolve().unwrap().runtime())
                            .unwrap()
                            .values(),
                        [VirRuntimeValue::U64(if row == other || col == next {
                            0
                        } else {
                            42
                        })]
                    );
                }
            }
        }
    }
}

#[test]
fn three_dynamic_partitions_and_fixed_width_chunks() {
    frontend_checks::checked("empty-row-chunk.nera", "fn main()->u64 { return edit(1usize,1usize); }
        fn edit(row:usize,col:usize)->u64 { let mut a=[[1,2],[3,4]];
        if row<2usize { if col<2usize { let empty=&mut a[row][col..col];
        let cell=&mut a[row][col]; let nested=&mut empty[..]; *cell=42; return *cell; }} return 0; }",42);
    frontend_checks::checked("strided-chunks.nera", CHUNKS, 42);
    frontend_checks::checked(
        "three-partitions.nera",
        "fn main() -> u64 { return edit(1usize,3usize); }
        fn edit(i:usize,j:usize)->u64 { let mut a=[10,20,30,40];
        if i>0usize { if i<j { if j<len(a) { let p=&mut a[..];
        let x=&mut p[..i]; let y=&mut p[i..j]; let z=&mut p[j..];
        x[0]=10; y[0]=12; z[0]=20; return x[0]+y[0]+z[0]; }}} return 0; }",
        42,
    );
    let chunks = "fn main()->u64 { return edit(0usize,2usize); }
        fn edit(i:usize,j:usize)->u64 { let mut a=[10,20,30,40,50,60];
        if i<=4usize { if j<=4usize { let end=i+2usize; let other=j+2usize; if end<=j {
        let l=&mut a[i..end]; let r=&mut a[j..other];
        l[1]=12; r[1]=30; return l[1]+r[1]; }}} return 0; }";
    frontend_checks::checked("chunks.nera", chunks, 42);
    let inline = chunks
        .replace(
            "let end=i+2usize; let other=j+2usize; if end<=j",
            "if i+2usize<=j",
        )
        .replace("i..end", "i..i+2usize")
        .replace("j..other", "j..j+2usize");
    frontend_checks::checked("inline-chunks.nera", &inline, 42);
}

#[test]
fn nested_field_layout_offsets_do_not_change_two_dimensional_disjointness() {
    let source = format!(
        "struct Grid {{ flag:bool, cells:[[u64;4];3], }} {}",
        SOURCE
            .replace("let mut a = [[", "let mut grid=Grid { flag:true, cells:[[")
            .replace("[12, 22, 32, 42]];", "[12, 22, 32, 42]] };")
            .replace("len(a)", "len(grid.cells)")
            .replace("a[row]", "grid.cells[row]")
            .replace("a[other]", "grid.cells[other]")
    );
    frontend_checks::checked("nested-field-grid.nera", &source, 42);
}

#[test]
fn missing_bounds_overlap_and_uninitialized_regions_are_not_promoted() {
    // Different starts alone do not separate two-element chunks.
    let overlapping = CHUNKS
        .replace("i + 2usize <= j", "i < j")
        .replace("edit(0usize, 2usize)", "edit(0usize, 1usize)");
    let out = frontend_checks::accepted("overlapping-chunks.nera", &overlapping);
    let resolved = out.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(matches!(
        interpret(resolved.runtime()).unwrap_err().kind(),
        nera::VirExecutionErrorKind::LoanConflict { .. }
    ));
    for (before, after) in [
        ("if row != other", "if true"),
        ("if col != next", "if true"),
        ("if col < 4usize", "if true"),
        ("if other < len(a)", "if true"),
        (
            "let mut a = [[10, 20, 30, 40], [11, 21, 31, 41], [12, 22, 32, 42]];",
            "let mut a:[[u64;4];3];",
        ),
        ("*left = 10;", "a[row][col]=10;"),
    ] {
        let source = SOURCE.replace(before, after);
        assert_ne!(source, SOURCE);
        let out = frontend_checks::accepted("bad-grid.nera", &source);
        let result = verify_program(
            &out.vir().unwrap().resolve().unwrap(),
            CfgAnalysisConfig::default(),
        )
        .unwrap();
        assert!(!result.is_memory_checked_core0(), "{source}");
        assert!(!result.diagnostics().is_empty());
    }
    for (before, after, args) in [
        (
            "if row != other",
            "if true",
            "edit(0usize, 0usize, 1usize, 2usize)",
        ),
        (
            "if col != next",
            "if true",
            "edit(0usize, 1usize, 1usize, 1usize)",
        ),
        (
            "if col < 4usize",
            "if true",
            "edit(0usize, 1usize, 4usize, 1usize)",
        ),
        (
            "if other < len(a)",
            "if true",
            "edit(0usize, 18446744073709551615usize, 1usize, 2usize)",
        ),
    ] {
        let source = SOURCE
            .replace(before, after)
            .replace("edit(0usize, 1usize, 1usize, 2usize)", args);
        let out = frontend_checks::accepted("concrete-fault.nera", &source);
        assert!(interpret(out.vir().unwrap().resolve().unwrap().runtime()).is_err());
    }
}

#[test]
fn region_pair_budget_is_shared_and_exhaustion_never_creates_a_partial_authority() {
    let out = frontend_checks::accepted("budget.nera", SOURCE);
    let unit = out.vir().unwrap();
    let resolved = unit.resolve().unwrap();
    let config = CfgAnalysisConfig {
        max_region_pairs_per_instruction: 1,
        ..CfgAnalysisConfig::default()
    };
    assert!(
        !verify_program(&resolved, config)
            .unwrap()
            .is_memory_checked_core0()
    );
    let analysis =
        nera::analyze_function_cfg_with_config(&resolved, VirFunctionId::new(1), config).unwrap();
    assert!(analysis.obligations().iter().any(|o| matches!(
        o.obligation().kind(),
        ResourceObligationKind::LoanPairQueriesWithinBudget {
            queries: 2,
            limit: 1
        }
    ) && !o.obligation().status().is_proven()));
    assert!(unit.runtime().functions[1].blocks.iter().all(|b| {
        analysis
            .block(b.id)
            .unwrap()
            .instruction_states()
            .iter()
            .all(|s| {
                s.loan(VirLoanId::new(2))
                    .is_none_or(|l| l.activity() != LoanActivity::Active)
            })
    }));
}

#[test]
fn region_query_growth_is_bounded_by_region_count_not_array_length() {
    for length in [16, 64] {
        for count in [2, 4, 8, 12] {
            let started = std::time::Instant::now();
            let source = format!(
                "fn main()->u64 {{ let mut a=[{}]; {} return {}; }}",
                vec!["1"; length].join(","),
                (0..count)
                    .map(|i| format!("let r{i}=&mut a[{i}..{}];", i + 1))
                    .collect::<String>(),
                (0..count)
                    .map(|i| format!("r{i}[0]"))
                    .collect::<Vec<_>>()
                    .join("+")
            );
            let out = frontend_checks::accepted("scaling.nera", &source);
            let resolved = out.vir().unwrap().resolve().unwrap();
            let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
            assert!(
                result.is_memory_checked_core0(),
                "{:?}",
                result.diagnostics()
            );
            let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0)).unwrap();
            eprintln!(
                "region-growth length={length} regions={count} elapsed_us={} visits={} states={} queries={}",
                started.elapsed().as_micros(),
                analysis.block_visits(),
                analysis
                    .blocks()
                    .values()
                    .map(|b| b.entry_conditional_state().cases().len()
                        + b.instruction_conditional_states()
                            .iter()
                            .map(|s| s.cases().len())
                            .sum::<usize>())
                    .sum::<usize>(),
                analysis.relation_queries().len()
            );
            let queries = analysis
                .obligations()
                .iter()
                .filter_map(|o| match o.obligation().kind() {
                    ResourceObligationKind::LoanPairQueriesWithinBudget { queries, .. } => {
                        Some(queries)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(queries.iter().sum::<usize>(), count * (count - 1) / 2);
            assert_eq!(queries.iter().copied().max(), Some(count - 1));
            assert_eq!(out.vir().unwrap().runtime().functions[0].blocks.len(), 1);
            assert_eq!(
                analysis
                    .block(nera::VirBlockId::new(0))
                    .unwrap()
                    .instruction_states()
                    .iter()
                    .map(|s| s
                        .loans()
                        .values()
                        .filter(|l| l.activity() == LoanActivity::Active)
                        .count())
                    .max(),
                Some(count)
            );
        }
    }
}

#[test]
fn object_copy_uses_replayable_two_dimensional_band_evidence() {
    let out = frontend_checks::accepted("object-grid.nera", SOURCE);
    let mut raw = out.vir().unwrap().as_unit().clone();
    let mut first = None;
    let mut changed = false;
    for i in raw.runtime.functions[1]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.instructions)
    {
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
        } = i.instruction
        {
            // Scalar initialization precedes loans; stores through returned
            // loan references only occur in the innermost branch.
            if let Some((source, source_permission)) = first {
                i.instruction = VirInstruction::ObjectTransfer {
                    destination: pointer,
                    destination_permission: permission,
                    source,
                    source_permission,
                    access,
                    destination_mode: nera::VirObjectDestinationMode::Replace,
                    source_mode: nera::VirObjectSourceMode::Copy,
                };
                changed = true;
                break;
            }
            first = Some((pointer, permission));
        }
    }
    assert!(changed);
    let unit = raw.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let result = verify_program(&resolved, config).unwrap();
    assert!(
        result.is_memory_checked_core0(),
        "{:?}",
        result.diagnostics()
    );
    let evidence = result
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_evidence())
        .find(|e| e.disjoint.as_ref().is_some_and(|d| d.bands.is_some()))
        .unwrap();
    assert!(
        nera::verifier::relation::replay_relation_evidence(&resolved, config, evidence).unwrap()
    );
    let mut forged = evidence.clone();
    forged.disjoint.as_mut().unwrap().bands = None;
    assert!(
        !nera::verifier::relation::replay_relation_evidence(&resolved, config, &forged).unwrap()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(40)]
    );
}
