#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{CfgAnalysisConfig, ResourceObligationKind, VirInstruction, interpret, verify_program};

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("relation-composition.nera", source, expected);
}

fn revalidate(mut raw: nera::VirUnit) -> nera::ValidatedVirUnit {
    raw.rebuild_source_map_from_runtime("relation-mutation.vir", 10000);
    let origin = |function| {
        raw.source_map
            .origin_at(nera::VirLocation::FunctionEntry { function })
            .unwrap()
            .id
    };
    raw.borrows = nera::VirBorrowEnvironment::from_tables(
        raw.borrows
            .regions()
            .iter()
            .cloned()
            .map(|mut r| {
                r.source_origin = origin(r.owner);
                r
            })
            .collect(),
        raw.borrows
            .constraints()
            .iter()
            .copied()
            .map(|mut c| {
                c.source_origin = origin(c.owner);
                c
            })
            .collect(),
    );
    raw.into_validated().unwrap()
}

fn rejected(source: &str, fault: bool) {
    let out = frontend_checks::accepted("relation-composition-negative.nera", source);
    let resolved = out.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0(), "{source}");
    if fault {
        assert!(interpret(resolved.runtime()).is_err(), "{source}");
    }
}

const PREFIX: &str = "fn main()->u64 { return build(3usize,1usize); }
    fn build(n:usize,j:usize)->u64 { let mut a:[u64;4];
    if n<=4usize { for i in 0usize..n { a[i]=42; }
    if j<n { return a[j]; }} return 0; }";

#[test]
fn dynamic_read_and_view_are_contained_in_the_constructed_prefix() {
    checked(PREFIX, 42);
    checked(
        &PREFIX.replace("return a[j];", "let r=&a[j]; return *r;"),
        42,
    );
    checked(
        &PREFIX.replace("return a[j];", "let r=&a[..n]; return r[j];"),
        42,
    );
    checked(
        &PREFIX.replace("return a[j];", "let r=&mut a[j..n]; r[0]=42; return r[0];"),
        42,
    );
}

#[test]
fn loop_chunks_cleanup_on_continue_break_and_return() {
    for control in ["continue;", "break;", "return left[0];", ""] {
        checked(
            &format!(
                "fn main()->u64 {{ let mut a=[0,0,0,0];
            for i in 0usize..3usize {{ let end=i+1usize;
            {{ let left=&mut a[i..end]; let right=&mut a[end..];
            left[0]=42; right[0]=42; {control} }} }} return a[1]; }}"
            ),
            42,
        );
    }
}

#[test]
fn prefix_bounds_and_disjointness_do_not_fill_missing_elements() {
    rejected(
        &PREFIX
            .replace("if j<n", "if j<4usize")
            .replace("3usize,1usize", "1usize,2usize"),
        true,
    );
    rejected(
        &PREFIX.replace("a[i]=42;", "if i!=1usize { a[i]=42; }"),
        true,
    );
    rejected(
        &PREFIX.replace("return a[j];", "let r=&a[..]; return r[j];"),
        true,
    );
    rejected(
        &PREFIX.replace("return a[j];", "let l=&a[..n]; let r=&a[n..]; return l[j];"),
        true,
    );
}

#[test]
fn slice_callees_check_their_own_relations_and_restore_the_parent() {
    checked(
        include_str!("../spec/cases/verify/relation-composition.nera"),
        42,
    );
    checked(
        "fn main()->u64 { let mut a=[1,2,3,4]; let p=&mut a[..]; edit(p,1usize); return p[1]; }
        fn edit(p:&mut [u64],mid:usize) { if mid>0usize { if mid<len(p) {
        let l=&mut p[..mid]; let r=&mut p[mid..]; l[0]=20; r[0]=42; }} return; }",
        42,
    );
    checked("fn main()->u64 { let a=[20,22]; return read(&a[..],1usize,false); }
        fn read(p:&[u64],i:usize,stop:bool)->u64 { if stop { if i<len(p) { return p[i]; } return 0; }
        return read(p,i,true); }",22);
    rejected(
        "fn main()->u64 { let a=[42]; return read(&a[..],0usize); }
        fn read(p:&[u64],i:usize)->u64 { return p[i]; }",
        false,
    );
}

#[test]
fn identity_views_and_result_buffers_keep_only_their_interface_facts() {
    let source = format!(
        "{} fn identity(p:&[u64])->&[u64] {{ return p; }}",
        PREFIX.replace(
            "return a[j];",
            "let r=identity(&a[..n]); if j<len(r) { return r[j]; }"
        )
    );
    checked(&source, 42);
    checked(
        "fn main()->u64 { let a=build(); return a[3]; }
        fn build()->[u64;4] { let mut a:[u64;4]; for i in 0usize..4usize { a[i]=42; } return a; }",
        42,
    );
    // Caller constants do not excuse an unchecked callee access. A closed
    // constant-return leaf, on the other hand, now exports its proven result.
    rejected(
        "fn main()->u64 { let a=[42]; return read(&a[..],0usize); }
        fn read(p:&[u64],i:usize)->u64 { return p[i]; }",
        false,
    );
    checked(
        "fn main()->u64 { let a=[42]; let i=index(); return a[i]; }
        fn index()->usize { return 0usize; }",
        42,
    );
    rejected(
        &format!(
            "{} fn inspect(p:&[u64]) {{ return; }}",
            PREFIX.replace("return a[j];", "inspect(&a[..n]); return a[3];")
        ),
        true,
    );
}

#[test]
fn missing_loop_cleanup_cannot_reuse_an_active_child_in_the_next_iteration() {
    const SOURCE: &str = "fn main()->u64 { let mut a=[0,0,0,0]; let p=&mut a[..];
        for i in 0usize..4usize { let c=&mut p[i..i+1usize]; c[0]=42; } return p[3]; }";
    checked(SOURCE, 42);
    let out = frontend_checks::accepted("loop-child.nera", SOURCE);
    let mut raw = out.vir().unwrap().as_unit().clone();
    let child = raw.runtime.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find_map(|i| match i.instruction {
            VirInstruction::LoanReborrow { effect, .. } => Some(effect.loan),
            _ => None,
        })
        .unwrap();
    let mut removed = 0;
    for block in &mut raw.runtime.functions[0].blocks {
        block.instructions.retain(|i| {
            let remove =
                matches!(i.instruction, VirInstruction::LoanEnd {effect} if effect.loan==child);
            removed += usize::from(remove);
            !remove
        });
    }
    assert!(removed > 0);
    let validated = revalidate(raw);
    let resolved = validated.resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(
        result
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::LoanEndedExactlyOnce { .. }
                    | ResourceObligationKind::LoanCompatible { .. }
            ) && !o.obligation().is_proven())
    );
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn loop_exit_and_relation_budgets_do_not_assume_an_unproved_prefix() {
    rejected(
        &PREFIX
            .replace("a[i]=42;", "a[i]=42; break;")
            .replace("3usize,1usize", "3usize,2usize"),
        true,
    );
    rejected(
        &PREFIX.replace("a[i]=42;", "if i==1usize { continue; } a[i]=42;"),
        true,
    );
    let out = frontend_checks::accepted("prefix-budget.nera", PREFIX);
    let resolved = out.vir().unwrap().resolve().unwrap();
    assert!(
        verify_program(
            &resolved,
            CfgAnalysisConfig {
                max_block_visits: 1,
                ..Default::default()
            }
        )
        .is_err()
    );
    let limited = CfgAnalysisConfig {
        relation_limits: nera::verifier::relation::difference::DifferenceLimits {
            max_variables: 0,
            max_constraints: 0,
            max_steps: 0,
            max_derivations: 0,
            max_branches: 0,
        },
        ..Default::default()
    };
    assert!(
        !verify_program(&resolved, limited)
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn runtime_prefix_scales_without_unrolling_and_zero_iterations_stay_empty() {
    for length in [4, 64, 512] {
        let source = PREFIX
            .replace("[u64;4]", &format!("[u64;{length}]"))
            .replace("n<=4usize", &format!("n<={length}usize"));
        checked(&source, 42);
        let started = std::time::Instant::now();
        let out = frontend_checks::accepted("prefix-scale.nera", &source);
        let resolved = out.vir().unwrap().resolve().unwrap();
        let cfg = nera::analyze_function_cfg(&resolved, nera::VirFunctionId::new(1)).unwrap();
        let states: usize = cfg
            .blocks()
            .values()
            .map(|b| {
                b.entry_conditional_state().cases().len()
                    + b.instruction_conditional_states()
                        .iter()
                        .map(|s| s.cases().len())
                        .sum::<usize>()
            })
            .sum();
        eprintln!(
            "prefix-growth length={length} elapsed_us={} visits={} states={states} queries={}",
            started.elapsed().as_micros(),
            cfg.block_visits(),
            cfg.relation_queries().len()
        );
        assert!(
            cfg.block_visits() < 80,
            "length {length}: {} visits",
            cfg.block_visits()
        );
    }
    checked(&PREFIX.replace("3usize,1usize", "0usize,0usize"), 0);
    checked(
        &PREFIX.replace(
            "for i in 0usize..n { a[i]=42; }",
            "let mut i=0usize; while i<n { a[i]=42; i=i+1usize; }",
        ),
        42,
    );
}

#[test]
fn call_length_is_rechecked_instead_of_trusting_the_pointer_footprint() {
    const SOURCE: &str = "fn main()->u64 { let a=[42]; inspect(&a[..]); return 42; }
        fn inspect(p:&[u64]) { return; }";
    checked(SOURCE, 42);
    let out = frontend_checks::accepted("call-length.nera", SOURCE);
    let mut raw = out.vir().unwrap().as_unit().clone();
    let length = raw.runtime.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find_map(|i| match i.instruction {
            VirInstruction::SliceAddress { length_result, .. } => Some(length_result.id),
            _ => None,
        })
        .unwrap();
    // Keep the same type/SSA definition, change only the ABI length value.
    let block = &mut raw.runtime.functions[0].blocks[0];
    let insertion = block
        .instructions
        .iter()
        .position(|i| matches!(i.instruction, VirInstruction::Call { .. }))
        .unwrap();
    let span = block.instructions[insertion].source_span;
    let forged = nera::VirValueId::new(10000);
    block.instructions.insert(
        insertion,
        nera::SpannedVirInstruction {
            instruction: VirInstruction::Constant {
                result: nera::VirValue {
                    id: forged,
                    ty: nera::VirType::U64,
                },
                value: nera::VirConstant::U64(2),
            },
            source_span: span,
        },
    );
    if let VirInstruction::Call { arguments, .. } =
        &mut block.instructions[insertion + 1].instruction
    {
        assert_eq!(arguments[1], length);
        arguments[1] = forged;
    }
    let validated = revalidate(raw);
    let resolved = validated.resolve().unwrap();
    let v = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!v.is_memory_checked_core0());
    assert!(
        v.functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|r| matches!(
                r.obligation().kind(),
                ResourceObligationKind::PermissionCoversAccess { .. }
            ) && !r.obligation().is_proven())
    );
    assert!(interpret(resolved.runtime()).is_err());
}
