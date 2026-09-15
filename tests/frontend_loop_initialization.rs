#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, SourceFile, VirInstruction, VirUnit, analyze, interpret, verify_program,
};

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("loop-initialization.nera", source, expected);
}

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("loop-initialization.nera", source)
}

fn rejected(unit: VirUnit, execution_fault: bool) -> Vec<nera::ResourceObligationKind> {
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!verification.is_memory_checked_core0());
    if execution_fault {
        assert!(interpret(resolved.runtime()).is_err());
    }
    verification
        .functions()
        .values()
        .flat_map(|function| function.cfg().obligations())
        .filter(|record| !record.obligation().is_proven())
        .map(|record| record.obligation().kind())
        .collect()
}

#[test]
fn sequential_fixed_array_loop_initializes_complete_value() {
    for length in [1, 4, 64, 512] {
        let source = format!(
            "fn main() -> u64 {{ let mut values: [u64; {length}]; for i in 0usize..{length}usize {{ values[i] = 42; }} let whole = values; return whole[{}]; }}",
            length - 1
        );
        frontend_checks::checked("loop-initialization.nera", &source, 42);
        let output = accepted(&source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let cfg = nera::analyze_function_cfg(&resolved, nera::VirFunctionId::new(0)).unwrap();
        assert!(
            cfg.block_visits() < 50,
            "proof must not unroll {length} iterations"
        );
    }
}

#[test]
fn nonzero_and_dynamic_starts_initialize_only_the_selected_interval() {
    checked(
        "fn main() -> u64 { let mut a: [u64; 64];
        for i in 2usize..64usize { a[i] = 42; } return a[63]; }",
        42,
    );
    checked(
        "fn main() -> u64 { return fill(2usize, 48usize); }
        fn fill(begin: usize, end: usize) -> u64
        { if begin >= end { return 0; } if end > 64usize { return 0; }
          let a = alloc<[u64; 64]>(1); let mut i = begin;
          while i < end { a[i] = 42; let value = a[i]; i = i + 1usize; }
          free(a); return 42; }",
        42,
    );
}

#[test]
fn nonzero_ranges_do_not_cover_gaps_or_assume_dynamic_exit_facts() {
    for (body, read) in [("a[i] = 42;", 1), ("if i != 4usize { a[i] = 42; }", 4)] {
        let source = format!(
            "fn main() -> u64 {{ let mut a: [u64; 8];
            for i in 2usize..8usize {{ {body} }} return a[{read}]; }}"
        );
        rejected(accepted(&source).vir().unwrap().as_unit().clone(), true);
    }
    // The range domain supports arbitrary SSA origins, but the implicit CFG
    // fixed point can still lose the input/cursor relation at a complex exit.
    // Do not silently install a resource invariant to make this example pass.
    let source = "fn main() -> u64 { return fill(2usize, 48usize); }
        fn fill(begin: usize, end: usize) -> u64 {
          if begin >= end { return 0; } if end > 64usize { return 0; }
          let a = alloc<[u64; 64]>(1); let mut i = begin;
          while i < end { a[i] = 42; i = i + 1usize; }
          let answer = a[begin]; free(a); return answer; }";
    let output = accepted(source);
    let kinds = rejected(output.vir().unwrap().as_unit().clone(), false);
    assert!(kinds.iter().any(|kind| matches!(
        kind,
        nera::ResourceObligationKind::MemoryInitialized { .. }
            | nera::ResourceObligationKind::ObjectValueBytesInitialized { .. }
    )));
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [nera::VirRuntimeValue::U64(42)]
    );
}

#[test]
fn while_heap_nested_fields_and_boolean_elements() {
    checked("fn main() -> u64 { let values = alloc<[u64; 8]>(1); let mut i = 0usize;
      while i < 8usize { values[i] = 42; i = i + 1usize; } let whole = *values; free(values); return whole[7]; }", 42);
    checked("struct Table { words: [u64; 4], flag: bool, } fn main() -> u64 { let mut t: Table;
      for i in 0usize..4usize { t.words[i] = 42; } t.flag = true; let r = &t; if r.flag { return r.words[3]; } return 0; }", 42);
    checked(
        "fn main() -> u64 { let mut flags: [bool; 4]; for i in 0usize..4usize { flags[i] = true; }
      let r = &flags; if r[3] { return 42; } return 0; }",
        42,
    );
}

#[test]
fn zero_iterations_and_early_exit_export_only_the_proven_prefix() {
    checked(
        "fn main() -> u64 { let p = alloc<[u64; 4]>(1); for i in 0usize..0usize { p[i] = 1; } free(p); return 42; }",
        42,
    );
    for body in [
        "values[i] = 42; break;",
        "values[i] = 42; return values[0];",
        "values[i] = 42; continue;",
    ] {
        checked(
            &format!(
                "fn main() -> u64 {{ let mut values: [u64; 4]; for i in 0usize..4usize {{ {body} }} return values[0]; }}"
            ),
            42,
        );
    }
    for (range, body, read) in [
        ("0usize..0usize", "values[i] = 42;", 0),
        ("1usize..4usize", "values[i] = 42;", 0),
        (
            "0usize..4usize",
            "if i == 2usize { break; } values[i] = 42;",
            2,
        ),
        (
            "0usize..4usize",
            "if i == 1usize { continue; } values[i] = 42;",
            1,
        ),
        ("0usize..4usize", "values[0] = 42;", 3),
    ] {
        let source = format!(
            "fn main() -> u64 {{ let mut values: [u64; 4]; for i in {range} {{ {body} }} return values[{read}]; }}"
        );
        rejected(accepted(&source).vir().unwrap().as_unit().clone(), true);
    }
}

#[test]
fn runtime_bound_is_evaluated_once_and_needs_its_own_bounds() {
    checked(
        "fn main() -> u64 { let mut values: [u64; 4]; let bound = extent();
      if bound == 0usize { return 0; } if bound > 4usize { return 0; }
      for i in 0usize..bound { values[i] = 42; } return values[0]; }
      fn extent() -> usize { return 3usize; }",
        42,
    );
    let source = "fn main() -> u64 { let mut values: [u64; 4]; for i in 0usize..5usize { values[i] = 42; } return values[0]; }";
    rejected(accepted(source).vir().unwrap().as_unit().clone(), true);
}

#[test]
fn missing_write_skipped_increment_and_retirement_cannot_forge_a_prefix() {
    let source = "fn main() -> u64 { let mut values: [u64; 4]; for i in 0usize..4usize { values[i] = 42; } let whole = values; return whole[3]; }";
    let original = accepted(source).vir().unwrap().as_unit().clone();
    let mut missing = original.clone();
    for block in &mut missing.runtime.functions[0].blocks {
        block
            .instructions
            .retain(|item| !matches!(item.instruction, VirInstruction::Write { .. }));
    }
    missing.rebuild_source_map_from_runtime("missing-write.vir", 1000);
    rejected(missing, true);
    let mut skipped = original.clone();
    for block in &mut skipped.runtime.functions[0].blocks {
        for item in &mut block.instructions {
            if let VirInstruction::Constant {
                value: nera::VirConstant::U64(value),
                ..
            } = &mut item.instruction
                && *value == 1
            {
                *value = 2;
            }
        }
    }
    skipped.rebuild_source_map_from_runtime("skipped-increment.vir", 1000);
    rejected(skipped, true);
    let mut retired = original;
    for block in &mut retired.runtime.functions[0].blocks {
        let mut rewritten = Vec::new();
        for item in &block.instructions {
            rewritten.push(item.clone());
            if let VirInstruction::Write {
                pointer,
                permission,
                access,
                ..
            } = item.instruction
            {
                rewritten.push(nera::SpannedVirInstruction {
                    instruction: VirInstruction::ObjectDeinitialize {
                        pointer,
                        permission,
                        access,
                    },
                    source_span: item.source_span,
                });
            }
        }
        block.instructions = rewritten;
    }
    // Exercise the original initialization transfer, not an inferred interface
    // whose admitted instruction profile no longer matches this mutation.
    retired.rebuild_implicit_contracts_from_runtime();
    retired.rebuild_source_map_from_runtime("retired-prefix.vir", 1000);
    rejected(retired, true);
}

#[test]
fn analysis_budget_and_resource_arrays_fail_closed() {
    let output = accepted(
        "fn main() -> u64 { let mut a: [u64; 4]; for i in 0usize..4usize { a[i] = 42; } return a[3]; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let cfg = CfgAnalysisConfig {
        max_block_visits: 1,
        ..CfgAnalysisConfig::default()
    };
    assert!(verify_program(&resolved, cfg).is_err());
    let source = "fn main() -> u64 { let mut a: [Own<u64>; 4]; for i in 0usize..4usize { let p = alloc<u64>(1); *p = 42; a[i] = p; } return 42; }";
    let output = analyze(&SourceFile::from_text("resource-prefix-gated.nera", source));
    if let Some(unit) = output.vir() {
        rejected(unit.as_unit().clone(), false);
    } else {
        assert_eq!(output.status(), nera::FrontendStatus::Unsupported);
    }
}

#[test]
fn malformed_stride_overflow_and_unknown_calls_are_not_initialization_proofs() {
    let original = accepted(include_str!(
        "../spec/cases/verify/loop-initialization.nera"
    ));
    let mut stride = original.vir().unwrap().as_unit().clone();
    let mut changed = false;
    for block in &mut stride.runtime.functions[0].blocks {
        for item in &mut block.instructions {
            if let VirInstruction::IndexAddress { stride_bytes, .. } = &mut item.instruction {
                *stride_bytes += 1;
                changed = true;
            }
        }
    }
    assert!(changed);
    stride.rebuild_source_map_from_runtime("wrong-stride.vir", 10000);
    assert!(stride.into_validated().is_err());
    let overflow = accepted(
        "fn main() -> u64 { let mut a: [u64; 4]; let mut i = 18446744073709551615usize;
      while i > 0usize { a[0] = 42; i = i + 1usize; } return a[0]; }",
    );
    // Runtime word addition wraps; verification must still reject this as
    // checked induction progress rather than treating the wrap as a proof.
    rejected(overflow.vir().unwrap().as_unit().clone(), false);
    let unknown = analyze(&SourceFile::from_text(
        "unknown-call.nera",
        "fn main() -> u64 { let mut a: [u64; 4];
      for i in 0usize..4usize { a[i] = unknown(); } return a[0]; }",
    ));
    assert!(unknown.vir().is_none());
    assert!(!unknown.issues().is_empty());
}
