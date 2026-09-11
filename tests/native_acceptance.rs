#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64SystemToolchain};
use nera::{
    ByteSpan, FrontendStatus, SourceFile, SpannedVirInstruction, SpannedVirTerminator,
    ValidatedVirUnit, VirBasicBlock, VirBlockId, VirBlockTarget, VirCallTarget, VirConstant,
    VirContractId, VirFunction, VirFunctionId, VirInstruction, VirIntegerPredicate, VirRegionId,
    VirRuntimeValue, VirSignature, VirTerminator, VirType, VirUnit, VirValue, VirValueId, analyze,
    interpret, verify_program,
};

#[path = "support/address_program.rs"]
mod address_program;
#[path = "support/enum_construction_program.rs"]
mod enum_construction_program;
#[path = "support/local_storage_program.rs"]
mod local_storage_program;
#[path = "support/object_effect_program.rs"]
mod object_effect_program;
#[path = "../src/bin/fuzz_support/provenance_cases.rs"]
mod provenance_cases;
#[path = "support/resource_payload_program.rs"]
mod resource_payload_program;
#[path = "support/slice_program.rs"]
mod slice_program;
#[path = "../src/bin/fuzz_support/summary_cases.rs"]
mod summary_cases;

#[path = "support/auto_memory_cases.rs"]
mod auto_memory_cases;

#[test]
fn ordinary_memory_corpus_matches_native_and_independent_resource_ledgers() {
    for case in auto_memory_cases::cases() {
        assert_resource_ledger(&case.source, case.allocations, None);
    }
}

#[test]
fn summary_acceptance_compositions_match_native_and_branch_release_ledgers() {
    for family in 0..4 {
        for entropy in [0, 3] {
            let allocations = if family == 2 {
                if entropy & 1 == 0 { 1 } else { 2 }
            } else {
                0
            };
            assert_resource_ledger(&summary_cases::source(family, entropy), allocations, None);
        }
    }
}

#[test]
fn summary_baseline_wrappers_and_mutual_recursion_preserve_native_resource_ledger() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/summary-baseline.nera"),
        1,
        None,
    );
}

#[test]
fn closed_summary_calls_preserve_native_results_and_two_fresh_lifetimes() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/summary-calls.nera"),
        2,
        None,
    );
}

#[test]
fn conditional_summary_owner_identity_and_replacement_free_exactly_once() {
    let source = include_str!("../spec/cases/verify/summary-conditional-payload.nera");
    assert_resource_ledger(source, 1, None);
    assert_resource_ledger(&source.replace("run(true)", "run(false)"), 2, None);
}

#[test]
fn recursive_summary_components_preserve_native_values_and_exact_owner_release() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/summary-recursive.nera"),
        3,
        None,
    );
}

#[test]
fn provenance_acceptance_families_match_native_with_exact_release_ledgers() {
    for family in 0..provenance_cases::POSITIVE_COUNT {
        for entropy in [0, 3] {
            let allocations = match family {
                1 => entropy as usize % 4 + 1,
                4 => 1,
                _ => 0,
            };
            assert_resource_ledger(
                &provenance_cases::source(family, entropy),
                allocations,
                None,
            );
        }
    }
}

#[test]
fn provenance_byte_address_baseline_matches_native_and_frees_once() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/provenance-baseline.nera"),
        1,
        None,
    );
}

#[test]
fn provenance_nested_subobjects_match_native_and_free_only_the_root() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/provenance-schema.nera"),
        1,
        None,
    );
}

#[test]
fn repeated_allocation_instances_match_native_with_exact_resource_ledger() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/provenance-instance.nera"),
        13,
        None,
    );
}

#[test]
fn raw_address_formation_matches_native_without_adding_owners() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/raw-address.nera"),
        1,
        None,
    );
}

#[test]
fn subobject_offsets_and_one_past_match_native_without_extra_allocations() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/pointer-domain.nera"),
        1,
        None,
    );
}

#[test]
fn pointer_comparisons_and_byte_distance_match_native() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/pointer-comparison.nera"),
        0,
        None,
    );
}

#[test]
fn cfg_loop_and_borrowed_call_provenance_match_native() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/provenance-flow.nera"),
        0,
        None,
    );
}

#[test]
fn address_model_stack_arguments_empty_results_and_fresh_heaps_match_native() {
    for condition in ["true", "false"] {
        let source = include_str!("../spec/cases/verify/native-address-model.nera")
            .replace("return true;", &format!("return {condition};"));
        assert_resource_ledger(&source, 3, Some(123));
    }
}

#[test]
fn deferred_local_initialization_matches_interpreter_and_native() {
    for (name, source) in [
        (
            "deferred-scalar",
            "fn main() -> u64 { let mut v: u64; if choose() { v = 1; }
          v = 42; return v; } fn choose() -> bool { return false; }",
        ),
        (
            "deferred-padded",
            "struct S { flag: bool, word: u64, }
          fn main() -> u64 { let mut v: S; v.flag = true; v.word = 42;
          let r = &v; return r.word; }",
        ),
        (
            "deferred-partial-replace",
            "fn main() -> u64 { let mut v: [u64; 2]; v[0] = 9;
          v = [40, 2]; v = v; return v[0] + v[1]; }",
        ),
        (
            "deferred-loop",
            "fn main() -> u64 { let mut count = 0; while count < 2 {
          let mut v: u64; v = count; count = v + 1; } return count; }",
        ),
    ] {
        let output = analyze(&SourceFile::from_text(name, source));
        assert_eq!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{name}: {:?}",
            output.issues()
        );
        let program = output.vir().unwrap();
        assert!(
            verify_program(
                &program.resolve().unwrap(),
                nera::CfgAnalysisConfig::default()
            )
            .unwrap()
            .is_memory_checked_core0()
        );
        assert_interpreter_matches_native(name, program);
    }
}

#[test]
fn typed_field_and_index_addresses_match_interpreter_and_native() {
    let program = address_program::validated();
    assert_interpreter_matches_native("typed-address", &program);
}

#[test]
fn evaluated_symbolic_footprint_matches_native_and_interpreter() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/symbolic-footprint.nera"),
        0,
        None,
    );
}

#[test]
fn unknown_length_slice_checks_match_native_and_interpreter() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/relation-bounds.nera"),
        0,
        None,
    );
}

#[test]
fn loop_prefix_and_recursive_slice_calls_match_native_and_interpreter() {
    let source = include_str!("../spec/cases/verify/relation-composition.nera");
    let heap = source
        .replace("let mut a: [u64; 4];", "let a = alloc<[u64; 4]>(1);")
        .replace("&mut a[..n]", "&mut *a[..n]");
    assert_resource_ledger(&heap, 1, None);
}

#[test]
fn heap_prefix_three_children_and_calls_restore_and_free_exactly_once() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/relation-acceptance.nera"),
        1,
        None,
    );
}

#[test]
fn two_live_dynamic_element_loans_match_native_and_interpreter() {
    let source = include_str!("../spec/cases/verify/disjoint-elements.nera").replace(
        "update(0usize, 2usize)",
        "update(0usize, 2usize) + update(3usize, 1usize)",
    );
    assert_resource_ledger(&source, 0, None);
}

#[test]
fn sibling_slices_and_parameter_reborrows_match_native_and_interpreter() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/sibling-parameters.nera"),
        0,
        None,
    );
    for mid in [0, 4] {
        let source = format!(
            "fn main() -> u64 {{ return edit({mid}usize); }}
            fn edit(mid: usize) -> u64 {{ let mut a=[1,2,3,4]; if mid <= len(a) {{
            let p=&mut a[..]; let l=&mut p[..mid]; let r=&mut p[mid..];
            let size=len(l)+len(r); p[0]=42; return p[0]; }} return 0; }}"
        );
        assert_resource_ledger(&source, 0, None);
    }
}

#[test]
fn strided_regions_and_chunks_match_interpreter_and_native() {
    let grid = include_str!("../spec/cases/verify/strided-regions.nera");
    assert_resource_ledger(grid, 0, None);
    assert_resource_ledger(
        &grid.replace(
            "edit(0usize, 1usize, 1usize, 2usize)",
            "edit(2usize, 0usize, 3usize, 1usize)",
        ),
        0,
        None,
    );
    assert_resource_ledger(
        include_str!("../spec/cases/verify/strided-chunks.nera"),
        0,
        None,
    );
}

#[test]
fn partial_refill_native_releases_each_allocation_exactly_once() {
    let cases = [
        ("struct Inner { owner: Own<u64>, word: u64, } struct Outer { nested: Inner, sibling: Own<u64>, }
          fn main() -> u64 { let a = alloc<u64>(1); *a = 42; let b = alloc<u64>(1); *b = 2;
          let v = Outer { nested: Inner { owner: a, word: 9 }, sibling: b };
          let moved = v.nested; let answer = moved.owner; return *answer; }", 2),
        ("struct Inner { owner: Own<u64>, word: u64, } struct Outer { nested: Inner, sibling: Own<u64>, }
          fn main() -> u64 { let a = alloc<u64>(1); *a = 1; let b = alloc<u64>(1); *b = 2;
          let mut v = Outer { nested: Inner { owner: a, word: 9 }, sibling: b };
          let c = alloc<u64>(1); *c = 42; v.nested = Inner { owner: c, word: 0 };
          v = v; let answer = v.nested.owner; return *answer; }", 3),
    ];
    for (source, allocations) in cases {
        assert_resource_ledger(source, allocations, None);
    }
}

fn assert_resource_ledger(source: &str, allocations: usize, order: Option<u64>) {
    let output = analyze(&SourceFile::from_text("resource-ledger.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    assert_program_resource_ledger(output.vir().unwrap(), allocations, order);
}

fn assert_program_resource_ledger(
    program: &ValidatedVirUnit,
    allocations: usize,
    order: Option<u64>,
) {
    let resolved = program.resolve().unwrap();
    let verification = verify_program(&resolved, nera::CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification.is_memory_checked_core0(),
        "{:?}",
        verification.diagnostics()
    );
    let expected = exact_process_status(interpret(resolved.runtime()).unwrap().values());
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();
    let assembly = X86_64_UNKNOWN_LINUX_GNU.emit_assembly(&machine).unwrap();
    for omit_cleanup in [false, true] {
        let artifact = NativeArtifact::create("resource-ledger");
        let asm = artifact.directory.join("program.s");
        let assembly = if omit_cleanup {
            assembly.replace("call free@PLT", "nop")
        } else {
            assembly.clone()
        };
        std::fs::write(&asm, assembly).unwrap();
        let mut command = Command::new("cc");
        command.arg(format!("-DEXPECTED_ALLOCATIONS={allocations}"));
        if let Some(order) = order {
            command.arg(format!("-DEXPECTED_RELEASE_ORDER={order}"));
        }
        let build = command
            .args([
                "-no-pie",
                "-std=c11",
                "-Wl,--wrap=aligned_alloc",
                "-Wl,--wrap=free",
            ])
            .arg(&asm)
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/support/count_resource.c"))
            .arg("-o")
            .arg(artifact.executable())
            .output()
            .unwrap();
        std::fs::remove_file(&asm).unwrap();
        assert!(
            build.status.success(),
            "{}",
            String::from_utf8_lossy(&build.stderr)
        );
        let status = Command::new(artifact.executable()).status().unwrap();
        assert_eq!(
            status.code(),
            Some(if omit_cleanup && allocations > 0 {
                122
            } else {
                expected
            })
        );
    }
}

#[test]
fn partial_construction_native_cleanup_is_exact_and_ordered() {
    for condition in ["true", "false"] {
        let source = include_str!("../spec/cases/verify/partial-construction.nera")
            .replace("return true;", &format!("return {condition};"));
        assert_resource_ledger(&source, 1, Some(1));
    }
    assert_resource_ledger(
        include_str!("../spec/cases/verify/partial-construction-loop.nera"),
        2,
        Some(12),
    );
    assert_resource_ledger(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
        fn main() -> u64 { let mut value: Pair; return 42; }",
        0,
        Some(0),
    );
    assert_resource_ledger(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
        fn main() -> u64 { let mut value: Pair;
        let right = alloc<u64>(1); *right = 1; value.right = right;
        let left = alloc<u64>(1); *left = 2; value.left = left; return 42; }",
        2,
        Some(21),
    );
    assert_resource_ledger(
        "struct Slot { value: Own<u64>, }
        fn main() -> u64 { let mut value: Slot; let a = alloc<u64>(1); *a = 1;
        value.value = a; let moved = value; let b = alloc<u64>(1); *b = 42;
        value.value = b; return 42; }",
        2,
        Some(12),
    );
}

#[test]
fn enum_partial_construction_native_cleanup_matches_presence_and_order() {
    for present in [false, true] {
        let program = enum_construction_program::partial_unit(present)
            .into_validated()
            .unwrap();
        assert_program_resource_ledger(&program, usize::from(present), None);
    }
    let source = include_str!("../spec/cases/verify/enum-partial-construction.nera");
    assert_resource_ledger(source, 2, Some(21));
    assert_resource_ledger(
        &source.replace("    match packet", "    packet = packet;\n    match packet"),
        2,
        Some(21),
    );
    assert_resource_ledger(&source.replace("packet = Packet::Empty;", ""), 2, Some(12));
    assert_resource_ledger(
        "enum Item { Empty, Full(Own<u64>), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 1; let b = alloc<u64>(1); *b = 42;
      let mut value = Item::Full(a); value = Item::Full(b); value = Item::Empty; return 42; }",
        2,
        Some(12),
    );
}

#[test]
fn recursive_local_storage_matches_interpreter_and_native() {
    let program = local_storage_program::recursive_program();
    assert_interpreter_matches_native("recursive-local-storage", &program);
}

#[test]
fn heap_construction_releases_present_inner_payloads_before_outer_storage() {
    let source = include_str!("../spec/cases/verify/heap-construction.nera");
    assert_resource_ledger(source, 2, Some(21));
    assert_resource_ledger(&source.replace("free(storage);", ""), 2, Some(21));
    assert_resource_ledger(
        include_str!("../spec/cases/verify/heap-enum-construction.nera"),
        3,
        Some(231),
    );
    for body in [
        "",
        "*p = Item::Empty;",
        "let a = alloc<u64>(1); *a = 42; *p = Item::Full(a); let moved = *p;",
    ] {
        let allocations = if body.contains("alloc") { 2 } else { 1 };
        let order = if allocations == 2 { 12 } else { 1 };
        assert_resource_ledger(
            &format!(
                "enum Item {{ Empty, Full(Own<u64>), }} fn main() -> u64 {{ let p = alloc<Item>(1); {body} free(p); return 42; }}"
            ),
            allocations,
            Some(order),
        );
    }
    assert_resource_ledger(
        "struct Slot { owner: Own<u64>, word: u64, } fn main() -> u64 {
        let p = alloc<Slot>(1); let a = alloc<u64>(1); *a = 1; p.owner = a; p.word = 1;
        let moved = *p; let b = alloc<u64>(1); *b = 42; p.owner = b; free(p); return 42; }",
        3,
        Some(312),
    );
}

#[test]
fn loop_initialization_matches_native_and_preserves_resource_cleanup() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/loop-initialization.nera"),
        0,
        None,
    );
    for body in [
        "for i in 0usize..8usize { p[i] = 42; } let whole = *p;",
        "let mut i = 0usize; while i < 8usize { p[i] = 42; i = i + 1usize; } let whole = *p;",
        "for i in 0usize..8usize { p[i] = 42; break; }",
    ] {
        assert_resource_ledger(
            &format!(
                "fn main() -> u64 {{ let p = alloc<[u64; 8]>(1); {body} let answer = p[0]; free(p); return answer; }}"
            ),
            1,
            Some(1),
        );
    }
    assert_resource_ledger("struct Batch { words: [u64; 8], owner: Own<u64>, }
        fn main() -> u64 { let p = alloc<Batch>(1); let a = alloc<u64>(1); *a = 1; p.owner = a;
        for i in 0usize..8usize { p.words[i] = 42; } let answer = p.words[7]; free(p); return answer; }", 2, Some(21));
}

#[test]
fn initialization_interfaces_preserve_values_padding_and_exact_cleanup() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/initialization-interfaces.nera"),
        0,
        None,
    );
    let owning = include_str!("../spec/cases/verify/initialization-interfaces-owning.nera");
    assert_resource_ledger(owning, 1, Some(1));
    assert_resource_ledger(
        &owning.replace("repair(p, true)", "repair(p, false)"),
        1,
        Some(1),
    );
    assert_resource_ledger("fn main() -> u64 { let p = alloc<[u64; 4]>(1);
      for i in 0usize..4usize { p[i] = 42; } let values = pass(*p, false); free(p); return values[3]; }
      fn pass(values: [u64; 4], stop: bool) -> [u64; 4] { if stop { return values; } return pass(values, true); }", 1, Some(1));
}

#[test]
fn initialization_acceptance_combines_calls_heap_loops_and_partial_cleanup() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/initialization-acceptance.nera"),
        8,
        None,
    );
}

#[test]
fn relation_evidence_baseline_does_not_change_native_execution() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/relation-baseline.nera"),
        0,
        None,
    );
}

#[test]
fn local_difference_query_matches_interpreter_and_native() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/difference-local.nera"),
        0,
        None,
    );
}

#[test]
fn cfg_difference_join_matches_interpreter_and_native() {
    assert_resource_ledger(
        include_str!("../spec/cases/verify/relation-cfg.nera"),
        0,
        None,
    );
}

#[test]
fn reference_refill_matches_interpreter_and_native() {
    for source in [
        "struct Slot { value: &u64, } fn main() -> u64 { let left = 20; let right = 22;
          let mut v = Slot { value: &left }; let alias = v.value; v.value = &right;
          v = v; let copy = v; let value = copy.value; return *alias + *value; }",
        "struct Inner { value: &mut u64, word: u64, } struct Outer { nested: Inner, sibling: u64, }
          fn main() -> u64 { let mut word = 40;
          let mut v = Outer { nested: Inner { value: &mut word, word: 2 }, sibling: 9 };
          let moved = v.nested; v.nested = moved; v = v;
          let reference = v.nested.value; return *reference + v.nested.word; }",
    ] {
        let output = analyze(&SourceFile::from_text("reference-refill.nera", source));
        assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
        let vir = output.vir().unwrap();
        assert!(
            verify_program(&vir.resolve().unwrap(), nera::CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0()
        );
        assert_interpreter_matches_native("reference-refill", vir);
    }
}

#[test]
fn object_effects_match_interpreter_and_native_processes() {
    for (name, program) in [
        (
            "object-record-copy",
            object_effect_program::validated_record(nera::VirObjectSourceMode::Copy),
        ),
        (
            "object-record-move",
            object_effect_program::validated_record(nera::VirObjectSourceMode::Move),
        ),
        (
            "object-enum-copy",
            object_effect_program::validated_enum(nera::VirObjectSourceMode::Copy),
        ),
        (
            "object-enum-move",
            object_effect_program::validated_enum(nera::VirObjectSourceMode::Move),
        ),
    ] {
        assert_interpreter_matches_native(name, &program);
    }
}

#[test]
fn owning_resource_move_matches_interpreter_and_native_processes() {
    let program = resource_payload_program::validated();
    let resolved = program
        .resolve()
        .expect("resource payload fixture resolves");
    let analysis = nera::analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("resource payload verification converges");
    assert!(analysis.all_obligations_proven());
    assert_interpreter_matches_native("owning-resource-move", &program);
}

#[test]
fn slice_range_matches_interpreter_and_native_processes() {
    assert_interpreter_matches_native("slice-range", &slice_program::validated());
}

#[test]
fn safe_source_corpus_matches_interpreter_and_native() {
    for (name, source) in [
        (
            "memory",
            include_bytes!("../spec/cases/vir/memory.nera").as_slice(),
        ),
        (
            "unit",
            include_bytes!("../spec/cases/vir/unit.nera").as_slice(),
        ),
        (
            "structured-control-flow",
            include_bytes!("../spec/cases/control-flow/structured.nera").as_slice(),
        ),
        (
            "while-control-flow",
            include_bytes!("../spec/cases/control-flow/while.nera").as_slice(),
        ),
        (
            "nested-loop-control-flow",
            include_bytes!("../spec/cases/control-flow/nested-loop.nera").as_slice(),
        ),
        (
            "for-range-control-flow",
            include_bytes!("../spec/cases/control-flow/for-range.nera").as_slice(),
        ),
        (
            "match-control-flow",
            include_bytes!("../spec/cases/control-flow/match.nera").as_slice(),
        ),
        (
            "direct-call",
            include_bytes!("../spec/cases/control-flow/direct-call.nera").as_slice(),
        ),
        (
            "recursive-call",
            include_bytes!("../spec/cases/control-flow/recursive-call.nera").as_slice(),
        ),
        (
            "recursive-owned-call",
            include_bytes!("../spec/cases/control-flow/recursive-owned-call.nera").as_slice(),
        ),
        (
            "owned-call",
            include_bytes!("../spec/cases/control-flow/owned-call.nera").as_slice(),
        ),
        (
            "aggregate-surface",
            include_bytes!("../spec/cases/aggregate/surface.nera").as_slice(),
        ),
        (
            "aggregate-dynamic-object",
            include_bytes!("../spec/cases/aggregate/dynamic-object.nera").as_slice(),
        ),
        (
            "aggregate-bounded-dynamic-object",
            include_bytes!("../spec/cases/aggregate/bounded-dynamic-object.nera").as_slice(),
        ),
        (
            "aggregate-abi-direct",
            include_bytes!("../spec/cases/aggregate/abi-direct.nera").as_slice(),
        ),
        (
            "aggregate-abi-indirect",
            include_bytes!("../spec/cases/aggregate/abi-indirect.nera").as_slice(),
        ),
        (
            "aggregate-abi-recursive",
            include_bytes!("../spec/cases/aggregate/abi-recursive.nera").as_slice(),
        ),
        (
            "aggregate-abi-register-stack",
            include_bytes!("../spec/cases/aggregate/abi-register-stack.nera").as_slice(),
        ),
        (
            "enum-surface",
            include_bytes!("../spec/cases/aggregate/enum-surface.nera").as_slice(),
        ),
        (
            "enum-switch",
            include_bytes!("../spec/cases/aggregate/enum-switch.nera").as_slice(),
        ),
        (
            "aggregate-copy-move",
            include_bytes!("../spec/cases/aggregate/copy-move.nera").as_slice(),
        ),
        (
            "aggregate-pattern-move",
            include_bytes!("../spec/cases/aggregate/pattern-move.nera").as_slice(),
        ),
        (
            "aggregate-owning-abi",
            include_bytes!("../spec/cases/aggregate/owning-abi.nera").as_slice(),
        ),
        (
            "stage7-resource-acceptance",
            include_bytes!("../spec/cases/verify/resource-acceptance.nera").as_slice(),
        ),
        (
            "stage7-local-shared-borrow",
            include_bytes!("../spec/cases/verify/local-shared-borrow.nera").as_slice(),
        ),
        (
            "stage7-local-mutable-borrow",
            include_bytes!("../spec/cases/verify/local-mutable-borrow.nera").as_slice(),
        ),
        (
            "stage7-local-reborrow",
            include_bytes!("../spec/cases/verify/local-reborrow.nera").as_slice(),
        ),
        (
            "stage7-local-nll",
            include_bytes!("../spec/cases/verify/local-nll.nera").as_slice(),
        ),
        (
            "stage7-guarded-loan-cfg",
            include_bytes!("../spec/cases/verify/guarded-loan-cfg.nera").as_slice(),
        ),
        (
            "stage7-reference-aggregate",
            include_bytes!("../spec/cases/verify/reference-aggregate.nera").as_slice(),
        ),
        (
            "stage7-safe-slice",
            include_bytes!("../spec/cases/verify/safe-slice.nera").as_slice(),
        ),
        (
            "stage7-borrow-calls",
            include_bytes!("../spec/cases/verify/borrow-calls.nera").as_slice(),
        ),
        (
            "stage7-borrow-acceptance",
            include_bytes!("../spec/cases/verify/borrow-acceptance.nera").as_slice(),
        ),
        (
            "stage7-runtime-semantics",
            include_bytes!("../spec/cases/verify/runtime-semantics.nera").as_slice(),
        ),
    ] {
        let output = analyze(&SourceFile::new(format!("{name}.nera"), source));
        assert_eq!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{name} frontend issues: {:?}",
            output.issues()
        );
        let program = output.vir().expect("accepted source corpus has VIR");
        if matches!(
            name,
            "stage7-resource-acceptance"
                | "stage7-local-shared-borrow"
                | "stage7-local-mutable-borrow"
                | "stage7-local-reborrow"
                | "stage7-local-nll"
                | "stage7-guarded-loan-cfg"
                | "stage7-reference-aggregate"
                | "stage7-safe-slice"
                | "stage7-borrow-calls"
                | "stage7-borrow-acceptance"
                | "stage7-runtime-semantics"
        ) {
            let resolved = program.resolve().expect("checked stage 7 source resolves");
            let verification = verify_program(&resolved, nera::CfgAnalysisConfig::default())
                .expect("stage 7 verification converges");
            assert!(
                verification.is_memory_checked_core0(),
                "{name}: the stage 7 native differential must first be verified: {:?}",
                verification.diagnostics()
            );
        }
        assert_interpreter_matches_native(name, program);
    }
}

#[test]
fn complete_vir_v0_program_matches_native_on_both_cfg_arms() {
    let then_program = complete_program(VirIntegerPredicate::Equal);
    assert_complete_runtime_coverage(&then_program);
    let then_program = then_program
        .into_validated()
        .expect("complete then-arm VIR is structurally valid");
    assert_permission_values_are_erased(&then_program);
    assert_interpreter_matches_native("complete-then", &then_program);

    let else_program = complete_program(VirIntegerPredicate::NotEqual);
    assert_complete_runtime_coverage(&else_program);
    let else_program = else_program
        .into_validated()
        .expect("complete else-arm VIR is structurally valid");
    assert_permission_values_are_erased(&else_program);
    assert_interpreter_matches_native("complete-else", &else_program);
}

fn assert_interpreter_matches_native(name: &str, program: &ValidatedVirUnit) {
    let resolved = program.resolve().expect("acceptance VIR resolves");
    let execution = interpret(resolved.runtime()).expect("acceptance VIR executes safely");
    let expected_status = exact_process_status(execution.values());

    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("acceptance VIR lowers to a complete machine plan");
    let assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("acceptance machine plan emits legal GNU assembly");
    let artifact = NativeArtifact::create(name);
    X86_64SystemToolchain::default()
        .build_executable(&assembly, artifact.executable())
        .expect("system as/cc build the acceptance executable");

    let status = Command::new(artifact.executable())
        .status()
        .expect("acceptance executable starts");
    assert_eq!(
        status.code(),
        Some(expected_status),
        "{name}: native process result differs from the VIR interpreter"
    );
}

fn exact_process_status(values: &[VirRuntimeValue]) -> i32 {
    let value = match values {
        [] => 0,
        [VirRuntimeValue::Bool(value)] => u64::from(*value),
        [VirRuntimeValue::U64(value)] => *value,
        other => panic!("native v0 process result cannot represent {other:?}"),
    };
    i32::try_from(value)
        .ok()
        .filter(|value| (0..=u8::MAX.into()).contains(value))
        .expect("acceptance values must fit the exact Unix process-status domain")
}

fn assert_permission_values_are_erased(program: &ValidatedVirUnit) {
    let resolved = program.resolve().expect("acceptance VIR resolves");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("acceptance VIR lowers");
    let frame = machine
        .planning()
        .function(VirFunctionId::new(0))
        .expect("entry plan exists")
        .frame();
    for id in [2, 8, 9, 10, 11, 22, 32, 42] {
        assert_eq!(
            frame.value_slot(VirValueId::new(id)),
            None,
            "permission %{id} must not receive a native frame slot"
        );
    }
    let callee_frame = machine
        .planning()
        .function(VirFunctionId::new(1))
        .expect("identity plan exists")
        .frame();
    assert_eq!(
        frame.value_slot(VirValueId::new(24)),
        None,
        "permission call result must not receive a native frame slot"
    );
    assert_eq!(
        callee_frame.value_slot(VirValueId::new(1)),
        None,
        "permission callee parameter must not receive a native frame slot"
    );
}

fn assert_complete_runtime_coverage(program: &VirUnit) {
    let instruction_kinds = program
        .runtime
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.instructions)
        .map(|instruction| match instruction.instruction {
            VirInstruction::Constant { .. } => "constant",
            VirInstruction::WordAdd { .. } => "word-add",
            VirInstruction::Compare { .. } => "compare",
            VirInstruction::Allocate { .. } => "allocate",
            VirInstruction::LocalStorage { .. } => "local-storage",
            VirInstruction::Initialize { .. } => "initialize",
            VirInstruction::Write { .. } => "write",
            VirInstruction::Load { .. } => "load",
            VirInstruction::EnumDiscriminant { .. } => "enum-discriminant",
            VirInstruction::Store { .. } => "store",
            VirInstruction::ResourceInitialize { .. } => "resource-initialize",
            VirInstruction::ResourceTake { .. } => "resource-take",
            VirInstruction::DropOwn { .. } => "drop-own",
            VirInstruction::ObjectTransfer { .. } => "object-transfer",
            VirInstruction::ObjectDeinitialize { .. } => "object-deinitialize",
            VirInstruction::StorageReset { .. } => "storage-reset",
            VirInstruction::ResourceStorageReset { .. } => "resource-storage-reset",
            VirInstruction::ObjectDrop { .. } => "object-drop",
            VirInstruction::EnumSetDiscriminant { .. } => "enum-set-discriminant",
            VirInstruction::PointerOffset { .. } => "pointer-offset",
            VirInstruction::FieldAddress { .. } => "field-address",
            VirInstruction::TupleElementAddress { .. } => "tuple-element-address",
            VirInstruction::ObjectLeafAddress { .. } => "object-leaf-address",
            VirInstruction::IndexAddress { .. } => "index-address",
            VirInstruction::SliceRange { .. } => "slice-range",
            VirInstruction::SliceAddress { .. } => "slice-address",
            VirInstruction::Free { .. } => "free",
            VirInstruction::PermissionSplit { .. } => "permission-split",
            VirInstruction::PermissionJoin { .. } => "permission-join",
            VirInstruction::PermissionMove { .. } => "permission-move",
            VirInstruction::LoanBegin { .. } => "loan-begin",
            VirInstruction::LoanAliasShared { .. } => "loan-alias-shared",
            VirInstruction::LoanReborrow { .. } => "loan-reborrow",
            VirInstruction::LoanReborrowAuthority { .. } => "loan-reborrow-authority",
            VirInstruction::LoanEnd { .. } => "loan-end",
            VirInstruction::LoanAliasAuthority { .. } => "loan-alias-authority",
            VirInstruction::LoanEndAuthority { .. } => "loan-end-authority",
            VirInstruction::Check { .. } => "check",
            VirInstruction::Call { .. } => "call",
            VirInstruction::RawAddress { .. } => "raw-address",
            VirInstruction::PointerCompare { .. } => "pointer-compare",
            VirInstruction::PointerDistance { .. } => "pointer-distance",
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        instruction_kinds,
        BTreeSet::from([
            "allocate",
            "check",
            "call",
            "compare",
            "constant",
            "free",
            "initialize",
            "load",
            "permission-join",
            "permission-move",
            "permission-split",
            "pointer-offset",
            "store",
            "word-add",
            "write",
        ])
    );

    let terminator_kinds = program
        .runtime
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .map(|block| match block.terminator.terminator {
            VirTerminator::Jump { .. } => "jump",
            VirTerminator::Branch { .. } => "branch",
            VirTerminator::Return { .. } => "return",
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        terminator_kinds,
        BTreeSet::from(["branch", "jump", "return"])
    );
}

fn complete_program(branch_predicate: VirIntegerPredicate) -> VirUnit {
    let pointer = VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    };
    let identity_signature = VirSignature {
        parameters: vec![VirType::U64, VirType::Permission],
        results: vec![VirType::U64, VirType::Permission],
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![
            VirFunction {
                id: VirFunctionId::new(0),
                name: "complete_entry".to_owned(),
                signature: VirSignature {
                    parameters: vec![],
                    results: vec![VirType::U64],
                },
                contract: VirContractId::new(0),
                entry: VirBlockId::new(0),
                blocks: vec![
                    VirBasicBlock {
                        id: VirBlockId::new(0),
                        parameters: vec![],
                        instructions: vec![
                            constant_u64(0, 8),
                            constant_u64(3, 41),
                            instruction(VirInstruction::Allocate {
                                pointer_result: value(1, pointer),
                                permission_result: value(2, VirType::Permission),
                                size_bytes: VirValueId::new(0),
                                alignment: 8,
                                region: VirRegionId::new(0),
                                element: nera::VirMemoryAccess::core_u64(),
                            }),
                            instruction(VirInstruction::Initialize {
                                pointer: VirValueId::new(1),
                                value: VirValueId::new(3),
                                permission: VirValueId::new(2),
                                access: nera::VirMemoryAccess::core_u64(),
                            }),
                            instruction(VirInstruction::Load {
                                result: value(4, VirType::U64),
                                pointer: VirValueId::new(1),
                                permission: VirValueId::new(2),
                                access: nera::VirMemoryAccess::core_u64(),
                            }),
                            constant_u64(5, 0),
                            instruction(VirInstruction::PointerOffset {
                                result: value(6, pointer),
                                base: VirValueId::new(1),
                                delta_bytes: VirValueId::new(5),
                            }),
                            instruction(VirInstruction::Store {
                                pointer: VirValueId::new(6),
                                value: VirValueId::new(4),
                                permission: VirValueId::new(2),
                                access: nera::VirMemoryAccess::core_u64(),
                            }),
                            instruction(VirInstruction::Write {
                                pointer: VirValueId::new(6),
                                value: VirValueId::new(4),
                                permission: VirValueId::new(2),
                                access: nera::VirMemoryAccess::core_u64(),
                            }),
                            instruction(VirInstruction::Compare {
                                result: value(7, VirType::Bool),
                                predicate: branch_predicate,
                                left: VirValueId::new(4),
                                right: VirValueId::new(3),
                            }),
                            constant_u64(12, 4),
                            instruction(VirInstruction::PermissionSplit {
                                left_result: value(8, VirType::Permission),
                                right_result: value(9, VirType::Permission),
                                source: VirValueId::new(2),
                                split_at_bytes: VirValueId::new(12),
                            }),
                            instruction(VirInstruction::PermissionJoin {
                                result: value(10, VirType::Permission),
                                left: VirValueId::new(8),
                                right: VirValueId::new(9),
                            }),
                            instruction(VirInstruction::PermissionMove {
                                result: value(11, VirType::Permission),
                                source: VirValueId::new(10),
                            }),
                            instruction(VirInstruction::Constant {
                                result: value(13, VirType::Bool),
                                value: VirConstant::Bool(true),
                            }),
                            instruction(VirInstruction::Check {
                                condition: VirValueId::new(13),
                            }),
                        ],
                        terminator: terminator(VirTerminator::Branch {
                            condition: VirValueId::new(7),
                            then_target: target(1, &[4, 1, 11]),
                            else_target: target(2, &[4, 1, 11]),
                        }),
                        source_span: span(),
                    },
                    VirBasicBlock {
                        id: VirBlockId::new(1),
                        parameters: vec![
                            value(20, VirType::U64),
                            value(21, pointer),
                            value(22, VirType::Permission),
                        ],
                        instructions: vec![instruction(VirInstruction::Call {
                            results: vec![value(23, VirType::U64), value(24, VirType::Permission)],
                            target: VirCallTarget {
                                symbol: "identity".to_owned(),
                                signature: identity_signature.clone(),
                                contract: VirContractId::new(1),
                                abi: None,
                            },
                            arguments: vec![VirValueId::new(20), VirValueId::new(22)],
                        })],
                        terminator: terminator(VirTerminator::Jump {
                            target: target(3, &[23, 21, 24]),
                        }),
                        source_span: span(),
                    },
                    VirBasicBlock {
                        id: VirBlockId::new(2),
                        parameters: vec![
                            value(30, VirType::U64),
                            value(31, pointer),
                            value(32, VirType::Permission),
                        ],
                        instructions: vec![instruction(VirInstruction::WordAdd {
                            result: value(33, VirType::U64),
                            left: VirValueId::new(30),
                            right: VirValueId::new(30),
                        })],
                        terminator: terminator(VirTerminator::Jump {
                            target: target(3, &[33, 31, 32]),
                        }),
                        source_span: span(),
                    },
                    VirBasicBlock {
                        id: VirBlockId::new(3),
                        parameters: vec![
                            value(40, VirType::U64),
                            value(41, pointer),
                            value(42, VirType::Permission),
                        ],
                        instructions: vec![instruction(VirInstruction::Free {
                            pointer: VirValueId::new(41),
                            permission: VirValueId::new(42),
                        })],
                        terminator: terminator(VirTerminator::Return {
                            values: vec![VirValueId::new(40)],
                        }),
                        source_span: span(),
                    },
                ],
                source_span: span(),
            },
            VirFunction {
                id: VirFunctionId::new(1),
                name: "identity".to_owned(),
                signature: identity_signature,
                contract: VirContractId::new(1),
                entry: VirBlockId::new(0),
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![value(0, VirType::U64), value(1, VirType::Permission)],
                    instructions: vec![],
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(0), VirValueId::new(1)],
                    }),
                    source_span: span(),
                }],
                source_span: span(),
            },
        ],
    )
}

fn constant_u64(id: u32, constant: u64) -> SpannedVirInstruction {
    instruction(VirInstruction::Constant {
        result: value(id, VirType::U64),
        value: VirConstant::U64(constant),
    })
}

fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

fn terminator(terminator: VirTerminator) -> SpannedVirTerminator {
    SpannedVirTerminator {
        terminator,
        source_span: span(),
    }
}

fn target(block: u32, arguments: &[u32]) -> VirBlockTarget {
    VirBlockTarget {
        block: VirBlockId::new(block),
        arguments: arguments.iter().copied().map(VirValueId::new).collect(),
    }
}

const fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("test span is valid")
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
            "nera-native-acceptance-{}-{nonce}-{name}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).expect("create native acceptance directory");
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
