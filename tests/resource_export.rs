use nera::*;

const EXPORT: &str = include_str!("../spec/cases/verify/resource-export.nera");

fn check(source: &str) -> (FrontendOutput, ProgramVerification) {
    let output = analyze(&SourceFile::from_text("resource-export.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("{:?}", output.issues()));
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    (output, report)
}

#[test]
fn initialized_views_return_authority_and_leave_the_remaining_backing_usable() {
    let (output, report) = check(EXPORT);
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let unit = output.vir().unwrap().resolve().unwrap();
    assert!(
        output
            .vir()
            .unwrap()
            .as_unit()
            .specs
            .trust_entries()
            .is_empty()
    );
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(58)]
    );
    backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
}

#[test]
fn export_contracts_cannot_hide_missing_writes_or_widen_the_view() {
    for bad in [
        EXPORT.replace("storage[1] = 1;", ""),
        EXPORT.replace(
            "writes storage[0usize..2usize];",
            "writes storage[0usize..1usize];",
        ),
        EXPORT.replace(
            "writable(result, 0usize..2usize)",
            "writable(result, 0usize..3usize)",
        ),
        EXPORT.replace(
            "initialized(result, 0usize..2usize)",
            "initialized(result, 0usize..3usize)",
        ),
        EXPORT.replace("backing[3usize..5usize]", "backing[3usize..6usize]"),
    ] {
        let (_, report) = check(&bad);
        assert!(!report.is_memory_checked_core0(), "{bad}");
    }
}

#[test]
fn live_exports_exclude_overlapping_loans_reset_and_release() {
    for bad in [
        EXPORT.replace("backing[3usize..5usize]", "backing[2usize..4usize]"),
        EXPORT.replace("backing[7] = 9;", "backing[1] = 9;"),
        EXPORT.replace("backing[7] = 9;", "free(backing);"),
        EXPORT.replace("free(backing);", "free(backing); free(backing);"),
    ] {
        let output = analyze(&SourceFile::from_text("invalid-export.nera", &bad));
        if let Some(unit) = output.vir() {
            assert!(
                !verify_program(&unit.resolve().unwrap(), Default::default())
                    .is_ok_and(|report| report.is_memory_checked_core0()),
                "{bad}"
            );
        } else {
            assert!(!output.issues().is_empty());
        }
    }
}

#[test]
fn uninitialized_backing_does_not_become_initialized_by_calling_a_view_interface() {
    for bad in [
        EXPORT.replace(
            "backing[cursor] = 0;",
            "if cursor != 2usize { backing[cursor] = 0; }",
        ),
        EXPORT.replace(
            "let total = left[0]",
            "let hole = backing[6]; let total = hole + left[0]",
        ),
    ] {
        let (_, report) = check(&bad);
        assert!(!report.is_memory_checked_core0(), "{bad}");
    }
}

const SLICE_LOOP: &str = "
fn main()->u64 {
    let mut data=[7,0,0,0,0,9];
    let view=fill(&mut data[1usize..5usize]);
    let total=view[0]+view[3];
    data[1]=0;
    return total+data[0]+data[5];
}
fn fill(storage:&mut[u64])->&mut[u64]
requires len(storage)==4usize;
{
    let mut i=0usize;
    while i<4usize {
        invariant i<=4usize;
        invariant initialized(storage,0usize..i);
        storage[i]=21;
        i=i+1usize;
    }
    return storage;
}";

#[test]
fn loop_initialization_uses_the_slice_extent_instead_of_one_element() {
    let (output, report) = check(SLICE_LOOP);
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(58)]
    );
}

#[test]
fn slice_loop_observations_cannot_reach_initialized_neighbors() {
    for bad in [
        SLICE_LOOP.replace(
            "invariant initialized(storage,0usize..i);",
            "invariant initialized(storage,0usize..5usize);",
        ),
        SLICE_LOOP.replace(
            "invariant initialized(storage,0usize..i);",
            "invariant writable(storage,0usize..5usize);",
        ),
        SLICE_LOOP.replace("storage[i]=21;", "storage[4]=21;"),
    ] {
        let (_, report) = check(&bad);
        assert!(!report.is_memory_checked_core0(), "{bad}");
    }
}

#[test]
fn raw_nodes_relink_across_calls_without_owning_their_neighbors() {
    let (output, report) = check(include_str!("../spec/cases/verify/raw-node.nera"));
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
}

#[test]
fn raw_links_never_supply_initialization_or_access_authority() {
    let source = include_str!("../spec/cases/verify/raw-node.nera");
    for bad in [
        source.replace("a.next = link(pb);", ""),
        source.replace("a.prev = null<Node>();", ""),
        source.replace(
            "let total = a.value + b.value;",
            "free(b); let total = a.value + b.value;",
        ),
        source.replace(
            "let total = a.value + b.value;",
            "let raw = a.next; let total = raw.value;",
        ),
        source.replace(
            "let total = a.value + b.value;",
            "let raw = null<Node>(); let total = raw.value;",
        ),
        source.replace("a.next = link(pb);", "a.next = null<List>();"),
        source.replace("a.next == pb", "a.next < pb"),
    ] {
        let output = analyze(&SourceFile::from_text("invalid-node.nera", &bad));
        if let Some(unit) = output.vir() {
            assert!(
                !verify_program(&unit.resolve().unwrap(), Default::default())
                    .is_ok_and(|r| r.is_memory_checked_core0()),
                "{bad}"
            );
        } else {
            assert!(!output.issues().is_empty());
        }
    }
}

#[test]
fn typed_nulls_and_address_equality_cross_allocation_and_liveness_boundaries() {
    let source = "fn main()->u64 {
        let a=alloc<u64>(1); let b=alloc<u64>(1);
        let pa=&raw mut *a; let pb=&raw mut *b;
        free(a); free(b);
        if pa == pb { return 0; }
        if pa == null<u64>() { return 0; }
        if null<u64>() != null<u64>() { return 0; }
        return 42;
    }";
    let (output, report) = check(source);
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn explicit_raw_types_resolve_nested_and_recursive_referents() {
    for source in [
        "fn main()->u64 { let p=empty(); if p == null<[u64;2]>() { return 42; } return 0; } fn empty()->ptr<[u64;2]> { return null<[u64;2]>(); }",
        "struct Node<T> { next: ptr<Node<T>>, value: T, } fn main()->u64 { let p=alloc<Node<u64>>(1); let address: ptr<Node<u64>> = &raw *p; p.next=null<Node<u64>>(); p.value=42; let answer=p.value; free(p); return answer; }",
    ] {
        let (output, report) = check(source);
        assert!(
            report.is_memory_checked_core0(),
            "{:?}",
            report.diagnostics()
        );
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn vir_rejects_mistyped_nulls_and_raw_field_payloads_independently() {
    let (output, _) = check(include_str!("../spec/cases/verify/raw-node.nera"));
    for null in [true, false] {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let instruction = unit.runtime.functions[0].blocks[0].instructions.iter_mut().find(|i| {
            if null { matches!(i.instruction, VirInstruction::Constant { value: VirConstant::NullPointer(_), .. }) }
            else { matches!(i.instruction, VirInstruction::Initialize { access, .. } | VirInstruction::Write { access, .. } | VirInstruction::Store { access, .. }
                if matches!(unit.memory.kind(access.ty), Some(VirMemoryTypeKind::Pointer { kind: VirPointerKind::Raw, .. }))) }
        }).unwrap();
        if let VirInstruction::Constant { value, .. } = &mut instruction.instruction {
            *value = VirConstant::NullPointer(VirMemoryAccess::core_u64());
        } else {
            match &mut instruction.instruction {
                VirInstruction::Initialize { access, .. }
                | VirInstruction::Write { access, .. }
                | VirInstruction::Store { access, .. } => *access = VirMemoryAccess::core_u64(),
                _ => unreachable!(),
            }
        }
        assert!(unit.validate().is_err());
    }
}
