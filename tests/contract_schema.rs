use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};
use nera::{FrontendStatus, SourceFile, VirRuntimeValue, interpret};

fn session(files: &[(&str, &str)]) -> CompilerSession {
    CompilerSession::modules(
        SourceDatabase::new(
            files
                .iter()
                .map(|(name, text)| {
                    SourceInput::new(*name, SourceFile::from_text(format!("{name}.nera"), text))
                })
                .collect(),
        )
        .unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap()
}

#[test]
fn source_contracts_keep_module_and_generic_instance_identity() {
    let app = "module app; use lib::identity; fn main()->u64 {let x=identity<usize>(7usize); assert x==7usize; return identity<u64>(42);}";
    let library = "module lib; pub fn identity<T>(x:T)->T ensures result == old(x); {return x;}";
    let compiler = session(&[("app", app), ("lib", library)]);
    assert!(compiler.verify("app").unwrap().is_checked());
    let bad = library.replace("result == old(x)", "result < old(x)");
    let compiler = session(&[("app", app), ("lib", &bad)]);
    assert!(!compiler.verify("app").unwrap().is_checked());
}

#[test]
fn equal_spans_in_distinct_files_keep_spec_origins_and_unused_module_identity() {
    let app = "module app; use aaa::a; use bbb::b; fn main()->u64{return a()+b();}";
    let a = "module aaa; pub fn a()->u64 {let x=1; assert x == 1; return x;}";
    let b = "module bbb; pub fn b()->u64 {let x=2; assert x == 2; return x;}";
    let files = [("app", app), ("aaa", a), ("bbb", b), ("aab", "module aab;")];
    let compiler = session(&files);
    let analysis = compiler.analyze("app").unwrap();
    let frontend = analysis.frontend();
    assert_eq!(
        frontend.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        frontend.issues()
    );
    let unit = frontend.vir().unwrap();
    let raw = unit.as_unit();
    assert_eq!(raw.source_map.sources().len(), 3);
    assert_eq!(raw.specs.proves().len(), 2);
    let left = raw
        .source_map
        .source_span_for_origin(raw.specs.proves()[0].origin)
        .unwrap();
    let right = raw
        .source_map
        .source_span_for_origin(raw.specs.proves()[1].origin)
        .unwrap();
    assert_eq!(left.span, right.span);
    assert_ne!(left.source, right.source);
    assert!(compiler.verify("app").unwrap().is_checked());
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(3)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.resolve().unwrap().runtime())
        .unwrap();
    let reordered = session(&[files[3], files[2], files[1], files[0]]);
    assert_eq!(analysis, reordered.analyze("app").unwrap());
    // A proof in another file at the same byte span cannot satisfy this one.
    let bad = b.replace("x == 2", "x == 1");
    let rejected = session(&[("app", app), ("aaa", a), ("bbb", &bad)]);
    assert!(!rejected.verify("app").unwrap().is_checked());
    let mut forged = raw.clone();
    forged.specs.proves_mut()[1].origin = raw.specs.proves()[0].origin;
    assert!(forged.into_validated().is_err());
}

#[test]
fn repeated_generic_instances_rename_clause_owners_without_changing_source_identity() {
    let compiler = session(&[
        (
            "app",
            "module app; use lib::item; fn main()->u64{return item<u64>(1)+item<bool>(true);}",
        ),
        (
            "lib",
            "module lib; pub fn item<T>(x:T)->u64 {assert true;return 21;}",
        ),
    ]);
    let analysis = compiler.analyze("app").unwrap();
    let output = analysis.frontend();
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let unit = output.vir().unwrap();
    let proves = unit.as_unit().specs.proves();
    assert_eq!(proves.len(), 2);
    assert_ne!(proves[0].function, proves[1].function);
    assert_ne!(proves[0].clause, proves[1].clause);
    assert_eq!(proves[0].origin, proves[1].origin);
    assert!(compiler.verify("app").unwrap().is_checked());
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn aggregate_result_slots_use_the_existing_abi_without_new_runtime_parameters() {
    use nera::{
        VirContractPosition, VirInstruction, VirLocation, VirSpecClauseId, VirSpecClauseKind,
        VirSpecClauseOrigin, VirSpecSnapshot, VirSpecTerm, VirSpecTermId, VirSpecTermKind,
        VirSpecType, VirType,
    };
    let output = nera::analyze(&SourceFile::from_text(
        "contract-result-slots.nera",
        "fn main()->u64 {let p=0;let pair=make(&p,42);return pair.0;} fn make(p:&u64,value:u64)->(u64,bool){return (value,true);}",
    ));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let original = output.vir().unwrap();
    let mut raw = original.as_unit().clone();
    let callee = raw.runtime.functions[1].clone();
    let origin = raw
        .source_map
        .origin_at(VirLocation::FunctionEntry {
            function: callee.id,
        })
        .unwrap()
        .id;
    let mut terms = vec![];
    for (slot, ty) in callee.signature.results.iter().enumerate() {
        let ty = match ty {
            VirType::U64 => VirSpecType::U64,
            VirType::Bool => VirSpecType::Bool,
            _ => continue,
        };
        let clause = VirSpecClauseId::new(raw.specs.clauses().len() as u32);
        let id = VirSpecTermId::new(raw.specs.terms().len() as u32);
        let root = VirSpecTermId::new(id.get() + 1);
        raw.specs.terms_mut().extend([
            VirSpecTerm {
                id,
                clause,
                ty,
                kind: VirSpecTermKind::Snapshot(VirSpecSnapshot::Result {
                    function: callee.id,
                    slot: slot as u32,
                }),
                origin,
            },
            VirSpecTerm {
                id: root,
                clause,
                ty: VirSpecType::Bool,
                kind: VirSpecTermKind::Equal {
                    left: id,
                    right: id,
                },
                origin,
            },
        ]);
        raw.specs
            .add_contract_clause(
                callee.contract,
                VirContractPosition::Ensures,
                VirSpecClauseOrigin::Explicit { origin },
                VirSpecClauseKind::Logic { root },
            )
            .unwrap();
        terms.push((slot, id));
    }
    assert_eq!(
        terms.len(),
        2,
        "the fixture exercises two scalar aggregate result slots"
    );
    let unit = raw.into_validated().unwrap();
    assert_eq!(
        unit.runtime().stable_dump(),
        original.runtime().stable_dump()
    );
    let resolved = unit.resolve().unwrap();
    for block in &resolved.runtime().functions[0].blocks {
        for (ordinal, instruction) in block.instructions.iter().enumerate() {
            if let VirInstruction::Call { results, .. } = &instruction.instruction {
                let binding = resolved
                    .contract_call_binding(VirLocation::Instruction {
                        function: resolved.runtime().entry,
                        block: block.id,
                        ordinal: ordinal as u64,
                    })
                    .unwrap();
                for (slot, id) in &terms {
                    assert_eq!(
                        binding.snapshot(*id),
                        Some((VirContractPosition::Ensures, results[*slot].id))
                    );
                }
            }
        }
    }
    assert!(
        nera::verify_program(&resolved, Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}
