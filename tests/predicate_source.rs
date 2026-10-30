use nera::*;

const SOURCE: &str = include_str!("../spec/cases/verify/predicate-storage.nera");

fn accepted(source: &str) -> FrontendOutput {
    let output = analyze(&SourceFile::from_text("predicate.nera", source));
    assert!(output.vir().is_some(), "{:?}\n{source}", output.issues());
    output
}
fn checked(source: &str) -> FrontendOutput {
    let output = accepted(source);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .expect("bounded analysis");
    if !report.is_memory_checked_core0() {
        for (id, function) in report.functions() {
            eprintln!("function {id:?} summary {:?}", function.summary().state);
            for check in function.cfg().obligations() {
                if !check.obligation().is_proven() {
                    eprintln!("unproved {:?}", check.obligation());
                }
            }
        }
    }
    assert!(
        report.is_memory_checked_core0(),
        "{:?}\n{source}",
        report.diagnostics()
    );
    output
}
fn rejected(source: &str) {
    let output = analyze(&SourceFile::from_text("predicate.nera", source));
    if let Some(unit) = output.vir() {
        assert!(
            !verify_program(&unit.resolve().unwrap(), Default::default())
                .is_ok_and(|r| r.is_memory_checked_core0()),
            "unexpectedly checked:\n{source}"
        );
    } else {
        assert!(!output.issues().is_empty());
    }
}

fn checked_logical_prefix(source: &str) {
    let output = accepted(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&resolved, Default::default()).expect("bounded prefix analysis");
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let replay =
        nera::verifier::relation::audit::RelationReplayCache::new(&resolved, Default::default())
            .unwrap();
    for (&id, function) in report.functions() {
        assert_eq!(
            function.summary().state,
            nera::verifier::summary::SummaryState::Closed
        );
        let cfg = function.cfg();
        assert!(replay.accepts_memory_trace(
            id,
            cfg.provenance_evidence(),
            cfg.relation_queries(),
            cfg.relation_evidence()
        ));
    }
}

#[test]
fn hidden_initialization_endpoints_survive_checked_loop_abstraction() {
    let source = include_str!("../spec/cases/verify/predicate-logical-prefix-loop.nera");
    checked_logical_prefix(source);
    for (invalid, fold_failure) in [
        (
            source.replace("let value=q.slots[0];", "let value=q.slots[1];"),
            false,
        ),
        (source.replace("used=saved", "used=3usize"), true),
        (source.replace("p.slots[0]=42;", ""), true),
    ] {
        let output = accepted(&invalid);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("semantic negative must complete analysis");
        assert!(!report.is_memory_checked_core0(), "{invalid}");
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .map(|c| c.obligation())
                .any(|o| !o.is_proven()
                    && if fold_failure {
                        matches!(
                            o.kind(),
                            ResourceObligationKind::PredicateActionValid { .. }
                        )
                    } else {
                        matches!(
                            o.kind(),
                            ResourceObligationKind::MemoryInitialized { .. }
                                | ResourceObligationKind::ObjectValueBytesInitialized { .. }
                        )
                    }),
            "wrong failure layer: {:?}",
            report.diagnostics()
        );
    }
}

#[test]
fn dynamic_access_consumes_a_logical_prefix_without_an_equal_runtime_endpoint() {
    let source = include_str!("../spec/cases/verify/predicate-logical-prefix-access.nera");
    checked_logical_prefix(source);
    checked_logical_prefix(&source.replace(
        "struct Buffer { slots:[u64;4], }",
        "struct Buffer { pad:u64, slots:[u64;4], }",
    ));
    for (invalid, fold_failure) in [
        (
            source.replace(
                "let value=p.slots[index];",
                "let value=p.slots[index+1usize];",
            ),
            false,
        ),
        (source.replace("index<used;", "index<=used;"), false),
        (source.replace("p.slots[1]=42;", ""), true),
    ] {
        let output = accepted(&invalid);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("semantic negative must complete analysis");
        assert!(!report.is_memory_checked_core0(), "{invalid}");
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .map(|c| c.obligation())
                .any(|o| !o.is_proven()
                    && if fold_failure {
                        matches!(
                            o.kind(),
                            ResourceObligationKind::PredicateActionValid { .. }
                        )
                    } else {
                        matches!(
                            o.kind(),
                            ResourceObligationKind::MemoryInitialized { .. }
                                | ResourceObligationKind::ObjectValueBytesInitialized { .. }
                        )
                    }),
            "wrong failure layer: {:?}",
            report.diagnostics()
        );
    }
}

#[test]
fn slice_borrow_and_ordinary_call_consume_the_same_logical_initialization() {
    let source = include_str!("../spec/cases/verify/predicate-logical-prefix-borrow.nera");
    checked_logical_prefix(source);
    checked_logical_prefix(&source.replace(
        "struct Buffer { slots:[u64;4], }",
        "struct Buffer { pad:u64, slots:[u64;4], }",
    ));
    for (invalid, fold_failure) in [
        (
            source.replace("let end=index+1usize;", "let end=index+2usize;"),
            false,
        ),
        (source.replace("index<used;", "index<=used;"), false),
    ] {
        let output = accepted(&invalid);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("semantic negative must complete analysis");
        assert!(!report.is_memory_checked_core0(), "{invalid}");
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .map(|c| c.obligation())
                .any(|o| !o.is_proven()
                    && if fold_failure {
                        matches!(
                            o.kind(),
                            ResourceObligationKind::PredicateActionValid { .. }
                        )
                    } else {
                        matches!(
                            o.kind(),
                            ResourceObligationKind::MemoryInitialized { .. }
                                | ResourceObligationKind::ObjectValueBytesInitialized { .. }
                        )
                    }),
            "wrong failure layer: {:?}",
            report.diagnostics()
        );
    }
}

#[test]
fn source_predicate_effects_are_checked_and_erased() {
    let output = checked(SOURCE);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        output
            .vir()
            .unwrap()
            .as_unit()
            .specs
            .predicate_actions()
            .len(),
        5
    );
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
        [VirRuntimeValue::U64(5)]
    );
    let erased = SOURCE[SOURCE.find("fn main").unwrap()..]
        .lines()
        .filter(|line| {
            !["fold ", "unfold ", "finish "]
                .iter()
                .any(|s| line.trim_start().starts_with(s))
        })
        .collect::<Vec<_>>()
        .join("\n");
    let erased = checked(&erased);
    let runtime = erased.vir().unwrap().resolve().unwrap();
    // The entire emitted machine code is independent of representation effects.
    assert_eq!(
        backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(unit.runtime())
            .unwrap(),
        backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(runtime.runtime())
            .unwrap()
    );
}

#[test]
fn predicates_do_not_fabricate_authority_initialization_or_invariants() {
    for source in [
        SOURCE.replace("backing[0] = 0;", ""),
        SOURCE.replace("backing[0] = 5;", "backing[0] = 9;"),
        SOURCE.replace("assert true;", "backing[0] = 1;"),
        SOURCE.replace("assert true;", "let forbidden = backing[0];"),
        SOURCE.replace("assert true;", "free(backing);"),
        SOURCE.replace("assert true;", "fold Slots(backing);"),
        SOURCE.replacen(
            "unfold Slots(backing);",
            "unfold Slots(backing); unfold Slots(backing);",
            1,
        ),
        SOURCE.replace("finish Slots(backing);", ""),
        SOURCE.replace("free(backing);", ""),
        SOURCE.replace(
            "finish Slots(backing);",
            "finish Slots(backing); finish Slots(backing);",
        ),
        SOURCE.replace("fold Slots(backing);", "fold Slots(null<[u64; 8]>());"),
    ] {
        rejected(&source);
    }
}

#[test]
fn finite_declarations_reject_unowned_recursive_and_mistyped_bodies() {
    for source in [
        SOURCE.replace("owns(storage);", ""),
        SOURCE.replace("owns(storage);", "owns(storage); owns(storage);"),
        SOURCE.replace("owns(storage);", "Slots(storage);"),
        SOURCE.replace("1usize);", "9usize);"),
        SOURCE.replace("storage[0] <= 8", "storage[9] <= 8"),
        SOURCE.replace("storage[0] <= 8", "storage[0] <= storage[1]"),
        SOURCE.replace("ptr<[u64; 8]>", "u64"),
        SOURCE.replace("alloc<[u64; 8]>", "alloc<[u64; 4]>"),
    ] {
        rejected(&source);
    }
}

#[test]
fn ordinary_call_boundaries_require_folded_state_and_preserve_the_frame() {
    let source = format!("fn ping() -> u64 {{ return 0; }}\n{SOURCE}");
    checked(&source.replace("assert true;", "let ignored = ping();"));
    rejected(&source.replace("backing[0] = 5;", "backing[0] = 5; let ignored = ping();"));
}

#[test]
fn folded_resources_survive_cfg_projection_without_gaining_permissions() {
    checked(&SOURCE.replace(
        "assert true;",
        "if true { assert true; } else { assert false; }",
    ));
    rejected(&SOURCE.replace("assert true;", "if true { free(backing); }"));
    rejected(&SOURCE.replace("assert true;", "let alias = backing; free(alias);"));
}

fn spec_tables(unit: &VirUnit) -> VirSpecTables {
    VirSpecTables {
        assertions: unit.specs.assertions().to_vec(),
        contracts: unit.specs.contracts().to_vec(),
        predicates: unit.specs.predicates().to_vec(),
        predicate_actions: unit.specs.predicate_actions().to_vec(),
        predicate_interfaces: unit.specs.predicate_interfaces().to_vec(),
        binders: unit.specs.binders().to_vec(),
        terms: unit.specs.terms().to_vec(),
        clauses: unit.specs.clauses().to_vec(),
        proves: unit.specs.proves().to_vec(),
        trust_entries: unit.specs.trust_entries().to_vec(),
        loop_invariants: unit.specs.loop_invariants().to_vec(),
    }
}

#[test]
fn vir_validation_rejects_forged_effects_and_representation_tables() {
    let output = accepted(SOURCE);
    let base = output.vir().unwrap().as_unit();
    for mutation in 0..7 {
        let mut unit = base.clone();
        let mut tables = spec_tables(&unit);
        match mutation {
            0 => tables.predicate_actions[0].id = 9,
            1 => tables.predicate_actions[0].predicate = VirPredicateId::new(99),
            2 => {
                tables.predicates[0]
                    .representation
                    .as_mut()
                    .unwrap()
                    .resources[0]
                    .initialized = vec![(0, 65)]
            }
            3 => tables.predicates[0].representation.as_mut().unwrap().bounds[0].offset = 64,
            4 => {
                tables.predicate_actions[0].location = VirLocation::BlockEntry {
                    function: VirFunctionId::new(0),
                    block: VirBlockId::new(0),
                }
            }
            5 => {
                if let VirPredicateActionKind::Fold { bindings, .. } =
                    &mut tables.predicate_actions[0].kind
                {
                    bindings[0].permission = bindings[0].pointer;
                }
            }
            6 => unit.version = VirUnitVersion::V29,
            _ => unreachable!(),
        }
        unit.specs = VirSpecEnvironment::from_tables(tables);
        assert!(unit.validate().is_err(), "mutation {mutation}");
    }
}

#[test]
fn modules_cannot_open_each_others_representation() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let lib = format!(
        "module lib; {}",
        SOURCE
            .replace("predicate Slots", "pub predicate Slots")
            .replace("fn main", "pub fn run")
    );
    for (app, valid) in [
        (
            "module app; use lib::run; fn main() -> u64 { return run(); }",
            true,
        ),
        (
            "module app; use lib::Slots; fn main() -> u64 { let backing = alloc<[u64; 8]>(1); backing[0] = 0; fold Slots(backing); unfold Slots(backing); free(backing); finish Slots(backing); return 0; }",
            false,
        ),
    ] {
        let inputs = [("app", app), ("lib", lib.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        let preview = compiler.verify("app").unwrap();
        assert_eq!(preview.is_checked(), valid, "{preview:?}");
    }
}

#[test]
fn two_allocations_require_distinct_authority_and_actual_cleanup() {
    let source = "predicate Pair(a: ptr<u64>, b: ptr<u64>) { owns(a); owns(b); initialized(a, 0usize..1usize); }
        fn main() -> u64 { let a = alloc<u64>(1); let b = alloc<u64>(1); *a = 7;
        fold Pair(a, b); unfold Pair(a, b); let total = *a; free(a); free(b); finish Pair(a, b); return total; }";
    checked(source);
    rejected(&source.replace("Pair(a, b)", "Pair(a, a)"));
    rejected(&source.replace("free(b);", ""));
    rejected(&source.replace("let total = *a;", "let total = *b;"));
}

fn hir_tables(program: &HirProgram) -> HirProgramTables {
    HirProgramTables {
        data_layout: program.data_layout(),
        entry_module: program.entry_module_id(),
        entry_function: program.entry_function_id(),
        modules: program.modules().to_vec(),
        types: program.types().to_vec(),
        type_capabilities: program.type_capability_table().to_vec(),
        layouts: program.layouts().to_vec(),
        fields: program.fields().to_vec(),
        variants: program.variants().to_vec(),
        generic_parameters: program.generic_parameters().to_vec(),
        regions: program.regions().to_vec(),
        region_constraints: program.region_constraints().to_vec(),
        functions: program.functions().to_vec(),
        contracts: program.contracts().to_vec(),
        predicates: program.predicates().to_vec(),
        specs: program.specs().clone(),
    }
}

#[test]
fn hir_validation_rechecks_effect_identity_types_and_statement_anchors() {
    let output = accepted(SOURCE);
    let program = output.hir().unwrap();
    for mutation in 0..6 {
        let mut tables = hir_tables(program);
        match mutation {
            0 => tables.specs.predicate_actions[0].id = 7,
            1 => tables.specs.predicate_actions[0].function = HirFunctionId::new(99),
            2 => tables.specs.predicate_actions.clear(),
            3 => tables
                .specs
                .predicate_actions
                .push(tables.specs.predicate_actions[0].clone()),
            4 => tables.predicates[0].representation.as_mut().unwrap().bounds[0].offset = 64,
            5 => {
                if let HirPredicateActionKind::Fold { locals, .. } =
                    &mut tables.specs.predicate_actions[0].kind
                {
                    locals[0] = HirLocalId::new(99);
                }
            }
            _ => unreachable!(),
        }
        assert!(
            HirProgram::from_tables(tables).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn branches_loans_and_repetition_cannot_drop_or_duplicate_holders() {
    let source = format!(
        "{}\nfn main() -> u64 {{ return exercise(true); }}",
        SOURCE.replace("fn main()", "fn exercise(flag: bool)")
    );
    checked(&source.replace(
        "assert true;",
        "if flag { assert true; } else { assert true; }",
    ));
    rejected(&source.replace("assert true;", "if flag { unfold Slots(backing); }"));
    rejected(&source.replace("assert true;", "while flag { unfold Slots(backing); }"));
    rejected(&SOURCE.replace(
        "fold Slots(backing);\n    assert true;",
        "let borrowed = &mut backing; fold Slots(backing); borrowed[0] = 2;",
    ));
    // Only the requested prefix is initialized, even after a successful reopen.
    rejected(&SOURCE.replace("let total = backing[0];", "let total = backing[1];"));
}

#[test]
fn colocated_effect_order_is_semantically_observable_and_replayed() {
    let output = accepted(SOURCE);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let mut tables = spec_tables(&unit);
    assert_eq!(
        tables.predicate_actions[2].location,
        tables.predicate_actions[3].location
    );
    let fold = tables.predicate_actions[2].kind.clone();
    tables.predicate_actions[2].kind = tables.predicate_actions[3].kind.clone();
    tables.predicate_actions[3].kind = fold;
    unit.specs = VirSpecEnvironment::from_tables(tables);
    let validated = unit.into_validated().unwrap();
    let report = verify_program(&validated.resolve().unwrap(), Default::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
}

const MOVE: &str = include_str!("../spec/cases/verify/predicate-move.nera");

#[test]
fn ordinary_moves_transfer_the_sealed_carrier_without_opening_it() {
    let output = checked(MOVE);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(6)]
    );
    for source in [
        MOVE.replace("unfold Slots(last);", "unfold Slots(backing);"),
        MOVE.replace("unfold Slots(last);", "unfold Slots(next);"),
        MOVE.replace("let last = next;", "let last = backing;"),
        MOVE.replace("unfold Slots(last);", "last[0] = 1; unfold Slots(last);"),
        MOVE.replace("unfold Slots(last);", "free(last); unfold Slots(last);"),
        MOVE.replace(
            "unfold Slots(last);",
            "unfold Slots(last); unfold Slots(last);",
        ),
        MOVE.replace("finish Slots(last);", "finish Slots(backing);"),
        MOVE.replace(
            "unfold Slots(last);",
            "unfold Slots(last); let stolen = last;",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn multiple_owned_resources_move_without_duplicating_their_predicate() {
    let source = "predicate Pair(a: ptr<u64>, b: ptr<u64>) { owns(a); owns(b); initialized(a, 0usize..1usize); }
        fn main() -> u64 { let a = alloc<u64>(1); let b = alloc<u64>(1); *a = 7;
        fold Pair(a, b); let x = a; let y = b;
        unfold Pair(x, y); let total = *x; free(x); free(y); finish Pair(x, y); return total; }";
    checked(source);
    rejected(&source.replace("unfold Pair(x, y)", "unfold Pair(x, b)"));
    rejected(&source.replace("let y = b;", "let y = a;"));
    rejected(&source.replace("free(y);", ""));
}

#[test]
fn typed_owner_abi_can_feed_private_predicate_operations() {
    let source = include_str!("../spec/cases/verify/predicate-owner-abi.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(6)]
    );
    rejected(&source.replace("storage[1] = 1;", ""));
    rejected(&source.replace("storage[0] = 5;", "storage[0] = 9;"));
    rejected(&source.replace("Own<[u64; 2]>", "Own<[u64; 3]>"));
    // This ABI transfers ordinary owners, never a sealed predicate implicitly.
    rejected(&source.replace("return storage;", "fold Slots(storage); return storage;"));
}

#[test]
fn generic_owner_types_are_normalized_before_abi_classification() {
    let source = "fn main() -> u64 { let p = alloc<[u64; 2]>(1); p[0] = 3; p[1] = 4;
        let q = relay<2>(p); let total = q[0] + q[1]; free(q); return total; }
        fn relay<const N: usize>(p: Own<[u64; N]>) -> Own<[u64; N]> { return p; }";
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(7)]
    );
    let source = "struct Cell { word: u64, }
        fn main() -> u64 { let p = alloc<Cell>(1); p.word = 7;
        let q = relay<Cell>(p); let total = q.word; free(q); return total; }
        fn relay<T>(p: Own<T>) -> Own<T> { return p; }";
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(7)]
    );
}

const CALLS: &str = include_str!("../spec/cases/verify/predicate-calls.nera");

#[test]
fn ordinary_calls_transfer_closed_predicates_and_check_actual_callee_bodies() {
    let output = checked(CALLS);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(5)]
    );
    for source in [
        CALLS.replace("p[0] = 5;", "p[0] = 9;"),
        CALLS.replace("fold Slots(p);", ""),
        CALLS.replace("p[0] = 0;", ""),
        CALLS.replace("unfold Slots(p);", ""),
        CALLS.replace("free(p);", ""),
        CALLS.replace("finish Slots(p);", ""),
        CALLS.replace("let total = p[0];", "let total = p[1];"),
        CALLS.replace("let b = update(a);", "a[0] = 1; let b = update(a);"),
        CALLS.replace(
            "return destroy(b);",
            "let total = destroy(b); let again = destroy(b); return total + again;",
        ),
        CALLS.replace("requires Slots(p);", ""),
        CALLS.replacen("ensures Slots(result);", "", 1),
    ] {
        rejected(&source);
    }
}

#[test]
fn distinct_factory_results_preserve_framed_predicates_and_existential_identity() {
    let source = CALLS
        .replace("let a = make();", "let frame = make(); let a = make();")
        .replace(
            "return destroy(b);",
            "let first = destroy(b); return first + destroy(frame);",
        );
    let output = checked(&source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(5)]
    );
    let identity = CALLS.replace(
        "    unfold Slots(p);\n    p[0] = 5;\n    fold Slots(p);",
        "",
    );
    checked(&identity);
    rejected(&source.replace("destroy(frame)", "destroy(b)"));
}

#[test]
fn predicate_interface_validation_rejects_forged_and_overlapping_abi_slots() {
    let output = accepted(CALLS);
    for mutation in 0..6 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let mut specs = spec_tables(&unit);
        match mutation {
            0 => specs.predicate_interfaces[0].predicate = VirPredicateId::new(99),
            1 => specs.predicate_interfaces[0].function = VirFunctionId::new(99),
            2 => specs.predicate_interfaces[0].bindings[0] = (1, 0),
            3 => specs
                .predicate_interfaces
                .push(specs.predicate_interfaces[0].clone()),
            4 => specs.predicate_interfaces[0].bindings.clear(),
            5 => specs.predicate_interfaces[0].origin = specs.predicates[0].origin,
            _ => unreachable!(),
        }
        unit.specs = VirSpecEnvironment::from_tables(specs);
        assert!(unit.validate().is_err(), "mutation {mutation}");
    }
    for mutation in 0..4 {
        let mut tables = hir_tables(output.hir().unwrap());
        match mutation {
            0 => tables.specs.predicate_interfaces[0].parameters = vec![99],
            1 => tables.specs.predicate_interfaces[0].function = HirFunctionId::new(99),
            2 => tables
                .specs
                .predicate_interfaces
                .push(tables.specs.predicate_interfaces[0].clone()),
            3 => tables.specs.predicate_interfaces[0].predicate = HirPredicateId::new(99),
            _ => unreachable!(),
        }
        assert!(HirProgram::from_tables(tables).is_err());
    }
}

#[test]
fn clients_can_move_and_forward_opaque_resources_but_cannot_open_the_representation() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let declarations = &CALLS[..CALLS.find("fn main").unwrap()];
    let functions = &CALLS[CALLS.find("fn make").unwrap()..];
    let lib = format!("module storage; {declarations}{functions}")
        .replace("predicate Slots", "pub predicate Slots")
        .replace("fn make", "pub fn make")
        .replace("fn update", "pub fn update")
        .replace("fn destroy", "pub fn destroy");
    let app = "module app; use storage::Slots; use storage::make; use storage::update; use storage::destroy;
        fn main() -> u64 { let frame = make(); let p = relay(make()); let q = update(p); return destroy(q) + destroy(frame); }
        fn relay(p: Own<[u64; 8]>) -> Own<[u64; 8]>
        requires Slots(p); ensures Slots(result); { return p; }";
    for (source, valid) in [
        (app.to_owned(), true),
        (
            app.replace(
                "{ return p; }",
                "{ unfold Slots(p); fold Slots(p); return p; }",
            ),
            false,
        ),
        (
            app.replace("{ return p; }", "{ p[0] = 7; return p; }"),
            false,
        ),
        (
            app.replace("{ return p; }", "{ let leaked = p[0]; return p; }"),
            false,
        ),
        (app.replace("requires Slots(p);", ""), false),
    ] {
        let inputs = [("app", source.as_str()), ("storage", lib.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        let preview = compiler.verify("app").unwrap();
        assert_eq!(preview.is_checked(), valid, "{preview:?}");
        if valid {
            let analysis = compiler.analyze("app").unwrap();
            let unit = analysis.frontend().vir().unwrap().resolve().unwrap();
            assert_eq!(
                interpret(unit.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(5)]
            );
        }
    }
}

#[test]
fn predicate_contracts_compose_across_multiple_owner_parameters() {
    let source = CALLS.replace("return destroy(b);", "return destroy_both(b, make());");
    let source = format!(
        "{source}\nfn destroy_both(a: Own<[u64; 8]>, b: Own<[u64; 8]>) -> u64\n\
         requires Slots(a);\nrequires Slots(b);\n\
         {{ let x = destroy(a); return x + destroy(b); }}"
    );
    checked(&source);
    rejected(&source.replace("destroy_both(b, make())", "destroy_both(b, b)"));
    rejected(&source.replace("requires Slots(b);", ""));
}

#[test]
fn opaque_arena_checks_cursor_bounds_and_local_loan_restoration() {
    let source = include_str!("../spec/cases/verify/predicate-opaque-arena.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for invalid in [
        source.replace("p.cursor = 4usize;", "p.cursor = 9usize;"),
        source.replace("p.slots = [0, 0, 0, 0, 0, 0, 0, 0];", ""),
        source.replace(
            "p.cursor = 4usize;",
            "p.cursor = 4usize; fold Ready(p); let still_live = right[0];",
        ),
        source.replace("p.slots[0] = total;", "free(p); let still_live = left[0];"),
        source.replace(
            "let right = &mut p.slots[2usize..4usize];",
            "let right = &mut p.slots[1usize..4usize];",
        ),
        source.replace(
            "let right = &mut p.slots[2usize..4usize];",
            "let right = &mut p.slots[2usize..9usize];",
        ),
        source.replace("p.cursor = 4usize;", "p.cursor = 4usize; unfold Ready(p);"),
    ] {
        rejected(&invalid);
    }
    let unit = output.vir().unwrap().as_unit();
    for offset in [1, 4, u64::MAX] {
        let mut specs = spec_tables(unit);
        specs.predicates[0].representation.as_mut().unwrap().bounds[0].offset = offset;
        let mut forged = unit.clone();
        forged.specs = VirSpecEnvironment::from_tables(specs);
        assert!(forged.validate().is_err());
    }
}

#[test]
fn closed_owner_frames_keep_cross_call_views_and_wait_for_loan_return() {
    let source = include_str!("../spec/cases/verify/predicate-borrow-calls.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    // Read-only views may cover constrained scalars without granting writes.
    let shared = source
        .replace(
            "p.cursor = 4usize;",
            "p.cursor = 4usize; let cursor = &p.cursor;",
        )
        .replace(
            "let returned = prepare(left);",
            "assert *cursor <= 8usize; let returned = prepare(left);",
        );
    checked(&shared);
    for invalid in [
        source.replace(
            "let returned = prepare(left);",
            "unfold Ready(p); let returned = prepare(left);",
        ),
        source.replace(
            "let returned = prepare(left);",
            "let next = reset(p); let returned = prepare(left);",
        ),
        source.replace(
            "let returned = prepare(left);",
            "free(p); let returned = prepare(left);",
        ),
        source.replace(
            "let total = returned[0] + right[0];",
            "unfold Ready(p); let total = returned[0] + right[0];",
        ),
        source.replace("view[0] = 12;", "view[2] = 12;"),
        source.replace("p.cursor = 4usize;", "p.cursor = 9usize;"),
        source
            .replace(
                "let left = &mut p.slots[0usize..2usize];",
                "let left = &mut p.slots[0usize..2usize]; let cursor = &mut p.cursor;",
            )
            .replace(
                "let returned = prepare(left);",
                "*cursor = 4usize; let returned = prepare(left);",
            ),
    ] {
        rejected(&invalid);
    }
}

const BORROWED_ARENA: &str = include_str!("../spec/cases/verify/predicate-borrowed-arena.nera");

#[test]
fn borrowed_predicates_preserve_loan_authority_across_calls_and_return_views() {
    let output = checked(BORROWED_ARENA);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn borrowed_predicates_cannot_bypass_invariants_or_loan_lifetimes() {
    for source in [
        BORROWED_ARENA.replace("p.cursor = 2usize;", "p.cursor = 9usize;"),
        BORROWED_ARENA.replace("p.cursor = 4usize;", "p.cursor = 9usize;"),
        BORROWED_ARENA.replace("finish Ready(p);", ""),
        BORROWED_ARENA.replace("finish Ready(p);", "finish Ready(p); finish Ready(p);"),
        BORROWED_ARENA.replace("finish Ready(p);", "free(p); finish Ready(p);"),
        BORROWED_ARENA.replace(
            "let total = slice[0] + slice[1];",
            "free(a); let total = slice[0] + slice[1];",
        ),
        BORROWED_ARENA.replace(
            "let total = slice[0] + slice[1];",
            "let again = begin(&mut *a); let total = slice[0] + slice[1];",
        ),
        BORROWED_ARENA.replace(
            "let b = fill(view);",
            "let b = fill(view); unfold Ready(view);",
        ),
        BORROWED_ARENA.replace("requires Ready(p);", ""),
        BORROWED_ARENA.replace("&mut Arena", "&Arena"),
    ] {
        rejected(&source);
    }
}

#[test]
fn modules_forward_borrowed_predicates_without_private_representation_access() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let declarations = &BORROWED_ARENA[..BORROWED_ARENA.find("fn main").unwrap()];
    let functions = &BORROWED_ARENA[BORROWED_ARENA.find("fn make").unwrap()..];
    let library = format!("module arena; {declarations}{functions}")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let main = &BORROWED_ARENA
        [BORROWED_ARENA.find("fn main").unwrap()..BORROWED_ARENA.find("fn make").unwrap()];
    let app = format!("module app; use arena::Arena; use arena::Ready; use arena::make; use arena::begin; use arena::fill; use arena::reset; use arena::take; {main}")
        .replace("let b = fill(view);", "let b = fill(relay(view));");
    let app = format!(
        "{app} fn relay(p:&mut Arena)->&mut Arena requires Ready(p); ensures Ready(result); {{ return p; }}"
    );
    for (source, valid) in [
        (app.clone(), true),
        (
            app.replace(
                "{ return p; }",
                "{ unfold Ready(p); fold Ready(p); return p; }",
            ),
            false,
        ),
        (
            app.replace("{ return p; }", "{ p.cursor = 0usize; return p; }"),
            false,
        ),
        (app.replace("requires Ready(p);", ""), false),
    ] {
        let inputs = [("app", source.as_str()), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        let preview = compiler.verify("app").unwrap();
        assert_eq!(preview.is_checked(), valid, "{preview:?}");
    }
}

const IN_PLACE: &str = include_str!("../spec/cases/verify/predicate-in-place.nera");

#[test]
fn in_place_postconditions_restore_real_parameter_loans() {
    let output = checked(IN_PLACE);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    checked(&IN_PLACE.replace(
        "let previous = reset(b);",
        "let first = reset(b); let previous = reset(b);",
    ));
    let branch = IN_PLACE.replace("reset(b);", "reset(b, true);").replace(
        "fn reset(p: &mut Arena)",
        "fn reset(p: &mut Arena, choose: bool)",
    );
    checked(&branch.replace("p.cursor = 0usize;\n    fold Ready(p);\n    return 0;", "if (choose) { p.cursor = 0usize; } else { p.cursor = 1usize; }\n    fold Ready(p);\n    return 0;"));
    // A postcondition can establish a new instance from the actual body.
    let establish = IN_PLACE.replace(
        "let view = begin(&mut *a);",
        "let view = &mut *a; let status = start(view);",
    );
    checked(&format!(
        "{establish} fn start(p:&mut Arena)->u64 ensures Ready(p); {{ p.cursor=0usize; fold Ready(p); return 0; }}"
    ));
}

#[test]
fn in_place_postconditions_reject_missing_proofs_wrong_carriers_and_loan_escape() {
    for source in [
        IN_PLACE.replace("ensures Ready(p);", ""),
        IN_PLACE.replace("    fold Ready(p);\n    return 0;", "    return 0;"),
        IN_PLACE.replace(
            "p.cursor = 0usize;\n    fold Ready(p);\n    return 0;",
            "p.cursor = 9usize;\n    fold Ready(p);\n    return 0;",
        ),
        IN_PLACE.replace("ensures Ready(p);", "ensures Ready(p); ensures Ready(p);"),
        IN_PLACE.replace(
            "let previous = reset(b);",
            "free(a); let previous = reset(b);",
        ),
        IN_PLACE.replace("fn reset(p: &mut Arena)", "fn reset(p: Own<Arena>)"),
        IN_PLACE.replace("fn reset(p: &mut Arena)", "fn reset(p: &Arena)"),
        IN_PLACE.replace(
            "fn take(p: &mut Arena) -> &mut [u64; 8]\nrequires Ready(p);",
            "fn take(p: &mut Arena) -> &mut [u64; 8]\nrequires Ready(p); ensures Ready(p);",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn in_place_metadata_is_independently_checked() {
    let output = accepted(IN_PLACE);
    for mutation in 0..4 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let mut specs = spec_tables(&unit);
        let interface = specs
            .predicate_interfaces
            .iter_mut()
            .find(|i| i.in_place)
            .unwrap();
        match mutation {
            0 => interface.ensures = false,
            1 => interface.bindings[0].0 += 1,
            2 => interface.bindings[0].1 = 0,
            3 => interface.in_place = false,
            _ => unreachable!(),
        }
        unit.specs = VirSpecEnvironment::from_tables(specs);
        assert!(unit.validate().is_err(), "mutation {mutation}");
    }
    for mutation in 0..3 {
        let mut tables = hir_tables(output.hir().unwrap());
        let interface = tables
            .specs
            .predicate_interfaces
            .iter_mut()
            .find(|i| i.in_place)
            .unwrap();
        match mutation {
            0 => interface.ensures = false,
            1 => interface.parameters[0] = 99,
            2 => interface.in_place = false,
            _ => unreachable!(),
        }
        assert!(HirProgram::from_tables(tables).is_err());
    }
}

#[test]
fn private_predicates_can_be_restored_in_place_by_public_calls() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let library = format!(
        "module arena; {}{}",
        &IN_PLACE[..IN_PLACE.find("fn main").unwrap()],
        &IN_PLACE[IN_PLACE.find("fn make").unwrap()..]
    )
    .replace("opaque struct", "pub opaque struct")
    .replace("predicate Ready", "pub predicate Ready")
    .replace("fn ", "pub fn ");
    let main = &IN_PLACE[IN_PLACE.find("fn main").unwrap()..IN_PLACE.find("fn make").unwrap()];
    let app = format!("module app; use arena::Arena; use arena::Ready; use arena::make; use arena::begin; use arena::fill; use arena::reset; use arena::take; {main}")
        .replace("reset(b)", "relay(b)");
    let app = format!(
        "{app} fn relay(p:&mut Arena)->u64 requires Ready(p); ensures Ready(p); {{ let status=reset(p); return status; }}"
    );
    for (source, valid) in [
        (app.clone(), true),
        (
            app.replace(
                "let status=reset(p);",
                "unfold Ready(p); let status=reset(p);",
            ),
            false,
        ),
        (app.replace("requires Ready(p);", ""), false),
    ] {
        let inputs = [("app", source.as_str()), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        let preview = compiler.verify("app").unwrap();
        assert_eq!(preview.is_checked(), valid, "{preview:?}");
    }
}

const ARENA_SLICE: &str = include_str!("../spec/cases/verify/predicate-arena-slice.nera");

#[test]
fn arena_returns_parameter_bounded_slices_after_restoring_its_representation() {
    let output = checked(ARENA_SLICE);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for source in [
        ARENA_SLICE.replace("take(b, 2usize)", "take(b, 9usize)"),
        ARENA_SLICE.replace("take(b, 2usize)", "take(b, 0usize)"),
        ARENA_SLICE.replace("let total = slice[0]", "free(a); let total = slice[0]"),
        ARENA_SLICE.replace(
            "let total = slice[0]",
            "let again = begin(&mut *a); let total = slice[0]",
        ),
        ARENA_SLICE.replace("p.cursor = 2usize;", "p.cursor = 9usize;"),
        ARENA_SLICE.replace("finish Ready(p);", ""),
    ] {
        rejected(&source);
    }
}

const RETURNED_VIEW: &str = include_str!("../spec/cases/verify/predicate-returned-view.nera");

#[test]
fn predicate_survives_a_returned_subview() {
    let output = checked(RETURNED_VIEW);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn returned_views_preserve_predicates_without_restoring_parent_access() {
    for source in [
        RETURNED_VIEW.replace(
            "let total = slice[0]",
            "let bad = reset(b); let total = slice[0]",
        ),
        RETURNED_VIEW.replace(
            "let total = slice[0]",
            "unfold Ready(b); let total = slice[0]",
        ),
        RETURNED_VIEW.replace("let total = slice[0]", "free(a); let total = slice[0]"),
        RETURNED_VIEW.replace(
            "let total = slice[0]",
            "let bad = take(b, 2usize); let total = slice[0]",
        ),
        RETURNED_VIEW.replace(
            "let total = slice[0]",
            "let bad = close(b); let total = slice[0]",
        ),
        RETURNED_VIEW.replace(
            "let total = slice[0]",
            "b.cursor = 1usize; let total = slice[0]",
        ),
        RETURNED_VIEW.replace("p.cursor = 2usize;", "p.cursor = 9usize;"),
        RETURNED_VIEW.replace(
            "let view = &mut p.slots[0usize..count];\n    fold Ready(p);",
            "let view = &mut p.slots[0usize..count];",
        ),
        RETURNED_VIEW.replace("take(b, 2usize)", "take(b, 9usize)"),
        RETURNED_VIEW.replace("take(b, 2usize)", "take(b, 0usize)"),
        RETURNED_VIEW.replace("let ended = close(b);", "let ended = 0;"),
        RETURNED_VIEW
            .replace(
                "-> &mut [u64]\nrequires Ready(p);",
                "-> &mut usize\nrequires Ready(p);",
            )
            .replace("&mut p.slots[0usize..count]", "&mut p.cursor"),
    ] {
        rejected(&source);
    }
    // Repeat the complete borrow/return cycle, and mutate unconstrained cells
    // while the parent remains sealed. The second call needs the restored loan.
    checked(
        &RETURNED_VIEW
            .replace(
                "let total = slice[0]",
                "slice[0] = 42; let total = slice[0]",
            )
            .replace(
                "let status = reset(b);",
                "let next = take(b, 2usize); let value = next[0]; let status = reset(b);",
            ),
    );
    // The same rule works for an ordinary fixed field projection.
    checked(
        &RETURNED_VIEW
            .replace(
                "-> &mut [u64]\nrequires Ready(p);",
                "-> &mut [u64; 8]\nrequires Ready(p);",
            )
            .replace("&mut p.slots[0usize..count]", "&mut p.slots"),
    );
}

#[test]
fn opaque_module_returns_a_view_and_retains_its_private_predicate() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    for (fixture, requires) in [
        (RETURNED_VIEW, ""),
        (HEAP_RANGE, "requires count <= 1usize;"),
        (HEAP_START, ""),
    ] {
        let start = fixture.find("fn main").unwrap();
        let end = fixture.find("fn make").unwrap();
        let library = format!("module arena; {}{}", &fixture[..start], &fixture[end..])
            .replace("opaque struct", "pub opaque struct")
            .replace("predicate Ready", "pub predicate Ready")
            .replace("fn ", "pub fn ");
        let app = format!(
            "module app; use arena::Arena; use arena::Ready; use arena::make; use arena::begin; use arena::fill; use arena::reset; use arena::take; use arena::close; {}",
            &fixture[start..end]
        );
        let forwarded = format!(
            "{} fn relay(p: &mut Arena, count: usize) -> &mut [u64] requires Ready(p); {requires} ensures Ready(p); {{ let view = take(p, count); return view; }}",
            app.replace("take(b,", "relay(b,")
        );
        let forwarded = if fixture == HEAP_START {
            format!(
                "{} fn relay(p:&mut Arena)->&mut [u64] requires Ready(p); ensures Ready(p); {{ let view=take(p); return view; }}",
                app.replace("take(b)", "relay(b)")
            )
        } else {
            forwarded
        };
        for app in [app, forwarded] {
            let inputs = [("app", app.as_str()), ("arena", library.as_str())]
                .into_iter()
                .map(|(name, text)| {
                    SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
                })
                .collect();
            let compiler = CompilerSession::modules(
                SourceDatabase::new(inputs).unwrap(),
                Default::default(),
                "app::main",
            )
            .unwrap();
            let preview = compiler.verify("app").unwrap();
            assert!(preview.is_checked(), "{preview:?}");
        }
    }
}

const HEAP_PREFIX: &str = include_str!("../spec/cases/verify/predicate-heap-prefix.nera");
#[test]
fn heap_cursor_selects_a_checked_returned_prefix() {
    let output = checked(HEAP_PREFIX);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn returned_heap_length_keeps_its_symbolic_result_identity() {
    let output = checked(HEAP_PREFIX);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    use nera::verifier::summary::{Knowledge, SummaryRange, SummaryValue};
    assert!(report.functions().values().any(|function| {
        let Knowledge::Known(alternatives) = &function.summary().normal_returns else { return false; };
        alternatives.iter().flat_map(|a| &a.worlds).flat_map(|w| &w.values).any(|mapping| {
            matches!(&mapping.value, SummaryValue::Permission(permission)
                if matches!(&permission.range, SummaryRange::Symbolic { end, .. } if end.result_terms == [(1, 8)]))
        })
    }));
}

#[test]
fn heap_prefix_does_not_assume_cursor_bounds_or_restore_parent_access() {
    for source in [
        HEAP_PREFIX.replace("p.cursor <= 8usize;", "p.cursor <= 9usize;"),
        // Omitting a redundant declaration bound is legal when the actual
        // returned length remains two. Make the returned slice truly empty.
        HEAP_PREFIX
            .replace("p.cursor >= 2usize;", "")
            .replace("p.cursor = 2usize;", "p.cursor = 0usize;"),
        HEAP_PREFIX.replace("p.cursor = 2usize;", "p.cursor = 9usize;"),
        HEAP_PREFIX.replace(
            "let view = &mut p.slots[0usize..p.cursor];",
            "p.cursor = 9usize; let view = &mut p.slots[0usize..p.cursor];",
        ),
        HEAP_PREFIX.replace(
            "let total = slice[0]",
            "let bad = reset(b); let total = slice[0]",
        ),
        HEAP_PREFIX.replace("let total = slice[0]", "free(a); let total = slice[0]"),
        HEAP_PREFIX.replace(
            "let view = &mut p.slots[0usize..p.cursor];",
            "let view = &mut p.slots[p.cursor..8usize];",
        ),
    ] {
        rejected(&source);
    }
    // Updating the heap after reading the endpoint must not change the saved length.
    let changed_cursor = HEAP_PREFIX.replace(
        "let view = &mut p.slots[0usize..p.cursor];",
        "let end = p.cursor; p.cursor = 8usize; let view = &mut p.slots[0usize..end];",
    );
    checked(&changed_cursor);
    rejected(&changed_cursor.replace("slice[1]", "slice[7]"));
    checked(&HEAP_PREFIX.replace(
        "let view = &mut p.slots[0usize..p.cursor];",
        "let end = p.cursor; let view = &mut p.slots[0usize..end];",
    ));

    checked(&HEAP_PREFIX.replace(
        "let status = reset(b);",
        "let next = take(b); let item = next[0]; let status = reset(b);",
    ));
    checked(&format!(
        "{} fn relay(p: &mut Arena)->&mut [u64] requires Ready(p); ensures Ready(p); {{ let view=take(p); return view; }}",
        HEAP_PREFIX.replace("take(b)", "relay(b)")
    ));
}

#[test]
fn forged_dynamic_prefix_length_is_rejected_by_independent_ssa_validation() {
    let output = accepted(HEAP_PREFIX);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let function = unit
        .runtime
        .functions
        .iter_mut()
        .find(|function| {
            unit.runtime
                .abis
                .function(function.id)
                .unwrap()
                .signature
                .borrow_result()
                .is_some_and(|r| {
                    matches!(
                        r.projection,
                        BorrowProjection::ArraySlice {
                            end: BorrowSliceBound::ReturnedLength,
                            ..
                        }
                    )
                })
        })
        .unwrap();
    let zero = function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find_map(|i| match i.instruction {
            VirInstruction::Constant {
                result,
                value: VirConstant::U64(0),
            } => Some(result.id),
            _ => None,
        })
        .unwrap();
    for block in &mut function.blocks {
        if let VirTerminator::Return { values } = &mut block.terminator.terminator {
            values[1] = zero;
        }
    }
    assert!(
        unit.into_validated().is_err(),
        "a returned slice must retain its constructor's paired length"
    );
}

#[test]
fn returned_length_coordinates_reject_invalid_summary_slots_and_low_budgets() {
    use nera::verifier::summary::{Knowledge, SummaryRange, SummaryValue};
    let output = checked(HEAP_PREFIX);
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, Default::default()).unwrap();
    let mut exercised = false;
    for (&id, function) in report.functions() {
        let mut summary = function.summary().clone();
        let Knowledge::Known(alternatives) = &mut summary.normal_returns else {
            continue;
        };
        for bound in alternatives
            .iter_mut()
            .flat_map(|a| &mut a.worlds)
            .flat_map(|w| &mut w.values)
            .filter_map(|mapping| {
                let SummaryValue::Permission(permission) = &mut mapping.value else {
                    return None;
                };
                let SummaryRange::Symbolic { end, .. } = &mut permission.range else {
                    return None;
                };
                (!end.result_terms.is_empty()).then_some(end)
            })
        {
            bound.result_terms[0].0 = usize::MAX;
            exercised = true;
        }
        if exercised {
            assert!(
                summary
                    .validate_structure(&unit, id, Default::default())
                    .is_err()
            );
            break;
        }
    }
    assert!(exercised);
    let config = CfgAnalysisConfig {
        max_summary_evidence: 0,
        ..Default::default()
    };
    let invalid = accepted(&HEAP_PREFIX.replace("p.cursor <= 8usize;", "p.cursor <= 9usize;"));
    let invalid = invalid.vir().unwrap().resolve().unwrap();
    assert!(!verify_program(&invalid, config).is_ok_and(|r| r.is_memory_checked_core0()));
}

const HEAP_RANGE: &str = include_str!("../spec/cases/verify/predicate-heap-range.nera");
#[test]
fn parameter_start_and_heap_end_preserve_the_returned_view() {
    let output = checked(HEAP_RANGE);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn dynamic_end_ranges_keep_both_coordinates_across_calls() {
    let relay = format!(
        "{} fn relay(p: &mut Arena, start: usize)->&mut [u64] requires Ready(p); requires start <= 1usize; ensures Ready(p); {{ let view=take(p,start); return view; }}",
        HEAP_RANGE.replace("take(b, 1usize)", "relay(b, 1usize)")
    );
    checked(&relay);
    let helper = format!(
        "{} fn endpoint(p: &mut Arena)->usize requires Ready(p); ensures Ready(p); {{ unfold Ready(p); let end=p.cursor; fold Ready(p); return end; }}",
        HEAP_RANGE.replace(
            "unfold Ready(p);\n    let view = &mut p.slots[start..p.cursor];",
            "let end=endpoint(p); unfold Ready(p); let view=&mut p.slots[start..end];"
        )
    );
    checked(&helper);

    checked(&HEAP_RANGE.replace("start..p.cursor", "1usize..p.cursor"));
    checked(&HEAP_RANGE.replace(
        "let status = reset(b);",
        "let next = take(b, 1usize); let value=next[0]; let status = reset(b);",
    ));
    let saved = HEAP_RANGE.replace(
        "let view = &mut p.slots[start..p.cursor];",
        "let end=p.cursor; p.cursor=8usize; let view=&mut p.slots[start..end];",
    );
    checked(&saved);
    for source in [
        HEAP_RANGE.replace("take(b, 1usize)", "take(b, 2usize)"),
        HEAP_RANGE.replace("requires start <= 1usize;", ""),
        HEAP_RANGE.replace("p.cursor >= 2usize;", "p.cursor >= 0usize;"),
        HEAP_RANGE.replace("p.cursor <= 8usize;", "p.cursor <= 9usize;"),
        HEAP_RANGE.replace("slice[0] + previous", "slice[7] + previous"),
        HEAP_RANGE.replace(
            "let total = slice[0]",
            "let bad=reset(b); let total = slice[0]",
        ),
        HEAP_RANGE.replace("let total = slice[0]", "free(a); let total = slice[0]"),
        saved.replace("slice[0] + previous", "slice[7] + previous"),
    ] {
        rejected(&source);
    }
}

#[test]
fn dynamic_slice_length_cannot_be_taken_from_another_call() {
    let source = format!(
        "{} fn relay(p: &mut Arena, start: usize)->&mut [u64] requires Ready(p); requires start <= 1usize; ensures Ready(p); {{ let first=take(p,start); let old_length=len(first); let status=reset(p); let second=take(p,start); return second; }}",
        HEAP_RANGE.replace("take(b, 1usize)", "relay(b, 1usize)")
    );
    let output = checked(&source);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let relay = unit.runtime.functions.last_mut().unwrap();
    let lengths = relay
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter_map(|i| {
            let VirInstruction::Call {
                target, results, ..
            } = &i.instruction
            else {
                return None;
            };
            let abi = target.abi.as_ref()?;
            abi.borrow_result()
                .is_some_and(|r| {
                    matches!(
                        r.projection,
                        BorrowProjection::ArraySlice {
                            end: BorrowSliceBound::ReturnedLength,
                            ..
                        }
                    )
                })
                .then(|| results[abi.results()[0].result_slots()[1] as usize].id)
        })
        .collect::<Vec<_>>();
    assert_eq!(lengths.len(), 2);
    for block in &mut relay.blocks {
        if let VirTerminator::Return { values } = &mut block.terminator.terminator {
            values[1] = lengths[0];
        }
    }
    assert!(unit.into_validated().is_err());
}

const HEAP_START: &str = include_str!("../spec/cases/verify/predicate-heap-start.nera");
#[test]
fn heap_start_preserves_the_actual_returned_range() {
    let output = checked(HEAP_START);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn heap_start_is_scoped_to_the_saved_view_and_can_be_forwarded() {
    checked(&format!(
        "{} fn relay(p:&mut Arena)->&mut [u64] requires Ready(p); ensures Ready(p); {{ let view=take(p); return view; }}",
        HEAP_START.replace("take(b)", "relay(b)")
    ));
    checked(&HEAP_START.replace(
        "let status = reset(b);",
        "let next=take(b); let value=next[0]; let status=reset(b);",
    ));
    checked(&format!(
        "{} fn endpoint(p:&mut Arena)->usize requires Ready(p); ensures Ready(p); {{ unfold Ready(p); let start=p.cursor; fold Ready(p); return start; }}",
        HEAP_START.replace(
            "unfold Ready(p);\n    let view = &mut p.slots[p.cursor..8usize];",
            "let start=endpoint(p); unfold Ready(p); let view=&mut p.slots[start..8usize];"
        )
    ));
    checked(&HEAP_START.replace("slice[0] + previous", "slice[3] + previous"));
    let saved = HEAP_START.replace(
        "let view = &mut p.slots[p.cursor..8usize];",
        "let start=p.cursor; p.cursor=4usize; let view=&mut p.slots[start..8usize];",
    );
    checked(&saved);
    checked(&HEAP_START.replace(
        "let view = &mut p.slots[p.cursor..8usize];",
        "let start=p.cursor; let view=&mut p.slots[start..start+2usize];",
    ));
    for source in [
        HEAP_START.replace("p.cursor <= 4usize;", "p.cursor <= 9usize;"),
        HEAP_START.replace("p.cursor <= 4usize;", ""),
        HEAP_START.replace("p.cursor..8usize", "p.cursor..1usize"),
        HEAP_START.replace("slice[0] + previous", "slice[7] + previous"),
        HEAP_START.replace("slice[0] + previous", "slice[4] + previous"),
        HEAP_START.replace(
            "let total = slice[0]",
            "let bad=reset(b); let total = slice[0]",
        ),
        HEAP_START.replace("let total = slice[0]", "free(a); let total = slice[0]"),
        HEAP_START.replace(
            "let total = slice[0]",
            "unfold Ready(b); let total = slice[0]",
        ),
        saved.replace("slice[0] + previous", "slice[7] + previous"),
    ] {
        rejected(&source);
    }
}

#[test]
fn heap_start_offset_summary_coordinates_are_typed() {
    use nera::verifier::summary::{Knowledge, SummaryValue};
    let output = checked(HEAP_START);
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, Default::default()).unwrap();
    let mut exercised = false;
    for (&id, function) in report.functions() {
        for bad_slot in [1, usize::MAX] {
            let mut summary = function.summary().clone();
            let Knowledge::Known(alternatives) = &mut summary.normal_returns else {
                continue;
            };
            let mut mutated = false;
            for bound in alternatives
                .iter_mut()
                .flat_map(|a| &mut a.worlds)
                .flat_map(|w| &mut w.values)
                .filter_map(|v| {
                    let SummaryValue::Pointer(p) = &mut v.value else {
                        return None;
                    };
                    p.offset_expression.as_mut()
                })
                .filter(|b| !b.result_offset_terms.is_empty())
            {
                bound.result_offset_terms[0].0 = bad_slot;
                mutated = true;
            }
            if mutated {
                assert!(
                    summary
                        .validate_structure(&unit, id, Default::default())
                        .is_err()
                );
                exercised = true;
            }
        }
    }
    assert!(exercised);
}

#[test]
fn heap_start_pointer_and_length_cannot_be_mixed_between_calls() {
    let source = format!(
        "{} fn relay(p:&mut Arena)->&mut [u64] requires Ready(p); ensures Ready(p); {{ let first=take(p); let old_length=len(first); let status=reset(p); let second=take(p); return second; }}",
        HEAP_START.replace("take(b)", "relay(b)")
    );
    let output = checked(&source);
    for slot in [0, 1] {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let relay = unit.runtime.functions.last_mut().unwrap();
        let results = relay
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter_map(|i| {
                let VirInstruction::Call {
                    target, results, ..
                } = &i.instruction
                else {
                    return None;
                };
                let abi = target.abi.as_ref()?;
                abi.borrow_result()
                    .is_some_and(|r| {
                        matches!(
                            r.projection,
                            BorrowProjection::ArraySlice {
                                start: BorrowSliceBound::ReturnedOffset,
                                ..
                            }
                        )
                    })
                    .then(|| results[abi.results()[0].result_slots()[slot] as usize].id)
            })
            .collect::<Vec<_>>();
        assert_eq!(results.len(), 2);
        for block in &mut relay.blocks {
            if let VirTerminator::Return { values } = &mut block.terminator.terminator {
                values[slot] = results[0];
            }
        }
        assert!(unit.into_validated().is_err());
    }
}

const PARTIAL_FIELDS: &str = include_str!("../spec/cases/verify/predicate-partial-fields.nera");
#[test]
fn partial_field_initialization_survives_owner_calls() {
    rejected("predicate Cell(p:ptr<u64>) { owns(p); p <= 8; } fn main()->u64 {return 0;}");
    let output = checked(PARTIAL_FIELDS);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for source in [
        PARTIAL_FIELDS.replace("p.slots[1] = 0;", ""),
        PARTIAL_FIELDS.replace("p.slots[0] + p.slots[1]", "p.slots[0] + p.slots[2]"),
        PARTIAL_FIELDS.replace(
            "initialized(p.cursor, 0usize..1usize)",
            "initialized(p.cursor, 0usize..2usize)",
        ),
        PARTIAL_FIELDS.replace(
            "initialized(p.slots, 0usize..2usize)",
            "initialized(p.slots, 0usize..9usize)",
        ),
        PARTIAL_FIELDS.replace("p.slots, 0usize..2usize", "p.slots[8], 0usize..1usize"),
        PARTIAL_FIELDS.replace(
            "p.slots, 0usize..2usize",
            "p.slots[p.cursor], 0usize..1usize",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn nested_predicate_fields_use_canonical_offsets_and_selected_extents() {
    let source=PARTIAL_FIELDS.replace("opaque struct Arena {\n    cursor: usize,\n    slots: [u64; 8],\n}",
        "struct Block { unused: bool, cursor:usize, slots:[u64;8], } opaque struct Arena { blocks:[Block;2], }")
        .replace("p.cursor", "p.blocks[1].cursor").replace("p.slots", "p.blocks[1].slots");
    assert_ne!(source, PARTIAL_FIELDS);
    let output = checked(&source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for offset in [80, 89, 160] {
        let mut tables = hir_tables(output.hir().unwrap());
        tables.predicates[0].representation.as_mut().unwrap().bounds[0].offset = offset;
        assert!(HirProgram::from_tables(tables).is_err());
        let mut unit = output.vir().unwrap().as_unit().clone();
        unit.specs.predicates_mut()[0]
            .representation
            .as_mut()
            .unwrap()
            .bounds[0]
            .offset = offset;
        assert!(unit.into_validated().is_err());
    }
    for invalid in [
        source.replace(
            "initialized(p.blocks[1].slots",
            "initialized(p.blocks[0].slots",
        ),
        source.replace("p.blocks[1].cursor <=", "p.blocks[1].unused <="),
        source.replace(
            "initialized(p.blocks[1].cursor, 0usize..1usize)",
            "initialized(p.blocks[1].cursor, 0usize..2usize)",
        ),
        source.replace(
            "initialized(p.blocks[1].slots",
            "initialized(p.blocks[2].slots",
        ),
    ] {
        rejected(&invalid);
    }
}

#[test]
fn partial_field_predicates_preserve_module_privacy() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let library = format!(
        "module lib; {}",
        PARTIAL_FIELDS
            .replace("opaque struct", "pub opaque struct")
            .replace("predicate Ready", "pub predicate Ready")
            .replace("fn main", "fn example")
            .replace("fn make", "pub fn make")
            .replace("fn update", "pub fn update")
            .replace("fn destroy", "pub fn destroy")
    );
    let library = format!(
        "{library} pub opaque struct Hidden {{ word:usize, }} pub struct Wrapper {{ hidden:Hidden, }}"
    );
    let app="module app; use lib::Wrapper; use lib::Arena; use lib::Ready; use lib::make; use lib::update; use lib::destroy;
        fn main()->u64 {let a=make(); let b=relay(a); return destroy(b);}
        fn relay(p:Own<Arena>)->Own<Arena> requires Ready(p); ensures Ready(result); {return update(p);}";
    for (source, valid) in [
        (app.to_owned(), true),
        (
            format!(
                "{app} predicate Peek(p:ptr<Arena>) {{owns(p); initialized(p.cursor,0usize..1usize);}}"
            ),
            false,
        ),
        (
            format!(
                "{app} predicate Peek(p:ptr<Arena>) {{owns(p); initialized(p.slots,0usize..2usize);}}"
            ),
            false,
        ),
        (
            format!(
                "{app} predicate Peek(p:ptr<Wrapper>) {{owns(p); initialized(p.hidden.word,0usize..1usize);}}"
            ),
            false,
        ),
        (
            format!("{app} predicate Peek(p:ptr<Wrapper>) {{owns(p); p.hidden.word <= 8usize;}}"),
            false,
        ),
    ] {
        let inputs = [("app", source.as_str()), ("lib", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

const DYNAMIC_PREFIX: &str = include_str!("../spec/cases/verify/predicate-dynamic-prefix.nera");
#[test]
fn heap_cursor_tracks_initialized_prefix_across_owner_calls() {
    let output = checked(DYNAMIC_PREFIX);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn dynamic_prefix_requires_real_initialization_and_bounded_cursor() {
    for source in [
        DYNAMIC_PREFIX.replace("p.slots[n]=value;", ""),
        DYNAMIC_PREFIX.replace("p.slots[n]=value;", "p.slots[n+1usize]=value;"),
        DYNAMIC_PREFIX.replace("p.cursor=n+1usize;", "p.cursor=8usize;"),
        DYNAMIC_PREFIX.replace("p.slots[n]=value;", "p.slots[0]=value;"),
        DYNAMIC_PREFIX.replace("p.cursor=n+1usize;", "p.cursor=n+2usize;"),
        DYNAMIC_PREFIX.replace("p.cursor=0usize;", "p.cursor=1usize;"),
        DYNAMIC_PREFIX.replace("p.cursor=0usize;", ""),
        DYNAMIC_PREFIX.replace("if n>=2usize", "if n>=1usize"),
        DYNAMIC_PREFIX.replace("p.slots[0]+p.slots[1]", "p.slots[0]+p.slots[n]"),
        DYNAMIC_PREFIX.replace("p.cursor <= 8usize;", "p.cursor <= 9usize;"),
        DYNAMIC_PREFIX.replace("p.cursor <= 8usize;", ""),
        DYNAMIC_PREFIX.replace("0usize..p.cursor", "1usize..p.cursor"),
        DYNAMIC_PREFIX.replace("0usize..p.cursor", "0usize..p.slots[0]"),
        DYNAMIC_PREFIX.replace("fold Ready(p);\n    return p;", "return p;"),
        DYNAMIC_PREFIX.replace("free(p);", ""),
    ] {
        rejected(&source);
    }
    let output = accepted(&DYNAMIC_PREFIX.replace("p.slots[n]=value;", ""));
    let config = CfgAnalysisConfig {
        max_summary_evidence: 0,
        ..Default::default()
    };
    assert!(
        !verify_program(&output.vir().unwrap().resolve().unwrap(), config)
            .is_ok_and(|r| r.is_memory_checked_core0())
    );
}

#[test]
fn dynamic_prefix_geometry_is_rechecked_in_hir_and_vir() {
    let output = accepted(DYNAMIC_PREFIX);
    for mutation in 0..5 {
        let mut hir = hir_tables(output.hir().unwrap());
        let mut unit = output.vir().unwrap().as_unit().clone();
        let a = &mut hir.predicates[0].representation.as_mut().unwrap().prefixes[0];
        let b = &mut unit.specs.predicates_mut()[0]
            .representation
            .as_mut()
            .unwrap()
            .prefixes[0];
        match mutation {
            0 => {
                a.count = nera::PredicatePrefixCount::Stored { offset: 8 };
                b.count = nera::PredicatePrefixCount::Stored { offset: 8 };
            }
            1 => {
                a.array_offset = 0;
                b.array_offset = 0;
            }
            2 => {
                a.length = 9;
                b.length = 9;
            }
            3 => {
                a.stride = 1;
                b.stride = 1;
            }
            4 => {
                a.resource = 99;
                b.resource = 99;
            }
            _ => unreachable!(),
        }
        assert!(HirProgram::from_tables(hir).is_err());
        assert!(unit.into_validated().is_err());
    }
}

#[test]
fn dynamic_prefix_capacity_and_module_forwarding() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let start = DYNAMIC_PREFIX.find("fn main").unwrap();
    let end = DYNAMIC_PREFIX.find("fn make").unwrap();
    let library = format!(
        "module lib; {}{}",
        &DYNAMIC_PREFIX[..start],
        &DYNAMIC_PREFIX[end..]
    )
    .replace("opaque struct", "pub opaque struct")
    .replace("predicate Ready", "pub predicate Ready")
    .replace("fn ", "pub fn ");
    let app=format!("module app; use lib::Arena; use lib::Ready; use lib::make; use lib::append; use lib::destroy; {}
        fn relay(p:Own<Arena>,value:u64)->Own<Arena> requires Ready(p); ensures Ready(result); {{return append(p,value);}}",
        DYNAMIC_PREFIX[start..end].replace("append(","relay("));
    let inputs = [("app", app.as_str()), ("lib", library.as_str())]
        .into_iter()
        .map(|(name, text)| {
            SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
        })
        .collect();
    let compiler = CompilerSession::modules(
        SourceDatabase::new(inputs).unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap();
    assert!(compiler.verify("app").unwrap().is_checked());
    let mut main = "fn main()->u64 { let p0=make();".to_owned();
    for i in 1..=9 {
        main.push_str(&format!(
            "let p{i}=append(p{},{});",
            i - 1,
            if i == 1 { 20 } else { 22 }
        ));
    }
    main.push_str("return destroy(p9);}");
    let source = format!(
        "{}{}{}",
        &DYNAMIC_PREFIX[..start],
        main,
        &DYNAMIC_PREFIX[end..]
    );
    let output = checked(&source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn scalar_backing_updates_preserve_only_the_existing_heap_prefix() {
    for body in [
        "p.slots[0]=21; p.slots[1]=21;",
        "let n=p.cursor; if n<8usize { p.slots[n]=99; }",
        "let n=p.cursor; let view=&mut p.slots[0usize..n]; if len(view)>=2usize { view[0]=21; view[1]=21; }",
    ] {
        let source = DYNAMIC_PREFIX
            .replace("return destroy(c);", "let d=edit(c); return destroy(d);")
            + &format!(
                "\nfn edit(p:Own<Arena>)->Own<Arena> requires Ready(p); ensures Ready(result); {{ unfold Ready(p); {body} fold Ready(p); return p; }}"
            );
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
        // Preserving the old prefix does not justify advancing its endpoint.
        rejected(&source.replace(
            "fold Ready(p); return p;",
            "p.cursor=8usize; fold Ready(p); return p;",
        ));
    }
}

#[test]
fn partial_backing_updates_through_local_slices_keep_the_owner_contract() {
    let source = include_str!("../spec/cases/verify/predicate-prefix-update.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for (from, to) in [
        ("p.slots[7]=7;", "p.slots[8]=7;"),
        ("p.slots[7]=7;", "free(p); p.slots[7]=7;"),
        ("p.slots[7]=7;", "p.slots[7]=7; p.cursor=8usize;"),
        ("p.slots[7]=7;", "p.slots[7]=7; let hole=p.slots[6];"),
        ("if len(view)>=2usize", "if len(view)>=1usize"),
        ("view[1]=21;", "view[len(view)]=21;"),
        ("view[0]=21;", "p.slots[0]=21; view[0]=21;"),
        ("fold Ready(p);\n    return p;\n}", "return p;\n}"),
    ] {
        rejected(&source.replace(from, to));
    }
}

const PREFIX_CALL: &str = include_str!("../spec/cases/verify/predicate-prefix-call.nera");

#[test]
fn partially_initialized_owner_frames_a_borrowed_slice_call() {
    let output = checked(PREFIX_CALL);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.summary().state == nera::verifier::summary::SummaryState::Closed)
    );
    assert!(report.functions().values().any(|f| {
        f.summary().call_uses.iter().any(|c| {
            c.symbol == "paint" && c.outcome == nera::verifier::summary::CallSummaryOutcome::Applied
        })
    }));
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    let returned = PREFIX_CALL
        .replace(
            "paint(view);",
            "let child=paint(view); let size=len(child);",
        )
        .replace(
            "fn paint(view:&mut [u64]) {",
            "fn paint(view:&mut [u64])->&mut [u64] {",
        )
        .replace("    return;", "    return view;");
    checked(&returned);
}

#[test]
fn borrowed_slice_call_frames_do_not_hide_missing_initialization_or_authority() {
    for (from, to) in [
        ("if n>=2usize", "if n>=1usize"),
        ("if len(view)>=2usize", "if len(view)>=1usize"),
        ("p.slots[n]=value;", ""),
        (
            "paint(view);",
            "paint(view); unfold Ready(p); p.cursor=8usize; fold Ready(p);",
        ),
        ("paint(view);", "unfold Ready(p); paint(view);"),
        ("paint(view);", "paint(view); let hole=p.slots[6];"),
        ("paint(view);", "paint(view); free(p); let x=view[0];"),
        ("paint(view);", "paint(view); p.slots[0]=0; let x=view[0];"),
        ("view[1]=21;", "view[len(view)]=21;"),
    ] {
        rejected(&PREFIX_CALL.replace(from, to));
    }
}

#[test]
fn a_private_partial_owner_can_call_an_external_slice_worker() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    for source in [
        PREFIX_CALL,
        include_str!("../spec/cases/verify/predicate-dynamic-call.nera"),
        include_str!("../spec/cases/verify/predicate-symbolic-write.nera"),
    ] {
        let (owner, worker) = source.split_once("fn paint").unwrap();
        let owner = format!(
            "module lib; use worker::paint; {}",
            owner
                .replace("opaque struct", "pub opaque struct")
                .replace("fn main", "pub fn example")
        );
        let app = "module app; use lib::example; fn main()->u64 { return example(); }";
        for valid in [true, false] {
            let worker = format!(
                "module worker; pub fn paint{}",
                if valid {
                    worker.to_owned()
                } else {
                    worker
                        .replace("if len(view)>=2usize", "if len(view)>=1usize")
                        .replace("index<len(view)", "index<=len(view)")
                }
            );
            let inputs = [
                ("app", app),
                ("lib", owner.as_str()),
                ("worker", worker.as_str()),
            ]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
            let compiler = CompilerSession::modules(
                SourceDatabase::new(inputs).unwrap(),
                Default::default(),
                "app::main",
            )
            .unwrap();
            assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
        }
    }
}

#[test]
fn a_dynamic_initialized_prefix_maps_into_a_closed_slice_call() {
    let source = include_str!("../spec/cases/verify/predicate-dynamic-call.nera");

    let output = checked(source);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.summary().state == nera::verifier::summary::SummaryState::Closed)
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let replay =
        nera::verifier::relation::audit::RelationReplayCache::new(&resolved, Default::default())
            .unwrap();
    let mut multiple = false;
    for (&id, function) in report.functions() {
        let cfg = function.cfg();
        assert!(replay.accepts_memory_trace(
            id,
            cfg.provenance_evidence(),
            cfg.relation_queries(),
            cfg.relation_evidence()
        ));
        for event in cfg
            .provenance_evidence()
            .iter()
            .filter(|e| e.outcome_ordinal > 0)
        {
            multiple = true;
            assert!(replay.accepts_provenance(event));
            let mut changed = event.clone();
            changed.outcome_ordinal = usize::MAX;
            assert!(!replay.accepts_provenance(&changed));
        }
        if let Some(index) = cfg
            .provenance_evidence()
            .iter()
            .position(|e| e.outcome_ordinal > 0)
        {
            let mut missing = cfg.provenance_evidence().to_vec();
            missing.remove(index);
            assert!(!replay.accepts_memory_trace(
                id,
                &missing,
                cfg.relation_queries(),
                cfg.relation_evidence()
            ));
        }
    }
    assert!(multiple);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn dynamic_call_mapping_does_not_initialize_the_possible_envelope() {
    let source = include_str!("../spec/cases/verify/predicate-dynamic-call.nera");
    for (from, to) in [
        ("p.slots[n]=value;", ""),
        ("p.slots[0usize..n]", "p.slots[0usize..n+1usize]"),
        ("if len(view)>=2usize", "if len(view)>=1usize"),
        (
            "paint(view);",
            "paint(view); unfold Ready(p); let hole=p.slots[6]; fold Ready(p);",
        ),
        (
            "paint(view);",
            "paint(view); unfold Ready(p); p.cursor=8usize; fold Ready(p);",
        ),
        ("view[1]=21;", "view[len(view)]=21;"),
    ] {
        rejected(&source.replace(from, to));
    }
    checked(include_str!(
        "../spec/cases/verify/predicate-symbolic-write.nera"
    ));
    let invalid = accepted(&source.replace("p.slots[n]=value;", ""));
    let config = CfgAnalysisConfig {
        max_summary_evidence: 0,
        ..Default::default()
    };
    assert!(
        !verify_program(&invalid.vir().unwrap().resolve().unwrap(), config)
            .is_ok_and(|r| r.is_memory_checked_core0())
    );
}

#[test]
fn parameter_selected_writes_preserve_only_the_actual_initialized_slice() {
    let source = include_str!("../spec/cases/verify/predicate-symbolic-write.nera");
    let output = checked(source);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.summary().state == nera::verifier::summary::SummaryState::Closed)
    );
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    let unknown_index = source
        .replace("let d=edit(c);", "let d=edit(c,1usize);")
        .replace("fn edit(p:Own<Arena>)", "fn edit(p:Own<Arena>,index:usize)")
        .replace("paint(view,1usize);", "paint(view,index);");
    checked(&unknown_index);
    let returned = unknown_index
        .replace(
            "paint(view,index);",
            "let child=paint(view,index); if index<len(child) { let value=child[index]; }",
        )
        .replace(
            "fn paint(view:&mut [u64],index:usize) {",
            "fn paint(view:&mut [u64],index:usize)->&mut [u64] {",
        )
        .replace("    return;", "    return view;");
    checked(&returned);
}

#[test]
fn symbolic_writes_forget_contents_without_filling_initialization_holes() {
    let source = include_str!("../spec/cases/verify/predicate-symbolic-write.nera");
    for (from, to) in [
        ("p.slots[n]=value;", ""),
        ("index<len(view)", "index<=len(view)"),
        ("view[index]=21;", "view[index+1usize]=21;"),
        ("p.slots[0usize..n]", "p.slots[0usize..n+1usize]"),
        (
            "paint(view,1usize);",
            "paint(view,1usize); unfold Ready(p); let hole=p.slots[6]; fold Ready(p);",
        ),
        (
            "paint(view,1usize);",
            "paint(view,1usize); unfold Ready(p); p.cursor=8usize; fold Ready(p);",
        ),
        (
            "paint(view,1usize);",
            "paint(view,1usize); free(p); let x=view[0];",
        ),
    ] {
        rejected(&source.replace(from, to));
    }
    // A stale scalar value would hide this bad read behind a false branch.
    let stale = source.replace("p.slots[7]=7;", "p.slots[7]=7; p.slots[0]=20;")
        .replace("paint(view,1usize);", "paint(view,1usize); unfold Ready(p); if p.slots[0]!=20 { let hole=p.slots[6]; } fold Ready(p);");
    accepted(&stale);
    rejected(&stale);
}

#[test]
fn a_full_prefix_uses_the_same_symbolic_write_interface() {
    let source = include_str!("../spec/cases/verify/predicate-full-prefix-call.nera");
    let output = checked(source);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.summary().state == nera::verifier::summary::SummaryState::Closed)
    );
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn empty_partial_and_full_prefixes_share_one_owner_api() {
    let template = include_str!("../spec/cases/verify/predicate-symbolic-write.nera");
    let body_start = template.find("fn main()->u64 {").unwrap();
    let body_end = template[body_start..].find("\nfn make").unwrap() + body_start;
    for count in 0..=8 {
        let mut main = String::from("fn main()->u64 { let a0=make();");
        for i in 0..count {
            main.push_str(&format!("let a{}=append(a{},21);", i + 1, i));
        }
        main.push_str(&format!(
            "let edited=edit(a{count}); return destroy(edited); }}\n"
        ));
        let source = format!(
            "{}{}{}",
            &template[..body_start],
            main,
            &template[body_end..]
        )
        .replace(
            "if n>=2usize {\n        let view",
            "if true {\n        let view",
        );
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(if count >= 2 { 42 } else { 0 })]
        );
    }
}

#[test]
fn full_prefix_retry_never_substitutes_the_declaration_for_real_storage() {
    let source = include_str!("../spec/cases/verify/predicate-full-prefix-call.nera");
    for (from, to) in [
        ("p.slots=[0,0,0,0,0,0,0,0];", ""),
        ("p.slots=[0,0,0,0,0,0,0,0];", "p.slots[0]=0; p.slots[1]=0;"),
        ("p.cursor=8usize;", "p.cursor=7usize;"),
        ("index<len(view)", "index<=len(view)"),
        ("view[index]=21;", "view[index+1usize]=21;"),
    ] {
        rejected(&source.replace(from, to));
    }
    // A failed first transaction must not retain a callee allocation instance.
    let fresh = source.replace(
        "if index<len(view)",
        "let temporary=alloc<u64>(1); free(temporary); if index<len(view)",
    );
    let output = checked(&fresh);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn borrowed_prefix_contracts_expose_only_their_initialized_representation() {
    let source = include_str!("../spec/cases/verify/predicate-borrow-prefix.nera");
    let output = checked(source);
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, Default::default()).unwrap();
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.summary().state == nera::verifier::summary::SummaryState::Closed)
    );
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    for bad in [
        source.replace("let n=p.cursor;", "let hidden=p.slots[7]; let n=p.cursor;"),
        source.replace("p.slots[n]=value;", ""),
        source.replace("p.slots=[0;8];", ""),
        source.replace("p.cursor=n+1usize;", "p.cursor=n+2usize;"),
        source.replace("if n>=2usize", "if n>=1usize"),
        source.replace("if n<8usize", "if n<=8usize"),
        source.replace("fold Ready(p);\n        return p;", "return p;"),
    ] {
        rejected(&bad);
    }
}

#[test]
fn borrowed_prefixes_restore_in_place_without_claiming_the_full_backing() {
    let source = include_str!("../spec/cases/verify/predicate-borrow-prefix.nera");
    let (before, append) = source.split_once("fn append").unwrap();
    let (append, after) = append.split_once("// Releasing").unwrap();
    let source = format!(
        "{before}fn append{}// Releasing{after}",
        append
            .replace("->&mut Arena", "->u64")
            .replace("ensures Ready(result);", "ensures Ready(p);")
            .replace("return p;", "return 0;")
    )
    .replace("let b=append(view,20);", "let first=append(view,20);")
    .replace("let c=append(b,22);", "let second=append(view,22);")
    .replace("finish_view(c)", "finish_view(view)");
    let output = checked(&source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("ensures Ready(p);", ""));
    rejected(&source.replace("fold Ready(p);\n        return 0;", "return 0;"));
}

#[test]
fn borrowed_prefix_interfaces_cover_empty_partial_and_full_states() {
    let source = include_str!("../spec/cases/verify/predicate-borrow-prefix.nera");
    let main_start = source.find("fn main()").unwrap();
    let main_end = source.find("fn make()").unwrap();
    for count in 0..=8 {
        let mut main = String::from("fn main()->u64 { let a=make(); let v0=begin(&mut *a);\n");
        for i in 0..count {
            main.push_str(&format!("let v{}=append(v{i},21);\n", i + 1));
        }
        main.push_str(&format!(
            "let total=finish_view(v{count}); free(a); return total; }}\n"
        ));
        let program = format!("{}{main}{}", &source[..main_start], &source[main_end..]);
        let output = checked(&program);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(if count < 2 { 0 } else { 42 })]
        );
    }
}

#[test]
fn borrowed_prefix_contracts_cross_an_opaque_module_boundary() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-borrow-prefix.nera");
    let (declarations, body) = source.split_once("fn main()").unwrap();
    let (main, functions) = body.split_once("fn make()").unwrap();
    let library = format!("module arena; {declarations}fn make(){functions}")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let app = format!(
        "module app; use arena::Arena; use arena::Ready; use arena::make; use arena::begin; use arena::append; use arena::finish_view; fn main(){main}"
    );
    for valid in [true, false] {
        let library = if valid {
            library.clone()
        } else {
            library.replace("p.slots[n]=value;", "")
        };
        let inputs = [("app", app.as_str()), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn a_partial_owner_hands_its_predicate_to_a_whole_mutable_loan_and_back() {
    let source = include_str!("../spec/cases/verify/predicate-owner-borrow.nera");
    let output = checked(source);
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, Default::default()).unwrap();
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.summary().state == nera::verifier::summary::SummaryState::Closed)
    );
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn whole_predicate_handoffs_reject_missing_returns_and_conflicting_owner_access() {
    let source = include_str!("../spec/cases/verify/predicate-owner-borrow.nera");
    for bad in [
        source.replace("p.slots[n]=value;", ""),
        source.replace("ensures Ready(p);", ""),
        source.replace("fold Ready(p);\n        return 0;", "return 0;"),
        source.replace("p.cursor=n+1usize;", "p.cursor=n+2usize;"),
        source.replace("let n=p.cursor;", "let hole=p.slots[7]; let n=p.cursor;"),
        source.replace("let ignored=append(&mut *p,value);", "let view=&mut *p; unfold Ready(p); let ignored=append(view,value);"),
        source.replace("let ignored=append(&mut *p,value);", "let view=&mut *p; free(p); let ignored=append(view,value);"),
        source.replace("let ignored=append(&mut *p,value);", "let view=&mut *p; let moved=p; let ignored=append(view,value);"),
        source.replace("let ignored=append(&mut *p,value);", "let left=&mut *p; let right=&mut *p; let x=append(left,value); let y=append(right,value);"),
        source.replace("let ignored=append(&mut *p,value);", "unfold Ready(p); let ignored=append(&mut *p,value);"),
    ] {
        rejected(&bad);
    }
    let output = accepted(source);
    for config in [
        CfgAnalysisConfig {
            max_active_loans_per_case: 0,
            ..Default::default()
        },
        CfgAnalysisConfig {
            max_aliases_per_loan: 0,
            ..Default::default()
        },
        CfgAnalysisConfig {
            max_summary_evidence: 0,
            ..Default::default()
        },
    ] {
        assert!(
            !verify_program(&output.vir().unwrap().resolve().unwrap(), config)
                .is_ok_and(|r| r.is_memory_checked_core0())
        );
    }
}

#[test]
fn whole_predicate_handoffs_restore_after_returned_references_and_branches() {
    let source = include_str!("../spec/cases/verify/predicate-owner-borrow.nera");
    let returned = source
        .replace(
            "fn append(p:&mut Arena,value:u64)->u64",
            "fn append(p:&mut Arena,value:u64)->&mut Arena",
        )
        .replace("ensures Ready(p);", "ensures Ready(result);");
    let (before, append) = returned.split_once("fn append(").unwrap();
    let (append, after) = append.split_once("fn destroy(").unwrap();
    let returned = format!(
        "{before}fn append({}fn destroy({after}",
        append.replace("return 0;", "return p;")
    );
    let branched = source.replace(
        "let ignored=append(&mut *p,value);",
        "if value<21 { let left=append(&mut *p,value); } else { let right=append(&mut *p,value); }",
    );
    for program in [returned, branched] {
        let output = checked(&program);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn an_opaque_partial_owner_can_be_borrowed_by_a_client_module() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-owner-borrow.nera");
    let (declarations, body) = source.split_once("fn main()").unwrap();
    let (_, functions) = body.split_once("fn make()").unwrap();
    let library = format!("module arena; {declarations}fn make(){functions}")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let main = "module app; use arena::Arena; use arena::Ready; use arena::make; use arena::append; use arena::destroy;
        fn main()->u64 { let p=make(); let first=append(&mut *p,20); let second=append(&mut *p,22); return destroy(p); }";
    for valid in [true, false] {
        let library = if valid {
            library.clone()
        } else {
            library.replace("p.slots[n]=value;", "")
        };
        let inputs = [("app", main), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn sealed_mutable_predicates_can_be_reborrowed_through_nested_calls() {
    let source = include_str!("../spec/cases/verify/predicate-owner-borrow.nera");
    let source = source.replace(
        "let ignored=append(&mut *p,value);",
        "let ignored=relay(&mut *p,value);",
    );
    let source = format!(
        "{source}\nfn relay(p:&mut Arena,value:u64)->u64 requires Ready(p); ensures Ready(p); {{ let ignored=relay_inner(&mut *p,value); return 0; }}\nfn relay_inner(p:&mut Arena,value:u64)->u64 requires Ready(p); ensures Ready(p); {{ let ignored=append(&mut *p,value); return 0; }}"
    );
    let local = source.replace("let ignored=append(&mut *p,value); return 0;", "let child=&mut *p; let grandchild=&mut *child; let ignored=append(grandchild,value); return 0;");
    let local_output = checked(&local);
    assert_eq!(
        interpret(local_output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    assert!(
        !verify_program(
            &local_output.vir().unwrap().resolve().unwrap(),
            CfgAnalysisConfig {
                max_reborrow_depth: 0,
                ..Default::default()
            }
        )
        .is_ok_and(|r| r.is_memory_checked_core0())
    );
    let output = checked(&source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for bad in [
        source.replace("let ignored=append(&mut *p,value); return 0;", "let child=&mut *p; unfold Ready(p); let ignored=append(child,value); return 0;"),
        source.replace("p.slots[n]=value;", ""),
        source.replace("let ignored=append(&mut *p,value); return 0;", "let child=&mut *p; let other=&mut *p; let first=append(child,value); let second=append(other,value); return 0;"),
    ] { rejected(&bad); }
}

#[test]
fn sealed_owners_follow_local_aggregate_storage_and_moves() {
    let source = include_str!("../spec/cases/verify/predicate-owner-borrow.nera");
    for transfer in [
        "let box=Box { value:a }; let extracted=box.value;",
        "let box=Box { value:a }; let moved=box; let extracted=moved.value;",
        "let mut box:Box; box.value=a; let extracted=box.value;",
        "let array=[a]; let moved=array; let extracted=moved[0];",
    ] {
        let source = format!("struct Box {{ value:Own<Arena>, }}\n{source}").replace(
            "let b=append_owner(a,20);",
            &format!("{transfer} let b=append_owner(extracted,20);"),
        );
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn stored_sealed_owner_cleanup_releases_the_real_allocation() {
    let source = include_str!("../spec/cases/verify/predicate-owner-borrow.nera");
    let start = source.find("fn main()").unwrap();
    let end = source.find("fn make()").unwrap();
    for body in [
        "let box=Box { value:make() }; return 42;",
        "let box=Box { value:make() }; let moved=box; return 42;",
        "let mut box:Box; box.value=make(); return 42;",
        "let mut box=Box { value:make() }; box.value=make(); return 42;",
    ] {
        let source = format!(
            "struct Box {{ value:Own<Arena>, }} {} fn main()->u64 {{ {body} }} {}",
            &source[..start],
            &source[end..]
        );
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn stored_predicates_preserve_unique_authority_and_cleanup_obligations() {
    let source = include_str!("../spec/cases/verify/predicate-aggregate-storage.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for bad in [
        source.replace("let extracted=moved.value;", "let extracted=moved.value; let alias=moved.value;"),
        source.replace("let moved=box;", "let moved=box; let alias=box;"),
        source.replace("let box=Box { value:a };", "let box=Box { value:a }; unfold Ready(a);"),
        source.replace("let extracted=moved.value;", "let extracted=moved.value; free(extracted);"),
        source.replace("let moved=box;", "let moved=forward(box);") + "\nfn forward(p:Box)->Box { return p; }",
        source.replace("let b=append_owner(extracted,20);", "let borrowed=&mut *extracted; let stored=Box { value:extracted }; let ignored=append(borrowed,20); let b=stored.value;"),
    ] { rejected(&bad); }
}

#[test]
fn a_multi_resource_predicate_survives_field_storage_and_complete_cleanup() {
    let source = "struct PairStorage { left:Own<u64>, right:Own<u64>, }
        predicate Pair(a:ptr<u64>,b:ptr<u64>) { owns(a); owns(b); initialized(a,0usize..1usize); }
        fn main()->u64 { let a=alloc<u64>(1); let b=alloc<u64>(1); *a=42; fold Pair(a,b);
        let storage=PairStorage { left:a, right:b }; let moved=storage;
        let x=moved.left; let y=moved.right;
        unfold Pair(x,y); let total=*x; free(x); free(y); finish Pair(x,y); return total; }";
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    checked(&source.replace("let x=moved.left; let y=moved.right;\n        unfold Pair(x,y); let total=*x; free(x); free(y); finish Pair(x,y); return total;", "return 42;"));
    rejected(&source.replace("let y=moved.right;", "let y=moved.left;"));
}

#[test]
fn complete_predicate_groups_keep_responsibility_across_staged_cleanup() {
    let source = include_str!("../spec/cases/verify/predicate-group-drop.nera");
    let call = source.replace(
        "let storage=PairStorage { left:a, right:b };\n    let moved=storage;\n    return total;",
        "return destroy(a,b);",
    ) + "\nfn destroy(a:Own<u64>,b:Own<u64>)->u64 requires Pair(a,b); { let storage=PairStorage { left:a, right:b }; return 42; }";
    for source in [source.to_owned(),
        source.replace("left:a, right:b", "left:b, right:a"),
        source.replace("let moved=storage;", "let moved=storage; let extracted=moved.left;"),
        source.replace("let moved=storage;", "let mut moved=storage; let replacement=alloc<u64>(1); moved.left=replacement;"),
        format!("predicate Cell(p:ptr<u64>) {{ owns(p); }}\n{}", source.replace("let moved=storage;", "let mut moved=storage; let replacement=alloc<u64>(1); fold Cell(replacement); moved.left=replacement;")),
        source.replace("let storage=PairStorage { left:a, right:b };\n    let moved=storage;", "let extracted=a; let stored=[b];"),

        call.clone(),
        source.replace("let storage=PairStorage { left:a, right:b };\n    let moved=storage;", "let left=[a]; let right=[b];"),
        format!("enum Envelope {{ Full(PairStorage), Empty, }}\n{}", source.replace("let moved=storage;", "let moved=Envelope::Full(storage);")),
        source.replace("let storage=PairStorage { left:a, right:b };", "let mut storage:PairStorage; storage.left=a; storage.right=b;"),
        source.replace("let storage=PairStorage { left:a, right:b };", "let storage=[a,b];"),
        source.replace("let moved=storage;", "let mut moved=storage; let c=alloc<u64>(1); let d=alloc<u64>(1); *c=42; fold Pair(c,d); moved=PairStorage { left:c, right:d };")
    ] {
        let output=checked(&source);
        assert_eq!(interpret(output.vir().unwrap().resolve().unwrap().runtime()).unwrap().values(),[VirRuntimeValue::U64(42)]);
    }
    for bad in [
        call.replace("requires Pair(a,b);", ""),
        source.replace("let moved=storage;", "let moved=storage; let extracted=moved.left; free(extracted);"),
        source.replace("let moved=storage;", "let mut moved=storage; let replacement=alloc<u64>(1); moved.left=replacement; let stolen=moved.right;"),
        source.replace("*a=42;", ""),
        source.replace(
            "let moved=storage;",
            "let moved=storage; let duplicate=storage;",
        ),
    ] {
        rejected(&bad);
    }
}

#[test]
fn aggregate_owner_fields_enter_predicate_contracts_without_extra_initialization() {
    let source = include_str!("../spec/cases/verify/predicate-group-drop.nera").replace(
        "let moved=storage;\n    return total;",
        "return destroy(storage);",
    ) + "\nfn destroy(p:PairStorage)->u64 requires Pair(p.left,p.right); { return 42; }";
    let output = checked(&source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn partial_owner_predicates_survive_aggregate_parameter_transfer() {
    let source = include_str!("../spec/cases/verify/predicate-aggregate-parameter.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    let updated=source.replace("return destroy(owned);", "unfold Ready(owned); let n=owned.cursor; if n<8usize { owned.slots[n]=0; owned.cursor=n+1usize; } fold Ready(owned); return destroy(owned);");
    checked(&updated);
    rejected(&updated.replace("owned.slots[n]=0;", ""));
    let forwarded = source.replace("return consume(package);", "return forward(package);")
        + "\nfn forward(p:Box)->u64 requires Ready(p.value); { return consume(p); }";
    checked(&forwarded);
    let nested = format!("struct Outer {{ inner:Box, }}\n{source}")
        .replace(
            "return consume(package);",
            "return consume(Outer { inner:package });",
        )
        .replace("fn consume(p:Box)", "fn consume(p:Outer)")
        .replace("Ready(p.value)", "Ready(p.inner.value)")
        .replace("let owned=p.value;", "let owned=p.inner.value;");
    checked(&nested);
    for bad in [
        source.replace("requires Ready(p.value);", ""),
        source.replace("Ready(p.value)", "Ready(p.missing)"),
        source.replace("return destroy(owned);", "unfold Ready(owned); let hole=owned.slots[7]; free(owned); finish Ready(owned); return hole;"),
        source.replace("requires Ready(p.value);", "requires Ready(p.value); requires Ready(p.value);"),
    ] { rejected(&bad); }
}

#[test]
fn aggregate_predicate_paths_are_independently_validated() {
    let output = accepted(include_str!(
        "../spec/cases/verify/predicate-aggregate-parameter.nera"
    ));
    for mutation in 0..5 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let mut specs = spec_tables(&unit);
        let interface = specs
            .predicate_interfaces
            .iter_mut()
            .find(|i| i.fields.iter().any(|p| !p.is_empty()))
            .unwrap();
        match mutation {
            0 => interface.fields.clear(),
            1 => interface.fields[0] = vec![VirFieldId::new(u32::MAX)],
            2 => interface.fields[0] = vec![interface.fields[0][0]; 17],
            3 => interface.fields[0].clear(),
            4 => interface.ensures = true,
            _ => unreachable!(),
        }
        unit.specs = VirSpecEnvironment::from_tables(specs);
        assert!(unit.validate().is_err(), "VIR mutation {mutation}");
        let mut tables = hir_tables(output.hir().unwrap());
        let interface = tables
            .specs
            .predicate_interfaces
            .iter_mut()
            .find(|i| i.fields.iter().any(|p| !p.is_empty()))
            .unwrap();
        match mutation {
            0 => interface.fields.clear(),
            1 => interface.fields[0] = vec![HirFieldId::new(u32::MAX)],
            2 => interface.fields[0] = vec![interface.fields[0][0]; 17],
            3 => interface.fields[0].clear(),
            4 => interface.ensures = true,
            _ => unreachable!(),
        }
        assert!(
            HirProgram::from_tables(tables).is_err(),
            "HIR mutation {mutation}"
        );
    }
}

#[test]
fn aggregate_contracts_do_not_weaken_uncovered_fields_or_duplicate_holders() {
    let source = include_str!("../spec/cases/verify/predicate-aggregate-parameter.nera");
    let mixed = source
        .replace(
            "struct Box { value:Own<Arena>, }",
            "struct Box { value:Own<Arena>, plain:Own<u64>, }",
        )
        .replace(
            "let package=Box { value:c };",
            "let extra=alloc<u64>(1); *extra=1; let package=Box { value:c, plain:extra };",
        );
    checked(&mixed);
    rejected(&mixed.replace("*extra=1;", ""));
    let pair = source
        .replace(
            "struct Box { value:Own<Arena>, }",
            "struct Box { value:Own<Arena>, other:Own<Arena>, }",
        )
        .replace(
            "let package=Box { value:c };",
            "let extra=make(); let package=Box { value:c, other:extra };",
        )
        .replace(
            "requires Ready(p.value);",
            "requires Ready(p.value); requires Ready(p.other);",
        );
    checked(&pair);
    rejected(&pair.replace("requires Ready(p.other);", "requires Ready(p.value);"));
}

#[test]
fn aggregate_predicate_parameters_preserve_opaque_module_boundaries() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-aggregate-parameter.nera");
    let (types, rest) = source.split_once("fn main()").unwrap();
    let (_, functions) = rest.split_once("fn make()").unwrap();
    let library = format!("module arena; {types}fn make(){functions}")
        .replace("struct Box", "pub struct Box")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let main="module app; use arena::Box; use arena::make; use arena::append_owner; use arena::consume;
        fn main()->u64 { let a=make(); let b=append_owner(a,20); let c=append_owner(b,22); return consume(Box { value:c }); }";
    for valid in [true, false] {
        let library = if valid {
            library.clone()
        } else {
            library.replace("p.slots[n]=value;", "")
        };
        let inputs = [("app", main), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn partial_owner_predicates_survive_aggregate_results() {
    let source = include_str!("../spec/cases/verify/predicate-aggregate-result.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("ensures Ready(result.value);", ""));
}

#[test]
fn aggregate_results_preserve_nested_and_independent_predicates() {
    let source = include_str!("../spec/cases/verify/predicate-aggregate-result.nera");
    let forwarded = source.replace(
        "return consume(package);",
        "return consume(forward(package));",
    ) + "\nfn forward(p:Box)->Box requires Ready(p.value); ensures Ready(result.value); { return p; }";
    checked(&forwarded);
    let nested = format!("struct Outer {{ inner:Box, }}\n{source}")
        .replace(
            "fn package(p:Own<Arena>)->Box",
            "fn package(p:Own<Arena>)->Outer",
        )
        .replace("Ready(result.value)", "Ready(result.inner.value)")
        .replace(
            "return Box { value:p };",
            "return Outer { inner:Box { value:p } };",
        )
        .replace("fn consume(p:Box)", "fn consume(p:Outer)")
        .replace("Ready(p.value)", "Ready(p.inner.value)")
        .replace("let owned=p.value;", "let owned=p.inner.value;");
    checked(&nested);
    let pair = source
        .replace(
            "struct Box { value:Own<Arena>, }",
            "struct Box { value:Own<Arena>, other:Own<Arena>, }",
        )
        .replace(
            "ensures Ready(result.value);",
            "ensures Ready(result.value); ensures Ready(result.other);",
        )
        .replace(
            "return Box { value:p };",
            "let q=make(); return Box { value:p, other:q };",
        )
        .replace(
            "requires Ready(p.value);",
            "requires Ready(p.value); requires Ready(p.other);",
        );
    checked(&pair);
    rejected(&pair.replace("ensures Ready(result.other);", ""));
    rejected(&pair.replace(
        "ensures Ready(result.other);",
        "ensures Ready(result.value);",
    ));
    let mixed = source
        .replace(
            "struct Box { value:Own<Arena>, }",
            "struct Box { value:Own<Arena>, plain:Own<u64>, }",
        )
        .replace(
            "return Box { value:p };",
            "let q=alloc<u64>(1); *q=7; return Box { value:p, plain:q };",
        );
    checked(&mixed);
    rejected(&mixed.replace("*q=7;", ""));
    rejected(&source.replace(
        "return Box { value:p };",
        "unfold Ready(p); return Box { value:p };",
    ));
    rejected(&source.replace("return destroy(owned);", "unfold Ready(owned); let hole=owned.slots[7]; free(owned); finish Ready(owned); return hole;"));
}

#[test]
fn aggregate_results_transfer_multi_resource_predicates() {
    let source = include_str!("../spec/cases/verify/predicate-group-drop.nera")
        .replace("let moved=storage;", "let moved=forward(storage);")
        + "\nfn forward(p:PairStorage)->PairStorage requires Pair(p.left,p.right); ensures Pair(result.left,result.right); { return p; }";
    checked(&source);
    rejected(&source.replace("ensures Pair(result.left,result.right);", ""));
    rejected(&source.replace(
        "Pair(result.left,result.right)",
        "Pair(result.left,result.left)",
    ));
}

#[test]
fn aggregate_result_paths_and_hidden_slots_are_independently_validated() {
    let output = accepted(include_str!(
        "../spec/cases/verify/predicate-aggregate-result.nera"
    ));
    for mutation in 0..6 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let mut specs = spec_tables(&unit);
        let interface = specs
            .predicate_interfaces
            .iter_mut()
            .find(|i| i.ensures && i.fields.iter().any(|p| !p.is_empty()))
            .unwrap();
        match mutation {
            0 => interface.fields[0].clear(),
            1 => interface.fields[0] = vec![VirFieldId::new(u32::MAX)],
            2 => interface.bindings[0].0 = u32::MAX,
            3 => interface.bindings[0].1 = u32::MAX,
            4 => interface.in_place = true,
            5 => interface.ensures = false,
            _ => unreachable!(),
        }
        unit.specs = VirSpecEnvironment::from_tables(specs);
        assert!(unit.validate().is_err(), "VIR result mutation {mutation}");
        let mut tables = hir_tables(output.hir().unwrap());
        let interface = tables
            .specs
            .predicate_interfaces
            .iter_mut()
            .find(|i| i.ensures && i.fields.iter().any(|p| !p.is_empty()))
            .unwrap();
        match mutation {
            0 => interface.fields[0].clear(),
            1 => interface.fields[0] = vec![HirFieldId::new(u32::MAX)],
            2 => interface.parameters[0] = 1,
            3 => interface.fields[0] = vec![interface.fields[0][0]; 17],
            4 => interface.in_place = true,
            5 => interface.ensures = false,
            _ => unreachable!(),
        }
        assert!(
            HirProgram::from_tables(tables).is_err(),
            "HIR result mutation {mutation}"
        );
    }
}

#[test]
fn aggregate_predicate_results_cross_opaque_module_boundaries() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-aggregate-result.nera");
    let (types, rest) = source.split_once("fn main()").unwrap();
    let (_, functions) = rest.split_once("fn make()").unwrap();
    let library = format!("module arena; {types}fn make(){functions}")
        .replace("struct Box", "pub opaque struct Box")
        .replace("opaque struct Arena", "pub opaque struct Arena")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let main="module app; use arena::make; use arena::append_owner; use arena::package; use arena::consume;
        fn main()->u64 { let a=make(); let b=append_owner(a,20); let c=append_owner(b,22); return consume(package(c)); }";
    for valid in [true, false] {
        let library = if valid {
            library.clone()
        } else {
            library.replace("p.slots[n]=value;", "")
        };
        let inputs = [("app", main), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn sealed_predicate_cursor_contracts_observe_old_and_current_values() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-observation.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("old(p.cursor)+1usize", "old(p.cursor)+2usize"));
    rejected(&source.replace("p.slots[n]=value;", ""));
    rejected(&source.replace("p.cursor=0usize;", "p.cursor=1usize;"));
    rejected(&source.replace("unfold Ready(p);", ""));
}

#[test]
fn sealed_cursor_observations_preserve_history_and_definedness() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-observation.nera");
    let retired = source.replace("fn destroy(p:Own<Arena>)->u64\nrequires Ready(p);", "fn destroy(p:Own<Arena>)->u64\nrequires Ready(p); requires p.cursor==1usize; ensures old(p.cursor)==1usize;");
    checked(&retired);
    rejected(&retired.replace("old(p.cursor)==1usize", "p.cursor==1usize"));
    rejected(&retired.replace("old(p.cursor)==1usize", "p.cursor==p.cursor"));
    rejected(&retired.replace("old(p.cursor)==1usize", "true || p.cursor==1usize"));
    rejected(&source.replace(
        "ensures result.cursor==0usize;",
        "ensures result.slots[7]==0;",
    ));
    // The increment now follows a checked entry-cell origin, not interval equality.
    checked(&source.replace("requires p.cursor==0usize;", "requires p.cursor<8usize;"));
}

#[test]
fn cursor_observations_preserve_nonempty_prefixes_and_opaque_boundaries() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-cursor-increment.nera");
    let nonempty = source
        .replace("==0usize", "==1usize")
        .replace("p.cursor=0usize;", "p.slots[0]=20; p.cursor=1usize;")
        .replace("append_owner(a,42)", "append_owner(a,22)")
        .replace("n>=1usize", "n>=2usize")
        .replace("let total=p.slots[0];", "let total=p.slots[0]+p.slots[1];");
    let output = checked(&nonempty);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&nonempty.replace("p.slots[0]=20;", ""));
    let (types, rest) = source.split_once("fn main()").unwrap();
    let (_, functions) = rest.split_once("fn make()").unwrap();
    let library = format!("module arena; {types}fn make(){functions}")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let main = "module app; use arena::make; use arena::append_owner; use arena::destroy; fn main()->u64 {let p=make(); let q=append_owner(p,42); return destroy(q);}";
    for valid in [true, false] {
        let library = if valid {
            library.clone()
        } else {
            library.replace("old(p.cursor)+1usize", "old(p.cursor)+2usize")
        };
        let inputs = [("app", main), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn symbolic_cursor_increments_survive_borrows_and_calls() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-increment.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("old(p.cursor)+1usize", "old(p.cursor)+2usize"));
    rejected(&source.replace("p.cursor=n+1usize;", "p.cursor=1usize;"));
    rejected(&source.replace("p.slots[n]=value;", ""));
}

#[test]
fn symbolic_cursor_summaries_compose_without_reusing_current_values_as_history() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-increment.nera");
    let twice=source.replace("requires p.cursor<8usize;\nensures Ready(result);\nensures result.cursor==old(p.cursor)+1usize;", "requires p.cursor<7usize;\nensures Ready(result);\nensures result.cursor==old(p.cursor)+2usize;")
        .replace("let ignored=append(&mut *p,value);", "let ignored=append(&mut *p,value); let second=append(&mut *p,value);");
    checked(&twice);
    rejected(&twice.replace(
        "ensures result.cursor==old(p.cursor)+2usize;",
        "ensures result.cursor==old(p.cursor)+1usize;",
    ));
    // Both snapshots refer to entry cells; writing a constant loses the relation.
    rejected(&source.replace("p.cursor=n+1usize;", "p.cursor=7usize;"));
}

#[test]
fn symbolic_cursor_relations_survive_aggregate_wrappers() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-increment.nera");
    let wrapped = format!("struct Box {{value:Own<Arena>,}}\n{source}").replace(
        "let ignored=append(&mut *p,value);\n    return p;",
        "let ignored=append(&mut *p,value); let boxed=pack(p); return unpack(forward(boxed));",
    ) + "\nfn pack(p:Own<Arena>)->Box requires Ready(p); ensures Ready(result.value); {return Box {value:p};}\nfn forward(p:Box)->Box requires Ready(p.value); ensures Ready(result.value); {return p;}\nfn unpack(p:Box)->Own<Arena> requires Ready(p.value); ensures Ready(result); {return p.value;}";
    checked(&wrapped);
    rejected(&wrapped.replace(
        "ensures result.cursor==old(p.cursor)+1usize;",
        "ensures result.cursor==old(p.cursor)+2usize;",
    ));
}

#[test]
fn scalar_cursor_returns_preserve_sealed_history_across_borrow_calls() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-return.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("return n;", "return n+1usize;"));
    rejected(&source.replace("result==old(p.cursor);", "result==p.cursor;"));
    rejected(&source.replace("p.slots[n]=value;", ""));
    let twice = source.replace("return append(p,value);", "let first=append(&mut *p,value); return append(p,value);")
        .replace("fn append_index(p:&mut Arena,value:u64)->usize\nrequires Ready(p);\nrequires p.cursor<8usize;\nensures Ready(p);\nensures p.cursor==old(p.cursor)+1usize;\nensures result==old(p.cursor);", "fn append_index(p:&mut Arena,value:u64)->usize\nrequires Ready(p);\nrequires p.cursor<7usize;\nensures Ready(p);\nensures p.cursor==old(p.cursor)+2usize;\nensures result==old(p.cursor)+1usize;")
        .replace("requires p.cursor<8usize;\nensures Ready(result);\nensures result.cursor==old(p.cursor)+1usize;", "requires p.cursor<7usize;\nensures Ready(result);\nensures result.cursor==old(p.cursor)+2usize;");
    checked(&twice);
    rejected(&twice.replace(
        "ensures result==old(p.cursor)+1usize;",
        "ensures result==old(p.cursor);",
    ));
}

#[test]
fn opaque_module_scalar_cursor_returns_refine_actual_call_results() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-cursor-return.nera");
    let (types, rest) = source.split_once("fn main()").unwrap();
    let (_, functions) = rest.split_once("fn make()").unwrap();
    let library = format!("module arena; {types}fn make(){functions}")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let app = "module app; use arena::make; use arena::append_index; use arena::destroy; fn main()->u64 {let p=make(); let first=append_index(&mut *p,42); expect_zero(first); let second=append_index(&mut *p,7); expect_one(second); return destroy(p);} fn expect_zero(n:usize) requires n==0usize; {return;} fn expect_one(n:usize) requires n==1usize; {return;}";
    for valid in [true, false] {
        let app = if valid {
            app.to_owned()
        } else {
            app.replace("expect_one(second)", "expect_one(first)")
        };
        let inputs = [("app", app.as_str()), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn nested_cursor_contracts_preserve_partial_initialization_and_returns() {
    let source = include_str!("../spec/cases/verify/predicate-nested-cursor.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("p.slots[n]=value;", ""));
    rejected(&source.replace("old(p.state.cursor)+1usize", "old(p.state.cursor)+2usize"));
    rejected(&source.replace(
        "ensures result.state.cursor==0usize;",
        "ensures result.state.unused;",
    ));
    rejected(&source.replace(
        "ensures result.state.cursor==0usize;",
        "ensures result.state.unused==result.state.unused;",
    ));
}

#[test]
fn stored_cursor_steps_preserve_sealed_history_and_initialized_backing() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-step.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace(
        "let end=p.state.cursor+p.state.step;",
        "let end=p.state.cursor+p.state.cursor;",
    ));
    rejected(&source.replace("let end=p.state.cursor+p.state.step;", "let end=2usize;"));
    rejected(&source.replace("p.state.step=2usize;", ""));
    rejected(&source.replace("p.slots=[42,0,0,0,0,0,0,0];", "p.slots[0]=42;"));
    let missing_prefix = source
        .replace(
            "initialized(p.slots,0usize..8usize);",
            "initialized(p.slots,0usize..p.state.cursor);",
        )
        .replace("p.slots=[42,0,0,0,0,0,0,0];", "p.slots[0]=42;");
    rejected(&missing_prefix);
}

#[test]
fn stored_cursor_steps_refine_distinct_opaque_module_calls() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-cursor-step.nera");
    let (types, rest) = source.split_once("fn main()").unwrap();
    let (_, functions) = rest.split_once("fn make()").unwrap();
    let library = format!("module arena; {types}fn make(){functions}")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ");
    let app = "module app; use arena::make; use arena::advance_index; use arena::destroy; fn main()->u64 {let p=make(); let first=advance_index(&mut *p); expect_two(first); let second=advance_index(&mut *p); expect_four(second); return destroy(p);} fn expect_two(n:usize) requires n==2usize; {return;} fn expect_four(n:usize) requires n==4usize; {return;}";
    for valid in [true, false] {
        let app = if valid {
            app.to_owned()
        } else {
            app.replace("expect_four(second)", "expect_four(first)")
        };
        let inputs = [("app", app.as_str()), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn repeated_stored_steps_preserve_history_through_sealed_borrow_calls() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-repeat.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace(
        "old(p.state.cursor)+old(p.state.step)+old(p.state.step);",
        "old(p.state.cursor)+old(p.state.step);",
    ));
    rejected(&source.replace("let first=advance(&mut *p);", ""));
    rejected(&source.replace(
        "requires p.state.cursor<2usize;",
        "requires p.state.cursor<4usize;",
    ));
    let missing_prefix = source
        .replace(
            "initialized(p.slots,0usize..8usize);",
            "initialized(p.slots,0usize..p.state.cursor);",
        )
        .replace("p.slots=[42,0,0,0,0,0,0,0];", "p.slots[0]=42;");
    rejected(&missing_prefix);
}

#[test]
fn repeated_step_summaries_refine_weighted_results_across_opaque_modules() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-cursor-repeat.nera");
    let (types, rest) = source.split_once("fn main()").unwrap();
    let (_, functions) = rest.split_once("fn make()").unwrap();
    let library = format!("module arena; {types}fn make(){functions}")
        .replace("opaque struct", "pub opaque struct")
        .replace("predicate Ready", "pub predicate Ready")
        .replace("fn ", "pub fn ")
        .replace("result.state.cursor==0usize", "result.state.cursor==1usize")
        .replace("p.state.cursor=0usize", "p.state.cursor=1usize");
    let app = "module app; use arena::make; use arena::advance_index; use arena::destroy; fn main()->u64 {let p=make(); let n=advance_index(&mut *p); exact(n); return destroy(p);} fn exact(n:usize) requires n==3usize; {return;}";
    for valid in [true, false] {
        let app = if valid {
            app.to_owned()
        } else {
            app.replace("n==3usize", "n==2usize")
        };
        let inputs = [("app", app.as_str()), ("arena", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), valid);
    }
}

#[test]
fn scalar_parameters_advance_sealed_partial_representations() {
    let source = include_str!("../spec/cases/verify/predicate-cursor-parameter.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace(
        "old(p.state.cursor)+count+count",
        "old(p.state.cursor)+count",
    ));
    rejected(&source.replace(
        "let end=p.state.cursor+count;",
        "let end=p.state.cursor+1usize;",
    ));
    rejected(&source.replace("requires count<2usize;", ""));
}

#[test]
fn resource_groups_borrow_and_restore_through_aggregate_owner_calls() {
    let source = include_str!("../spec/cases/verify/predicate-multi-borrow.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace(
        "if left.value<64 {left.value=left.value+1;}",
        "left.value=65;",
    ));
    let overwritten = source.replace(
        "if left.value<64 {left.value=left.value+1;}",
        "if left.value<64 {left.value=64;left.value=left.value+1;}",
    );
    let output = accepted(&overwritten);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .expect("overwrite negative reaches the verifier");
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.message().contains("predicate effect")),
        "old branch bound must not discharge the refold after a write"
    );
    rejected(&source.replace("    fold Ready(left,right);\n    return;", "    return;"));
    rejected(&source.replace(
        "bump(&mut *left,&mut *right)",
        "bump(&mut *left,&mut *left)",
    ));
}

#[test]
fn predicate_existentials_require_real_typed_witnesses_and_remain_local() {
    let source = include_str!("../spec/cases/verify/predicate-existential.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for invalid in [
        source.replace("p.cursor=0usize;", ""),
        source.replace(
            "exists used:usize = p.cursor;",
            "exists used:bool = p.cursor;",
        ),
        source.replace("exists used:usize = p.cursor;", "exists used:usize = used;"),
        source.replace(
            "exists used:usize = p.cursor;",
            "exists used:usize = later; exists later:usize = p.cursor;",
        ),
        source.replace(
            "exists used:usize = p.cursor;",
            "exists used:usize = p.cursor; exists used:usize = p.cursor;",
        ),
        source.replace(
            "exists used:usize = p.cursor;",
            "exists p:usize = p.cursor;",
        ),
        source.replace("let n=p.cursor;", "let n=used;"),
        source.replace("p.slots[n]=value;", ""),
    ] {
        rejected(&invalid);
    }
    for mutation in 0..4 {
        let mut tables = hir_tables(output.hir().unwrap());
        let a = tables.predicates[0].representation.as_mut().unwrap();
        let mut unit = output.vir().unwrap().as_unit().clone();
        let b = unit.specs.predicates_mut()[0]
            .representation
            .as_mut()
            .unwrap();
        match mutation {
            0 => {
                a.witnesses[0].resource = 32;
                b.witnesses[0].resource = 32;
            }
            1 => {
                a.witnesses[0].offset = 1;
                b.witnesses[0].offset = 1;
            }
            2 => {
                a.witnesses[0].name = "p".into();
                b.witnesses[0].name = "p".into();
            }
            3 => {
                a.resources[0].initialized.clear();
                b.resources[0].initialized.clear();
            }
            _ => unreachable!(),
        }
        assert!(HirProgram::from_tables(tables).is_err());
        assert!(unit.into_validated().is_err());
    }
}

#[test]
fn stored_borrowed_predicates_move_take_and_restore_on_real_drop() {
    let source = include_str!("../spec/cases/verify/predicate-stored-borrow.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("let saved=LoanBox{view:active};", "unfold Ready(active); active.cursor=9usize; fold Ready(active); let saved=LoanBox{view:active};"));
    rejected(&source.replace("let moved=first;", "let moved=first; let again=first;"));
    rejected(&source.replace(
        "let saved=LoanBox{view:active};",
        "let saved=LoanBox{view:active}; unfold Ready(p);",
    ));
}

#[test]
fn opaque_arena_candidate_preserves_baseline_frames_and_restores_owner() {
    let source = include_str!("../spec/cases/verify/predicate-arena-encapsulation.nera");
    checked_logical_prefix(source); // Every summary closes and address evidence replays.
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(49)]
    );
    for (invalid, precondition) in [
        (
            source.replace("reserve(&mut *arena,6usize)", "reserve(&mut *arena,7usize)"),
            true,
        ),
        (source.replace("p.cursor=end;", "p.cursor=7usize;"), false),
    ] {
        let output = accepted(&invalid);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("arena misuse must reach resource verification");
        assert!(!report.is_memory_checked_core0());
        assert!(
            report
                .functions()
                .values()
                .flat_map(|function| function.cfg().obligations())
                .map(|check| check.obligation())
                .any(|obligation| !obligation.is_proven()
                    && if precondition {
                        matches!(
                            obligation.kind(),
                            ResourceObligationKind::CallContractPrecondition { .. }
                        )
                    } else {
                        matches!(
                            obligation.kind(),
                            ResourceObligationKind::PredicateActionValid { .. }
                        )
                    }),
            "wrong failure layer: {:?}",
            report.diagnostics()
        );
    }
    rejected(&source.replace("remaining[0]=7;", "reset(&mut *arena); remaining[0]=7;"));
    rejected(&source.replace("fold Ready(p);", "fold Ready(p); fold Ready(p);"));
    rejected(&source.replace("unfold Ready(p);", "unfold Ready(p); unfold Ready(p);"));
    rejected(&source.replace(
        "let total=client(&mut *arena,1usize,3usize);",
        "let live=reserve(&mut *arena,6usize); destroy(arena); let total=live[0];",
    ));
}

#[test]
fn arena_client_uses_only_public_predicates_and_slice_operations() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let library = include_str!("../spec/cases/modules/arena/arena.nera");
    let forward = include_str!("../spec/cases/modules/arena/forward.nera");
    let app = include_str!("../spec/cases/modules/arena/app.nera");
    let inputs = [("app", app), ("arena", library), ("forward", forward)]
        .into_iter()
        .map(|(name, text)| {
            SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
        })
        .collect();
    let compiler = CompilerSession::modules(
        SourceDatabase::new(inputs).unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap();
    assert!(compiler.verify("app").unwrap().is_checked());
    // The expanded visibility and semantic negative matrix lives in opaque_arena.
}

// P3 uses targeted execution; P6 retains the final full acceptance suite.
const EXPLICIT_WITNESS: &str = include_str!("../spec/cases/verify/predicate-explicit-witness.nera");

#[test]
fn explicit_predicate_witnesses_use_fold_point_ssa_and_defaults() {
    let output = checked(EXPLICIT_WITNESS);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    checked(&EXPLICIT_WITNESS.replace("used = candidate * 2usize", "used = 7usize"));
    checked(&EXPLICIT_WITNESS.replace("exists used:usize;", "exists used:usize = 0usize;"));
}

#[test]
fn explicit_witnesses_reject_missing_duplicate_wrong_type_and_failed_constraints() {
    for source in [
        EXPLICIT_WITNESS.replace(" with (used = candidate * 2usize, enabled = true)", ""),
        EXPLICIT_WITNESS.replace("used = candidate * 2usize", "used = 7u64"),
        EXPLICIT_WITNESS.replace("candidate * 2usize", "candidate * 2u64"),
        EXPLICIT_WITNESS.replace("used = candidate * 2usize", "absent = 7usize"),
        EXPLICIT_WITNESS.replace("used = candidate * 2usize", "used = 7usize, used = 7usize"),
        EXPLICIT_WITNESS.replace("used = candidate * 2usize", "used = 8usize"),
        EXPLICIT_WITNESS.replace(
            "used = candidate * 2usize",
            "used = 18446744073709551615usize",
        ),
        EXPLICIT_WITNESS.replace("enabled = true", "enabled = false"),
        EXPLICIT_WITNESS.replace("exists used:usize;", "exists used:usize = next;"),
    ] {
        rejected(&source);
    }
}

#[test]
fn independent_vir_admission_rejects_forged_explicit_witness_inputs() {
    let output = accepted(EXPLICIT_WITNESS);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let action = unit
        .specs
        .predicate_actions_mut()
        .iter_mut()
        .find(|a| !a.witnesses.inputs.is_empty())
        .unwrap();
    action.witnesses.inputs[0].1 = predicate_logic::WitnessInput::Scalar(VirValueId::new(u32::MAX));
    assert!(unit.validate().is_err());
}

#[test]
fn opened_predicate_names_are_ghost_inputs_to_the_same_instance() {
    let source = EXPLICIT_WITNESS.replace(
        "    unfold Ready(p);",
        "    unfold Ready(p) as (saved, successor, enabled_now);\n    fold Ready(p) with (used = saved, enabled = enabled_now);\n    unfold Ready(p);",
    );
    checked(&source);
    rejected(&source.replace("let outcome=p.value;", "let outcome=saved;"));
    rejected(&source.replace(
        "(saved, successor, enabled_now)",
        "(saved, saved, enabled_now)",
    ));
    rejected(&source.replace(
        "(saved, successor, enabled_now)",
        "(candidate, successor, enabled_now)",
    ));
    rejected(&source.replace("(saved, successor, enabled_now)", "(saved)"));
    rejected(&source.replace(
        "let outcome=p.value;",
        "let saved=0usize; let outcome=p.value;",
    ));
}

#[test]
fn refold_and_scope_exit_invalidate_opened_predicate_names() {
    let stale = EXPLICIT_WITNESS.replace("    unfold Ready(p);",
        "    unfold Ready(p) as (saved, successor, enabled_now);\n    fold Ready(p) with (used = saved);\n    unfold Ready(p);\n    fold Ready(p) with (used = saved);\n    unfold Ready(p);");
    rejected(&stale);
    let escaped = EXPLICIT_WITNESS.replace("    unfold Ready(p);",
        "    if true {\n        unfold Ready(p) as (saved, successor, enabled_now);\n    }\n    fold Ready(p) with (used = saved);\n    unfold Ready(p);");
    rejected(&escaped);
}

#[test]
fn opened_predicate_inputs_are_independently_typed_in_vir() {
    let source = EXPLICIT_WITNESS.replace("    unfold Ready(p);",
        "    unfold Ready(p) as (saved, successor, enabled_now);\n    fold Ready(p) with (used = saved);\n    unfold Ready(p);");
    let output = accepted(&source);
    for mutation in 0..3 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let input = unit
            .specs
            .predicate_actions_mut()
            .iter_mut()
            .flat_map(|a| &mut a.witnesses.inputs)
            .find(|(_, input)| matches!(input, predicate_logic::WitnessInput::Opened { .. }))
            .unwrap();
        let predicate_logic::WitnessInput::Opened {
            action,
            holder,
            binder,
        } = &mut input.1
        else {
            unreachable!()
        };
        match mutation {
            0 => *action = u32::MAX,
            1 => *holder = u32::MAX,
            _ => *binder = u32::MAX,
        }
        assert!(unit.validate().is_err());
    }
}

#[test]
fn opened_root_resource_witness_preserves_existing_authority() {
    let source = include_str!("../spec/cases/verify/predicate-opened-witness.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace("let value=p.value;", "let value=storage.value;"));
    rejected(&source.replace("saved + 1usize", "saved + 3usize"));
}

const LOGICAL_ARGUMENTS: &str =
    include_str!("../spec/cases/verify/predicate-logical-arguments.nera");
#[test]
fn predicate_logical_arguments_preserve_order_types_and_instance_parameters() {
    let output = checked(LOGICAL_ARGUMENTS);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    let body = output.vir().unwrap().as_unit().specs.predicates()[0]
        .representation
        .as_ref()
        .unwrap();
    assert_eq!(
        body.logic
            .parameters
            .iter()
            .map(|p| p.position)
            .collect::<Vec<_>>(),
        vec![0, 2, 3]
    );
    for source in [
        LOGICAL_ARGUMENTS.replace("capacity,p,true,40u64 + 2u64", "7u64,p,true,42u64"),
        LOGICAL_ARGUMENTS.replace("capacity,p,true,40u64 + 2u64", "capacity,p,42u64,true"),
        LOGICAL_ARGUMENTS.replace("capacity,p,true,40u64 + 2u64", "capacity,p,true"),
        LOGICAL_ARGUMENTS.replace(
            "unfold Ready(capacity,p,true,42u64)",
            "unfold Ready(6usize,p,true,42u64)",
        ),
        LOGICAL_ARGUMENTS.replace(
            "finish Ready(7usize,p,true,42u64)",
            "finish Ready(8usize,p,true,42u64)",
        ),
        LOGICAL_ARGUMENTS.replace("let capacity=7usize;", "let capacity=0usize;"),
        LOGICAL_ARGUMENTS.replace("capacity,p,true,40u64 + 2u64", "capacity,p,false,42u64"),
    ] {
        rejected(&source);
    }
}
#[test]
fn independent_predicate_parameter_validation_rejects_forged_positions_and_actual_types() {
    let output = accepted(LOGICAL_ARGUMENTS);
    let mut unit = output.vir().unwrap().as_unit().clone();
    unit.specs.predicates_mut()[0]
        .representation
        .as_mut()
        .unwrap()
        .logic
        .parameters[1]
        .position = 0;
    assert!(unit.validate().is_err());
    let mut unit = output.vir().unwrap().as_unit().clone();
    unit.specs.predicate_actions_mut()[0].witnesses.arguments[0].nodes[0].ty =
        predicate_logic::LogicType::U64;
    assert!(unit.validate().is_err());
}

#[test]
fn logical_preconditions_map_scalar_slots_through_ordinary_calls() {
    let source = include_str!("../spec/cases/verify/predicate-logical-requires.nera");
    let output = checked(source);
    let interfaces = output.vir().unwrap().as_unit().specs.predicate_interfaces();
    assert_eq!(interfaces.len(), 2);
    // consume takes the owner first (two slots), whereas relay takes limit first.
    assert_eq!(
        interfaces[0].arguments.inputs[0].1,
        predicate_logic::WitnessInput::Scalar(2)
    );
    assert_eq!(
        interfaces[1].arguments.inputs[0].1,
        predicate_logic::WitnessInput::Scalar(0)
    );
    rejected(&source.replace("return relay(7usize,p);", "return relay(8usize,p);"));
    rejected(&source.replace(
        "return consume(p,limit);",
        "return consume(p,limit + 1usize);",
    ));
    rejected(&source.replace("requires Ready(limit,p);", "requires Ready(p,limit);"));
    rejected(&source.replace("limit:usize", "limit:u64"));
    rejected(&source.replace(
        "limit == limit;",
        "exists hidden:usize = limit; hidden == limit;",
    ));
}

#[test]
fn logical_precondition_metadata_is_independently_validated() {
    let output = accepted(include_str!(
        "../spec/cases/verify/predicate-logical-requires.nera"
    ));
    let original = output.vir().unwrap().as_unit();
    for forged in 0..4 {
        let mut unit = original.clone();
        let interface = &mut unit.specs.predicate_interfaces_mut()[0];
        match forged {
            0 => interface.arguments.inputs[0].1 = predicate_logic::WitnessInput::Scalar(0), // pointer, not scalar
            1 => interface.arguments.inputs[0].0 = predicate_logic::LogicType::U64, // erased ABI words still have nominal types
            2 => interface.arguments.arguments.clear(),
            _ => interface.ensures = true,
        }
        assert!(unit.validate().is_err());
    }
    let mut old = original.clone();
    old.version = VirUnitVersion::V47;
    assert!(old.validate().is_err());
}

#[test]
fn logical_postconditions_keep_entry_arguments_through_branches_and_forwarding() {
    let source = include_str!("../spec/cases/verify/predicate-logical-ensures.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    rejected(&source.replace(
        "ensures Ready(limit,result);",
        "ensures Ready(8usize,result);",
    ));
    rejected(&source.replace("return consume(q,7usize);", "return consume(q,8usize);"));
    rejected(&source.replace(
        "return select(p,limit,true);",
        "return select(p,8usize,true);",
    ));
}

#[test]
fn logical_in_place_postconditions_check_the_actual_closed_instance() {
    checked("struct Cell {value:u64,} predicate Ready(limit:usize,p:ptr<Cell>) {owns(p); initialized(p.value,0..1); limit==limit;}
        fn touch(p:&mut Cell,limit:usize)->u64 requires Ready(limit,p); ensures Ready(limit,p); {
            unfold Ready(limit,p); let value=p.value; fold Ready(limit,p); return value;
        }");
    rejected("struct Cell {value:u64,} predicate Ready(limit:usize,p:ptr<Cell>) {owns(p); initialized(p.value,0..1); limit==limit;}
        fn touch(p:&mut Cell,limit:usize)->u64 requires Ready(limit,p); ensures Ready(limit,p); {
            unfold Ready(limit,p); let value=p.value; fold Ready(8usize,p); return value;
        }");
}

#[test]
fn logical_postconditions_follow_owner_fields_and_field_to_ssa_returns() {
    let source = include_str!("../spec/cases/verify/predicate-logical-ensures.nera");
    let source = format!("struct Box {{ value:Own<Cell>, }}\n{source}\n
        fn pack(p:Own<Cell>,limit:usize)->Box requires Ready(limit,p); ensures Ready(limit,result.value); {{
            return Box {{value:p}};
        }}
        fn unpack(b:Box,limit:usize)->Own<Cell> requires Ready(limit,b.value); ensures Ready(limit,result); {{
            return b.value;
        }}");
    let source = source.replace(
        "let q=forward(7usize,p);",
        "let boxed=pack(p,7usize); let q=unpack(boxed,7usize);",
    );
    checked(&source);
    rejected(&source.replace(
        "ensures Ready(limit,result.value);",
        "ensures Ready(8usize,result.value);",
    ));
    rejected(&source.replace("let q=unpack(boxed,7usize);", "let q=unpack(boxed,8usize);"));
}

#[test]
fn boolean_logical_preconditions_preserve_unknown_parameter_identity() {
    let source = include_str!("../spec/cases/verify/predicate-logical-requires.nera")
        .replace("limit:usize", "limit:bool")
        .replace("7usize", "true");
    checked(&source);
    rejected(&source.replace("return consume(p,limit);", "return consume(p,false);"));
    rejected(&source.replace("return relay(true,p);", "return relay(false,p);"));
}

#[test]
fn boolean_logical_postconditions_match_immutable_entry_snapshots() {
    let source = include_str!("../spec/cases/verify/predicate-logical-ensures.nera")
        .replace("limit:usize", "limit:bool")
        .replace("7usize", "true");
    checked(&source);
    rejected(&source.replace(
        "ensures Ready(limit,result);",
        "ensures Ready(false,result);",
    ));
    rejected(&source.replace(
        "return select(p,limit,true);",
        "return select(p,false,true);",
    ));
    rejected(&source.replace("return consume(q,true);", "return consume(q,false);"));
}

#[test]
fn boolean_field_observations_follow_parameter_stores_and_loads() {
    let source = "struct Cell {flag:bool,}
        predicate Ready(flag:bool,p:ptr<Cell>) {
            owns(p); initialized(p.flag,0..1); p.flag==flag;
        }
        fn consume(flag:bool)->u64 {
            let p=alloc<Cell>(1); p.flag=flag;
            let saved=p.flag;
            fold Ready(saved,p);
            unfold Ready(saved,p);
            p.flag=flag;
            fold Ready(saved,p);
            unfold Ready(saved,p);
            free(p); finish Ready(saved,p); return 42;
        }";
    checked(source);
    rejected(&source.replace(
        "p.flag=flag;\n            fold",
        "p.flag=false;\n            fold",
    ));
    rejected(
        &source
            .replace("fn consume(flag:bool)", "fn consume(flag:bool,other:bool)")
            .replace(
                "p.flag=flag;\n            fold",
                "p.flag=other;\n            fold",
            ),
    );
}

#[test]
fn boolean_predicate_arguments_survive_branch_refinement_and_return_splitting() {
    let source = include_str!("../spec/cases/verify/predicate-logical-ensures.nera")
        .replace("limit:usize", "limit:bool")
        .replace("7usize", "true")
        .replace("if left", "if limit");
    checked(&source);
    rejected(&source.replace(
        "ensures Ready(limit,result);",
        "ensures Ready(false,result);",
    ));
    checked(
        "struct Cell {value:u64,}
        predicate Ready(flag:bool,p:ptr<Cell>) {owns(p); initialized(p.value,0..1); flag==flag;}
        fn touch(p:&mut Cell,flag:bool)->bool requires Ready(flag,p); ensures Ready(flag,p); {
            return flag;
        }",
    );
}

#[test]
fn boolean_call_results_and_field_effects_preserve_actual_input_identity() {
    let source = "struct Cell {flag:bool,}
        predicate Ready(flag:bool,p:ptr<Cell>) {owns(p); initialized(p.flag,0..1); p.flag==flag;}
        fn identity(flag:bool)->bool {return flag;}
        fn store(p:&mut Cell,flag:bool)->u64 {p.flag=flag; return 0;}
        fn consume(flag:bool,other:bool)->u64 {
            let p=alloc<Cell>(1); p.flag=flag;
            let same=identity(flag);
            let ignored=store(&mut *p,same);
            fold Ready(flag,p); unfold Ready(flag,p);
            free(p); finish Ready(flag,p); return 42;
        }";
    checked(source);
    rejected(&source.replace("let same=identity(flag);", "let same=identity(other);"));
}

#[test]
fn interfaces_cannot_reselect_nonprojected_existentials_from_defaults() {
    for default in [
        "exists hidden:u64 = 0;",
        "exists hidden:bool = true;",
        "exists hidden:u64;",
    ] {
        let prefix = format!(
            "struct Cell {{value:u64,}} predicate Ready(p:ptr<Cell>) {{{default} owns(p); initialized(p.value,0..1);}}"
        );
        let witness = if default.contains("bool") {
            "false"
        } else {
            "9"
        };
        checked(&format!(
            "{prefix}
            fn main()->u64 {{let p=alloc<Cell>(1); p.value=0; fold Ready(p) with (hidden={witness}); return consume(p);}}
            fn consume(p:Own<Cell>)->u64 requires Ready(p); {{unfold Ready(p); free(p); finish Ready(p); return 0;}}"
        ));
        let make = format!(
            "{prefix} fn make()->Own<Cell> ensures Ready(result); {{let p=alloc<Cell>(1); p.value=0; fold Ready(p); return p;}}"
        );
        if default.contains('=') {
            checked(&make);
        } else {
            rejected(&make);
        }
    }
    // A projection descriptor must agree with the logical default, in both IRs.
    let output = accepted(include_str!(
        "../spec/cases/verify/predicate-existential.nera"
    ));
    let mut tables = hir_tables(output.hir().unwrap());
    let body = tables.predicates[0].representation.as_mut().unwrap();
    body.logic.existentials[0].default.as_mut().unwrap().nodes[0].kind =
        predicate_logic::LogicNodeKind::Word(0);
    assert!(HirProgram::from_tables(tables).is_err());
    let mut unit = output.vir().unwrap().as_unit().clone();
    let body = unit.specs.predicates_mut()[0]
        .representation
        .as_mut()
        .unwrap();
    body.logic.existentials[0].default.as_mut().unwrap().nodes[0].kind =
        predicate_logic::LogicNodeKind::Word(0);
    assert!(unit.into_validated().is_err());
    checked(EXPLICIT_WITNESS); // Local witness selection remains supported.
}

#[test]
fn abstract_existentials_cross_checked_calls_and_refold_with_opened_identity() {
    let source = include_str!("../spec/cases/verify/predicate-abstract-existential.nera");
    checked(source);
    checked(&source.replace("used=saved+0usize", "used=saved"));
    checked(&source.replace("exists used:usize = 999usize;", "exists used:usize;"));
    for bad in [
        source.replace("used=saved+0usize,enabled=on", "used=999usize,enabled=on"),
        source.replace("used=saved+0usize,enabled=on", "used=saved,enabled=false"),
        source.replace(
            "fold Ready(p,limit,flag) with (used=saved+0usize,enabled=on,location=place)",
            "fold Ready(p,limit,flag)",
        ),
        source.replace("consume(q,8usize,true)", "consume(q,9usize,true)"),
    ] {
        // These must reach verification; an unrelated frontend gate is not
        // evidence that a wrong witness or parameter was rejected.
        let output = accepted(&bad);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .unwrap();
        assert!(!report.is_memory_checked_core0(), "{bad}");
    }
}

#[test]
fn projected_field_witnesses_compose_with_logical_interface_parameters() {
    let source = "struct Cell {value:u64,}
        predicate Ready(limit:usize,p:ptr<Cell>) {
            exists used:u64 = p.value;
            owns(p); initialized(p.value,0..1); used<=8; limit==limit;
        }
        fn main()->u64 {
            let p=alloc<Cell>(1); p.value=7;
            fold Ready(3usize,p);
            let q=forward(p,3usize); return consume(q,3usize);
        }
        fn forward(p:Own<Cell>,limit:usize)->Own<Cell>
        requires Ready(limit,p); ensures Ready(limit,result); {return p;}
        fn consume(p:Own<Cell>,limit:usize)->u64 requires Ready(limit,p); {
            unfold Ready(limit,p); let value=p.value; free(p); finish Ready(limit,p); return value;
        }
";
    checked(source);
    rejected(&source.replace("forward(p,3usize)", "forward(p,4usize)"));
    rejected(&source.replace(
        "ensures Ready(limit,result);",
        "ensures Ready(4usize,result);",
    ));
    checked(&source.replace("exists used:u64 = p.value;", "exists used:u64 = 7;"));
}

#[test]
fn explicit_projected_counts_must_equal_the_real_initialized_cursor() {
    let source = "struct Buffer {cursor:usize,slots:[u64;8],}
        predicate Ready(p:ptr<Buffer>) {
            exists used:usize = p.cursor;
            owns(p); initialized(p.slots,0usize..used); used<=8usize;
        }
        fn main()->u64 {
            let p=alloc<Buffer>(1); p.cursor=1usize; p.slots[0]=42;
            fold Ready(p) with (used = 1usize);
            unfold Ready(p) as (saved);
            fold Ready(p) with (used = saved);
            unfold Ready(p); let outcome=p.slots[0]; free(p); finish Ready(p); return outcome;
        }";
    checked(source);
    rejected(&source.replace("used = 1usize", "used = 0usize"));
    rejected(&source.replace(
        "fold Ready(p) with (used = saved);",
        "p.cursor=0usize; fold Ready(p) with (used = saved);",
    ));
    rejected(&source.replace("p.slots[0]=42;", ""));
    let output = accepted(source);
    let mut tables = hir_tables(output.hir().unwrap());
    tables.predicates[0]
        .representation
        .as_mut()
        .unwrap()
        .logic
        .existentials[0]
        .default
        .as_mut()
        .unwrap()
        .nodes[0]
        .kind = predicate_logic::LogicNodeKind::Word(0);
    assert!(HirProgram::from_tables(tables).is_err());
    let mut unit = output.vir().unwrap().as_unit().clone();
    unit.specs.predicates_mut()[0]
        .representation
        .as_mut()
        .unwrap()
        .logic
        .existentials[0]
        .default
        .as_mut()
        .unwrap()
        .nodes[0]
        .kind = predicate_logic::LogicNodeKind::Word(0);
    assert!(unit.into_validated().is_err());
}

#[test]
fn result_first_interfaces_accept_interleaved_logical_comparisons() {
    let source = "struct Cell {value:u64,}
        predicate Ready(p:ptr<Cell>,same:bool) {owns(p); initialized(p.value,0..1); same==same;}
        fn main()->u64 {
            let p=alloc<Cell>(1); p.value=42; fold Ready(p,true);
            let q=forward(p,7usize); return consume(q);
        }
        fn forward(p:Own<Cell>,limit:usize)->Own<Cell>
        requires Ready(p,limit==limit); ensures Ready(result,limit==limit); {return p;}
        fn consume(p:Own<Cell>)->u64 requires Ready(p,true); {
            unfold Ready(p,true); let value=p.value; free(p); finish Ready(p,true); return value;
        }
        ";
    checked(source);
    let boxed = format!(
        "struct Box {{value:Own<Cell>,}}\n{}",
        source
            .replace(
                "fn forward(p:Own<Cell>,limit:usize)->Own<Cell>",
                "fn forward(p:Own<Cell>,limit:usize)->Box"
            )
            .replace(
                "ensures Ready(result,limit==limit); {return p;}",
                "ensures Ready(result.value,limit==limit); {return Box {value:p};}"
            )
            .replace("return consume(q);", "return consume(q.value);")
    );
    checked(&boxed);
    for comparison in ["limit!=limit", "limit<limit", "limit>limit"] {
        checked(
            &source
                .replace("limit==limit", comparison)
                .replace("Ready(p,true)", "Ready(p,false)"),
        );
    }
    for comparison in [
        "limit<=limit",
        "limit>=limit",
        "limit + 1usize > limit",
        "limit < limit + 1usize",
    ] {
        // Bounded additions need an entry upper bound, so exercise literal
        // comparisons for the overflow-sensitive cases.
        let changed = source.replace("limit==limit", comparison);
        let changed = if comparison.contains('+') {
            changed.replace(comparison, &comparison.replace("limit", "7usize"))
        } else {
            changed
        };
        checked(&changed);
    }
    rejected(&source.replace(
        "ensures Ready(result,limit==limit);",
        "ensures Ready(result,limit!=limit);",
    ));
    rejected(&source.replace(
        "ensures Ready(result,limit==limit);",
        "ensures Ready(result,limit);",
    ));
    rejected(&source.replace("limit==limit", "limit==7u64"));
    rejected(&source.replace("limit==limit", "unknown(limit)==limit"));
}

#[test]
fn predicate_old_scalar_actuals_use_the_existing_entry_snapshot_protocol() {
    let source = include_str!("../spec/cases/verify/predicate-logical-ensures.nera");
    let explicit = source.replace(
        "ensures Ready(limit,result);",
        "ensures Ready(old(limit),result);",
    );
    let plain = accepted(source);
    let output = checked(&explicit);
    for (plain, explicit) in plain
        .vir()
        .unwrap()
        .as_unit()
        .specs
        .predicate_interfaces()
        .iter()
        .zip(output.vir().unwrap().as_unit().specs.predicate_interfaces())
    {
        assert_eq!(
            plain.arguments, explicit.arguments,
            "old must lower to the same entry input, not a runtime call"
        );
    }
    checked(&explicit.replace("old(limit)", "old(limit + 0usize)"));
    let boolean = explicit
        .replace("limit:usize", "limit:bool")
        .replace("7usize", "true");
    checked(&boolean);
    rejected(&explicit.replace("old(limit)", "old(limit + 1usize)"));
    for invalid in [
        "old()",
        "old(limit,limit)",
        "old(old(limit))",
        "old(result)",
        "old(p.value)",
        "old(side_effect(limit))",
    ] {
        rejected(&explicit.replace("old(limit)", invalid));
    }
    rejected(&source.replace("requires Ready(limit,p);", "requires Ready(old(limit),p);"));
}

#[test]
fn result_first_predicate_interfaces_allow_old_comparison_actuals() {
    let source = "struct Cell {value:u64,}
        predicate Ready(p:ptr<Cell>,same:bool) {owns(p); initialized(p.value,0..1); same==same;}
        fn main()->u64 {
            let p=alloc<Cell>(1); p.value=42; fold Ready(p,true);
            let q=forward(p,7usize); return consume(q);
        }
        fn forward(p:Own<Cell>,limit:usize)->Own<Cell>
        requires Ready(p,limit==limit); ensures Ready(result,old(limit==limit)); {return p;}
        fn consume(p:Own<Cell>)->u64 requires Ready(p,true); {
            unfold Ready(p,true); let value=p.value; free(p); finish Ready(p,true); return value;
        }
        ";
    checked(source);
    checked(&source.replace("old(limit==limit)", "old(limit)==old(limit)"));
    rejected(&source.replace("old(limit==limit)", "old(limit!=limit)"));
}

#[test]
fn boolean_field_witnesses_use_one_byte_and_cross_parameterized_interfaces() {
    let source = "struct Cell {flag:bool,}
        predicate Ready(p:ptr<Cell>,tag:usize) {
            exists enabled:bool = p.flag;
            owns(p); enabled==enabled; tag==tag;
        }
        fn main()->u64 {
            let p=alloc<Cell>(1); p.flag=true;
            fold Ready(p,7usize) with (enabled=true);
            unfold Ready(p,7usize) as (saved);
            fold Ready(p,7usize) with (enabled=saved);
            let q=forward(p,7usize); return consume(q,7usize);
        }
        fn forward(p:Own<Cell>,tag:usize)->Own<Cell>
        requires Ready(p,tag); ensures Ready(result,old(tag)); {return p;}
        fn consume(p:Own<Cell>,tag:usize)->u64 requires Ready(p,tag); {
            unfold Ready(p,tag); free(p); finish Ready(p,tag); return 42;
        }
";
    checked(source);
    rejected(&source.replace("enabled=true", "enabled=false"));
    rejected(&source.replace(
        "fold Ready(p,7usize) with (enabled=saved);",
        "p.flag=false; fold Ready(p,7usize) with (enabled=saved);",
    ));
    rejected(&source.replace("p.flag=true;", ""));
    rejected(&source.replace("forward(p,7usize)", "forward(p,8usize)"));
    let output = accepted(source);
    let mut tables = hir_tables(output.hir().unwrap());
    tables.predicates[0]
        .representation
        .as_mut()
        .unwrap()
        .witnesses[0]
        .offset = 1;
    assert!(HirProgram::from_tables(tables).is_err());
    let mut unit = output.vir().unwrap().as_unit().clone();
    unit.specs.predicates_mut()[0]
        .representation
        .as_mut()
        .unwrap()
        .witnesses[0]
        .offset = 1;
    assert!(unit.into_validated().is_err());
}

#[test]
fn projected_entry_fields_remain_equal_to_their_opened_witnesses() {
    for (ty, value, other) in [("bool", "true", "false"), ("u64", "42", "43")] {
        let source = format!(
            "struct Cell {{value:{ty},}}
            predicate Ready(p:ptr<Cell>) {{
                exists saved:{ty} = p.value;
                owns(p); saved==p.value;
            }}
                fn main()->u64 {{
                let p=alloc<Cell>(1); p.value={value}; fold Ready(p);
                let q=forward(p); return consume(q);
            }}
        fn forward(p:Own<Cell>)->Own<Cell>
            requires Ready(p); ensures Ready(result); {{
                unfold Ready(p) as (before);
                fold Ready(p) with (saved=before);
                return p;
            }}
            fn consume(p:Own<Cell>)->u64 requires Ready(p); {{
                unfold Ready(p); free(p); finish Ready(p); return 42;
            }}
"
        );
        checked(&source);
        if ty == "u64" {
            checked(&source.replace(
                "requires Ready(p); ensures Ready(result);",
                "requires Ready(p); requires p.value<=42; ensures Ready(result);",
            ));
        }
        rejected(&source.replace(
            "fold Ready(p) with (saved=before);",
            &format!("p.value={other}; fold Ready(p) with (saved=before);"),
        ));
    }
}

#[test]
fn predicate_interfaces_accept_the_bounded_pure_operator_profile() {
    let source = "struct Cell {value:u64,}
        predicate Ready(p:ptr<Cell>,count:usize,enabled:bool) {
            owns(p); initialized(p.value,0..1); count==count; enabled==enabled;
        }
        fn main()->u64 {
            let p=alloc<Cell>(1); p.value=42; fold Ready(p,0usize,true);
            let q=forward(p,7usize,false); return consume(q);
        }
        fn forward(p:Own<Cell>,limit:usize,flag:bool)->Own<Cell>
        requires Ready(p,limit-limit,!flag && true);
        ensures Ready(result,old(limit-limit),old(!flag && true)); {return p;}
        fn consume(p:Own<Cell>)->u64 requires Ready(p,0usize,true); {
            unfold Ready(p,0usize,true); let value=p.value;
            free(p); finish Ready(p,0usize,true); return value;
        }
        ";
    let explicit = checked(source);
    let implicit = checked(
        &source
            .replace("old(limit-limit)", "limit-limit")
            .replace("old(!flag && true)", "!flag && true"),
    );
    for (a, b) in explicit
        .vir()
        .unwrap()
        .as_unit()
        .specs
        .predicate_interfaces()
        .iter()
        .zip(
            implicit
                .vir()
                .unwrap()
                .as_unit()
                .specs
                .predicate_interfaces(),
        )
    {
        assert_eq!(
            a.arguments, b.arguments,
            "rich old actuals must use the same entry slots"
        );
    }
    let packed = format!(
        "struct Box {{value:Own<Cell>,}} {}",
        source
            .replace("flag:bool)->Own<Cell>", "flag:bool)->Box")
            .replace(
                "Ready(result,old(limit-limit)",
                "Ready(result.value,old(limit-limit)"
            )
            .replace("{return p;}", "{return Box {value:p};}")
            .replace("consume(q)", "consume(q.value)")
    );
    checked(&packed);
    let in_place = source
        .replace("fn forward(p:Own<Cell>,", "fn forward(p:&mut Cell,")
        .replace("flag:bool)->Own<Cell>", "flag:bool)->u64")
        .replace("Ready(result,old(limit-limit)", "Ready(p,old(limit-limit)")
        .replace("{return p;}", "{return 0;}")
        .replace(
            "let q=forward(p,7usize,false); return consume(q);",
            "let ignored=forward(&mut *p,7usize,false); return consume(p);",
        );
    checked(&in_place);
    for zero in ["limit * 0usize", "0usize * limit", "(limit-limit)*2usize"] {
        checked(&source.replace("limit-limit", zero));
    }
    for boolean in [
        "!flag || false",
        "!(flag && true)",
        "!flag && (limit==limit)",
    ] {
        checked(&source.replace("!flag && true", boolean));
    }
    for bad in [
        "limit-1usize", // unknown entry may underflow
        "limit*2usize", // unknown entry may overflow
        "limit*limit",  // non-affine multiplication
        "limit*0u64",   // nominal types must agree
        "side_effect(limit)-limit",
        "old(limit)-limit", // old in requires
    ] {
        rejected(&source.replace("limit-limit", bad));
    }
    rejected(&source.replace("old(!flag && true)", "old(flag || false)"));
    rejected(&source.replace("old(limit-limit)", "old(old(limit)-limit)"));
    rejected(&source.replace("old(limit-limit)", "old(result.value-1)"));
    rejected(&source.replace("old(!flag && true)", "old(!flag && true,flag)"));
    rejected(&source.replace(
        "Ready(result,old(limit-limit)",
        "Ready(result+1,old(limit-limit)",
    ));
    rejected(&source.replace("!flag && true", &format!("{}flag", "!".repeat(256))));
    rejected(&source.replace(
        "old(limit-limit)",
        &format!("{}limit{}", "old(".repeat(256), ")".repeat(256),),
    ));
    rejected(&source.replace(
        "Ready(p,limit-limit,!flag && true)",
        &format!("Ready(p,{})", vec!["!flag"; 33].join(","),),
    ));
    // Logical operators still cannot be used in ordinary runtime expressions.
    rejected("fn main()->u64 {assert true && true; return 0;}");
}

#[test]
fn unknown_comparison_actuals_survive_normal_predicate_forwarding() {
    for (operator, a, b) in [
        ("<", 1, 2),
        ("<=", 1, 2),
        (">", 2, 1),
        (">=", 2, 1),
        ("==", 1, 1),
        ("!=", 1, 2),
    ] {
        let source = format!("struct Cell {{value:u64,}}
            predicate Ready(p:ptr<Cell>,same:bool) {{owns(p); initialized(p.value,0..1); same==same;}}
                fn main()->u64 {{
                let p=alloc<Cell>(1); p.value=42; fold Ready(p,true);
                let q=forward(p,{a}usize,{b}usize); return consume(q);
            }}
        fn forward(p:Own<Cell>,a:usize,b:usize)->Own<Cell>
            requires Ready(p,a {operator} b);
            ensures Ready(result,old(a {operator} b)); {{return p;}}
            fn consume(p:Own<Cell>)->u64 requires Ready(p,true); {{
                unfold Ready(p,true); let value=p.value; free(p); finish Ready(p,true); return value;
            }}
");
        checked(&source);
        rejected(&source.replace(
            &format!("old(a {operator} b)"),
            &format!("old(!(a {operator} b))"),
        ));
        // The caller establishes the true comparison. Its sealed constraint
        // is a legitimate callee premise, including when the inputs are abstract.
        checked(&source.replace("same==same", "same==true"));
        let contradictory = source.replace("same==same", "same==false");
        accepted(&contradictory);
        rejected(&contradictory);
    }
}

#[test]
fn comparison_predicate_arguments_follow_proven_branch_bounds() {
    let source = "struct Cell {value:u64,}
        predicate Ready(p:ptr<Cell>,small:bool) {owns(p); initialized(p.value,0..1); small==small;}
        fn main()->u64 {
            let p=alloc<Cell>(1); p.value=42; fold Ready(p,true); return consume(p,1usize);
        }
        fn consume(p:Own<Cell>,a:usize)->u64 requires Ready(p,a<4usize); {
            if a<4usize {
                unfold Ready(p,true); free(p); finish Ready(p,true); return 42;
            } else {
                unfold Ready(p,false); free(p); finish Ready(p,false); return 0;
            }
        }
";
    checked(source);
    checked(&source.replace(
        "fold Ready(p,true); return consume(p,1usize)",
        "fold Ready(p,false); return consume(p,7usize)",
    ));
    rejected(&source.replace("unfold Ready(p,true)", "unfold Ready(p,false)"));
    rejected(&source.replace("unfold Ready(p,false)", "unfold Ready(p,true)"));
    for (operator, value) in [
        ("<", 1),
        ("<=", 1),
        (">", 7),
        (">=", 7),
        ("==", 4),
        ("!=", 1),
    ] {
        let source = source
            .replace("a<4usize", &format!("a {operator} 4usize"))
            .replace("consume(p,1usize)", &format!("consume(p,{value}usize)"));
        checked(&source);
        rejected(&source.replace("unfold Ready(p,true)", "unfold Ready(p,false)"));
        rejected(&source.replace("unfold Ready(p,false)", "unfold Ready(p,true)"));
    }
}

#[test]
fn comparison_predicate_arguments_follow_relational_branches() {
    for (operator, a, b) in [
        ("<", 1, 2),
        ("<=", 1, 2),
        (">", 2, 1),
        (">=", 2, 1),
        ("==", 1, 1),
        ("!=", 1, 2),
    ] {
        let source = format!("struct Cell {{value:u64,}}
            predicate Ready(p:ptr<Cell>,small:bool) {{owns(p); initialized(p.value,0..1); small==small;}}
                fn main()->u64 {{
                let p=alloc<Cell>(1); p.value=42; fold Ready(p,true); return consume(p,{a}usize,{b}usize);
            }}
        fn consume(p:Own<Cell>,a:usize,b:usize)->u64 requires Ready(p,a {operator} b); {{
                if a {operator} b {{
                    unfold Ready(p,true); free(p); finish Ready(p,true); return 42;
                }} else {{
                    unfold Ready(p,false); free(p); finish Ready(p,false); return 0;
                }}
            }}
");
        checked(&source);
        rejected(&source.replace("unfold Ready(p,true)", "unfold Ready(p,false)"));
        rejected(&source.replace("unfold Ready(p,false)", "unfold Ready(p,true)"));
    }
}

#[test]
fn predicate_postconditions_distinguish_scalar_results_from_entry_slots() {
    let source = include_str!("../spec/cases/verify/predicate-logical-result.nera");
    let output = checked(source);
    checked(&source.replace(
        "return n;",
        "unfold Ready(p,n); fold Ready(p,8usize); return 8usize;",
    ));
    assert!(
        output
            .vir()
            .unwrap()
            .as_unit()
            .specs
            .predicate_interfaces()
            .iter()
            .filter(|interface| interface.ensures)
            .all(|interface| interface
                .arguments
                .inputs
                .iter()
                .any(|(_, input)| matches!(input, predicate_logic::WitnessInput::Result(_))))
    );
    checked(&source.replace("usize", "bool").replace("7bool", "true"));
    let wrong = source.replace("return n;", "return 0usize;");
    let output = accepted(&wrong);
    assert!(
        !verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default()
        )
        .unwrap()
        .is_memory_checked_core0()
    );
    for bad in [
        source.replace("Ready(p,result)", "Ready(p,old(result))"),
        source.replace("requires Ready(p,n)", "requires Ready(p,result)"),
    ] {
        let output = analyze(&SourceFile::from_text("bad-result.nera", bad));
        assert!(
            output.vir().is_none(),
            "result cannot denote an entry value"
        );
    }
    let output = accepted(source);
    for mutation in 0..3 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let interface = unit
            .specs
            .predicate_interfaces_mut()
            .iter_mut()
            .find(|i| i.ensures)
            .unwrap();
        let input = interface
            .arguments
            .inputs
            .iter_mut()
            .find(|(_, input)| matches!(input, predicate_logic::WitnessInput::Result(_)))
            .unwrap();
        match mutation {
            0 => input.1 = predicate_logic::WitnessInput::Result(u32::MAX),
            1 => input.0 = predicate_logic::LogicType::U64,
            _ => interface.ensures = false,
        }
        assert!(unit.validate().is_err());
    }
    let mut tables = hir_tables(output.hir().unwrap());
    let interface = tables
        .specs
        .predicate_interfaces
        .iter_mut()
        .find(|i| i.ensures)
        .unwrap();
    interface
        .arguments
        .inputs
        .iter_mut()
        .find(|(_, input)| matches!(input, predicate_logic::WitnessInput::Result(_)))
        .unwrap()
        .1 = predicate_logic::WitnessInput::Result(HirLocalId::new(1));
    assert!(HirProgram::from_tables(tables).is_err());
}

#[test]
fn logical_prefix_counts_require_actual_bytes_and_keep_nominal_types() {
    let source = include_str!("../spec/cases/verify/predicate-logical-prefix.nera");
    checked(source);
    checked(&source.replace("0usize..n", "0usize..n+0usize"));
    checked(&source.replace("usize", "u64"));
    for source in [
        source.replace("p.slots[1]=22;", ""),
        source.replace("p.slots[1]=22;", "p.slots[2]=22;"),
        source.replace("2usize", "5usize"),
        source.replace("relay(p,2usize)", "relay(p,3usize)"),
    ] {
        accepted(&source);
        rejected(&source);
    }
    let output = accepted(source);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let prefix = &mut unit.specs.predicates_mut()[0]
        .representation
        .as_mut()
        .unwrap()
        .prefixes[0];
    let nera::PredicatePrefixCount::Logical(expression) = &mut prefix.count else {
        panic!("logical count lost");
    };
    expression.nodes[0].ty = nera::predicate_logic::LogicType::Bool;
    assert!(unit.into_validated().is_err());
}

#[test]
fn predicate_result_fields_use_direct_leaves_and_typed_indirect_storage() {
    use predicate_logic::{LogicType, WitnessInput};
    let source = include_str!("../spec/cases/verify/predicate-logical-result-field.nera");
    let output = checked(source);
    let unit = output.vir().unwrap().as_unit();
    assert!(
        unit.specs
            .predicate_interfaces()
            .iter()
            .flat_map(|i| &i.arguments.inputs)
            .any(|(_, i)| matches!(i, WitnessInput::Result(_)))
    );
    assert!(
        unit.specs
            .predicate_interfaces()
            .iter()
            .flat_map(|i| &i.arguments.inputs)
            .any(|(_, i)| matches!(i, WitnessInput::ResultField { .. }))
    );
    checked(&source.replace("result.meta.count", "result.meta.count+0usize"));
    for source in [
        source.replace("count:n", "count:0usize"),
        source.replace("valid:true", "valid:false"),
    ] {
        accepted(&source);
        rejected(&source);
    }
    for source in [
        source.replace("result.meta.count", "old(result.meta.count)"),
        source.replace("result.meta.count", "result.owner"),
        source.replace("result.meta.count", "result.meta.valid"),
    ] {
        assert!(
            analyze(&SourceFile::from_text("invalid-result-field.nera", source))
                .vir()
                .is_none()
        );
    }
    for mutation in 0..4 {
        let mut bad = unit.clone();
        let interface = bad
            .specs
            .predicate_interfaces_mut()
            .iter_mut()
            .find(|i| {
                i.arguments
                    .inputs
                    .iter()
                    .any(|(_, v)| matches!(v, WitnessInput::ResultField { .. }))
            })
            .unwrap();
        let (ty, input) = interface
            .arguments
            .inputs
            .iter_mut()
            .find(|(_, v)| matches!(v, WitnessInput::ResultField { .. }))
            .unwrap();
        let WitnessInput::ResultField { base, offset, .. } = input else {
            unreachable!()
        };
        match mutation {
            0 => *base = u32::MAX,
            1 => *offset = u64::MAX,
            2 => *ty = LogicType::Bool,
            3 => interface.ensures = false,
            _ => unreachable!(),
        }
        assert!(bad.into_validated().is_err());
    }
    let mut hir = hir_tables(output.hir().unwrap());
    let interface = hir
        .specs
        .predicate_interfaces
        .iter_mut()
        .find(|i| {
            i.arguments
                .inputs
                .iter()
                .any(|(_, v)| matches!(v, WitnessInput::ResultField { .. }))
        })
        .unwrap();
    let (_, WitnessInput::ResultField { offset, .. }) = interface
        .arguments
        .inputs
        .iter_mut()
        .find(|(_, v)| matches!(v, WitnessInput::ResultField { .. }))
        .unwrap()
    else {
        unreachable!()
    };
    *offset = 1;
    assert!(HirProgram::from_tables(hir).is_err());
}

#[test]
fn predicate_memory_arguments_distinguish_entry_from_current_observations() {
    use predicate_logic::{ObservationTime, WitnessInput};
    let source = include_str!("../spec/cases/verify/predicate-memory-coordinates.nera");
    let boolean = source
        .replace("cursor:usize", "cursor:bool")
        .replace("saved:usize", "saved:bool")
        .replace(
            "fn advance(p:&mut Cell)->usize",
            "fn advance(p:&mut Cell)->bool",
        )
        .replace(
            "if old<4usize { p.cursor=old+1usize; }",
            "if old { p.cursor=false; } else { p.cursor=true; }",
        )
        .replace("p.cursor=0usize;", "p.cursor=false;");
    checked(&boolean);
    rejected(&boolean.replace(
        "ensures Ready(p,old(p.cursor));",
        "ensures Ready(p,p.cursor);",
    ));
    let output = checked(source);
    let interfaces = output.vir().unwrap().as_unit().specs.predicate_interfaces();
    assert!(
        interfaces
            .iter()
            .flat_map(|i| &i.arguments.inputs)
            .any(|(_, i)| matches!(
                i,
                WitnessInput::Memory {
                    time: ObservationTime::Entry,
                    ..
                }
            ))
    );
    assert!(
        interfaces
            .iter()
            .flat_map(|i| &i.arguments.inputs)
            .any(|(_, i)| matches!(
                i,
                WitnessInput::Memory {
                    time: ObservationTime::Current,
                    ..
                }
            ))
    );
    let wrong = source.replace(
        "ensures Ready(p,old(p.cursor));",
        "ensures Ready(p,p.cursor);",
    );
    accepted(&wrong);
    rejected(&wrong);
    let wrong = source.replace("p.cursor=0usize;", "");
    accepted(&wrong);
    rejected(&wrong);
    assert!(
        analyze(&SourceFile::from_text(
            "invalid-old.nera",
            source.replace(
                "requires Ready(p,p.cursor);",
                "requires Ready(p,old(p.cursor));"
            )
        ))
        .vir()
        .is_none()
    );
    for mutation in 0..4 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let interface = unit
            .specs
            .predicate_interfaces_mut()
            .iter_mut()
            .find(|i| !i.ensures)
            .unwrap();
        let (
            _,
            WitnessInput::Memory {
                base,
                offset,
                access,
                time,
            },
        ) = &mut interface.arguments.inputs[0]
        else {
            panic!("missing typed memory actual");
        };
        match mutation {
            0 => *time = ObservationTime::Entry,
            1 => *offset = 1,
            2 => *base = u32::MAX,
            3 => access.layout = VirLayoutId::new(u32::MAX),
            _ => unreachable!(),
        }
        assert!(unit.into_validated().is_err());
    }
}

#[test]
fn opened_witnesses_are_typed_ghost_snapshots_in_loop_invariants() {
    let source = include_str!("../spec/cases/verify/predicate-opened-loop.nera");
    let output = checked(source);
    let snapshots: Vec<_> = output
        .vir()
        .unwrap()
        .as_unit()
        .specs
        .terms()
        .iter()
        .filter(|term| {
            matches!(
                term.kind,
                VirSpecTermKind::Snapshot(VirSpecSnapshot::Opened { .. })
            )
        })
        .collect();
    assert_eq!(snapshots.len(), 2);
    for mutation in 0..4 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let term = unit
            .specs
            .terms_mut()
            .iter_mut()
            .find(|term| {
                matches!(
                    term.kind,
                    VirSpecTermKind::Snapshot(VirSpecSnapshot::Opened { .. })
                )
            })
            .unwrap();
        let VirSpecTermKind::Snapshot(VirSpecSnapshot::Opened {
            function,
            action,
            holder,
            binder,
        }) = &mut term.kind
        else {
            unreachable!()
        };
        match mutation {
            0 => *function = VirFunctionId::new(u32::MAX),
            1 => *action = u32::MAX,
            2 => *holder = u32::MAX,
            _ => *binder = u32::MAX,
        }
        assert!(unit.validate().is_err());
    }
    let mut hir = hir_tables(output.hir().unwrap());
    let term = hir
        .specs
        .terms
        .iter_mut()
        .find(|term| {
            matches!(
                term.kind,
                HirSpecTermKind::Snapshot(HirSpecSnapshot::Opened { .. })
            )
        })
        .unwrap();
    let HirSpecTermKind::Snapshot(HirSpecSnapshot::Opened { binder, .. }) = &mut term.kind else {
        unreachable!()
    };
    *binder = u32::MAX;
    assert!(HirProgram::from_tables(hir).is_err());
    rejected(&source.replace("invariant saved<=7usize;", "invariant saved<0usize;"));
    rejected(&source.replace("invariant on;", "invariant !on;"));
    rejected(&source.replace("let outcome=p.value;", "let outcome=saved;"));
    rejected(&source.replace(
        "let mut i=0usize;",
        "fold Ready(p) with (used=saved,enabled=on); unfold Ready(p); let mut i=0usize;",
    ));
    rejected(&source.replace(
        "i=i+1usize;",
        "fold Ready(p) with (used=saved,enabled=on); unfold Ready(p); i=i+1usize;",
    ));
    rejected(&source.replace(
        "unfold Ready(p) as (saved,on);",
        "if true { unfold Ready(p) as (saved,on); }",
    ));
}

#[test]
fn opened_binders_cannot_be_captured_by_another_predicate_instance() {
    let source = r#"
struct Cell { value:u64, }
predicate Source(p:ptr<Cell>) {
    exists used:usize = 6usize;
    owns(p); initialized(p.value,0..1); used<=7usize;
}
predicate Target(p:ptr<Cell>,n:usize) {
    owns(p); initialized(p.value,0..1); n<=7usize;
}
fn main()->u64 {
    let p=alloc<Cell>(1); p.value=1;
    let q=alloc<Cell>(1); q.value=42;
    fold Source(p);
    unfold Source(p) as (saved);
    fold Target(q,saved);
    unfold Target(q,saved);
    let outcome=q.value;
    free(q); finish Target(q,saved);
    free(p); finish Source(p);
    return outcome;
}
"#;
    rejected(source);
    rejected(&source.replace("q.value=42;", ""));
    rejected(&source.replace(
        "fold Target(q,saved);",
        "fold Source(p) with (used=saved); unfold Source(p); fold Target(q,saved);",
    ));
    rejected(&source.replace("fold Target(q,saved);", "fold Target(p,saved);"));
}

#[test]
fn opened_invariants_match_symbolic_package_guarantees_by_leaf_identity() {
    let source = include_str!("../spec/cases/verify/predicate-opened-symbolic-loop.nera");
    checked(source);
    rejected(&source.replace("invariant saved<=limit;", "invariant saved<limit;"));
    rejected(&source.replace("invariant saved<=limit;", "invariant saved==limit;"));
    rejected(&source.replace("invariant saved<=limit;", "invariant limit<saved;"));
}

#[test]
fn scalar_induction_preserves_an_untouched_sealed_package() {
    let source = r#"
struct Cell { value:u64, }
predicate Ready(p:ptr<Cell>) { owns(p); initialized(p.value,0..1); }
fn main()->u64 {
    let p=alloc<Cell>(1); p.value=42; fold Ready(p);
    let q=walk(p,3usize); unfold Ready(q);
    let outcome=q.value; free(q); finish Ready(q); return outcome;
}
fn walk(p:Own<Cell>,limit:usize)->Own<Cell>
requires Ready(p);
ensures Ready(result);
{
    let mut i=0usize;
    while i<limit {
        invariant i<=limit;
        i=i+1usize;
    }
    return p;
}

"#;
    checked(source);
    rejected(&source.replace("i=i+1usize;", "p.value=0; i=i+1usize;"));
    rejected(&source.replace("i=i+1usize;", "unfold Ready(p); i=i+1usize;"));
}

#[test]
fn opened_affine_guarantees_prove_strict_bounds_without_exposing_hidden_ssa() {
    let source = include_str!("../spec/cases/verify/predicate-opened-affine-loop.nera");
    checked(source);
    checked(&source.replace("invariant saved<limit;", "invariant saved<=limit;"));
    for mutation in [
        source.replace("invariant saved<limit;", "invariant saved==limit;"),
        source.replace("invariant saved<limit;", "invariant limit<=saved;"),
        source.replace("used+1usize<=limit;", "used<=limit;"),
    ] {
        // This is a semantic negative: parsing and independent VIR admission
        // must succeed before the proof is rejected.
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded negative analysis");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
}

#[test]
fn hidden_relation_chains_survive_loop_frames_and_discharge_refold_constraints() {
    let source = include_str!("../spec/cases/verify/predicate-refold-relations.nera");
    checked(source);
    for mutation in [
        source.replace("high=lo);", "high=limit);"),
        source.replace("high=lo);", "high=hi+1usize);"),
        source.replace("invariant lo<limit;", "invariant lo==limit;"),
        source.replace("high<limit;", "high<=limit;"),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded relation negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
}

#[test]
fn opened_scalar_argument_matching_uses_established_equality() {
    let source = include_str!("../spec/cases/verify/predicate-opened-argument-equality.nera");
    let output = checked(source);
    for mutation in [
        source.replace("used==limit;", "used<=limit;"),
        source.replace("finish Ready(p,saved);", "finish Ready(p,0usize);"),
        source.replace("finish Ready(p,saved);", "finish Ready(p,saved+1usize);"),
        source.replace("finish Ready(p,saved);", "finish Ready(p,first);"),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded argument equality negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
    rejected(&source.replace("free(p);", ""));
    fn corrupt<V, T>(input: &mut predicate_logic::WitnessInput<V, T>, mutation: usize) {
        let predicate_logic::WitnessInput::Opened {
            action,
            holder,
            binder,
        } = input
        else {
            panic!("expected opened finish argument");
        };
        match mutation {
            0 => *action = u32::MAX,
            1 => *holder = u32::MAX,
            _ => *binder = u32::MAX,
        }
    }
    for mutation in 0..3 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let finish = unit
            .specs
            .predicate_actions_mut()
            .iter_mut()
            .find(|a| matches!(a.kind, VirPredicateActionKind::Finish { .. }))
            .unwrap();
        corrupt(&mut finish.witnesses.inputs[0].1, mutation);
        assert!(unit.validate().is_err());
        let mut tables = hir_tables(output.hir().unwrap());
        let finish = tables
            .specs
            .predicate_actions
            .iter_mut()
            .find(|a| matches!(a.kind, HirPredicateActionKind::Finish { .. }))
            .unwrap();
        corrupt(&mut finish.witnesses.inputs[0].1, mutation);
        assert!(HirProgram::from_tables(tables).is_err());
    }
}

#[test]
fn sealed_loop_packages_allow_refolded_witnesses_but_require_resource_preservation() {
    let source = include_str!("../spec/cases/verify/predicate-loop-refold.nera");
    checked(source);
    checked(&source.replace("3usize);", "0usize);"));
    for mutation in [
        source.replace("fold Ready(p,limit) with (used=0usize);", ""),
        source.replace(
            "fold Ready(p,limit) with (used=limit);",
            "fold Ready(p,0usize) with (used=0usize);",
        ),
        source.replace("used=limit);", "used=limit+1usize);"),
        source.replace("i=i+1usize;", "unfold Ready(p,limit); i=i+1usize;"),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded loop refold negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
    checked(&source.replace("if i==0usize {", "p.value=0; if i==0usize {"));
}

#[test]
fn loop_refolds_restore_written_scalar_representation_on_every_backedge() {
    let source = include_str!("../spec/cases/verify/predicate-loop-write.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    checked(&source.replace("3usize);", "0usize);"));
    let borrowed = source
        .replace(
            "fn update(p:Own<Cell>,steps:usize)->Own<Cell>",
            "fn update(p:&mut Cell,steps:usize)->u64",
        )
        .replace("ensures Ready(result);", "ensures Ready(p);")
        .replace("return p;", "return 0;")
        .replace(
            "let q=update(p,3usize);",
            "let ignored=update(&mut *p,3usize); let q=p;",
        );
    checked(&borrowed);
    for mutation in [
        source.replace("p.value=previous+1;", "p.value=43;"),
        source.replace("p.value=42;\n            fold Ready(p);", "p.value=42;"),
        source.replace("unfold Ready(p);\n        let previous", "let previous"),
        source.replace("i=i+1usize;", "unfold Ready(p); i=i+1usize;"),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded loop write negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
}

#[test]
fn loop_field_snapshots_remain_related_only_until_the_actual_cell_changes() {
    let source = include_str!("../spec/cases/verify/predicate-loop-observation.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    checked(&source.replace("3usize);", "0usize);"));
    // A runtime load preserves the actual current observation identity.
    checked(&source.replace("p.value=previous+1;", "p.value=previous;"));
    for mutation in [
        source.replace(
            "p.value=previous+1;\n            fold Ready(p);",
            "p.value=previous+1;\n            fold Ready(p) with (saved=previous);",
        ),
        source.replace(
            "p.value=previous+1;\n            fold Ready(p);",
            "p.value=previous+1;\n            fold Ready(p) with (saved=snapshot);",
        ),
        source.replace(
            "p.value=42;\n            fold Ready(p);",
            "p.value=42;\n            fold Ready(p) with (saved_flag=previous_flag);",
        ),
        source.replace(
            "p.value=42;\n            fold Ready(p);",
            "p.value=42;\n            fold Ready(p) with (saved_flag=snapshot_flag);",
        ),
        source.replace("p.flag=false;", ""),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded loop observation negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
}

#[test]
fn loop_prefix_updates_require_each_new_element_before_advancing_the_count() {
    let source = include_str!("../spec/cases/verify/predicate-loop-prefix.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    checked(&source.replace("3usize);", "0usize);"));
    for mutation in [
        source.replace("p.slots[n]=42;", ""),
        source.replace("p.cursor=n+1usize;", "p.cursor=n+2usize;"),
        source.replace("p.slots[n]=42;", "p.slots[0]=42;"),
        source.replace("let outcome=q.slots[0];", "let outcome=q.slots[7];"),
        source.replace("p.cursor=0usize;", "p.cursor=1usize;"),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded loop prefix negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
}

#[test]
fn hidden_prefix_expressions_use_correlations_and_actual_initialized_bytes() {
    let source = include_str!("../spec/cases/verify/predicate-correlated-prefix.nera");
    checked(source);
    checked(&source.replace("high<=low+1usize", "high<=low+2usize"));
    for mutation in [
        source
            .replace("high<=low+1usize;", "high<=low+2usize;")
            .replace("high=4usize", "high=5usize"),
        source.replace("p.slots[0]=42;", ""),
        source.replace("let outcome=q.slots[0];", "let outcome=q.slots[1];"),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded correlated prefix negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
    // These mutations remove the domain proof for the prefix expression in
    // requires. No valid entry representation can be built for relay; this is
    // distinct from a well-formed interface whose caller lacks actual bytes.
    for mutation in [
        source.replace("low<=high;", ""),
        source.replace("0usize..high-low", "0usize..low-high"),
    ] {
        let output = accepted(&mutation);
        let error = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .unwrap_err();
        assert!(
            matches!(error,
                VerificationError::Cfg { function, error: nera::verifier::CfgAnalysisError::PredicateEntry {
                    predicate, error: nera::verifier::PredicateError::UnprovedRepresentation,
                } } if function == VirFunctionId::new(1) && predicate == VirPredicateId::new(0)
            ),
            "wrong failure layer: {error:?}"
        );
        assert!(
            error
                .to_string()
                .contains("entry representation for predicate0")
        );
    }
}

#[test]
fn hidden_prefixes_reuse_existing_bytes_without_initializing_the_rest() {
    let source = include_str!("../spec/cases/verify/predicate-hidden-prefix.nera");
    checked(source);
    for mutation in [
        source.replace("p.slots[0]=42;", ""),
        source.replace("used=1usize", "used=2usize"),
        source.replace("let outcome=q.slots[0];", "let outcome=q.slots[1];"),
    ] {
        let output = accepted(&mutation);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("bounded prefix negative");
        assert!(
            !report.is_memory_checked_core0(),
            "unexpectedly checked: {mutation}"
        );
    }
}

#[test]
fn ordinary_calls_repack_loop_owners_and_reestablish_current_observations() {
    let source = include_str!("../spec/cases/verify/predicate-loop-call.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)],
    );
    checked(&source.replace("3usize);", "0usize);"));
    // Two returns use fresh holders; neither transfers the first call's SSA.
    checked(&source.replace("current=step(current);", "current=step(step(current));"));
    for mutation in [
        source.replace("p.value=previous+1;", "p.value=43;"),
        source.replace("fold Ready(p);\n    return p;", "return p;"),
        source.replace(
            "current=step(current);",
            "current=step(current); unfold Ready(current); current.value=43; fold Ready(current);",
        ),
        source.replace(
            "current=step(current);",
            "current=step(current); unfold Ready(current);",
        ),
        source.replace("p.flag=false;", ""),
    ] {
        rejected(&mutation);
    }
}

#[test]
fn branch_calls_keep_equivalent_abstract_binders_and_actual_owner_carriers() {
    let source = include_str!("../spec/cases/verify/predicate-branch-call.nera");
    for source in [
        source.to_owned(),
        source.replace("choose(p,true)", "choose(p,false)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("used=3usize", "used=8usize"),
        source.replace("p.value=42;", "p.value=43;"),
        source.replace(
            "current=refresh(current);",
            "current=refresh(current); unfold Ready(current);",
        ),
        source.replace("fold Ready(p) with (used=3usize);", ""),
    ] {
        rejected(&source);
    }
}

#[test]
fn branch_call_order_matches_distinct_packages_without_merging_their_binders() {
    let source = include_str!("../spec/cases/verify/predicate-branch-order.nera");
    for source in [
        source.to_owned(),
        source.replace("choose(p,q,true)", "choose(p,q,false)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("used=3usize", "used=8usize"),
        source.replace("p.value=21;", "p.value=22;"),
        source.replace("fold Ready(p) with (used=3usize);", ""),
        source.replacen(
            "right=refresh(right);",
            "right=refresh(right); unfold Ready(right);",
            1,
        ),
        source.replace("free(right);", ""),
    ] {
        rejected(&source);
    }
}

#[test]
fn branch_refolds_hide_concrete_witnesses_but_keep_only_declared_guarantees() {
    let source = include_str!("../spec/cases/verify/predicate-branch-witness.nera");
    for source in [
        source.to_owned(),
        source.replace("choose(p,true)", "choose(p,false)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("used=2usize", "used=8usize"),
        source.replace("fold Ready(p) with (used=2usize);", ""),
        source.replace("used=saved", "used=saved+7usize"),
        source.replace(
            "fold Ready(p) with (used=2usize);",
            "p.value=43; fold Ready(p) with (used=2usize);",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn branch_captures_from_scalar_calls_keep_the_sealed_existential_guarantee() {
    let source = include_str!("../spec/cases/verify/predicate-branch-capture.nera");
    for call in [
        "choose(p,true,true)",
        "choose(p,true,false)",
        "choose(p,false,true)",
        "choose(p,false,false)",
    ] {
        let output = checked(&source.replace("choose(p,true,true)", call));
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("return 6usize;", "return 8usize;"),
        source.replace("fold Ready(p) with (used=second);", ""),
        source.replace("used=saved", "used=saved+7usize"),
        source.replace(
            "fold Ready(p) with (used=second);",
            "p.value=43; fold Ready(p) with (used=second);",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn branch_public_captures_follow_the_selected_runtime_argument() {
    let source = include_str!("../spec/cases/verify/predicate-branch-parameter.nera");
    for call in [
        "choose(true,true)",
        "choose(true,false)",
        "choose(false,true)",
        "choose(false,false)",
    ] {
        let output = checked(&source.replace("choose(true,true)", call));
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("return 6usize;", "return 8usize;"),
        source.replace("used=2usize", "used=8usize"),
        source.replace(
            "unfold Ready(p,limit) as (saved);",
            "unfold Ready(p,limit+1usize) as (saved);",
        ),
        source.replace("used=saved", "used=saved+7usize"),
        source.replace("fold Ready(p,limit) with (used=2usize);", ""),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_public_parameter_tracks_each_refolded_header_value() {
    let source = include_str!("../spec/cases/verify/predicate-loop-parameter.nera");
    for source in [source.to_owned(), source.replace("run(true)", "run(false)")] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("count=count+1usize;", "count=count+7usize;"),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,count)",
            "count=count+1usize;\n        fold Ready(p,count-1usize)",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,count) with (used=count);",
            "fold Ready(p,count) with (used=count);\n        count=count+1usize;",
        ),
        source.replace("        fold Ready(p,count) with (used=count);", ""),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_expression_parameters_use_arbitrary_head_bounds_and_current_backedge_values() {
    let source = include_str!("../spec/cases/verify/predicate-loop-expression.nera");
    for source in [
        source.to_owned(),
        source.replace("run(true)", "run(false)"),
        source
            .replace("count+1usize)", "2usize*count)")
            .replace("limit<=8usize", "limit<=14usize"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("count=count+1usize;", "count=count+7usize;"),
        source.replace(
            "        fold Ready(p,count+1usize) with (used=count);",
            "        fold Ready(p,count) with (used=count);",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,count+1usize) with (used=count);",
            "fold Ready(p,count+1usize) with (used=count);\n        count=count+1usize;",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_mixed_parameters_keep_fixed_capture_while_rebinding_the_counter() {
    let source = include_str!("../spec/cases/verify/predicate-loop-mixed-parameter.nera");
    for source in [source.to_owned(), source.replace("run(true)", "run(false)")] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("count=count+1usize;", "count=count+7usize;"),
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,base+count-1usize,base) with (used=count);",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,base+count,base) with (used=count);",
            "fold Ready(p,base+count,base) with (used=count);\n        count=count+1usize;",
        ),
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,base+count,base+1usize) with (used=count);",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_difference_parameters_use_relations_and_reject_stale_or_missing_domains() {
    let source = include_str!("../spec/cases/verify/predicate-loop-difference.nera");
    for source in [
        source.to_owned(),
        source.replace("run(true)", "run(false)"),
        source
            .replace("remaining:usize", "fits:bool")
            .replace("    remaining<=7usize;", "")
            .replace("high-low)", "high-low<=3usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace(
            "        invariant low<=high;",
            "        invariant low<=7usize;",
        ),
        source.replace("low=low+1usize;", "low=low+2usize;"),
        source.replace(
            "low=low+1usize;\n        fold Ready(p,high-low) with (used=low);",
            "fold Ready(p,high-low) with (used=low);\n        low=low+1usize;",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_parameters_use_actual_function_entry_histories_without_pinning_updates() {
    let source = include_str!("../spec/cases/verify/predicate-loop-history.nera");
    for source in [
        source.to_owned(),
        source.replace("run(1usize,2usize)", "run(3usize,1usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,base+start,base) with (used=count);",
        ),
        source.replace("count=count+1usize;", "count=count+7usize;"),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,base+count,base) with (used=count);",
            "fold Ready(p,base+count,base) with (used=count);\n        count=count+1usize;",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_parameters_rebase_complete_affine_histories_and_check_current_backedges() {
    let source = include_str!("../spec/cases/verify/predicate-loop-composite-history.nera");
    for source in [
        source.to_owned(),
        source.replace("run(1usize,1usize,2usize)", "run(2usize,2usize,1usize)"),
        source.replace(
            "let mut count=start+offset+1usize;",
            // Runtime multiplication is not in this frontend's admitted
            // subset. Repeated addition keeps the same affine coefficient.
            "let mut count=start+start+1usize;",
        ),
        source.replace(
            "let mut count=start+offset+1usize;",
            "let mut count=start+1usize;",
        ),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("count=count+1usize;", "count=count+7usize;"),
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,base+start+offset+1usize,base) with (used=count);",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,base+count,base) with (used=count);",
            "fold Ready(p,base+count,base) with (used=count);\n        count=count+1usize;",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_parameters_rebase_overlapping_histories_without_reusing_old_values() {
    let source = include_str!("../spec/cases/verify/predicate-loop-overlapping-history.nera");
    for source in [
        source.to_owned(),
        source.replace("run(1usize,2usize)", "run(2usize,1usize)"),
        source.replace("start+base+1usize", "start+start+base"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("count=count+1usize;", "count=count+7usize;"),
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,base+start+base+1usize,base) with (used=count);",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,base+count,base) with (used=count);",
            "fold Ready(p,base+count,base) with (used=count);\n        count=count+1usize;",
        ),
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,count,base) with (used=count);",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_parameters_keep_complete_fixed_origins_across_refold_and_exit() {
    let source = include_str!("../spec/cases/verify/predicate-loop-fixed-composite.nera");
    for source in [
        source.to_owned(),
        source.replace("run(1usize,1usize,1usize)", "run(2usize,0usize,1usize)"),
        source.replace("let base=left+right+1usize;", "let base=left+left+1usize;"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("count=count+1usize;", "count=count+7usize;"),
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,base+start,base) with (used=count);",
        ),
        source.replace(
            "        fold Ready(p,base+count,base) with (used=count);",
            "        fold Ready(p,base+count,left+right) with (used=count);",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,base+count,base) with (used=count);",
            "fold Ready(p,base+count,base) with (used=count);\n        count=count+1usize;",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn numeric_loop_parameters_can_start_at_a_literal_without_losing_capture_identity() {
    let source = include_str!("../spec/cases/verify/predicate-loop-zero.nera");
    for source in [
        source.to_owned(),
        source.replace("let mut count=0usize;", "let mut count=3usize;"),
        source
            .replace("    count<=7usize;", "    count<=15usize;")
            .replace("Ready(p,count)", "Ready(p,2usize*count+1usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace("count=count+1usize;", "count=count+8usize;"),
        source.replace(
            "        fold Ready(p,count) with (used=count);",
            "        fold Ready(p,0usize) with (used=count);",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,count) with (used=count);",
            "fold Ready(p,count) with (used=count);\n        count=count+1usize;",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn loop_comparison_captures_survive_known_entry_truth_and_reject_stale_refolds() {
    let source = include_str!("../spec/cases/verify/predicate-loop-comparison.nera");
    for source in [
        source.to_owned(),
        source.replace("count<3usize", "count<=3usize"),
        source.replace("count<3usize", "count==3usize"),
        source.replace("count<3usize", "!(count<3usize)"),
        source.replace("count<3usize", "(count<3usize)==true"),
        source
            .replace("count<3usize", "count<=7usize")
            .replace("    used<=7usize;", "    used<=7usize;\n    fits;"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace(
            "        fold Ready(p,count<3usize) with (used=count);",
            "        fold Ready(p,true) with (used=count);",
        ),
        source.replace(
            "        fold Ready(p,count<3usize) with (used=count);",
            "        fold Ready(p,count<2usize) with (used=count);",
        ),
        source.replace(
            "count=count+1usize;\n        fold Ready(p,count<3usize) with (used=count);",
            "fold Ready(p,count<3usize) with (used=count);\n        count=count+1usize;",
        ),
        source.replace("    used<=7usize;", "    used<=7usize;\n    !fits;"),
    ] {
        rejected(&source);
    }
}

#[test]
fn known_boolean_loop_parameters_track_current_identity_across_refold() {
    let source = include_str!("../spec/cases/verify/predicate-loop-boolean.nera");
    for source in [
        source.to_owned(),
        source.replace("let mut flag=true;", "let mut flag=false;"),
        source.replace("Ready(p,flag)", "Ready(p,!flag)"),
        source.replace("Ready(p,flag)", "Ready(p,flag==false)"),
        source.replace("Ready(p,flag)", "Ready(p,flag&&true)"),
        source.replace("Ready(p,flag)", "Ready(p,flag||false)"),
        source
            .replace("flag:bool)", "flag:bool,fixed:bool)")
            .replace("    used<=7usize;", "    used<=7usize;\n    fixed;")
            .replace(
                "    let mut flag=true;",
                "    let mut flag=true;\n    let stable=true;",
            )
            .replace("Ready(p,flag)", "Ready(p,flag,stable)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        source.replace(
            "        fold Ready(p,flag) with (used=count);",
            "        fold Ready(p,true) with (used=count);",
        ),
        source.replace(
            "        fold Ready(p,flag) with (used=count);",
            "        fold Ready(p,!flag) with (used=count);",
        ),
        source.replace(
            "if flag { flag=false; } else { flag=true; }\n        fold Ready(p,flag) with (used=count);",
            "fold Ready(p,flag) with (used=count);\n        if flag { flag=false; } else { flag=true; }",
        ),
        source.replace("    used<=7usize;", "    used<=7usize;\n    !flag;"),
    ] {
        rejected(&source);
    }
}

#[test]
fn public_branch_parameters_join_known_booleans_and_distinct_numeric_ranges() {
    let boolean = include_str!("../spec/cases/verify/predicate-branch-boolean.nera");
    let numeric = include_str!("../spec/cases/verify/predicate-branch-bounds.nera");
    for source in [
        boolean.to_owned(),
        boolean.replace("choose(true)", "choose(false)"),
        boolean.replace("Ready(p,flag)", "Ready(p,!flag)"),
        boolean
            .replace("flag=true", "flag=1usize")
            .replace("flag=false", "flag=6usize")
            .replace("Ready(p,flag)", "Ready(p,flag<3usize)"),
        numeric.to_owned(),
        numeric.replace("choose(true)", "choose(false)"),
        numeric
            .replace("    limit<=7usize;", "    limit<=15usize;")
            .replace("Ready(p,limit)", "Ready(p,2usize*limit+1usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        boolean.replace(
            "    unfold Ready(p,flag) as (saved);",
            "    unfold Ready(p,true) as (saved);",
        ),
        boolean.replace(
            "        fold Ready(p,flag) with (used=2usize);",
            "        fold Ready(p,!flag) with (used=2usize);",
        ),
        numeric.replace(
            "    unfold Ready(p,limit) as (saved);",
            "    unfold Ready(p,1usize) as (saved);",
        ),
        numeric.replace(
            "        fold Ready(p,limit) with (used=2usize);",
            "        fold Ready(p,first) with (used=2usize);",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn branch_parameters_align_actual_historical_inputs_at_the_cfg_merge() {
    let numeric = include_str!("../spec/cases/verify/predicate-branch-history.nera");
    let boolean = include_str!("../spec/cases/verify/predicate-branch-bool-history.nera");
    for source in [
        numeric.to_owned(),
        numeric.replace("choose(1usize,6usize,true)", "choose(1usize,6usize,false)"),
        numeric
            .replace("    limit<=7usize;", "    limit<=15usize;")
            .replace("Ready(p,limit)", "Ready(p,2usize*limit+1usize)"),
        numeric
            .replace("limit:usize", "small:bool")
            .replace("    limit<=7usize;\n", "")
            .replace("Ready(p,limit)", "Ready(p,limit<3usize)"),
        boolean.to_owned(),
        boolean.replace("choose(true,false,true)", "choose(true,false,false)"),
        boolean.replace("Ready(p,flag)", "Ready(p,!flag)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for source in [
        numeric.replace(
            "        fold Ready(p,limit) with (used=2usize);",
            "        fold Ready(p,first) with (used=2usize);",
        ),
        numeric.replace(
            "    unfold Ready(p,limit) as (saved);",
            "    unfold Ready(p,first) as (saved);",
        ),
        boolean.replace(
            "        fold Ready(p,flag) with (used=2usize);",
            "        fold Ready(p,first) with (used=2usize);",
        ),
        boolean.replace(
            "    unfold Ready(p,flag) as (saved);",
            "    unfold Ready(p,true) as (saved);",
        ),
    ] {
        rejected(&source);
    }
}

#[test]
fn branch_parameters_align_complete_composite_history_coordinates() {
    let source = include_str!("../spec/cases/verify/predicate-branch-composite-history.nera");
    for program in [
        source.to_owned(),
        source.replace("choose(1usize,3usize,true)", "choose(1usize,3usize,false)"),
        source
            .replace("limit<=7usize;", "limit<=15usize;")
            .replace("Ready(p,limit)", "Ready(p,2usize*limit+1usize)"),
        source
            .replace("limit:usize", "small:bool")
            .replace("    limit<=7usize;\n", "")
            .replace("Ready(p,limit)", "Ready(p,limit<=5usize)"),
    ] {
        let output = checked(&program);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for program in [
        source.replace(
            "    unfold Ready(p,limit) as (saved);",
            "    unfold Ready(p,first) as (saved);",
        ),
        source.replace(
            "        fold Ready(p,limit) with (used=2usize);",
            "        fold Ready(p,second) with (used=2usize);",
        ),
        source.replace(
            "    unfold Ready(p,limit) as (saved);",
            "    limit=5usize;\n    unfold Ready(p,limit) as (saved);",
        ),
    ] {
        rejected(&program);
    }
}

#[test]
fn dependent_branch_coordinates_preserve_separate_actual_arguments() {
    let source = include_str!("../spec/cases/verify/predicate-branch-dependent-history.nera");
    for program in [
        source.to_owned(),
        source.replace("choose(1usize,3usize,true)", "choose(1usize,3usize,false)"),
        source.replace("limit=(count+count+count);", "limit=(count+count);"),
    ] {
        let output = checked(&program);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for actual in [
        "limit,count,count<=limit",
        "count,2usize*count,count<=limit",
    ] {
        rejected(&source.replace(
            "    unfold Ready(p,count,limit,count<=limit) as (saved);",
            &format!("    unfold Ready(p,{actual}) as (saved);"),
        ));
    }
    rejected(&source.replace(
        "    unfold Ready(p,count,limit,count<=limit) as (saved);",
        "    count=1usize;\n    limit=2usize;\n    unfold Ready(p,count,limit,count<=limit) as (saved);",
    ));
}

#[test]
fn compound_boolean_parameters_cross_calls_branches_and_loop_backedges() {
    let branch = include_str!("../spec/cases/verify/predicate-branch-boolean-expression.nera");
    let looping = include_str!("../spec/cases/verify/predicate-loop-boolean-expression.nera");
    for source in [
        branch.to_owned(),
        branch
            .replace(
                "    owns(p);",
                "    exists stored:bool = true;\n    stored==choice;\n    owns(p);",
            )
            .replace(
                "        fold Ready(p,a&&b);",
                "        fold Ready(p,a&&b) with (stored=a&&b);",
            ),
        branch.replace(
            "choose(true,false,false,true)",
            "choose(true,false,false,false)",
        ),
        branch.replace("a&&b", "a||b"),
        branch.replace("a&&b", "a==b"),
        branch.replace("a&&b", "!(a&&b)||(a==b)"),
        looping.to_owned(),
        looping.replace("flag&&(count<3usize)", "flag||(count<3usize)"),
        looping.replace("flag&&(count<3usize)", "flag==(count<3usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&branch.replace("    unfold Ready(p,a&&b);", "    unfold Ready(p,a||b);"));
    rejected(&branch.replace("        fold Ready(p,a&&b);", "        fold Ready(p,a||b);"));
    rejected(&looping.replace(
        "        fold Ready(p,flag&&(count<3usize)) with (used=count);",
        "        fold Ready(p,flag||(count<3usize)) with (used=count);",
    ));
}

#[test]
fn opened_boolean_consequences_cross_calls_loop_frames_and_refold() {
    let source = include_str!("../spec/cases/verify/predicate-opened-boolean-consequences.nera");
    for source in [
        source.to_owned(),
        source.replace("(a||b)&&(b==c);", "!(!a&&!b)&&(b==c);"),
        source.replace("(a||b)&&(b==c);", "(b==c)&&(a||b);"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("invariant y;", "invariant !y;"));
    rejected(&source.replace("invariant z;", "invariant !z;"));
    // An unknown disjunction cannot establish either branch by itself.
    rejected(&source.replace("    !a;", ""));
    // Independent symbols never become equal just because both are unknown.
    rejected(&source.replace("(a||b)&&(b==c);", "a||b;"));
    rejected(&source.replace("(a||b)&&(b==c);", "(a||b)||(b==c);"));
    rejected(&source.replace(
        "fold Ready(p) with (a=x,b=y,c=z);",
        "fold Ready(p) with (a=x,b=!y,c=z);",
    ));
}

#[test]
fn mixed_boolean_numeric_guarantees_cross_calls_loop_frames_and_refold() {
    let source = include_str!("../spec/cases/verify/predicate-opened-mixed-consequences.nera");
    for source in [
        source.to_owned(),
        source.replace("enabled||(used<limit)", "!(!enabled&&!(used<limit))"),
        source.replace("(used<limit)", "!(limit<=used)"),
        source.replace("enabled||(used<limit)", "enabled==(limit<=used)"),
        source
            .replace("enabled:bool = false", "enabled:bool = true")
            .replace("    !enabled;", "    limit<=used;")
            .replace("invariant saved<limit;", "invariant limit<=saved;")
            .replace("invariant !flag;", "invariant flag;")
            .replace("(used=6usize)", "(used=7usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("invariant saved<limit;", "invariant limit<=saved;"));
    rejected(&source.replace("    !enabled;", ""));
    rejected(&source.replace("invariant !flag;", "invariant flag;"));
    rejected(&source.replace("(used=6usize)", "(used=7usize)"));
    rejected(&source.replace(
        "(used=saved,enabled=flag)",
        "(used=saved+7usize,enabled=flag)",
    ));
}

#[test]
fn captured_numeric_comparisons_keep_types_across_calls_opening_and_loops() {
    let source = include_str!("../spec/cases/verify/predicate-captured-comparison-type.nera");
    for source in [
        source.to_owned(),
        source.replace("usize", "u64"),
        source.replace("count<limit", "!(limit<=count)"),
        source
            .replace("count<limit", "false||(count<limit)")
            .replace("6usize<7usize", "false||(6usize<7usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("invariant saved<limit;", "invariant limit<=saved;"));
    rejected(&source.replace("    inside;", ""));
    rejected(
        &source
            .replace("count<limit", "count<=limit")
            .replace("6usize<7usize", "6usize<=7usize"),
    );
    rejected(&source.replace("with (used=saved)", "with (used=saved+1usize)"));
}

#[test]
fn equivalent_boolean_forms_join_and_cross_contracts_using_actual_sources() {
    let source = include_str!("../spec/cases/verify/predicate-branch-boolean-normalization.nera");
    for source in [
        source.to_owned(),
        source.replace(
            "choose(true,false,true,false,true)",
            "choose(true,false,true,false,false)",
        ),
        source.replace("!(!c||(!b||!a))", "c&&(a&&b)"),
        source.replace("!(!c||(!b||!a))", "(b&&c)&&a"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for wrong in ["a||(b&&c)", "!(!c&&(!b||!a))", "a&&(b&&which)", "true"] {
        rejected(&source.replace("!(!c||(!b||!a))", wrong));
    }
    rejected(&source.replace(
        "    unfold Ready(p,c&&(b&&a));",
        "    unfold Ready(p,c||(b&&a));",
    ));
}

#[test]
fn distributive_boolean_parameters_join_then_match_call_and_unfold_arguments() {
    let source = include_str!("../spec/cases/verify/predicate-branch-boolean-equivalence.nera");
    for source in [
        source.to_owned(),
        source.replace(
            "choose(true,false,true,false,true)",
            "choose(true,false,true,false,false)",
        ),
        source.replace(
            "fold Ready(p,a&&(b||c));",
            "fold Ready(p,((a&&b)||(a&&c))&&(a||!a));",
        ),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for wrong in ["a||(b&&c)", "which&&(b||c)", "true", "a&&(b||!c)"] {
        rejected(&source.replace(
            "fold Ready(p,a&&(b||c));",
            &format!("fold Ready(p,{wrong});"),
        ));
    }
    rejected(&source.replace(
        "unfold Ready(p,(a&&c)||(a&&b));",
        "unfold Ready(p,a||(b&&c));",
    ));
}

#[test]
fn actual_numeric_relations_prove_captured_affine_boolean_arguments() {
    let source = include_str!("../spec/cases/verify/predicate-current-affine-facts.nera");
    for source in [source.to_owned(), source.replace("usize", "u64")] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("requires count<limit;", "requires count<=limit;"));
    rejected(&source.replace("    unfold Ready(p,true);", "    unfold Ready(p,false);"));
}

#[test]
fn current_relations_connect_saved_equalities_and_opened_queries() {
    let source = include_str!("../spec/cases/verify/predicate-opened-current-relations.nera");
    for source in [source.to_owned(), source.replace("usize", "u64")] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("requires count<limit;", "requires count<=limit;"));
    rejected(&source.replace("    end==limit;", ""));
    rejected(&source.replace("    used==count;", ""));
    rejected(&source.replace("invariant saved<stop;", "invariant stop<saved;"));
    rejected(&source.replace("invariant saved<limit;", "invariant saved<count;"));
    rejected(&source.replace("with (used=saved,end=stop)", "with (used=stop,end=saved)"));
}

#[test]
fn opened_queries_compose_guarantees_from_distinct_packages() {
    let source = include_str!("../spec/cases/verify/predicate-opened-package-relations.nera");
    for source in [
        source.to_owned(),
        source.replace("usize", "u64"),
        source.replace("invariant saved<stop;", "invariant saved<=stop;"),
        source.replace(
            "    unfold Ready(p,count) as (saved);\n    unfold Ready(q,limit) as (stop);",
            "    unfold Ready(q,limit) as (stop);\n    unfold Ready(p,count) as (saved);",
        ),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("requires count<limit;", "requires count<=limit;"));
    rejected(&source.replace("    used==n;", ""));
    rejected(&source.replace("invariant saved<stop;", "invariant stop<saved;"));
    rejected(&source.replace("invariant saved<stop;", "invariant saved==stop;"));
    rejected(&source.replace("with (used=saved);", "with (used=stop);"));
    rejected(&source.replace(
        "    let mut i=0usize;",
        "    fold Ready(q,limit) with (used=stop);\n    let mut i=0usize;",
    ));
}

#[test]
fn boolean_equalities_between_opened_packages_are_checked_at_loop_boundaries() {
    let source = include_str!("../spec/cases/verify/predicate-opened-package-boolean.nera");
    for source in [
        source.to_owned(),
        source.replace("true", "false"),
        source.replace("invariant left==right;", "invariant right==left;"),
        source.replace("invariant left==right;", "invariant left==flag;"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("    saved==flag;", ""));
    // The packages are related to each other, but the shared flag is unknown.
    rejected(&source.replace("invariant left==right;", "invariant left==true;"));
    rejected(&source.replace("invariant left==right;", "invariant right==false;"));
    rejected(&source.replace(
        "    let mut i=0usize;",
        "    fold Ready(q,flag) with (saved=right);\n    let mut i=0usize;",
    ));
}

#[test]
fn saved_guarantees_define_new_argument_and_witness_arithmetic() {
    let source = include_str!("../spec/cases/verify/predicate-opened-expression-inputs.nera");
    for source in [source.to_owned(), source.replace("usize", "u64")] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("width=hi-lo", "width=lo-hi"));
    rejected(&source.replace("Ready(p,hi3-lo3)", "Ready(p,lo3-hi3)"));
    rejected(&source.replace(
        "width=hi-lo",
        "width=(hi+18446744073709551615usize)-18446744073709551615usize-lo",
    ));
    rejected(
        &source
            .replace("    low<=high;", "    low<=10usize;")
            .replace("    width==high-low;", "    width==width;"),
    );
    rejected(&source.replace(
        "with (low=2usize,high=5usize)",
        "with (low=5usize,high=2usize)",
    ));
}

#[test]
fn opened_arithmetic_queries_preserve_relations_and_check_every_intermediate() {
    let source = include_str!("../spec/cases/verify/predicate-opened-arithmetic-query.nera");
    let paired = include_str!("../spec/cases/verify/predicate-opened-package-relations.nera");
    for source in [
        source.to_owned(),
        source.replace("usize", "u64"),
        paired.replace("invariant saved<stop;", "invariant saved+1usize<=stop;"),
        paired.replace("invariant saved<stop;", "invariant 1usize<=stop-saved;"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    rejected(&source.replace("invariant hi-lo==n;", "invariant lo-hi==n;"));
    rejected(&source.replace("invariant hi-lo==n;", "invariant hi-lo==n+1usize;"));
    rejected(&source.replace(
        "invariant lo+(hi-lo)==hi;",
        "invariant (hi+18446744073709551615usize)-18446744073709551615usize==hi;",
    ));
    rejected(&source.replace(
        "invariant lo+(hi-lo)==hi;",
        "invariant (hi+18446744073709551615usize)*0usize==0usize;",
    ));
    rejected(&source.replace("    n==high-low;", ""));
    rejected(&source.replace(
        "    let mut i=0usize;",
        "    fold Ready(p,n) with (low=lo,high=hi);\n    let mut i=0usize;",
    ));
}

#[test]
fn opened_boolean_queries_use_whole_guarantees_and_keep_nominal_domains_separate() {
    let source = include_str!("../spec/cases/verify/predicate-opened-boolean-query.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for expression in [
        "left",
        "right",
        "left&&right",
        "!left&&!right",
        "(left||right)==(lo-hi==n)",
        "(left||right)==((hi+18446744073709551615usize)-18446744073709551615usize==hi)",
        "(left||right)==(count<=9u64)",
    ] {
        rejected(&source.replace(
            "invariant left||right;",
            &format!("invariant {expression};"),
        ));
    }
    rejected(&source.replace("    a||b;", ""));
    rejected(&source.replace(
        "    let mut i=0usize;",
        "    fold Ready(p,n) with (low=lo,high=hi,a=left,b=right,count=count);\n    let mut i=0usize;",
    ));
}

#[test]
fn joint_opened_guarantees_support_call_loop_and_refold_without_branch_choices() {
    let source = include_str!("../spec/cases/verify/predicate-opened-joint-guarantees.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for missing in ["    a||b;", "    a||!b;"] {
        rejected(&source.replace(missing, ""));
    }
    for wrong in ["!x", "y", "!y", "y||z"] {
        rejected(&source.replace("invariant x;", &format!("invariant {wrong};")));
    }
    rejected(&source.replace("exists a:bool = true;", "exists a:bool = false;"));
    rejected(&source.replace(
        "    let mut i=0usize;",
        "    fold Ready(p) with (a=x,b=y,c=z);\n    let mut i=0usize;",
    ));
}

#[test]
fn joint_numeric_guarantees_support_checked_arithmetic_across_call_and_loop() {
    let source = include_str!("../spec/cases/verify/predicate-opened-joint-numeric.nera");
    for source in [
        source.to_owned(),
        source.replace("usize", "u64"),
        source.replace("with (used=6usize)", "with (used=6usize,enabled=true)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for missing in ["    enabled||(used<limit);", "    !enabled||(used<limit);"] {
        rejected(&source.replace(missing, ""));
    }
    rejected(&source.replace("used<limit", "used<=limit"));
    for wrong in [
        "flag",
        "!flag",
        "1usize<=saved-limit",
        "(saved+18446744073709551615usize)*0usize==0usize",
    ] {
        rejected(&source.replace(
            "invariant 1usize<=limit-saved;",
            &format!("invariant {wrong};"),
        ));
    }
    rejected(&source.replace(
        "    let mut i=0usize;",
        "    fold Ready(p,limit) with (used=saved,enabled=flag);\n    let mut i=0usize;",
    ));
}

#[test]
fn numeric_model_consistency_proves_opened_boolean_across_call_and_loop() {
    let source = include_str!("../spec/cases/verify/predicate-opened-numeric-models.nera");
    for source in [
        source.to_owned(),
        source.replace("usize", "u64"),
        source.replace("with (used=6usize)", "with (used=7usize)"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for missing in ["    enabled||(used<limit);", "    enabled||(limit<=used);"] {
        rejected(&source.replace(missing, ""));
    }
    // If both orders admit equality, the false flag branch remains possible.
    rejected(&source.replace("used<limit", "used<=limit"));
    rejected(&source.replace("invariant flag;", "invariant !flag;"));
    rejected(&source.replace("invariant flag;", "invariant saved<limit;"));
    rejected(&source.replace(
        "exists enabled:bool = true;",
        "exists enabled:bool = false;",
    ));
    rejected(&source.replace(
        "    let mut i=0usize;",
        "    fold Ready(p,limit) with (used=saved,enabled=flag);\n    let mut i=0usize;",
    ));
}

#[test]
fn current_direct_aggregate_parameter_fields_use_immutable_typed_abi_inputs() {
    use predicate_logic::{LogicType, WitnessInput};
    let source = include_str!("../spec/cases/verify/predicate-current-aggregate-parameter.nera");
    for source in [
        source.to_owned(),
        source.replace("usize", "u64"),
        source.replace("{ return; }", "{ let mut changed=meta; changed.meta.count=0usize; changed.meta.valid=false; return; }"),
        source
            .replace(
                "ensures Ready(p,meta.meta.count,meta.meta.valid);",
                "ensures Ready(p,old(meta.meta.count),old(meta.meta.valid));",
            )
            .replace(
                "ensures Ready(result,meta.meta.count,meta.meta.valid);",
                "ensures Ready(result,old(meta.meta.count),old(meta.meta.valid));",
            ),
        source
            .replace(
                "struct Meta { count:usize, valid:bool, }",
                "struct Meta { count:[usize;1], valid:bool, }",
            )
            .replace(".count", ".count[0usize]")
            .replace("count:7usize", "count:[7usize]")
            .replace("count:5usize", "count:[5usize]"),
    ] {
        let output = checked(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    let output = checked(source);
    let unit = output.vir().unwrap().as_unit();
    let function = unit
        .runtime
        .functions
        .iter()
        .find(|f| f.name == "forward")
        .unwrap();
    let abi = &unit.runtime.abis.function(function.id).unwrap().signature;
    let meta = &abi.parameters()[2];
    let decoy = &abi.parameters()[3];
    assert!(matches!(meta.value(), VirAbiValue::DirectAggregate { .. }));
    let interfaces = unit
        .specs
        .predicate_interfaces()
        .iter()
        .filter(|i| i.function == function.id)
        .collect::<Vec<_>>();
    assert_eq!(interfaces.len(), 2);
    for interface in interfaces {
        assert_eq!(
            interface.arguments.inputs,
            vec![
                (
                    LogicType::Usize,
                    WitnessInput::Scalar(meta.parameter_slots()[0])
                ),
                (
                    LogicType::Bool,
                    WitnessInput::Scalar(meta.parameter_slots()[1])
                ),
            ]
        );
    }
    for wrong in [
        "decoy.meta.count,meta.meta.valid",
        "meta.meta.count,decoy.meta.valid",
    ] {
        let source = source.replace(
            "ensures Ready(p,meta.meta.count,meta.meta.valid);",
            &format!("ensures Ready(p,{wrong});"),
        );
        accepted(&source);
        rejected(&source);
    }
    for operation in [
        "meta.meta.count=0usize;",
        "meta.meta.valid=false;",
        "let alias=&mut meta.meta.count;",
    ] {
        let source = source.replace("{ return; }", &format!("{{ {operation} return; }}"));
        assert!(
            analyze(&SourceFile::from_text("immutable-parameter.nera", source))
                .hir()
                .is_none()
        );
    }
    let changed_caller = source
        .replace("let meta=Wrapper", "let mut meta=Wrapper")
        .replace(
            "    let q=pass(p,1,meta,decoy);",
            "    let saved=meta;\n    let q=pass(p,1,meta,decoy);\n    meta.meta.count=0usize;",
        );
    accepted(&changed_caller);
    rejected(&changed_caller);
    checked(
        &changed_caller
            .replace(
                "unfold Ready(q,meta.meta.count,meta.meta.valid);",
                "unfold Ready(q,saved.meta.count,saved.meta.valid);",
            )
            .replace(
                "finish Ready(q,meta.meta.count,meta.meta.valid);",
                "finish Ready(q,saved.meta.count,saved.meta.valid);",
            ),
    );
    // Wrong nominal type is structural corruption; a same-typed foreign slot
    // is structurally legal but must fail the actual contract proof.
    for malformed in [true, false] {
        let mut bad = unit.clone();
        let interface = bad
            .specs
            .predicate_interfaces_mut()
            .iter_mut()
            .find(|i| i.function == function.id && i.ensures)
            .unwrap();
        if malformed {
            interface.arguments.inputs[0].0 = LogicType::Bool;
            assert!(bad.into_validated().is_err());
        } else {
            interface.arguments.inputs[0].1 = WitnessInput::Scalar(decoy.parameter_slots()[0]);
            let bad = bad.into_validated().unwrap();
            assert!(
                !verify_program(&bad.resolve().unwrap(), Default::default())
                    .is_ok_and(|r| r.is_memory_checked_core0())
            );
        }
    }
    // Body actions use actual aggregate storage, independently of the ABI
    // slot mapping used by the contracts above. Both need typed admission.
    for mutation in 0..4 {
        let mut hir = hir_tables(output.hir().unwrap());
        let (ty, input) = hir
            .specs
            .predicate_actions
            .iter_mut()
            .flat_map(|a| &mut a.witnesses.inputs)
            .find(|(_, input)| matches!(input, WitnessInput::Memory { .. }))
            .unwrap();
        let WitnessInput::Memory {
            base, offset, time, ..
        } = input
        else {
            unreachable!()
        };
        match mutation {
            0 => *base = HirLocalId::new(u32::MAX),
            1 => *offset = u64::MAX,
            2 => *time = predicate_logic::ObservationTime::Entry,
            _ => *ty = LogicType::Bool,
        }
        assert!(
            HirProgram::from_tables(hir).is_err(),
            "action field mutation {mutation}"
        );
    }
    let mut hir = hir_tables(output.hir().unwrap());
    let function = hir
        .functions
        .iter_mut()
        .find(|f| f.name == "forward")
        .unwrap();
    let body = function.body.as_mut().unwrap();
    body.locals[body.parameters[2].get() as usize].mutable = true;
    assert!(HirProgram::from_tables(hir).is_err());
}

#[test]
fn hidden_prefix_counts_use_saved_equality_to_actual_runtime_cursors() {
    let source = include_str!("../spec/cases/verify/predicate-hidden-cursor-source.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    let empty = source
        .replace("    p.slots[0]=42;", "")
        .replace(
            "fold Ready(p,1usize) with (used=1usize);",
            "fold Ready(p,0usize) with (used=0usize);",
        )
        .replace("consume(p,1usize)", "consume(p,0usize)");
    let output = checked(&empty);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(0)]
    );
    // A count bound alone cannot select which runtime prefix the package owns.
    for relation in ["used<=n", "n<=used"] {
        let wrong = source.replace("used==n", relation);
        accepted(&wrong);
        rejected(&wrong);
    }
    for wrong in [
        source.replace("    used==n;", ""),
        source.replace("    p.slots[0]=42;", ""),
        source.replace("with (used=1usize)", "with (used=2usize)"),
        source.replace("let value=q.slots[0];", "let value=q.slots[1];"),
        source.replace("let q=relay(p,n);", "let q=relay(p,4usize);"),
        source.replace("invariant saved==n;", "invariant saved<n;"),
    ] {
        accepted(&wrong);
        rejected(&wrong);
    }
}

#[test]
fn compound_prefix_counts_survive_ordinary_calls_without_a_runtime_count_slot() {
    let source = include_str!("../spec/cases/verify/predicate-compound-cursor-source.nera");
    for expression in ["n+m+1usize", "n+1usize", "n+n+1usize"] {
        let variant = source.replace("n+m+1usize", expression);
        let output = checked(&variant);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    // The constant offset gives one element even with both operands zero.
    let minimum = source
        .replace("    p.slots[1]=7;", "")
        .replace("    p.slots[2]=9;", "")
        .replace("Ready(p,1usize,1usize)", "Ready(p,0usize,0usize)")
        .replace("consume(p,1usize,1usize)", "consume(p,0usize,0usize)");
    let output = checked(&minimum);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for wrong in [
        source.replace("    p.slots[2]=9;", ""),
        source.replace("let value=q.slots[0];", "let value=q.slots[1];"),
        source.replace("let q=relay(p,n,m);", "let q=relay(p,1usize,m);"),
        source.replace("finish Ready(q,n,m);", "finish Ready(q,m,n);"),
        source.replace("n+m+1usize", "n+m+2usize"),
    ] {
        accepted(&wrong);
        rejected(&wrong);
    }
}

#[test]
fn hidden_prefix_counts_use_exact_offsets_without_a_ghost_cursor() {
    let source = include_str!("../spec/cases/verify/predicate-hidden-cursor-offset.nera");
    let minimum = source
        .replace("    p.slots[2]=9;", "")
        .replace(
            "fold Ready(p,1usize) with (used=3usize);",
            "fold Ready(p,0usize) with (used=2usize);",
        )
        .replace("consume(p,1usize)", "consume(p,0usize)");
    for variant in [source, minimum.as_str()] {
        let output = checked(variant);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for wrong in [
        source.replace("used==n+2usize", "used<=n+2usize"),
        source.replace("used==n+2usize", "n+2usize<=used"),
        source.replace("    used==n+2usize;", ""),
        source.replace("    p.slots[2]=9;", ""),
        source.replace("let value=q.slots[1];", "let value=q.slots[2];"),
        source.replace("let q=relay(p,n);", "let q=relay(p,1usize);"),
        source.replace("invariant saved==n+2usize;", "invariant saved==n+1usize;"),
    ] {
        accepted(&wrong);
        rejected(&wrong);
    }
}

#[test]
fn affine_prefix_constraints_supply_operand_domains_across_calls() {
    let source = include_str!("../spec/cases/verify/predicate-affine-cursor-domain.nera");
    let minimum = source
        .replace("    p.slots[1]=7;", "")
        .replace("    p.slots[2]=8;", "")
        .replace("    p.slots[3]=9;", "")
        .replace("    p.slots[4]=10;", "")
        .replace("Ready(p,2usize)", "Ready(p,0usize)")
        .replace("consume(p,2usize)", "consume(p,0usize)");
    for variant in [source, minimum.as_str()] {
        let output = checked(variant);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for wrong in [
        source.replace("    2usize*n+1usize<=5usize;", ""),
        source.replace("    p.slots[4]=10;", ""),
        source.replace("let value=q.slots[0];", "let value=q.slots[1];"),
        source.replace("let q=relay(p,n);", "let q=relay(p,2usize);"),
        source.replace("fold Ready(p,2usize);", "fold Ready(p,3usize);"),
    ] {
        accepted(&wrong);
        rejected(&wrong);
    }
}

#[test]
fn hidden_compound_counts_use_proved_actual_coordinates_across_calls() {
    let source = include_str!("../spec/cases/verify/predicate-hidden-compound-cursor.nera");
    let minimum = source
        .replace("    p.slots[1]=7;", "")
        .replace("    p.slots[2]=9;", "")
        .replace(
            "fold Ready(p,1usize,1usize) with (used=3usize);",
            "fold Ready(p,0usize,0usize) with (used=1usize);",
        )
        .replace("consume(p,1usize,1usize)", "consume(p,0usize,0usize)");
    for variant in [source, minimum.as_str()] {
        let output = checked(variant);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for wrong in [
        source.replace("used==n+m+1usize", "used<=n+m+1usize"),
        source.replace("used==n+m+1usize", "n+m+1usize<=used"),
        source.replace("    used==n+m+1usize;", ""),
        source.replace("    p.slots[2]=9;", ""),
        source.replace("let value=q.slots[0];", "let value=q.slots[1];"),
        source.replace("let q=relay(p,n,m);", "let q=relay(p,n,1usize);"),
        source.replace("invariant saved==n+m+1usize;", "invariant saved==n+m;"),
    ] {
        accepted(&wrong);
        rejected(&wrong);
    }
}

#[test]
fn compound_prefix_domains_use_actual_bounds_of_other_operands() {
    let source = include_str!("../spec/cases/verify/predicate-compound-cursor-domain.nera");
    let minimum = source
        .replace("    p.slots[2]=9;", "")
        .replace(
            "fold Ready(p,1usize,1usize) with (used=3usize);",
            "fold Ready(p,0usize,1usize) with (used=2usize);",
        )
        .replace("consume(p,1usize,1usize)", "consume(p,0usize,1usize)");
    for variant in [source, minimum.as_str()] {
        let output = checked(variant);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for wrong in [
        source.replace("requires m==1usize;", "requires m<=1usize;"),
        source.replace("used==n+m+1usize", "used<=n+m+1usize"),
        source.replace("    p.slots[2]=9;", ""),
        source.replace("let value=q.slots[1];", "let value=q.slots[2];"),
        source.replace("let q=relay(p,n,m);", "let q=relay(p,1usize,m);"),
    ] {
        accepted(&wrong);
        rejected(&wrong);
    }
}

#[test]
fn logical_initialization_survives_contract_calls_without_a_runtime_endpoint() {
    let source = include_str!("../spec/cases/verify/predicate-logical-initialization.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)],
    );
}

#[test]
fn logical_initialization_rejects_missing_storage_and_reads_above_the_guaranteed_prefix() {
    let source = include_str!("../spec/cases/verify/predicate-logical-initialization.nera");
    for (wrong, fold_failure) in [
        (source.replace("p.slots[1]=7;", ""), true),
        (
            source.replace("with (used=2usize)", "with (used=3usize)"),
            true,
        ),
        (
            source.replace("let value=q.slots[0];", "let value=q.slots[1];"),
            false,
        ),
    ] {
        let output = accepted(&wrong);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .expect("negative reaches resource verification");
        assert!(!report.is_memory_checked_core0());
        let expected = report
            .functions()
            .values()
            .flat_map(|function| function.cfg().obligations())
            .map(|check| check.obligation())
            .any(|obligation| {
                !obligation.is_proven()
                    && if fold_failure {
                        matches!(
                            obligation.kind(),
                            ResourceObligationKind::PredicateActionValid { action: 0 }
                        )
                    } else {
                        matches!(
                            obligation.kind(),
                            ResourceObligationKind::MemoryInitialized { .. }
                                | ResourceObligationKind::ObjectValueBytesInitialized { .. }
                        )
                    }
            });
        assert!(expected, "wrong failure layer: {:?}", report.diagnostics());
    }
}

#[test]
fn closed_existential_call_cases_do_not_require_a_single_state_projection() {
    let source = include_str!("../spec/cases/verify/predicate-call-alternatives.nera");
    let output = checked(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&resolved, Default::default()).unwrap();
    // Analysis retains all complete outcomes even if its optional single-state
    // view cannot represent the distinct closed predicate packages.
    assert!(report.functions().values().any(|f| {
        f.cfg().blocks().values().any(|b| {
            b.instruction_states().is_err()
                && b.instruction_conditional_states()
                    .iter()
                    .any(|s| s.cases().len() > 1)
        })
    }));
    let bounded = CfgAnalysisConfig {
        max_guarded_cases_per_block: 1,
        ..Default::default()
    };
    assert!(!verify_program(&resolved, bounded).is_ok_and(|r| r.is_memory_checked_core0()));

    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    let invalid = accepted(&source.replace("let value=q.slots[0];", "let value=q.slots[1];"));
    let report = verify_program(
        &invalid.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| {
                !o.obligation().is_proven()
                    && matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::MemoryInitialized { .. }
                            | ResourceObligationKind::ObjectValueBytesInitialized { .. }
                    )
            })
    );
}

#[test]
fn arena_reserve_closes_cursor_contracts_for_full_and_empty_returns() {
    let source = include_str!("../spec/cases/verify/predicate-arena-reserve.nera");
    let output = checked(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for invalid in [
        source.replace("p.cursor=end;", "p.cursor=start;"),
        source.replace(
            "p.cursor==old(p.cursor)+len(result)",
            "p.cursor==old(p.cursor)+len(result)+1usize",
        ),
    ] {
        let bad = accepted(&invalid);
        let report =
            verify_program(&bad.vir().unwrap().resolve().unwrap(), Default::default()).unwrap();
        assert!(!report.is_memory_checked_core0());
        assert!(
            report.diagnostics().iter().any(|d| matches!(
                d.kind(),
                VerifierDiagnosticKind::RefutedPostcondition
                    | VerifierDiagnosticKind::MissingPostconditionFact
            )),
            "incorrect cursor updates and equations fail at the postcondition"
        );
    }
}

#[test]
fn resource_field_witnesses_follow_actual_owner_payloads_across_calls() {
    checked_logical_prefix(include_str!(
        "../spec/cases/verify/predicate-resource-fields.nera"
    ));
}

#[test]
fn resource_field_witnesses_preserve_stored_reference_authority() {
    let source = "struct Holder { value: &mut u64, } predicate Held(p:ptr<Holder>) { exists item:ptr<u64> = p.value; owns(p); item == p.value; }
fn main()->u64 { let mut value=42; let p=alloc<Holder>(1); p.value=&mut value; fold Held(p); unfold Held(p); let view=p.value; let answer=*view; free(p); finish Held(p); return answer; }";
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn resource_field_witnesses_cross_borrowed_container_abi() {
    let source = include_str!("../spec/cases/verify/predicate-resource-reference-fields.nera");
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn resource_field_witnesses_keep_canonical_inline_paths_and_reject_uninitialized_children() {
    let source = include_str!("../spec/cases/verify/predicate-resource-fields.nera");
    let nested = source
        .replace("value: Own<u64>", "value: ([Own<u64>; 1],)")
        .replace("p.value", "p.value.0[0]");
    checked_logical_prefix(&nested);
    rejected_field_fold(&source.replace("*item = 42;", ""));
    rejected(
        "struct Holder { value: ptr<u64>, } predicate Held(p:ptr<Holder>) { exists item:ptr<u64> = p.value; owns(p); } fn main()->u64{return 0;}",
    );
}

#[test]
fn resource_field_witnesses_cross_shared_and_inline_reference_abi() {
    let source = include_str!("../spec/cases/verify/predicate-resource-reference-fields.nera");
    for source in [
        source
            .replace("value: &mut u64", "value: &u64")
            .replace("p.value = &mut value", "p.value = &value"),
        source
            .replace("value: &mut u64", "value: ([&mut u64; 1],)")
            .replace("p.value", "p.value.0[0]")
            .replace("view.value", "view.value.0[0]"),
    ] {
        checked_logical_prefix(&source);
        let output = accepted(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            &[VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn resource_field_witnesses_reject_replaced_child_identity() {
    let source = include_str!("../spec/cases/verify/predicate-resource-fields.nera").replace("    fold Held(p) with (item = item);", "    let previous=p.value; free(previous); let replacement=alloc<u64>(1); *replacement=7; p.value=replacement; fold Held(p) with (item=item);");
    accepted(&source);
    rejected_field_fold(&source);
}

#[test]
fn resource_field_witnesses_cross_owning_reference_container_abi() {
    let source = "struct Holder { value: &mut u64, } predicate Held(p:ptr<Holder>) { exists item:ptr<u64> = p.value; owns(p); item == p.value; }
fn main()->u64 { let mut value=42; let p=alloc<Holder>(1); p.value=&mut value; fold Held(p); return consume(p); }
fn consume(p:Own<Holder>)->u64 requires Held(p); { unfold Held(p); let q=p.value; let answer=*q; free(p); finish Held(p); return answer; }";
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn resource_field_witnesses_return_owned_reference_containers() {
    let source = "struct Holder { value: &mut u64, } predicate Held(p:ptr<Holder>) { exists item:ptr<u64> = p.value; owns(p); item == p.value; }
fn main()->u64 { let mut value=42; let p=alloc<Holder>(1); p.value=&mut value; fold Held(p); let q=relay(p); return consume(q); }
fn relay(p:Own<Holder>)->Own<Holder> requires Held(p); ensures Held(result); { return p; }
fn consume(p:Own<Holder>)->u64 requires Held(p); { unfold Held(p); let q=p.value; let answer=*q; free(p); finish Held(p); return answer; }";
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn resource_field_witnesses_paths_are_revalidated_without_frontend_trust() {
    let output = accepted(include_str!(
        "../spec/cases/verify/predicate-resource-fields.nera"
    ));
    for path in [vec![1], vec![8], vec![0, 0], vec![u64::MAX]] {
        let mut hir = hir_tables(output.hir().unwrap());
        let mut unit = output.vir().unwrap().as_unit().clone();
        {
            let logic = &mut hir.predicates[0]
                .representation
                .as_mut()
                .unwrap()
                .logic
                .existentials[0]
                .default
                .as_mut()
                .unwrap()
                .nodes[0]
                .kind;
            let nera::predicate_logic::LogicNodeKind::Resource { path: target, .. } = logic else {
                panic!()
            };
            *target = path.clone();
        }
        let nera::predicate_logic::LogicNodeKind::Resource { path: target, .. } =
            &mut unit.specs.predicates_mut()[0]
                .representation
                .as_mut()
                .unwrap()
                .logic
                .existentials[0]
                .default
                .as_mut()
                .unwrap()
                .nodes[0]
                .kind
        else {
            panic!()
        };
        *target = path;
        assert!(HirProgram::from_tables(hir).is_err());
        assert!(unit.into_validated().is_err());
    }
}

#[test]
fn resource_field_witnesses_stay_private_across_module_calls() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let source = include_str!("../spec/cases/verify/predicate-resource-fields.nera");
    let start = source.find("fn main").unwrap();
    let end = source.find("fn make").unwrap();
    let library = format!("module lib; {}{}", &source[..start], &source[end..])
        .replace("struct Holder", "pub opaque struct Holder")
        .replace("predicate Held", "pub predicate Held")
        .replace("fn ", "pub fn ");
    let app = format!(
        "module app; use lib::Holder; use lib::Held; use lib::make; use lib::relay; use lib::destroy; {}",
        &source[start..end]
    );
    let inputs = [("app", app.as_str()), ("lib", library.as_str())]
        .into_iter()
        .map(|(name, text)| {
            SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
        })
        .collect();
    let compiler = CompilerSession::modules(
        SourceDatabase::new(inputs).unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap();
    assert!(compiler.verify("app").unwrap().is_checked());
}

fn rejected_field_fold(source: &str) {
    let output = accepted(source);
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| !o.obligation().is_proven()
                && matches!(
                    o.obligation().kind(),
                    ResourceObligationKind::PredicateActionValid { .. }
                ))
    );
}

#[test]
fn predicate_resource_actions_precede_last_use_loan_cleanup() {
    let source = include_str!("../spec/cases/verify/predicate-ghost-loan-end.nera");
    for source in [
        source.to_owned(),
        source.replace(
            "    finish Held(view);",
            "    let unrelated = 1;\n    finish Held(view);",
        ),
    ] {
        checked_logical_prefix(&source);
        let output = accepted(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            &[VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn predicate_group_cleanup_spans_distinct_storage_objects() {
    let source = include_str!("../spec/cases/verify/predicate-split-group-drop.nera");
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn split_stored_borrows_restore_the_parent_only_after_the_complete_group() {
    let source = include_str!("../spec/cases/verify/predicate-split-borrow-drop.nera");
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
    for early in ["unfold Pair(a,b);", "free(a);", "let stolen=left.item;"] {
        let bad = source.replace(
            "{ let right=Storage { item:vb }; }",
            &format!("{{ let right=Storage {{ item:vb }}; }} {early}"),
        );
        accepted(&bad);
        rejected(&bad);
    }
}

#[test]
fn split_owner_groups_cleanup_on_early_return_and_loop_exit() {
    let source = include_str!("../spec/cases/verify/predicate-split-group-drop.nera");
    let start = source.find("    let left=Storage").unwrap();
    let end = source.find("    return total;").unwrap();
    let setup = &source[start..end];
    for body in [
        format!("{setup} if total==42 {{ return total; }} return 0;"),
        format!("while true {{ {setup} break; }} return total;"),
    ] {
        let variant = format!("{}{}\n}}", &source[..start], body);
        checked_logical_prefix(&variant);
        let output = accepted(&variant);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            &[VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn finite_nested_owner_drop_cleans_children_before_their_carrier() {
    let source = include_str!("../spec/cases/verify/predicate-nested-owner-drop.nera");
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
    let plain = "struct Holder { value:Own<u64>, } struct Box { item:Own<Holder>, } fn main()->u64 { let child=alloc<u64>(1); let p=alloc<Holder>(1); p.value=child; let b=Box {item:p}; return 42; }";
    checked_logical_prefix(plain);
    let output = accepted(plain);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn finite_cleanup_and_field_returns_cover_normal_exit_paths() {
    for source in [
        include_str!("../spec/cases/verify/predicate-nested-reference-drop.nera"),
        include_str!("../spec/cases/verify/predicate-exit-paths.nera"),
        include_str!("../spec/cases/verify/predicate-owner-field-return.nera"),
        include_str!("../spec/cases/verify/predicate-shared-container-read.nera"),
    ] {
        checked_logical_prefix(source);
        let output = accepted(source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            &[VirRuntimeValue::U64(42)]
        );
    }
    let source = include_str!("../spec/cases/verify/predicate-exit-paths.nera")
        .replace("paths(false)", "paths(true)");
    checked_logical_prefix(&source);
    let output = accepted(&source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn owner_enum_result_is_not_a_stored_reference_destination() {
    // This is a runtime compatibility check. Enum owner summaries are outside
    // the stored-reference profile and are not claimed Checked here.
    let source = "struct Holder { value:&u64, } enum Choice { Empty, Full(u64), } fn main()->u64 { let v=42; let h=Holder{value:&v}; let p=make(h); free(p); return v; } fn make(h:Holder)->Own<Choice> { let p=alloc<Choice>(1); *p=Choice::Empty; return p; }";
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn pointer_field_exits_reject_early_free_and_duplicate_authority() {
    let source = include_str!("../spec/cases/verify/predicate-owner-field-return.nera");
    for invalid in [
        source.replace(
            "let q=p.value;\n    free(p);",
            "free(p);\n    let q=p.value;",
        ),
        source.replace("let q=p.value;", "let q=p.value; let duplicate=p.value;"),
    ] {
        assert_ne!(invalid, source);
        let output = accepted(&invalid);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let report = verify_program(&resolved, Default::default()).unwrap();
        assert!(!report.is_memory_checked_core0());
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(|o| !o.obligation().is_proven()
                    && matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::ResourcePayloadAvailable { .. }
                            | ResourceObligationKind::AllocationResourcePayloadEmpty { .. }
                            | ResourceObligationKind::AllocationLive { .. }
                    ))
        );
        assert!(interpret(resolved.runtime()).is_err());
    }
}

#[test]
fn shared_field_split_between_container_and_result_preserves_every_alias() {
    let source = include_str!("../spec/cases/verify/predicate-shared-field-exit.nera");
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn pointer_field_sources_follow_all_branch_assignments() {
    let source = include_str!("../spec/cases/verify/predicate-field-source-change.nera");
    checked(source);
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
    let earlier = source.replace(
        "if flag { p.value=&mut second; }",
        "let old=p.value; p.value=old; if flag { p.value=&mut second; }",
    );
    checked_logical_prefix(&earlier);
    let output = accepted(&earlier);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
    for invalid in [
        source.replace("let q=take(p);", "first=0; let q=take(p);"),
        source.replace(
            "if flag { p.value=&mut second; }",
            "{ let mut temporary=7; p.value=&mut temporary; }",
        ),
    ] {
        rejected(&invalid);
    }
}

#[test]
fn shared_field_expands_into_multiple_aggregate_result_carriers() {
    let source = include_str!("../spec/cases/verify/predicate-shared-field-copies.nera");
    checked(source);
    checked_logical_prefix(source);
    let output = accepted(source);
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(
        &resolved,
        CfgAnalysisConfig {
            max_aliases_per_loan: 3,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(!report.is_memory_checked_core0());
    let callee = resolved
        .runtime()
        .functions
        .iter()
        .find(|f| f.name == "duplicate")
        .unwrap();
    assert_eq!(
        report.functions()[&callee.id].summary().state,
        verifier::summary::SummaryState::Closed
    );
    assert!(
        interpret_with_config(
            resolved.runtime(),
            VirInterpreterConfig {
                max_aliases_per_loan: 3,
                ..Default::default()
            }
        )
        .is_err()
    );
}

#[test]
fn borrowed_groups_cleanup_after_overwrite_move_join_and_loop_exit() {
    let source = include_str!("../spec/cases/verify/predicate-borrowed-exit-paths.nera");
    for source in [
        source.to_owned(),
        source.replace("paths(false)", "paths(true)"),
        source.replace("if iteration==2", "if iteration==4"),
        source.replace("left.item=moved;", ""),
        source
            .replace("let right=Storage {item:vb};", "")
            .replace("left.item=moved;", "let right=Storage {item:vb};"),
        source
            .replace(
                "fold Pair(a,b);\n        {",
                "fold Pair(a,b);\n        if iteration<3 {",
            )
            .replace("if iteration==2", "if iteration==4"),
        source
            .replace(
                "let mut left=Storage {item:va};",
                "let ca=&mut *va; let cb=&mut *vb; let mut left=Storage {item:ca};",
            )
            .replace(
                "let right=Storage {item:vb};",
                "let right=Storage {item:cb};",
            ),
    ] {
        checked(&source);
        checked_logical_prefix(&source);
        let output = accepted(&source);
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            &[VirRuntimeValue::U64(42)]
        );
    }
    for premature in ["unfold Pair(a,b);", "free(a);", "free(b);"] {
        let invalid = source.replace(
            "left.item=&mut replacement;",
            &format!("left.item=&mut replacement; {premature}"),
        );
        accepted(&invalid);
        rejected(&invalid);
    }
}
