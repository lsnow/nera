use nera::{
    HirProgram, HirProgramTables, HirSpecBinder, HirSpecBinderId, HirSpecBinderOwner,
    HirSpecClause, HirSpecClauseId, HirSpecClauseOwner, HirSpecContractPosition,
    HirSpecEnvironment, HirSpecLocation, HirSpecProve, HirSpecProveId, HirSpecSnapshot,
    HirSpecTerm, HirSpecTermId, HirSpecTermKind, HirTrustEntry, HirTrustEntryId,
    HirTrustPolicyKind, HirTrustScope, HirTypeId, HirTypeKind, SourceFile, analyze,
};

fn base_program() -> HirProgram {
    analyze(&SourceFile::from_text(
        "hir-spec.nera",
        "fn identity(value: u64) -> u64 { let other = 1; return value; }",
    ))
    .hir()
    .expect("fixture source is accepted")
    .clone()
}

fn tables(program: &HirProgram) -> HirProgramTables {
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

fn type_id(program: &HirProgram, kind: HirTypeKind) -> HirTypeId {
    program
        .types()
        .iter()
        .find(|definition| definition.kind == kind)
        .expect("fixture core type")
        .id
}

fn typed_spec_tables() -> HirProgramTables {
    let base = base_program();
    let mut tables = tables(&base);
    let function = &tables.functions[0];
    let function_id = function.id;
    let contract_id = function.contract;
    let body = function.body().expect("fixture body");
    let parameter = body.parameters[0];
    let span = function.span;
    let bool_ty = type_id(&base, HirTypeKind::Bool);
    let u64_ty = type_id(&base, HirTypeKind::Integer(nera::HirIntegerType::U64));

    tables.specs = HirSpecEnvironment {
        binders: vec![HirSpecBinder {
            id: HirSpecBinderId::new(0),
            owner: HirSpecBinderOwner::Clause(HirSpecClauseId::new(1)),
            name: "expected".to_owned(),
            ty: u64_ty,
            span,
        }],
        terms: vec![
            HirSpecTerm {
                id: HirSpecTermId::new(0),
                clause: HirSpecClauseId::new(0),
                ty: u64_ty,
                kind: HirSpecTermKind::Snapshot(HirSpecSnapshot::Local {
                    function: function_id,
                    local: parameter,
                }),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(1),
                clause: HirSpecClauseId::new(0),
                ty: u64_ty,
                kind: HirSpecTermKind::U64(10),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(2),
                clause: HirSpecClauseId::new(0),
                ty: bool_ty,
                kind: HirSpecTermKind::LessOrEqual {
                    left: HirSpecTermId::new(0),
                    right: HirSpecTermId::new(1),
                },
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(3),
                clause: HirSpecClauseId::new(1),
                ty: u64_ty,
                kind: HirSpecTermKind::Snapshot(HirSpecSnapshot::Result {
                    function: function_id,
                }),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(4),
                clause: HirSpecClauseId::new(1),
                ty: u64_ty,
                kind: HirSpecTermKind::Binder(HirSpecBinderId::new(0)),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(5),
                clause: HirSpecClauseId::new(1),
                ty: bool_ty,
                kind: HirSpecTermKind::Equal {
                    left: HirSpecTermId::new(3),
                    right: HirSpecTermId::new(4),
                },
                span,
            },
        ],
        clauses: vec![
            HirSpecClause {
                id: HirSpecClauseId::new(0),
                owner: HirSpecClauseOwner::Prove(HirSpecProveId::new(0)),
                location: HirSpecLocation::FunctionEntry {
                    function: function_id,
                },
                root: HirSpecTermId::new(2),
                span,
            },
            HirSpecClause {
                id: HirSpecClauseId::new(1),
                owner: HirSpecClauseOwner::Contract {
                    contract: contract_id,
                    position: HirSpecContractPosition::Ensures,
                },
                location: HirSpecLocation::FunctionResult {
                    function: function_id,
                },
                root: HirSpecTermId::new(5),
                span,
            },
        ],
        proves: vec![HirSpecProve {
            id: HirSpecProveId::new(0),
            function: function_id,
            location: HirSpecLocation::FunctionEntry {
                function: function_id,
            },
            clause: HirSpecClauseId::new(0),
            span,
        }],
        trust_entries: Vec::new(),
        loop_invariants: Vec::new(),
    };
    tables.contracts[contract_id.index()].clauses = vec![HirSpecClauseId::new(1)];
    tables
}

#[test]
fn minimal_typed_spec_hir_accepts_snapshots_ghost_binders_and_shared_clauses() {
    let program = HirProgram::from_tables(typed_spec_tables()).expect("typed Spec HIR validates");

    assert_eq!(program.specs().terms.len(), 6);
    assert_eq!(program.specs().clauses.len(), 2);
    assert_eq!(program.contracts()[0].clauses, [HirSpecClauseId::new(1)]);
}

#[test]
fn hir_spec_rejects_non_dominating_snapshots_foreign_terms_and_binders() {
    let mut duplicate_binder = typed_spec_tables();
    let mut second = duplicate_binder.specs.binders[0].clone();
    second.id = HirSpecBinderId::new(1);
    duplicate_binder.specs.binders.push(second);
    assert_eq!(
        HirProgram::from_tables(duplicate_binder)
            .expect_err("binder names are unique within one owner")
            .table(),
        "spec binder"
    );

    let mut non_parameter = typed_spec_tables();
    let body = non_parameter.functions[0].body().expect("fixture body");
    let other = body
        .locals
        .iter()
        .find(|local| !body.parameters.contains(&local.id))
        .expect("non-parameter local")
        .id;
    let function = non_parameter.functions[0].id;
    non_parameter.specs.terms[0].kind = HirSpecTermKind::Snapshot(HirSpecSnapshot::Local {
        function,
        local: other,
    });
    assert_eq!(
        HirProgram::from_tables(non_parameter)
            .expect_err("entry snapshots only admit parameters")
            .table(),
        "spec term"
    );

    let mut foreign_child = typed_spec_tables();
    foreign_child.specs.terms[5].kind = HirSpecTermKind::Equal {
        left: HirSpecTermId::new(0),
        right: HirSpecTermId::new(4),
    };
    assert_eq!(
        HirProgram::from_tables(foreign_child)
            .expect_err("terms cannot cross clause ownership")
            .table(),
        "spec term"
    );

    let mut foreign_binder = typed_spec_tables();
    foreign_binder.specs.binders[0].owner = HirSpecBinderOwner::Clause(HirSpecClauseId::new(0));
    assert_eq!(
        HirProgram::from_tables(foreign_binder)
            .expect_err("ghost binders are clause scoped")
            .table(),
        "spec term"
    );
}

#[test]
fn hir_spec_rejects_wrong_root_types_and_contract_locations() {
    let mut wrong_root = typed_spec_tables();
    wrong_root.specs.clauses[0].root = HirSpecTermId::new(0);
    assert_eq!(
        HirProgram::from_tables(wrong_root)
            .expect_err("clause roots are boolean")
            .table(),
        "spec clause"
    );

    let mut wrong_location = typed_spec_tables();
    wrong_location.specs.clauses[1].location = HirSpecLocation::FunctionEntry {
        function: wrong_location.functions[0].id,
    };
    wrong_location.specs.terms[3].kind = HirSpecTermKind::U64(7);
    assert_eq!(
        HirProgram::from_tables(wrong_location)
            .expect_err("ensures clauses belong to function result")
            .table(),
        "spec clause"
    );
}

#[test]
fn hir_trust_entries_are_explicitly_scoped_and_policy_checked() {
    let mut trusted = typed_spec_tables();
    let function = trusted.entry_function;
    let span = trusted.functions[function.index()].span;
    trusted.specs.clauses[0].owner = HirSpecClauseOwner::TrustEntry(HirTrustEntryId::new(0));
    trusted.specs.proves.clear();
    trusted.specs.trust_entries.push(HirTrustEntry {
        id: HirTrustEntryId::new(0),
        scope: HirTrustScope::FunctionEntry { function },
        policy: HirTrustPolicyKind::EntryPointAssumption,
        clause: HirSpecClauseId::new(0),
        span,
    });
    HirProgram::from_tables(trusted.clone()).expect("entry trust policy validates");

    let mut denied = trusted.clone();
    denied.specs.trust_entries[0].policy = HirTrustPolicyKind::ExternallyVerified;
    assert_eq!(
        HirProgram::from_tables(denied)
            .expect_err("external proof policy remains gated")
            .table(),
        "trust entry"
    );

    trusted.specs.trust_entries[0].scope = HirTrustScope::FunctionResult { function };
    assert_eq!(
        HirProgram::from_tables(trusted)
            .expect_err("entry trust cannot move to the result")
            .table(),
        "spec clause"
    );
}
