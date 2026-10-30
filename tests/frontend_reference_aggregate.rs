use nera::backend::X86_64_UNKNOWN_LINUX_GNU;
use nera::{
    CfgAnalysisConfig, FrontendStatus, HirRegionOrigin, HirRegionOwner, SourceFile, VirInstruction,
    VirLoanRange, VirOriginId, VirRuntimeValue, VirValidationErrorKind, analyze, interpret,
    verify_program,
};

fn accepted(name: &str, source: &str) -> nera::FrontendOutput {
    let output = analyze(&SourceFile::from_text(name, source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:?}",
        output.issues()
    );
    output
}

fn assert_checked_result(output: &nera::FrontendOutput, expected: u64) {
    let vir = output.vir().expect("accepted source has validated VIR");
    let resolved = vir.resolve().expect("reference aggregate VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("reference aggregate verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("reference aggregate executes")
            .values(),
        [VirRuntimeValue::U64(expected)]
    );
    X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("reference aggregate reaches native planning");
}

#[test]
fn shared_reference_struct_copy_tracks_each_stored_alias() {
    let output = accepted(
        "shared-reference-struct.nera",
        "struct Holder { value: &u64, }
         fn main() -> u64 {
             let word = 7;
             let holder = Holder { value: &word };
             let copied = holder;
             let copied_value = copied.value;
             let holder_value = holder.value;
             return *copied_value + *holder_value;
         }",
    );
    let hir = output.hir().expect("typed HIR");
    assert!(hir.regions().iter().any(|region| {
        matches!(region.owner, HirRegionOwner::Type(_))
            && matches!(region.origin, HirRegionOrigin::AggregateErased)
    }));
    let instructions = output.vir().expect("VIR").runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert!(instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::ObjectTransfer {
            source_mode: nera::VirObjectSourceMode::Copy,
            ..
        }
    )));
    assert!(instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::LoanEndAuthority { .. }
    )));
    assert_checked_result(&output, 14);
}

#[test]
fn mutable_reference_partial_move_and_field_replace_end_the_old_loan() {
    let moved = accepted(
        "mutable-reference-partial-move.nera",
        "struct Slot { value: &mut u64, }
         fn main() -> u64 {
             let mut word = 1;
             let slot = Slot { value: &mut word };
             let unique = slot.value;
             *unique = 9;
             return word;
         }",
    );
    assert_checked_result(&moved, 9);

    let replaced = accepted(
        "reference-field-replace.nera",
        "struct Holder { value: &u64, }
         fn main() -> u64 {
             let left = 3;
             let right = 5;
             let mut holder = Holder { value: &left };
             holder.value = &right;
             let value = holder.value;
             return left + *value;
         }",
    );
    assert_checked_result(&replaced, 8);

    let aggregate_replaced = accepted(
        "reference-aggregate-replace.nera",
        "struct Holder { value: &u64, }
         fn main() -> u64 {
             let left = 3;
             let right = 5;
             let mut holder = Holder { value: &left };
             holder = Holder { value: &right };
             let value = holder.value;
             return left + *value;
         }",
    );
    assert_checked_result(&aggregate_replaced, 8);
}

#[test]
fn arrays_and_enum_pattern_bindings_preserve_reference_authority() {
    let array = accepted(
        "reference-array.nera",
        "fn main() -> u64 {
             let left = 2;
             let right = 4;
             let values = [&left, &right];
             let first = values[0];
             let second = values[1];
             return *first + *second;
         }",
    );
    assert_checked_result(&array, 6);

    let enum_value = accepted(
        "reference-enum.nera",
        "enum MaybeRef { None, Some(&u64), }
         fn main() -> u64 {
             let word = 11;
             let value = MaybeRef::Some(&word);
             match value {
                 MaybeRef::Some(reference) => { return *reference; },
                 MaybeRef::None => { return 0; },
             }
         }",
    );
    assert_checked_result(&enum_value, 11);

    let mutable_enum = accepted(
        "mutable-reference-enum.nera",
        "enum MaybeRef { None, Some(&mut u64), }
         fn main() -> u64 {
             let mut word = 3;
             let value = MaybeRef::Some(&mut word);
             match value {
                 MaybeRef::Some(reference) => {
                     *reference = 13;
                     return word;
                 },
                 MaybeRef::None => { return 0; },
             }
         }",
    );
    assert_checked_result(&mutable_enum, 13);

    let switched = accepted(
        "reference-enum-variant-switch.nera",
        "enum MaybeRef { None, Some(&mut u64), }
         fn main() -> u64 {
             let mut word = 3;
             let mut value = MaybeRef::Some(&mut word);
             value = MaybeRef::None;
             word = 17;
             return word;
         }",
    );
    assert_checked_result(&switched, 17);
}

#[test]
fn bounded_dynamic_index_borrow_uses_a_conservative_candidate_range() {
    let output = accepted(
        "dynamic-reference-range.nera",
        "fn main() -> u64 {
             let values = [3, 5];
             let index = 1usize;
             let borrowed = &values[index];
             return *borrowed;
         }",
    );
    let ranges = output.vir().expect("VIR").runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::LoanBegin { effect, .. } => Some(effect.range),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        ranges,
        [VirLoanRange {
            start_bytes: 0,
            end_bytes: 16,
        }]
    );
    assert_checked_result(&output, 5);
}

#[test]
fn tuple_and_constant_array_subobjects_have_disjoint_exact_ranges() {
    let tuple = accepted(
        "tuple-subobject-ranges.nera",
        "fn main() -> u64 {
             let mut pair = (1, 2);
             let first = &mut pair.0;
             let second = &mut pair.1;
             *first = 5;
             *second = 7;
             return pair.0 + pair.1;
         }",
    );
    assert_checked_result(&tuple, 12);

    let array = accepted(
        "constant-array-subobject-ranges.nera",
        "fn main() -> u64 {
             let mut values = [1, 2];
             let first = &mut values[0];
             let second = &mut values[1];
             *first = 5;
             *second = 7;
             return values[0] + values[1];
         }",
    );
    assert_checked_result(&array, 12);
}

#[test]
fn evaluated_indices_use_actual_ranges_not_candidate_envelopes() {
    let output = accepted(
        "dynamic-reference-overlap.nera",
        "fn main() -> u64 {
             let mut values = [3, 5];
             let left = 0usize;
             let right = 1usize;
             let first = &mut values[left];
             let second = &mut values[right];
             *first = 7;
             *second = 9;
             return values[0] + values[1];
         }",
    );
    assert_checked_result(&output, 16);
}

#[test]
fn raw_pointer_fields_store_addresses_without_owning_the_referent() {
    let output = accepted(
        "raw-aggregate.nera",
        "struct RawHolder { value: ptr<u64>, }
         fn main() -> u64 {
             let word = 42;
             let holder = alloc<RawHolder>(1);
             holder.value = null<u64>();
             holder.value = null<u64>();
             let empty = holder.value == null<u64>();
             free(holder);
             if empty { return word; }
             return 0;
         }",
    );
    assert_checked_result(&output, 42);
}

#[test]
fn raw_aggregate_calls_copy_address_metadata_and_keep_overwrites_local() {
    let output = accepted(
        "raw-aggregate-call.nera",
        include_str!("../spec/cases/verify/raw-aggregate-call.nera"),
    );
    assert_checked_result(&output, 42);
}

#[test]
fn field_returns_preserve_nonzero_referent_offsets_and_actual_domains() {
    let output = accepted(
        "field-domain.nera",
        "struct View { tag:u64, view:&mut u64, }
         fn main()->u64 {
             let mut words=[1,2,3];
             let selected=relay(View {tag:0,view:&mut words[1]});
             *selected=38;
             return words[0]+words[1]+words[2];
         }
         fn relay(value:View)->&mut u64 {return take(value);}
         fn take(value:View)->&mut u64 {return value.view;}",
    );
    assert_checked_result(&output, 42);
}

#[test]
fn reference_fields_can_carry_bounded_nodes_with_raw_links() {
    let output = accepted(
        "borrowed-raw-node-field.nera",
        "struct Node { link:ptr<Node>, value:u64, }
         struct View { view:&mut Node, }
         fn main()->u64 {
             let mut node=Node {link:null<Node>(),value:40};
             let selected=take(View {view:&mut node});
             selected.value=42;
             return selected.value;
         }
         fn take(value:View)->&mut Node {return value.view;}",
    );
    assert_checked_result(&output, 42);
}

#[test]
fn unproved_aggregate_result_cannot_invent_a_returned_loan() {
    let output = accepted(
        "unproved-field-return.nera",
        "struct View { view:&mut u64, }
         fn main()->u64 {
             let mut word=42;
             let returned=broken(View {view:&mut word});
             let value=returned.view;
             return *value;
         }
         fn broken(value:View)->View {
             let first=value.view;
             let duplicate=value.view;
             return View {view:first};
         }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&resolved, Default::default())
        .expect("an unavailable loan mapping produces an obligation, not an internal error");
    assert!(!report.is_memory_checked_core0());
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn reference_aggregate_function_abi_preserves_actual_shared_authority() {
    let output = analyze(&SourceFile::from_text(
        "reference-aggregate-call.nera",
        "struct Holder { value: &u64, }
         fn main() -> u64 {
             let word = 7;
             let holder = Holder { value: &word };
             return read(holder);
         }
         fn read(holder: Holder) -> u64 {
             let value = holder.value;
             return *value;
         }",
    ));
    assert_checked_result(&output, 7);
}

#[test]
fn authority_effects_cannot_claim_a_user_source_origin() {
    let output = accepted(
        "reference-authority-origin.nera",
        "struct Holder { value: &u64, }
         fn main() -> u64 {
             let word = 7;
             let holder = Holder { value: &word };
             let copied = holder.value;
             return *copied;
         }",
    );
    let mut unit = output.vir().expect("VIR").as_unit().clone();
    let effect = unit.runtime.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::LoanEndAuthority { effect, .. } => Some(effect),
            _ => None,
        })
        .expect("shared aggregate field read emits a matching authority end");
    effect.origin = VirOriginId::new(0);
    assert_eq!(
        unit.validate()
            .expect_err("a user origin cannot forge a loan-authority effect")
            .kind(),
        &VirValidationErrorKind::InvalidLoanAuthorityEffectOrigin
    );
}

#[test]
fn field_call_profile_preserves_sources_results_and_aliases() {
    let output = accepted(
        "reference-fields.nera",
        include_str!("../spec/cases/verify/predicate-reference-fields.nera"),
    );
    assert_checked_result(&output, 192);
    let hir = output.hir().unwrap();
    for (name, parameter, field) in [
        ("extract", 0, 0),
        ("relay", 0, 0),
        ("second", 1, 0),
        ("nested", 0, 3),
        ("reshuffle", 0, 1),
        ("subaggregate", 0, 2),
        ("after_stored", 0, 1),
        ("tuple_extract", 0, 1),
        ("array_extract", 0, 0),
    ] {
        let function = hir.functions().iter().find(|f| f.name == name).unwrap();
        let relation = function.signature.borrow_result.unwrap();
        assert_eq!(relation.parameter, parameter);
        assert_eq!(relation.parameter_field, Some(field));
    }
}

#[test]
fn guarded_field_summary_rejects_swapped_source_claims() {
    let output = accepted(
        "guarded-fields.nera",
        include_str!("../spec/cases/verify/predicate-reference-fields.nera"),
    );
    let hir = output.hir().unwrap();
    let id = nera::VirFunctionId::new(
        hir.functions()
            .iter()
            .find(|f| f.name == "select")
            .unwrap()
            .id
            .get(),
    );
    let mut unit = output.vir().unwrap().as_unit().clone();
    let symbol = unit
        .runtime
        .functions
        .iter()
        .find(|f| f.id == id)
        .unwrap()
        .name
        .clone();
    let original = unit.runtime.abis.function(id).unwrap().signature.clone();
    let mut alternatives = original.borrow_result_alternatives().to_vec();
    assert_eq!(alternatives.len(), 2);
    for alternative in &mut alternatives {
        let field = alternative.relation.parameter_field.unwrap();
        alternative.relation.parameter_field = Some(1 - field);
    }
    let parameters = original
        .parameters()
        .iter()
        .map(|b| b.value().access().unwrap())
        .collect::<Vec<_>>();
    let results = original
        .results()
        .iter()
        .map(|b| b.value().access().unwrap())
        .collect::<Vec<_>>();
    let forged = nera::VirAbiSignature::classify_with_borrow_results(
        &unit.memory,
        &parameters,
        &results,
        None,
        alternatives,
    )
    .unwrap();
    unit.runtime
        .abis
        .functions
        .iter_mut()
        .find(|f| f.function == id)
        .unwrap()
        .signature = forged.clone();
    for function in &mut unit.runtime.functions {
        for block in &mut function.blocks {
            for instruction in &mut block.instructions {
                if let VirInstruction::Call { target, .. } = &mut instruction.instruction
                    && target.symbol == symbol
                {
                    target.abi = Some(forged.clone());
                }
            }
        }
    }
    let validated = unit
        .into_validated()
        .expect("types and unguarded pointer source set still match");
    let resolved = validated.resolve().unwrap();
    assert!(
        !verify_program(&resolved, Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn field_return_rejects_wrong_pointee_strength_and_unbounded_storage() {
    for (name, source) in [
        (
            "pointee",
            "struct V { value: &mut u64, } fn bad(v: V)->&mut bool { return v.value; } fn main()->u64{return 0;}",
        ),
        (
            "strength",
            "struct V { value: &u64, } fn bad(v: V)->&mut u64 { return v.value; } fn main()->u64{return 0;}",
        ),
        (
            "raw",
            "struct V { value: ptr<u64>, } fn bad(v: V)->&mut u64 { return v.value; } fn main()->u64{return 0;}",
        ),
        (
            "field-budget",
            "struct V { values: [&mut u64; 257], } fn bad(v: V)->&mut u64 { return v.values[0]; } fn main()->u64{return 0;}",
        ),
        (
            "stored-fat-view",
            "struct V { value: &mut [u64], } fn main()->u64{return 0;}",
        ),
    ] {
        let output = analyze(&SourceFile::from_text(format!("{name}.nera"), source));
        assert_ne!(output.status(), FrontendStatus::AcceptedProposal, "{name}");
        assert!(!output.issues().is_empty(), "{name}: missing diagnostic");
        assert!(
            output.vir().is_none(),
            "{name}: unsupported source reached VIR"
        );
    }
}

#[test]
fn a_moved_mutable_field_cannot_be_taken_again_across_a_call() {
    let output = accepted(
        "field-taken-twice.nera",
        "
        struct V { value: &mut u64, }
        fn identity(v: &mut u64)->&mut u64 { return v; }
        fn main()->u64 {
            let mut word = 7;
            let stored = V { value: &mut word };
            let first = identity(stored.value);
            let second = stored.value;
            return *first + *second;
        }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&resolved, Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn independent_ssa_rejects_wrong_field_after_move_construction_and_stored_call() {
    let output = accepted(
        "field-source.nera",
        include_str!("../spec/cases/verify/predicate-reference-fields.nera"),
    );
    for name in ["extract", "reshuffle", "after_stored", "subaggregate"] {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let function = unit
            .runtime
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap();
        let id = function.id;
        let original = &unit.runtime.abis.function(id).unwrap().signature;
        let mut relation = original.borrow_result().unwrap();
        relation.parameter_field = Some(if relation.parameter_field == Some(0) {
            1
        } else {
            0
        });
        let parameters = original
            .parameters()
            .iter()
            .map(|p| p.value().access().unwrap())
            .collect::<Vec<_>>();
        let results = original
            .results()
            .iter()
            .map(|r| r.value().access().unwrap())
            .collect::<Vec<_>>();
        let forged = nera::VirAbiSignature::classify_with_borrow_results(
            &unit.memory,
            &parameters,
            &results,
            Some(relation),
            vec![],
        )
        .unwrap();
        unit.runtime
            .abis
            .functions
            .iter_mut()
            .find(|f| f.function == id)
            .unwrap()
            .signature = forged.clone();
        for function in &mut unit.runtime.functions {
            for instruction in function.blocks.iter_mut().flat_map(|b| &mut b.instructions) {
                if let VirInstruction::Call { target, .. } = &mut instruction.instruction
                    && target.symbol == name
                {
                    target.abi = Some(forged.clone());
                }
            }
        }
        assert!(
            unit.validate().is_err(),
            "{name}: wrong field passed independent SSA validation"
        );
    }
}
