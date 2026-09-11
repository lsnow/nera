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
        VirInstruction::LoanAliasAuthority { .. }
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
fn raw_pointer_bearing_aggregate_remains_gated() {
    let output = analyze(&SourceFile::from_text(
        "raw-aggregate.nera",
        "struct RawHolder { value: ptr<u64>, }
         fn main() { return; }",
    ));
    assert_eq!(output.status(), FrontendStatus::Unsupported);
    assert!(output.hir().is_none());
    assert!(output.vir().is_none());
}

#[test]
fn reference_aggregate_function_abi_remains_gated() {
    let output = analyze(&SourceFile::from_text(
        "reference-aggregate-call.nera",
        "struct Holder { value: &u64, }
         fn read(holder: Holder) -> u64 {
             let value = holder.value;
             return *value;
         }
         fn main() -> u64 {
             let word = 7;
             let holder = Holder { value: &word };
             return read(holder);
         }",
    ));
    assert_eq!(output.status(), FrontendStatus::Unsupported);
    assert!(output.vir().is_none());
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
            VirInstruction::LoanAliasAuthority { effect, .. } => Some(effect),
            _ => None,
        })
        .expect("shared aggregate field read emits an authority alias");
    effect.origin = VirOriginId::new(0);
    assert_eq!(
        unit.validate()
            .expect_err("a user origin cannot forge a loan-authority effect")
            .kind(),
        &VirValidationErrorKind::InvalidLoanAuthorityEffectOrigin
    );
}
