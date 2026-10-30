use super::*;

fn fixture() -> HirProgram {
    fixture_with_prefix("")
}

fn fixture_with_prefix(prefix: &str) -> HirProgram {
    let source = crate::SourceFile::from_text(
        "parameter-reference-layout.nera",
        "struct Pair { x:u64, y:u64, } struct Leaf { pad:bool, view:&mut u64, } \
         struct Bundle { leaves:[Leaf;2], shared:&u64, owner:Own<u64>, link:ptr<u64>, } \
         fn main()->u64{return 0;} \
         fn consume(a:Bundle,b:Bundle)->u64{return 42;}"
            .replace("a:Bundle,b:Bundle", &format!("{prefix}a:Bundle,b:Bundle")),
    );
    let lexed = crate::lexer::lex(&source);
    let parsed = crate::frontend::parser::parse(&source, lexed.tokens(), false).unwrap();
    let graph = crate::frontend::modules::ModuleGraph::single(&parsed.ast).unwrap();
    crate::frontend::hir::elaborate_modules(&[&parsed.ast], graph).unwrap()
}

#[test]
fn parameter_fields_map_to_padded_array_layout_without_following_pointers() {
    let hir = fixture();
    let lowered = LoweredMemorySchema::build(&hir, ByteSpan::empty()).unwrap();
    let fields: Vec<_> = lowered.parameter_references.values().copied().collect();
    assert_eq!(fields.len(), 6);
    assert_eq!(
        fields
            .iter()
            .map(|field| field.loan)
            .collect::<BTreeSet<_>>()
            .len(),
        6
    );
    for (index, group) in fields.as_chunks::<3>().0.iter().enumerate() {
        assert_eq!(
            group.iter().map(|f| f.offset_bytes).collect::<Vec<_>>(),
            [8, 24, 32]
        );
        for (slot, field) in group.iter().enumerate() {
            assert_eq!(field.function, crate::HirFunctionId::new(1));
            assert_eq!(field.parameter, index as u32);
            assert_eq!(field.pointer_slot, 2 * index as u32);
            assert_eq!(field.permission_slot, 2 * index as u32 + 1);
            assert_eq!(field.slot, slot as u32);
            assert_eq!(
                field.loan,
                crate::vir::interface_loan_id(2 + (3 * index + slot) as u32)
            );
            assert_eq!(
                field.mutability,
                if slot == 2 {
                    VirMutability::Const
                } else {
                    VirMutability::Mutable
                }
            );
            assert!(lowered.schema.resolves_access(field.reference));
            assert!(lowered.schema.resolves_access(field.pointee));
        }
    }
    // Different parameter binders can map to the same nominal field types;
    // their parameter identities and storage offsets remain explicit.
    assert_eq!(fields[0].reference, fields[1].reference);
    assert_eq!(fields[0].reference, fields[3].reference);
    assert_ne!(fields[0].parameter, fields[3].parameter);
}

#[test]
fn reference_field_mapping_rejects_type_substitution_without_publishing_partial_map() {
    let hir = fixture();
    let mut lowered = LoweredMemorySchema::build(&hir, ByteSpan::empty()).unwrap();
    let original = lowered.parameter_references.clone();
    let parameter = hir.functions()[1].signature.parameters[0];
    let leaves = hir.aggregate_reference_types(parameter).unwrap();
    let mutable = leaves[0].0;
    let shared = leaves[2].0;
    let replacement = lowered.types[&mutable];
    // Keep the physical shared field, but corrupt its HIR-to-VIR type map.
    lowered.types.insert(shared, replacement);
    assert!(lowered.bind_parameter_references(&hir).is_err());
    assert_eq!(lowered.parameter_references, original);
}

#[test]
fn reference_storage_slots_follow_scalar_slice_and_direct_aggregate_parameters() {
    let hir = fixture_with_prefix("n:u64,items:&[u64],pair:Pair,");
    let lowered = LoweredMemorySchema::build(&hir, ByteSpan::empty()).unwrap();
    for field in lowered.parameter_references.values() {
        assert!(field.parameter == 3 || field.parameter == 4);
        // One scalar, a three-slot slice, and two direct aggregate leaves.
        assert_eq!(field.pointer_slot, 6 + 2 * (field.parameter - 3));
        assert_eq!(field.permission_slot, field.pointer_slot + 1);
        assert_eq!(
            field.loan,
            crate::vir::interface_loan_id(5 + 3 * (field.parameter - 3) + field.slot)
        );
    }
    let accesses = hir.functions()[1]
        .signature
        .parameters
        .iter()
        .map(|ty| lowered.access(*ty, ByteSpan::empty()).unwrap())
        .collect::<Vec<_>>();
    let entries =
        crate::vir::plan_parameter_reference_entries(lowered.schema(), &accesses).unwrap();
    assert_eq!(entries.len(), lowered.parameter_references.len());
    for (entry, field) in entries.iter().zip(lowered.parameter_references.values()) {
        assert_eq!(entry.loan, field.loan);
        assert_eq!(entry.pointer_slot, field.pointer_slot);
        assert_eq!(entry.permission_slot, field.permission_slot);
        assert_eq!(entry.offset_bytes, field.offset_bytes);
        assert_eq!(entry.reference, field.reference);
        assert_eq!(entry.pointee, field.pointee);
    }
    let prefix = hir.functions()[1].signature.parameters[..3]
        .iter()
        .map(|ty| lowered.access(*ty, ByteSpan::empty()).unwrap())
        .collect::<Vec<_>>();
    let ordinary = crate::VirAbiSignature::classify(lowered.schema(), &prefix, &[]).unwrap();
    let planned = crate::vir::plan_reference_parameter_slots(lowered.schema(), &prefix).unwrap();
    assert_eq!(
        planned,
        ordinary
            .parameters()
            .iter()
            .map(|binding| binding.parameter_slots().to_vec())
            .collect::<Vec<_>>()
    );
    let abi = crate::frontend::lower::abi::classify_hir_signature(
        crate::frontend::lower::ConcreteTypes::new(&hir),
        &lowered,
        &hir.functions()[1].signature,
        hir.functions()[1].span,
    )
    .unwrap();
    assert_eq!(
        crate::vir::plan_reference_parameter_slots(lowered.schema(), &accesses).unwrap(),
        abi.parameters()
            .iter()
            .map(|binding| binding.parameter_slots().to_vec())
            .collect::<Vec<_>>()
    );
}
