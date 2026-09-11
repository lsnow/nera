use nera::{
    DropCapability, FrontendIssueKind, FrontendStatus, SizeCapability, SourceFile, ValueCapability,
    VirAbiClass, VirAbiSignature, VirEndianness, VirInterfaceStorage, VirInterfaceTransfer,
    VirLayout, VirLayoutId, VirMemoryAccess, VirMemorySchema, VirMemorySchemaErrorKind,
    VirMemoryType, VirMemoryTypeKind, VirMutability, VirPointerKind, VirTargetDataLayout,
    VirTypeId, analyze,
};

const U64_TYPE: VirTypeId = VirTypeId::new(0);
const SHARED_REFERENCE_TYPE: VirTypeId = VirTypeId::new(1);
const MUTABLE_REFERENCE_TYPE: VirTypeId = VirTypeId::new(2);

fn reference_schema() -> VirMemorySchema {
    let mut schema = VirMemorySchema {
        target: VirTargetDataLayout {
            endianness: VirEndianness::Little,
            pointer_size_bytes: 8,
            pointer_alignment: 8,
            usize_size_bytes: 8,
            usize_alignment: 8,
        },
        types: vec![
            VirMemoryType {
                id: U64_TYPE,
                kind: VirMemoryTypeKind::Integer(nera::VirIntegerType::U64),
                layout: VirLayoutId::new(0),
            },
            VirMemoryType {
                id: SHARED_REFERENCE_TYPE,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: U64_TYPE,
                    kind: VirPointerKind::Reference,
                    mutability: VirMutability::Const,
                },
                layout: VirLayoutId::new(1),
            },
            VirMemoryType {
                id: MUTABLE_REFERENCE_TYPE,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: U64_TYPE,
                    kind: VirPointerKind::Reference,
                    mutability: VirMutability::Mutable,
                },
                layout: VirLayoutId::new(2),
            },
        ],
        type_capabilities: Vec::new(),
        layouts: vec![
            VirLayout {
                id: VirLayoutId::new(0),
                ty: U64_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(1),
                ty: SHARED_REFERENCE_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(2),
                ty: MUTABLE_REFERENCE_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
        ],
        fields: Vec::new(),
        variants: Vec::new(),
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("reference capabilities derive");
    schema
}

#[test]
fn explicit_regions_and_unchecked_borrow_forms_remain_gated() {
    let cases = [
        (
            "borrow-and-reborrow.nera",
            "fn main() -> u64 {
                 let value = 1;
                 let borrowed = &value;
                 let reborrowed = &borrowed;
                 return value;
             }",
        ),
        (
            "raw-pointer-borrow.nera",
            "fn main() -> u64 {
                 let owner = alloc<u64>(2);
                 let address = owner + 8;
                 let borrowed = &*address;
                 return *borrowed;
             }",
        ),
        (
            "slice-range-expression.nera",
            "fn main() -> u64 {
                 let values = [1, 2, 3];
                 return values[0usize..2usize][0usize];
             }",
        ),
    ];

    for (name, source) in cases {
        let output = analyze(&SourceFile::from_text(name, source));
        assert!(output.lexed().issues().is_empty(), "{name}");
        assert_eq!(
            output.status(),
            FrontendStatus::Unsupported,
            "{name}: {:?}",
            output.issues()
        );
        assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Unsupported);
        assert!(output.hir().is_none(), "{name}");
        assert!(output.vir().is_none(), "{name}");
    }
}

#[test]
fn reference_schema_and_abi_are_only_a_structural_skeleton() {
    let schema = reference_schema();
    schema.validate().expect("canonical reference schema");

    let shared = schema
        .type_capabilities(SHARED_REFERENCE_TYPE)
        .expect("shared reference capabilities");
    assert_eq!(shared.value, ValueCapability::Copy);
    assert_eq!(shared.drop, DropCapability::TrivialDrop);
    assert!(shared.contains_resource);
    assert_eq!(shared.size, SizeCapability::Sized);

    let mutable = schema
        .type_capabilities(MUTABLE_REFERENCE_TYPE)
        .expect("mutable reference capabilities");
    assert_eq!(mutable.value, ValueCapability::MoveOnly);
    assert_eq!(mutable.drop, DropCapability::TrivialDrop);
    assert!(mutable.contains_resource);
    assert_eq!(mutable.size, SizeCapability::Sized);

    let abi = VirAbiSignature::classify(
        &schema,
        &[
            VirMemoryAccess::new(SHARED_REFERENCE_TYPE, VirLayoutId::new(1)),
            VirMemoryAccess::new(MUTABLE_REFERENCE_TYPE, VirLayoutId::new(2)),
        ],
        &[],
    )
    .expect("reference ABI skeleton classifies");
    assert_eq!(
        abi.parameters()[0].interface().transfer,
        VirInterfaceTransfer::BorrowShared
    );
    assert_eq!(
        abi.parameters()[1].interface().transfer,
        VirInterfaceTransfer::BorrowMutable
    );
    assert!(
        abi.parameters()
            .iter()
            .all(|binding| binding.interface().storage == VirInterfaceStorage::Direct)
    );
}

#[test]
fn mutated_reference_capability_is_invalid_vir_schema() {
    let mut schema = reference_schema();
    schema.type_capabilities[SHARED_REFERENCE_TYPE.index()].value = ValueCapability::MoveOnly;

    assert_eq!(
        schema
            .validate()
            .expect_err("shared reference capability cannot be hand-forged")
            .kind(),
        &VirMemorySchemaErrorKind::TypeCapabilityMismatch {
            ty: SHARED_REFERENCE_TYPE
        }
    );
}
