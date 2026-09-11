use nera::{
    ByteSpan, HirIntegerType, SourceFile, SpannedVirInstruction, SpannedVirTerminator, VirAbiClass,
    VirAbiEnvironment, VirBasicBlock, VirContractId, VirEndianness, VirField, VirFieldId,
    VirFieldLayout, VirFunction, VirFunctionId, VirIndexBounds, VirInstruction, VirIntegerType,
    VirLayout, VirLayoutId, VirMemoryAccess, VirMemorySchema, VirMemorySchemaErrorKind,
    VirMemoryType, VirMemoryTypeKind, VirSignature, VirTargetDataLayout, VirTerminator, VirType,
    VirTypeId, VirUnit, VirValidationErrorKind, VirValue, VirValueId, VirVariant,
    VirVariantCaseLayout, VirVariantId, VirVariantLayout, analyze,
};

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("ordered span")
}

fn access(ty: u32, layout: u32) -> VirMemoryAccess {
    VirMemoryAccess::new(VirTypeId::new(ty), VirLayoutId::new(layout))
}

fn aggregate_schema() -> VirMemorySchema {
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
                id: VirTypeId::new(0),
                kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                layout: VirLayoutId::new(0),
            },
            VirMemoryType {
                id: VirTypeId::new(1),
                kind: VirMemoryTypeKind::Struct {
                    fields: vec![VirFieldId::new(0), VirFieldId::new(1)],
                },
                layout: VirLayoutId::new(1),
            },
            VirMemoryType {
                id: VirTypeId::new(2),
                kind: VirMemoryTypeKind::Array {
                    element: VirTypeId::new(0),
                    length: 2,
                },
                layout: VirLayoutId::new(2),
            },
            VirMemoryType {
                id: VirTypeId::new(3),
                kind: VirMemoryTypeKind::Enum {
                    variants: vec![VirVariantId::new(0)],
                },
                layout: VirLayoutId::new(3),
            },
            VirMemoryType {
                id: VirTypeId::new(4),
                kind: VirMemoryTypeKind::Tuple(vec![VirTypeId::new(0), VirTypeId::new(0)]),
                layout: VirLayoutId::new(4),
            },
        ],
        type_capabilities: vec![],
        layouts: vec![
            VirLayout {
                id: VirLayoutId::new(0),
                ty: VirTypeId::new(0),
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: vec![],
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(1),
                ty: VirTypeId::new(1),
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![
                    VirFieldLayout {
                        field: VirFieldId::new(0),
                        offset_bytes: 0,
                    },
                    VirFieldLayout {
                        field: VirFieldId::new(1),
                        offset_bytes: 8,
                    },
                ],
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(2),
                ty: VirTypeId::new(2),
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![],
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(3),
                ty: VirTypeId::new(3),
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![],
                variants: Some(VirVariantLayout {
                    tag_size_bytes: 8,
                    tag_alignment: 8,
                    cases: vec![VirVariantCaseLayout {
                        variant: VirVariantId::new(0),
                        payload_offset_bytes: 8,
                        fields: vec![VirFieldLayout {
                            field: VirFieldId::new(2),
                            offset_bytes: 0,
                        }],
                    }],
                }),
            },
            VirLayout {
                id: VirLayoutId::new(4),
                ty: VirTypeId::new(4),
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![],
                variants: None,
            },
        ],
        fields: vec![
            VirField {
                id: VirFieldId::new(0),
                owner: VirTypeId::new(1),
                ty: VirTypeId::new(0),
            },
            VirField {
                id: VirFieldId::new(1),
                owner: VirTypeId::new(1),
                ty: VirTypeId::new(0),
            },
            VirField {
                id: VirFieldId::new(2),
                owner: VirTypeId::new(3),
                ty: VirTypeId::new(0),
            },
        ],
        variants: vec![VirVariant {
            id: VirVariantId::new(0),
            owner: VirTypeId::new(3),
            fields: vec![VirFieldId::new(2)],
            discriminant: 0,
        }],
    };
    schema.assign_canonical_type_capabilities().unwrap();
    schema
}

#[test]
fn schema_validates_dense_nominal_ownership_and_target_layouts() {
    let schema = aggregate_schema();
    schema.validate().expect("canonical aggregate schema");
    assert_eq!(schema.access(VirTypeId::new(1)), Some(access(1, 1)));
    assert!(schema.resolves_access(access(2, 2)));

    let mut non_dense = schema.clone();
    non_dense.types[1].id = VirTypeId::new(7);
    assert!(matches!(
        non_dense
            .validate()
            .expect_err("non-dense ID must fail")
            .kind(),
        VirMemorySchemaErrorKind::NonDenseTable { table: "type" }
    ));

    let mut foreign_field = schema.clone();
    foreign_field.fields[0].owner = VirTypeId::new(3);
    assert!(matches!(
        foreign_field
            .validate()
            .expect_err("foreign field must fail")
            .kind(),
        VirMemorySchemaErrorKind::InvalidType {
            ty
        } if *ty == VirTypeId::new(1)
    ));

    let mut overlap = schema.clone();
    overlap.layouts[1].fields[1].offset_bytes = 0;
    assert!(matches!(
        overlap.validate().expect_err("overlap must fail").kind(),
        VirMemorySchemaErrorKind::InvalidLayout { layout }
            if *layout == VirLayoutId::new(1)
    ));

    let mut overflowing_array = schema.clone();
    overflowing_array.types[2].kind = VirMemoryTypeKind::Array {
        element: VirTypeId::new(0),
        length: u64::MAX,
    };
    assert!(matches!(
        overflowing_array
            .validate()
            .expect_err("array extent overflow must fail")
            .kind(),
        VirMemorySchemaErrorKind::InvalidType { ty } if *ty == VirTypeId::new(2)
    ));

    let mut overlapping_tag = schema;
    overlapping_tag.layouts[3]
        .variants
        .as_mut()
        .expect("enum layout")
        .cases[0]
        .payload_offset_bytes = 0;
    assert!(matches!(
        overlapping_tag
            .validate()
            .expect_err("payload/tag overlap must fail")
            .kind(),
        VirMemorySchemaErrorKind::InvalidLayout { layout }
            if *layout == VirLayoutId::new(3)
    ));

    let mut narrow_tag = aggregate_schema();
    let variant_layout = narrow_tag.layouts[3]
        .variants
        .as_mut()
        .expect("enum layout");
    variant_layout.tag_size_bytes = 1;
    variant_layout.tag_alignment = 1;
    narrow_tag.variants[0].discriminant = 256;
    assert!(matches!(
        narrow_tag
            .validate()
            .expect_err("discriminant must fit the canonical tag")
            .kind(),
        VirMemorySchemaErrorKind::InvalidLayout { layout }
            if *layout == VirLayoutId::new(3)
    ));
}

#[test]
fn schema_rejects_a_mutated_canonical_type_capability() {
    let mut schema = aggregate_schema();
    schema.type_capabilities[0].value = nera::ValueCapability::MoveOnly;

    assert_eq!(
        schema
            .validate()
            .expect_err("capability mutation must fail")
            .kind(),
        &VirMemorySchemaErrorKind::TypeCapabilityMismatch {
            ty: VirTypeId::new(0)
        }
    );
}

#[test]
fn hir_lowering_emits_only_reachable_concrete_memory_instances() {
    let output = analyze(&SourceFile::new(
        "memory.nera",
        include_bytes!("../spec/cases/vir/memory.nera"),
    ));
    let program = output.vir().expect("accepted corpus has VIR").runtime();
    program.memory.validate().expect("lowered schema is valid");
    assert_eq!(program.memory.types.len(), 3);
    assert_eq!(program.memory.layouts.len(), 3);
    assert!(program.memory.fields.is_empty());
    assert!(program.memory.variants.is_empty());
    assert!(matches!(
        program.memory.types[0].kind,
        VirMemoryTypeKind::Integer(VirIntegerType::U64)
    ));
    assert!(
        program
            .memory
            .types
            .iter()
            .all(|ty| !matches!(ty.kind, VirMemoryTypeKind::Bool | VirMemoryTypeKind::Unit))
    );
    assert!(
        output
            .hir()
            .expect("accepted corpus has HIR")
            .types()
            .iter()
            .any(|ty| matches!(ty.kind, nera::HirTypeKind::Bool))
    );
    assert!(
        output
            .hir()
            .expect("accepted corpus has HIR")
            .types()
            .iter()
            .any(|ty| matches!(ty.kind, nera::HirTypeKind::Integer(HirIntegerType::U64)))
    );
}

#[test]
fn typed_address_validation_enforces_canonical_projection_relationships() {
    let leaf_pointer = VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    };
    let record_pointer = VirType::Pointer {
        access: access(1, 1),
    };
    let array_pointer = VirType::Pointer {
        access: access(2, 2),
    };
    let tuple_pointer = VirType::Pointer {
        access: access(4, 4),
    };
    let program = VirUnit::from_runtime(
        aggregate_schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "address-schema".to_owned(),
            signature: VirSignature {
                parameters: vec![record_pointer, array_pointer, tuple_pointer, VirType::U64],
                results: vec![],
            },
            contract: VirContractId::new(0),
            entry: nera::VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: nera::VirBlockId::new(0),
                parameters: vec![
                    VirValue {
                        id: VirValueId::new(0),
                        ty: record_pointer,
                    },
                    VirValue {
                        id: VirValueId::new(1),
                        ty: array_pointer,
                    },
                    VirValue {
                        id: VirValueId::new(2),
                        ty: tuple_pointer,
                    },
                    VirValue {
                        id: VirValueId::new(3),
                        ty: VirType::U64,
                    },
                ],
                instructions: vec![
                    SpannedVirInstruction {
                        instruction: VirInstruction::FieldAddress {
                            result: VirValue {
                                id: VirValueId::new(4),
                                ty: leaf_pointer,
                            },
                            base: VirValueId::new(0),
                            field: VirFieldId::new(1),
                            owner: access(1, 1),
                            field_access: access(0, 0),
                            offset_bytes: 8,
                        },
                        source_span: span(),
                    },
                    SpannedVirInstruction {
                        instruction: VirInstruction::IndexAddress {
                            result: VirValue {
                                id: VirValueId::new(5),
                                ty: leaf_pointer,
                            },
                            base: VirValueId::new(1),
                            index: VirValueId::new(3),
                            source: access(2, 2),
                            element: access(0, 0),
                            stride_bytes: 8,
                            bounds: VirIndexBounds::Array { length: 2 },
                        },
                        source_span: span(),
                    },
                    SpannedVirInstruction {
                        instruction: VirInstruction::TupleElementAddress {
                            result: VirValue {
                                id: VirValueId::new(6),
                                ty: leaf_pointer,
                            },
                            base: VirValueId::new(2),
                            index: 1,
                            owner: access(4, 4),
                            element_access: access(0, 0),
                            offset_bytes: 8,
                        },
                        source_span: span(),
                    },
                ],
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return { values: vec![] },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    );
    let dump = program.stable_dump();
    assert!(
        dump.contains("field.address %0 field1 owner type1/layout1 result type0/layout0 offset 8")
    );
    assert!(dump.contains(
        "index.address %1, %3 source type2/layout2 element type0/layout0 stride 8 bounds array(2)"
    ));
    assert!(
        dump.contains(
            "tuple.address %2 element1 owner type4/layout4 result type0/layout0 offset 8"
        )
    );
    program
        .validate()
        .expect("canonical field/index projections validate");

    let mutate = |instruction_index: usize,
                  change: &dyn Fn(&mut VirInstruction)|
     -> VirValidationErrorKind {
        let mut mutated = program.clone();
        change(
            &mut mutated.runtime.functions[0].blocks[0].instructions[instruction_index].instruction,
        );
        mutated
            .validate()
            .expect_err("projection mutation must fail closed")
            .kind()
            .clone()
    };
    assert_eq!(
        mutate(0, &|instruction| {
            let VirInstruction::FieldAddress { offset_bytes, .. } = instruction else {
                unreachable!()
            };
            *offset_bytes = 0;
        }),
        VirValidationErrorKind::InvalidFieldProjection(VirFieldId::new(1))
    );
    assert_eq!(
        mutate(0, &|instruction| {
            let VirInstruction::FieldAddress { owner, .. } = instruction else {
                unreachable!()
            };
            *owner = access(2, 2);
        }),
        VirValidationErrorKind::TypeMismatch {
            context: "field address",
            expected: VirType::Pointer {
                access: access(2, 2),
            },
            found: record_pointer,
        }
    );
    assert_eq!(
        mutate(1, &|instruction| {
            let VirInstruction::IndexAddress { stride_bytes, .. } = instruction else {
                unreachable!()
            };
            *stride_bytes = 16;
        }),
        VirValidationErrorKind::InvalidIndexProjection
    );
    assert_eq!(
        mutate(1, &|instruction| {
            let VirInstruction::IndexAddress { bounds, .. } = instruction else {
                unreachable!()
            };
            *bounds = VirIndexBounds::Array { length: 3 };
        }),
        VirValidationErrorKind::InvalidIndexProjection
    );
    assert_eq!(
        mutate(1, &|instruction| {
            let VirInstruction::IndexAddress { bounds, .. } = instruction else {
                unreachable!()
            };
            *bounds = VirIndexBounds::Slice {
                length: VirValueId::new(1),
            };
        }),
        VirValidationErrorKind::TypeMismatch {
            context: "slice index address",
            expected: VirType::Pointer {
                access: access(0, 0),
            },
            found: array_pointer,
        }
    );
    assert_eq!(
        mutate(2, &|instruction| {
            let VirInstruction::TupleElementAddress { offset_bytes, .. } = instruction else {
                unreachable!()
            };
            *offset_bytes = 0;
        }),
        VirValidationErrorKind::InvalidTupleProjection(1)
    );

    let mut wrong_access =
        VirUnit::from_runtime(VirMemorySchema::core_u64(), VirFunctionId::new(0), vec![]);
    wrong_access.runtime.functions = vec![VirFunction {
        id: VirFunctionId::new(0),
        name: "wrong-access".to_owned(),
        signature: VirSignature {
            parameters: vec![leaf_pointer, VirType::Permission],
            results: vec![VirType::U64],
        },
        contract: VirContractId::new(0),
        entry: nera::VirBlockId::new(0),
        blocks: vec![VirBasicBlock {
            id: nera::VirBlockId::new(0),
            parameters: vec![
                VirValue {
                    id: VirValueId::new(0),
                    ty: leaf_pointer,
                },
                VirValue {
                    id: VirValueId::new(1),
                    ty: VirType::Permission,
                },
            ],
            instructions: vec![SpannedVirInstruction {
                instruction: VirInstruction::Load {
                    result: VirValue {
                        id: VirValueId::new(2),
                        ty: VirType::U64,
                    },
                    pointer: VirValueId::new(0),
                    permission: VirValueId::new(1),
                    access: access(0, 9),
                },
                source_span: span(),
            }],
            terminator: SpannedVirTerminator {
                terminator: VirTerminator::Return {
                    values: vec![VirValueId::new(2)],
                },
                source_span: span(),
            },
            source_span: span(),
        }],
        source_span: span(),
    }];
    wrong_access.runtime.abis = VirAbiEnvironment::identity(&wrong_access.runtime.functions);
    assert_eq!(
        wrong_access
            .validate()
            .expect_err("forged access must fail")
            .kind(),
        &VirValidationErrorKind::InvalidMemoryAccess(access(0, 9))
    );

    wrong_access.memory.target.pointer_alignment = 3;
    assert_eq!(
        wrong_access
            .validate()
            .expect_err("invalid schema must fail before function validation")
            .kind(),
        &VirValidationErrorKind::InvalidMemorySchema(VirMemorySchemaErrorKind::InvalidTarget)
    );
}
