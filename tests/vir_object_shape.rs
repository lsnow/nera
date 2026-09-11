use nera::{
    VIR_OBJECT_SHAPE_MAX_DEPTH, VIR_OBJECT_SHAPE_MAX_NODES, VirAbiClass, VirEndianness, VirField,
    VirFieldId, VirFieldLayout, VirIntegerType, VirLayout, VirLayoutId, VirMemoryAccess,
    VirMemorySchema, VirMemorySchemaErrorKind, VirMemoryType, VirMemoryTypeKind, VirMutability,
    VirObjectByteRange, VirObjectPathSegment, VirObjectShape, VirObjectShapeErrorKind,
    VirPointerKind, VirTargetDataLayout, VirTypeId, VirVariant, VirVariantCaseLayout, VirVariantId,
    VirVariantLayout,
};

fn access(raw: u32) -> VirMemoryAccess {
    VirMemoryAccess::new(VirTypeId::new(raw), VirLayoutId::new(raw))
}

fn target() -> VirTargetDataLayout {
    VirTargetDataLayout {
        endianness: VirEndianness::Little,
        pointer_size_bytes: 8,
        pointer_alignment: 8,
        usize_size_bytes: 8,
        usize_alignment: 8,
    }
}

fn layout(raw: u32, size_bytes: u64, alignment: u64, abi: VirAbiClass) -> VirLayout {
    VirLayout {
        id: VirLayoutId::new(raw),
        ty: VirTypeId::new(raw),
        size_bytes,
        alignment,
        abi,
        fields: Vec::new(),
        variants: None,
    }
}

fn object_schema() -> VirMemorySchema {
    let types = vec![
        VirMemoryType {
            id: VirTypeId::new(0),
            kind: VirMemoryTypeKind::Integer(VirIntegerType::U8),
            layout: VirLayoutId::new(0),
        },
        VirMemoryType {
            id: VirTypeId::new(1),
            kind: VirMemoryTypeKind::Integer(VirIntegerType::U16),
            layout: VirLayoutId::new(1),
        },
        VirMemoryType {
            id: VirTypeId::new(2),
            kind: VirMemoryTypeKind::Struct {
                fields: vec![VirFieldId::new(0), VirFieldId::new(1)],
            },
            layout: VirLayoutId::new(2),
        },
        VirMemoryType {
            id: VirTypeId::new(3),
            kind: VirMemoryTypeKind::Array {
                element: VirTypeId::new(2),
                length: 2,
            },
            layout: VirLayoutId::new(3),
        },
        VirMemoryType {
            id: VirTypeId::new(4),
            kind: VirMemoryTypeKind::Tuple(vec![VirTypeId::new(0), VirTypeId::new(1)]),
            layout: VirLayoutId::new(4),
        },
        VirMemoryType {
            id: VirTypeId::new(5),
            kind: VirMemoryTypeKind::Enum {
                variants: vec![VirVariantId::new(0), VirVariantId::new(1)],
            },
            layout: VirLayoutId::new(5),
        },
        VirMemoryType {
            id: VirTypeId::new(6),
            kind: VirMemoryTypeKind::Pointer {
                pointee: VirTypeId::new(2),
                kind: VirPointerKind::Raw,
                mutability: VirMutability::Mutable,
            },
            layout: VirLayoutId::new(6),
        },
        VirMemoryType {
            id: VirTypeId::new(7),
            kind: VirMemoryTypeKind::Unit,
            layout: VirLayoutId::new(7),
        },
    ];
    let mut layouts = vec![
        layout(0, 1, 1, VirAbiClass::Scalar),
        layout(1, 2, 2, VirAbiClass::Scalar),
        layout(2, 4, 2, VirAbiClass::Aggregate),
        layout(3, 8, 2, VirAbiClass::Aggregate),
        layout(4, 4, 2, VirAbiClass::Aggregate),
        layout(5, 4, 2, VirAbiClass::Aggregate),
        layout(6, 8, 8, VirAbiClass::Scalar),
        layout(7, 0, 1, VirAbiClass::Ignore),
    ];
    layouts[2].fields = vec![
        VirFieldLayout {
            field: VirFieldId::new(0),
            offset_bytes: 0,
        },
        VirFieldLayout {
            field: VirFieldId::new(1),
            offset_bytes: 2,
        },
    ];
    layouts[5].variants = Some(VirVariantLayout {
        tag_size_bytes: 1,
        tag_alignment: 1,
        cases: vec![
            VirVariantCaseLayout {
                variant: VirVariantId::new(0),
                payload_offset_bytes: 2,
                fields: vec![VirFieldLayout {
                    field: VirFieldId::new(2),
                    offset_bytes: 0,
                }],
            },
            VirVariantCaseLayout {
                variant: VirVariantId::new(1),
                payload_offset_bytes: 2,
                fields: vec![VirFieldLayout {
                    field: VirFieldId::new(3),
                    offset_bytes: 0,
                }],
            },
        ],
    });

    let mut schema = VirMemorySchema {
        target: target(),
        types,
        type_capabilities: vec![],
        layouts,
        fields: vec![
            VirField {
                id: VirFieldId::new(0),
                owner: VirTypeId::new(2),
                ty: VirTypeId::new(0),
            },
            VirField {
                id: VirFieldId::new(1),
                owner: VirTypeId::new(2),
                ty: VirTypeId::new(1),
            },
            VirField {
                id: VirFieldId::new(2),
                owner: VirTypeId::new(5),
                ty: VirTypeId::new(1),
            },
            VirField {
                id: VirFieldId::new(3),
                owner: VirTypeId::new(5),
                ty: VirTypeId::new(0),
            },
        ],
        variants: vec![
            VirVariant {
                id: VirVariantId::new(0),
                owner: VirTypeId::new(5),
                fields: vec![VirFieldId::new(2)],
                discriminant: 7,
            },
            VirVariant {
                id: VirVariantId::new(1),
                owner: VirTypeId::new(5),
                fields: vec![VirFieldId::new(3)],
                discriminant: 9,
            },
        ],
    };
    schema.assign_canonical_type_capabilities().unwrap();
    schema
}

fn ranges(ranges: &[VirObjectByteRange]) -> Vec<(u64, u64)> {
    ranges
        .iter()
        .map(|range| (range.start_bytes(), range.end_bytes()))
        .collect()
}

fn leaf_ranges(shape: &VirObjectShape) -> Vec<(u64, u64)> {
    shape
        .leaves()
        .iter()
        .map(|leaf| (leaf.bytes().start_bytes(), leaf.bytes().end_bytes()))
        .collect()
}

#[test]
fn derives_struct_tuple_array_enum_and_scalar_shapes() {
    let schema = object_schema();
    schema.validate().expect("object schema is valid");

    let scalar = schema.object_shape(access(0)).expect("u8 shape");
    assert_eq!(scalar.access(), access(0));
    assert_eq!((scalar.size_bytes(), scalar.alignment()), (1, 1));
    assert_eq!(leaf_ranges(&scalar), vec![(0, 1)]);
    assert_eq!(ranges(scalar.value_bytes()), vec![(0, 1)]);
    assert!(scalar.padding().is_empty());
    assert!(scalar.leaves()[0].path().segments().is_empty());

    let structure = schema.object_shape(access(2)).expect("struct shape");
    assert_eq!(leaf_ranges(&structure), vec![(0, 1), (2, 4)]);
    assert_eq!(ranges(structure.value_bytes()), vec![(0, 1), (2, 4)]);
    assert_eq!(ranges(structure.padding()), vec![(1, 2)]);
    assert_eq!(
        structure.leaves()[1].path().segments(),
        &[VirObjectPathSegment::Field(VirFieldId::new(1))]
    );

    let tuple = schema.object_shape(access(4)).expect("tuple shape");
    assert_eq!(leaf_ranges(&tuple), vec![(0, 1), (2, 4)]);
    assert_eq!(ranges(tuple.padding()), vec![(1, 2)]);
    assert_eq!(
        tuple.leaves()[1].path().segments(),
        &[VirObjectPathSegment::TupleElement(1)]
    );

    let array = schema.object_shape(access(3)).expect("array shape");
    assert_eq!(leaf_ranges(&array), vec![(0, 1), (2, 4), (4, 5), (6, 8)]);
    assert_eq!(ranges(array.value_bytes()), vec![(0, 1), (2, 5), (6, 8)]);
    assert_eq!(ranges(array.padding()), vec![(1, 2), (5, 6)]);
    assert_eq!(array.arrays().len(), 1);
    assert_eq!(array.arrays()[0].stride_bytes(), 4);
    assert_eq!(array.arrays()[0].length(), 2);
    assert_eq!(array.arrays()[0].access(), access(3));
    assert_eq!(array.arrays()[0].element_access(), access(2));
    assert_eq!(ranges(&[array.arrays()[0].extent()]), vec![(0, 8)]);
    assert_eq!(
        array.leaves()[2].path().segments(),
        &[
            VirObjectPathSegment::ArrayElement(1),
            VirObjectPathSegment::Field(VirFieldId::new(0)),
        ]
    );

    let enumeration = schema.object_shape(access(5)).expect("enum shape");
    assert_eq!(leaf_ranges(&enumeration), vec![(2, 4), (2, 3)]);
    assert!(
        enumeration.leaves()[0].bytes().start_bytes() < enumeration.leaves()[1].bytes().end_bytes()
    );
    assert_eq!(ranges(enumeration.value_bytes()), vec![(0, 1), (2, 4)]);
    assert_eq!(ranges(enumeration.padding()), vec![(1, 2)]);
    assert_eq!(enumeration.variants().len(), 2);
    let first = &enumeration.variants()[0];
    assert_eq!(first.variant(), VirVariantId::new(0));
    assert_eq!(first.discriminant(), 7);
    assert_eq!(ranges(&[first.tag()]), vec![(0, 1)]);
    assert_eq!(ranges(&[first.payload()]), vec![(2, 4)]);
    assert_eq!(ranges(first.value_bytes()), vec![(0, 1), (2, 4)]);
    assert_eq!(ranges(first.padding()), vec![(1, 2)]);
    let second = &enumeration.variants()[1];
    assert_eq!(ranges(second.value_bytes()), vec![(0, 1), (2, 3)]);
    assert_eq!(ranges(second.padding()), vec![(1, 2), (3, 4)]);

    let pointer = schema.object_shape(access(6)).expect("pointer is a leaf");
    assert_eq!(leaf_ranges(&pointer), vec![(0, 8)]);
    assert_eq!(pointer.leaves()[0].access(), access(6));

    let unit = schema.object_shape(access(7)).expect("unit shape");
    assert_eq!(unit.size_bytes(), 0);
    assert!(unit.leaves().is_empty());
    assert!(unit.value_bytes().is_empty());
    assert!(unit.padding().is_empty());
}

#[test]
fn canonical_order_is_independent_of_schema_vector_order() {
    let canonical = object_schema();
    let mut reordered = canonical.clone();
    if let VirMemoryTypeKind::Struct { fields } = &mut reordered.types[2].kind {
        fields.reverse();
    }
    reordered.layouts[2].fields.reverse();
    if let VirMemoryTypeKind::Enum { variants } = &mut reordered.types[5].kind {
        variants.reverse();
    }
    reordered.layouts[5]
        .variants
        .as_mut()
        .expect("enum layout")
        .cases
        .reverse();

    assert_eq!(
        canonical.object_shape(access(2)).expect("struct shape"),
        reordered.object_shape(access(2)).expect("reordered struct")
    );
    assert_eq!(
        canonical.object_shape(access(5)).expect("enum shape"),
        reordered.object_shape(access(5)).expect("reordered enum")
    );
}

#[test]
fn value_and_padding_masks_partition_each_small_active_shape() {
    let schema = object_schema();
    for raw in 0..8 {
        let shape = schema.object_shape(access(raw)).expect("small shape");
        assert_partition(shape.size_bytes(), shape.value_bytes(), shape.padding());
        for leaf in shape.leaves() {
            assert!(range_is_covered(leaf.bytes(), shape.value_bytes()));
        }
        for variant in shape.variants() {
            assert_partition(shape.size_bytes(), variant.value_bytes(), variant.padding());
            assert_non_overlapping(
                &variant
                    .leaves()
                    .iter()
                    .map(|leaf| leaf.bytes())
                    .collect::<Vec<_>>(),
            );
        }
    }
}

#[test]
fn malformed_or_unsupported_shapes_fail_closed() {
    let schema = object_schema();
    assert!(matches!(
        schema
            .object_shape(VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(1)))
            .expect_err("mismatched access must fail")
            .kind(),
        VirObjectShapeErrorKind::InvalidAccess { .. }
    ));

    let mut overlap = schema.clone();
    overlap.layouts[2].fields[1].offset_bytes = 0;
    assert!(matches!(
        overlap
            .object_shape(access(2))
            .expect_err("overlap must fail before derivation")
            .kind(),
        VirObjectShapeErrorKind::InvalidSchema(VirMemorySchemaErrorKind::InvalidLayout {
            layout
        }) if *layout == VirLayoutId::new(2)
    ));

    let mut wrong_owner = schema.clone();
    wrong_owner.fields[0].owner = VirTypeId::new(5);
    assert!(matches!(
        wrong_owner
            .object_shape(access(2))
            .expect_err("wrong owner must fail")
            .kind(),
        VirObjectShapeErrorKind::InvalidSchema(_)
    ));

    let mut fake_discriminant = schema.clone();
    fake_discriminant.variants[0].discriminant = 256;
    assert!(matches!(
        fake_discriminant
            .object_shape(access(5))
            .expect_err("discriminant wider than tag must fail")
            .kind(),
        VirObjectShapeErrorKind::InvalidSchema(VirMemorySchemaErrorKind::InvalidLayout {
            layout
        }) if *layout == VirLayoutId::new(5)
    ));

    let mut out_of_bounds_case = schema.clone();
    out_of_bounds_case.layouts[5]
        .variants
        .as_mut()
        .expect("enum layout")
        .cases[0]
        .payload_offset_bytes = 4;
    assert!(matches!(
        out_of_bounds_case
            .object_shape(access(5))
            .expect_err("payload outside enum must fail")
            .kind(),
        VirObjectShapeErrorKind::InvalidSchema(VirMemorySchemaErrorKind::InvalidLayout {
            layout
        }) if *layout == VirLayoutId::new(5)
    ));

    let mut empty_case_out_of_bounds = VirMemorySchema {
        target: target(),
        types: vec![VirMemoryType {
            id: VirTypeId::new(0),
            kind: VirMemoryTypeKind::Enum {
                variants: vec![VirVariantId::new(0)],
            },
            layout: VirLayoutId::new(0),
        }],
        type_capabilities: vec![],
        layouts: vec![VirLayout {
            id: VirLayoutId::new(0),
            ty: VirTypeId::new(0),
            size_bytes: 1,
            alignment: 1,
            abi: VirAbiClass::Aggregate,
            fields: Vec::new(),
            variants: Some(VirVariantLayout {
                tag_size_bytes: 1,
                tag_alignment: 1,
                cases: vec![VirVariantCaseLayout {
                    variant: VirVariantId::new(0),
                    payload_offset_bytes: 2,
                    fields: Vec::new(),
                }],
            }),
        }],
        fields: Vec::new(),
        variants: vec![VirVariant {
            id: VirVariantId::new(0),
            owner: VirTypeId::new(0),
            fields: Vec::new(),
            discriminant: 0,
        }],
    };
    empty_case_out_of_bounds
        .assign_canonical_type_capabilities()
        .unwrap();
    assert!(matches!(
        empty_case_out_of_bounds
            .object_shape(access(0))
            .expect_err("an empty payload base must still stay inside its enum")
            .kind(),
        VirObjectShapeErrorKind::InvalidSchema(VirMemorySchemaErrorKind::InvalidLayout {
            layout
        }) if *layout == VirLayoutId::new(0)
    ));

    let mut overflowing_array = schema.clone();
    overflowing_array.types[3].kind = VirMemoryTypeKind::Array {
        element: VirTypeId::new(2),
        length: u64::MAX,
    };
    assert!(matches!(
        overflowing_array
            .object_shape(access(3))
            .expect_err("array multiplication overflow must fail")
            .kind(),
        VirObjectShapeErrorKind::InvalidSchema(VirMemorySchemaErrorKind::InvalidType {
            ty
        }) if *ty == VirTypeId::new(3)
    ));

    let mut tuple_mismatch = schema.clone();
    tuple_mismatch.layouts[4].size_bytes = 6;
    tuple_mismatch
        .validate()
        .expect("the base schema does not duplicate tuple offsets");
    assert!(matches!(
        tuple_mismatch
            .object_shape(access(4))
            .expect_err("tuple derived layout mismatch must fail")
            .kind(),
        VirObjectShapeErrorKind::LayoutMismatch { access: found } if *found == access(4)
    ));
}

#[test]
fn recursive_slice_and_excessive_expansion_are_gated() {
    let mut recursive = object_schema();
    recursive.types.push(VirMemoryType {
        id: VirTypeId::new(8),
        kind: VirMemoryTypeKind::Struct {
            fields: vec![VirFieldId::new(4)],
        },
        layout: VirLayoutId::new(8),
    });
    let mut recursive_layout = layout(8, 4, 1, VirAbiClass::Aggregate);
    recursive_layout.fields.push(VirFieldLayout {
        field: VirFieldId::new(4),
        offset_bytes: 0,
    });
    recursive.layouts.push(recursive_layout);
    recursive.fields.push(VirField {
        id: VirFieldId::new(4),
        owner: VirTypeId::new(8),
        ty: VirTypeId::new(8),
    });
    assert!(matches!(
        recursive
            .assign_canonical_type_capabilities()
            .expect_err("by-value recursion has no finite capability")
            .kind(),
        VirMemorySchemaErrorKind::TypeCapabilityMismatch { ty }
            if *ty == VirTypeId::new(8)
    ));

    let mut slice = object_schema();
    slice.types.push(VirMemoryType {
        id: VirTypeId::new(8),
        kind: VirMemoryTypeKind::Slice {
            element: VirTypeId::new(0),
            mutability: VirMutability::Const,
        },
        layout: VirLayoutId::new(8),
    });
    slice
        .layouts
        .push(layout(8, 16, 8, VirAbiClass::ScalarPair));
    slice.assign_canonical_type_capabilities().unwrap();
    slice.validate().expect("slice metadata is valid");
    assert!(matches!(
        slice
            .object_shape(access(8))
            .expect_err("slice object semantics remain gated")
            .kind(),
        VirObjectShapeErrorKind::UnsupportedObjectType { ty }
            if *ty == VirTypeId::new(8)
    ));

    let mut huge = object_schema();
    let length = u64::try_from(VIR_OBJECT_SHAPE_MAX_NODES).expect("limit fits u64");
    huge.types.push(VirMemoryType {
        id: VirTypeId::new(8),
        kind: VirMemoryTypeKind::Array {
            element: VirTypeId::new(0),
            length,
        },
        layout: VirLayoutId::new(8),
    });
    huge.layouts
        .push(layout(8, length, 1, VirAbiClass::Aggregate));
    huge.assign_canonical_type_capabilities().unwrap();
    huge.validate().expect("large array schema is finite");
    assert!(matches!(
        huge.object_shape(access(8))
            .expect_err("unbounded mask expansion must fail")
            .kind(),
        VirObjectShapeErrorKind::ComplexityLimitExceeded { limit, .. }
            if *limit == VIR_OBJECT_SHAPE_MAX_NODES
    ));

    let mut deep = VirMemorySchema {
        target: target(),
        types: vec![VirMemoryType {
            id: VirTypeId::new(0),
            kind: VirMemoryTypeKind::Integer(VirIntegerType::U8),
            layout: VirLayoutId::new(0),
        }],
        type_capabilities: vec![],
        layouts: vec![layout(0, 1, 1, VirAbiClass::Scalar)],
        fields: Vec::new(),
        variants: Vec::new(),
    };
    let deepest = u32::try_from(VIR_OBJECT_SHAPE_MAX_DEPTH + 1).expect("depth fits u32");
    for raw in 1..=deepest {
        deep.types.push(VirMemoryType {
            id: VirTypeId::new(raw),
            kind: VirMemoryTypeKind::Tuple(vec![VirTypeId::new(raw - 1)]),
            layout: VirLayoutId::new(raw),
        });
        deep.layouts.push(layout(raw, 1, 1, VirAbiClass::Aggregate));
    }
    deep.assign_canonical_type_capabilities().unwrap();
    deep.validate().expect("deep but finite aggregate schema");
    assert!(matches!(
        deep.object_shape(access(deepest))
            .expect_err("excessive nesting must fail before stack exhaustion")
            .kind(),
        VirObjectShapeErrorKind::NestingLimitExceeded { limit, .. }
            if *limit == VIR_OBJECT_SHAPE_MAX_DEPTH
    ));
}

fn assert_partition(size_bytes: u64, value: &[VirObjectByteRange], padding: &[VirObjectByteRange]) {
    let size = usize::try_from(size_bytes).expect("small shape");
    let mut coverage = vec![0_u8; size];
    for range in value {
        for byte in range.start_bytes()..range.end_bytes() {
            coverage[usize::try_from(byte).expect("small byte")] += 1;
        }
    }
    for range in padding {
        for byte in range.start_bytes()..range.end_bytes() {
            coverage[usize::try_from(byte).expect("small byte")] += 1;
        }
    }
    assert!(coverage.iter().all(|count| *count == 1));
}

fn range_is_covered(range: VirObjectByteRange, cover: &[VirObjectByteRange]) -> bool {
    cover.iter().any(|candidate| {
        candidate.start_bytes() <= range.start_bytes() && range.end_bytes() <= candidate.end_bytes()
    })
}

fn assert_non_overlapping(ranges: &[VirObjectByteRange]) {
    let mut ranges = ranges.to_vec();
    ranges.sort_unstable();
    assert!(
        ranges
            .windows(2)
            .all(|pair| pair[0].end_bytes() <= pair[1].start_bytes())
    );
}
