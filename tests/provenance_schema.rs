#[path = "support/address_program.rs"]
mod address_program;
#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, VirAddressStep, VirFieldId, VirInstruction, VirMemoryAccess,
    VirObjectPathSegment as Path, VirOriginId, VirPointerSource, VirSequenceExtent,
    VirValidationErrorKind, verify_program,
};

const SOURCE: &str = include_str!("../spec/cases/verify/provenance-schema.nera");

#[test]
fn nested_field_array_and_slice_recipes_share_the_original_allocation() {
    frontend_checks::checked("provenance-schema.nera", SOURCE, 42);
    let output = frontend_checks::accepted("provenance-schema.nera", SOURCE);
    let unit = output.vir().unwrap();
    let catalog = unit.provenance_catalog();
    assert_eq!(catalog, unit.provenance_catalog());
    let roots: Vec<_> = catalog
        .entries()
        .iter()
        .filter(|(_, d)| matches!(d.source, VirPointerSource::AllocationSite { .. }))
        .collect();
    assert_eq!(roots.len(), 1, "subobjects are not additional allocations");
    let (root, _) = roots[0];
    let mut slices = 0;
    let mut indices = 0;
    for (key, description) in catalog.entries() {
        assert!(catalog.matches(*key, description));
        assert_eq!(
            unit.as_unit()
                .source_map
                .origin_at(description.location)
                .unwrap()
                .id,
            description.origin
        );
        let VirPointerSource::Derived { base, step } = &description.source else {
            continue;
        };
        assert_eq!(key.function, base.function);
        assert!(catalog.entries().contains_key(base));
        match step {
            VirAddressStep::Subobject(object) => {
                assert_eq!(object.access(), description.access);
                assert_eq!(object.root(), catalog.entries()[base].access);
                if base == root {
                    assert_eq!(object.path().len(), 1);
                    assert_ne!(key, root);
                }
            }
            VirAddressStep::Slice { sequence, .. } => {
                slices += 1;
                assert_eq!(
                    sequence.extent(),
                    VirSequenceExtent::Array {
                        length: 4,
                        size_bytes: 32
                    }
                );
                let mut current = *base;
                // Follow only this acyclic, straight-line fixture. Production
                // CFG parameters remain symbolic rather than being guessed.
                for _ in 0..3 {
                    if current == *root {
                        break;
                    }
                    let VirPointerSource::Derived { base, .. } = catalog.entries()[&current].source
                    else {
                        panic!("field chain");
                    };
                    current = base;
                }
                assert_eq!(current, *root);
            }
            VirAddressStep::Index { sequence, .. } => {
                indices += 1;
                assert_eq!(sequence.stride_bytes(), 8);
            }
            _ => {}
        }
    }
    assert!(slices > 0 && indices >= 2);
}

#[test]
fn canonical_path_preserves_array_domain_but_fields_narrow_it() {
    let output = frontend_checks::accepted("provenance-schema.nera", SOURCE);
    let memory = &output.vir().unwrap().as_unit().memory;
    let allocation = output.vir().unwrap().runtime().functions[0].blocks[0]
        .instructions
        .iter()
        .find_map(|i| {
            if let VirInstruction::Allocate { element, .. } = i.instruction {
                Some(element)
            } else {
                None
            }
        })
        .unwrap();
    let nera::VirMemoryTypeKind::Struct { fields } = memory.kind(allocation.ty).unwrap() else {
        panic!()
    };
    let inner = fields[0];
    let inner_access = memory.access(memory.field(inner).unwrap().ty).unwrap();
    let nera::VirMemoryTypeKind::Struct {
        fields: inner_fields,
    } = memory.kind(inner_access.ty).unwrap()
    else {
        panic!()
    };
    let values = inner_fields[0];
    let field = memory.subobject(allocation, &[Path::Field(inner)]).unwrap();
    assert_eq!(field.offset_bytes(), 0, "same address as root");
    assert_eq!(field.domain_path(), [Path::Field(inner)]);
    assert!(field.domain_size_bytes() < memory.layout(allocation.layout).unwrap().size_bytes);
    for index in 0..4 {
        let path = [
            Path::Field(inner),
            Path::Field(values),
            Path::ArrayElement(index),
        ];
        let element = memory.subobject(allocation, &path).unwrap();
        assert_eq!(element.offset_bytes(), index * 8);
        assert_eq!(element.size_bytes(), 8);
        assert_eq!(element.domain_path(), &path[..2]);
        assert_eq!(element.domain_offset_bytes(), 0);
        assert_eq!(element.domain_size_bytes(), 32);
    }
    assert!(
        memory
            .subobject(
                allocation,
                &[
                    Path::Field(inner),
                    Path::Field(values),
                    Path::ArrayElement(4)
                ]
            )
            .is_none()
    );
    assert!(
        memory
            .subobject(allocation, &[Path::Field(values)])
            .is_none(),
        "wrong owner path"
    );
    assert!(
        memory
            .subobject(allocation, &[Path::Field(VirFieldId::new(u32::MAX))])
            .is_none()
    );
}

#[test]
fn source_path_extent_type_and_origin_mutations_cannot_replay() {
    let unit = address_program::validated();
    let catalog = unit.provenance_catalog();
    let (key, original) = catalog
        .entries()
        .iter()
        .find(|(_, d)| {
            matches!(
                d.source,
                VirPointerSource::Derived {
                    step: VirAddressStep::Subobject(_),
                    ..
                }
            )
        })
        .unwrap();
    let mut mutations = Vec::new();
    let mut origin = original.clone();
    origin.origin = VirOriginId::new(u32::MAX);
    mutations.push(origin);
    let mut ty = original.clone();
    ty.access = address_program::U64_ACCESS;
    mutations.push(ty);
    let mut source = original.clone();
    if let VirPointerSource::Derived { base, .. } = &mut source.source {
        base.function = nera::VirFunctionId::new(99);
    }
    mutations.push(source);
    let mut wrong_path = original.clone();
    if let VirPointerSource::Derived { step, .. } = &mut wrong_path.source {
        // A valid but different path cannot replace this field with its root.
        *step = VirAddressStep::Subobject(
            unit.as_unit()
                .memory
                .subobject(address_program::RECORD_ACCESS, &[])
                .unwrap(),
        );
    }
    mutations.push(wrong_path);
    for mutation in mutations {
        assert!(!catalog.matches(*key, &mutation));
    }

    for mutation in 0..4 {
        let mut raw = unit.as_unit().clone();
        let field = raw.runtime.functions[0].blocks[0]
            .instructions
            .iter_mut()
            .find(|i| matches!(i.instruction, VirInstruction::FieldAddress { .. }))
            .unwrap();
        let VirInstruction::FieldAddress {
            field,
            field_access,
            offset_bytes,
            ..
        } = &mut field.instruction
        else {
            unreachable!()
        };
        match mutation {
            0 => *field = VirFieldId::new(99),
            1 => *offset_bytes += 8,
            2 => *field_access = VirMemoryAccess::core_u64(),
            _ => {
                // A forged field extent must be rejected as an invalid memory
                // schema, before a descriptor can be obtained from the unit.
                raw.memory.layouts[address_program::ARRAY_ACCESS.layout.index()].size_bytes += 8;
            }
        }
        let failure = raw.into_validated().unwrap_err();
        assert!(
            matches!(
                (mutation, failure.kind()),
                (0 | 1, VirValidationErrorKind::InvalidFieldProjection(_))
                    | (2, VirValidationErrorKind::TypeMismatch { .. })
                    | (3, VirValidationErrorKind::InvalidMemorySchema(_))
            ),
            "mutation {mutation}: {failure:?}"
        );
    }
    let mut raw = unit.as_unit().clone();
    let mut locations = raw.source_map.locations().to_vec();
    locations
        .iter_mut()
        .find(|entry| entry.location == original.location)
        .unwrap()
        .origin = VirOriginId::new(u32::MAX);
    raw.source_map = nera::VirSourceMap::from_tables(
        raw.source_map.sources().to_vec(),
        raw.source_map.origins().to_vec(),
        locations,
    );
    assert!(matches!(
        raw.into_validated().unwrap_err().kind(),
        VirValidationErrorKind::InvalidSourceMap(_)
    ));
}

#[test]
fn nested_arrays_tuples_and_same_address_variants_have_distinct_paths() {
    let source = "enum Item { Left(u64), Right(u64), }
      fn main() -> u64 { let value = ([[1, 2], [3, 4]], 42); let item = Item::Left(1); return value.1; }";
    let output = frontend_checks::accepted("nested-paths.nera", source);
    let unit = output.vir().unwrap();
    let memory = &unit.as_unit().memory;
    let tuple = memory
        .types
        .iter()
        .find(|ty| matches!(ty.kind, nera::VirMemoryTypeKind::Tuple(_)))
        .unwrap();
    let root = memory.access(tuple.id).unwrap();
    let object = memory
        .subobject(
            root,
            &[
                Path::TupleElement(0),
                Path::ArrayElement(1),
                Path::ArrayElement(0),
            ],
        )
        .unwrap();
    assert_eq!(object.offset_bytes(), 16);
    assert_eq!(object.domain_offset_bytes(), 16);
    assert_eq!(object.domain_size_bytes(), 16);
    assert_eq!(
        object.domain_path(),
        [Path::TupleElement(0), Path::ArrayElement(1)]
    );
    let enum_type = memory
        .types
        .iter()
        .find(|ty| matches!(ty.kind, nera::VirMemoryTypeKind::Enum { .. }))
        .unwrap();
    let nera::VirMemoryTypeKind::Enum { variants } = &enum_type.kind else {
        unreachable!()
    };
    let owner = memory.access(enum_type.id).unwrap();
    let projections: Vec<_> = variants
        .iter()
        .map(|variant| {
            memory
                .field_subobject(owner, memory.variant(*variant).unwrap().fields[0])
                .unwrap()
        })
        .collect();
    assert_eq!(projections[0].offset_bytes(), projections[1].offset_bytes());
    assert_ne!(projections[0].domain_path(), projections[1].domain_path());
    assert!(
        memory
            .subobject(owner, &[Path::Variant(variants[0])])
            .is_none()
    );
    assert!(
        memory
            .subobject(
                owner,
                &[
                    Path::Variant(variants[0]),
                    Path::Field(memory.variant(variants[1]).unwrap().fields[0])
                ]
            )
            .is_none()
    );
    assert!(
        memory
            .leaf_subobject(
                owner,
                projections[0].access(),
                projections[0].offset_bytes()
            )
            .is_none(),
        "ABI leaf offset alone must not choose an active variant"
    );
    assert!(!unit.provenance_catalog().entries().is_empty());
    // Exercise the legacy ABI encoding itself, not just the layout helper.
    // This instruction forms an address only; no active variant is asserted.
    let mut raw = unit.as_unit().clone();
    let (base, span) = raw.runtime.functions[0].blocks[0]
        .instructions
        .iter()
        .find_map(|i| {
            if let VirInstruction::LocalStorage {
                pointer_result,
                access,
                ..
            } = i.instruction
            {
                (access == owner).then_some((pointer_result.id, i.source_span))
            } else {
                None
            }
        })
        .unwrap();
    let result = nera::VirValueId::new(9999);
    raw.runtime.functions[0].blocks[0]
        .instructions
        .push(nera::SpannedVirInstruction {
            source_span: span,
            instruction: VirInstruction::ObjectLeafAddress {
                result: nera::VirValue {
                    id: result,
                    ty: nera::VirType::Pointer {
                        access: projections[0].access(),
                    },
                },
                base,
                owner,
                leaf: projections[0].access(),
                offset_bytes: projections[0].offset_bytes(),
            },
        });
    raw.rebuild_source_map_from_runtime("ambiguous-leaf.nera", source.len());
    raw.rebuild_implicit_contracts_from_runtime();
    let rebuilt = raw.into_validated().unwrap();
    let catalog = rebuilt.provenance_catalog();
    let key = nera::VirPointerKey {
        function: nera::VirFunctionId::new(0),
        value: result,
    };
    assert!(matches!(
        catalog.entries()[&key].source,
        VirPointerSource::Derived {
            step: VirAddressStep::UnresolvedLeaf { .. },
            ..
        }
    ));
}

#[test]
fn formal_and_cfg_roots_are_scoped_symbols_not_non_aliasing_allocations() {
    let source = "fn main() -> u64 { let a = [21, 21]; return read(&a[0], &a[0]); }
      fn read(a: &u64, b: &u64) -> u64 { return *a + *b; }";
    frontend_checks::checked("symbolic-provenance.nera", source, 42);
    let output = frontend_checks::accepted("symbolic-provenance.nera", source);
    let catalog = output.vir().unwrap().provenance_catalog();
    let parameters: Vec<_> = catalog
        .entries()
        .iter()
        .filter(|(_, d)| {
            matches!(
                d.source,
                VirPointerSource::SymbolicParameter {
                    function_entry: true
                }
            )
        })
        .collect();
    assert_eq!(parameters.len(), 2);
    assert_ne!(parameters[0].0, parameters[1].0);
    assert!(
        parameters
            .iter()
            .all(|(key, _)| key.function == nera::VirFunctionId::new(1))
    );
    // The caller intentionally passed exactly the same storage twice.
    let loop_source = SOURCE.replace(
        "let answer",
        "let mut counter = 0; while counter < 1 { counter = counter + 1; } let answer",
    );
    let output = frontend_checks::accepted("cfg-provenance.nera", &loop_source);
    let catalog = output.vir().unwrap().provenance_catalog();
    assert!(catalog.entries().values().any(|d| matches!(
        d.source,
        VirPointerSource::SymbolicParameter {
            function_entry: false
        }
    )));
}

#[test]
fn describing_an_unproven_access_does_not_grant_permission_or_initialization() {
    let source = SOURCE.replace(
        "owner.inner.values = [1, 20, 22, 4];",
        "owner.inner.values[0] = 1;",
    );
    let output = frontend_checks::accepted("uninitialized-subobject.nera", &source);
    let unit = output.vir().unwrap();
    let resolved = unit.resolve().unwrap();
    let before = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!before.is_memory_checked_core0());
    let catalog = unit.provenance_catalog();
    assert!(!catalog.entries().is_empty());
    assert_eq!(
        before,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
}

#[test]
fn huge_arrays_and_invalid_path_depth_do_not_expand_an_element_table() {
    let mut memory = address_program::schema();
    let nera::VirMemoryTypeKind::Array { length, .. } = &mut memory.types[1].kind else {
        panic!()
    };
    *length = 1_000_000;
    memory.layouts[1].size_bytes = 8_000_000;
    memory.layouts[2].size_bytes = 8_000_008;
    memory.validate().unwrap();
    let object = memory
        .subobject(
            address_program::RECORD_ACCESS,
            &[Path::Field(VirFieldId::new(0)), Path::ArrayElement(999_999)],
        )
        .unwrap();
    assert_eq!(object.offset_bytes(), 8_000_000);
    assert_eq!(object.domain_size_bytes(), 8_000_000);
    let path = vec![Path::ArrayElement(0); nera::VIR_OBJECT_SHAPE_MAX_DEPTH + 1];
    assert!(
        memory
            .subobject(address_program::ARRAY_ACCESS, &path)
            .is_none()
    );
    // Stronger array alignment is already a valid MemorySchema layout. Its
    // storage extent includes tail padding, its element arithmetic does not.
    let mut memory = address_program::schema();
    let nera::VirMemoryTypeKind::Array { length, .. } = &mut memory.types[1].kind else {
        unreachable!()
    };
    *length = 3;
    memory.layouts[1].alignment = 32;
    memory.layouts[2].alignment = 32;
    memory.layouts[2].size_bytes = 64;
    memory.layouts[2].fields[0].offset_bytes = 32;
    memory.validate().unwrap();
    let sequence = memory
        .sequence(
            address_program::ARRAY_ACCESS,
            nera::VirIndexBounds::Array { length: 3 },
        )
        .unwrap();
    assert_eq!(
        sequence.extent(),
        VirSequenceExtent::Array {
            length: 3,
            size_bytes: 24
        }
    );
    let object = memory
        .subobject(
            address_program::RECORD_ACCESS,
            &[Path::Field(VirFieldId::new(0)), Path::ArrayElement(2)],
        )
        .unwrap();
    assert_eq!(object.offset_bytes(), 48);
    assert_eq!(object.domain_offset_bytes(), 32);
    assert_eq!(object.domain_size_bytes(), 24);
}
