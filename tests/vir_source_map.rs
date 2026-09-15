use nera::{
    ByteSpan, SourceFile, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId,
    VirConstant, VirContractId, VirFunction, VirFunctionId, VirGeneratedReason, VirInstruction,
    VirLocation, VirLocationOrigin, VirMemorySchema, VirOrigin, VirOriginId, VirOriginKind,
    VirSignature, VirSource, VirSourceId, VirSourceMap, VirSourceMapErrorKind, VirSpecBinder,
    VirSpecBinderId, VirSpecBinderOwner, VirSpecClauseId, VirSpecEnvironment, VirSpecTables,
    VirSpecType, VirTerminator, VirType, VirUnit, VirUnitVersion, VirValidationErrorKind, VirValue,
    VirValueId, analyze,
};

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(start, end).expect("valid test span")
}

fn accepted(name: &str, source: &[u8]) -> nera::ValidatedVirUnit {
    analyze(&SourceFile::new(name, source))
        .vir()
        .unwrap_or_else(|| panic!("{name} must lower to validated VIR"))
        .clone()
}

fn simple_unit() -> VirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "source_map".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions: vec![SpannedVirInstruction {
                    instruction: VirInstruction::Constant {
                        result: VirValue {
                            id: VirValueId::new(0),
                            ty: VirType::U64,
                        },
                        value: VirConstant::U64(1),
                    },
                    source_span: span(2, 3),
                }],
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![VirValueId::new(0)],
                    },
                    source_span: span(10, 11),
                },
                source_span: span(0, 20),
            }],
            source_span: span(0, 20),
        }],
    )
}

fn replace_tables(
    unit: &mut VirUnit,
    sources: Vec<VirSource>,
    origins: Vec<nera::VirOrigin>,
    locations: Vec<VirLocationOrigin>,
) {
    unit.source_map = VirSourceMap::from_tables(sources, origins, locations);
}

fn assert_source_error(unit: &VirUnit, expected: VirSourceMapErrorKind) {
    assert_eq!(
        unit.validate()
            .expect_err("malformed source map must fail closed")
            .kind(),
        &VirValidationErrorKind::InvalidSourceMap(expected)
    );
}

#[test]
fn lowering_registers_every_runtime_location_and_generated_origin() {
    let for_source = include_bytes!("../spec/cases/control-flow/for-range.nera");
    let program = accepted("for-range.nera", for_source);
    let unit = program.as_unit();
    let source_map = &unit.source_map;

    assert_eq!(
        source_map.sources(),
        &[VirSource {
            id: VirSourceId::new(0),
            name: "for-range.nera".to_owned(),
            byte_len: for_source.len(),
        }]
    );

    let expected_locations = unit
        .runtime
        .functions
        .iter()
        .map(|function| {
            1 + function
                .blocks
                .iter()
                .map(|block| {
                    2 + block.parameters.len()
                        + block.instructions.len()
                        + block
                            .instructions
                            .iter()
                            .filter(|instruction| {
                                matches!(instruction.instruction, VirInstruction::Call { .. })
                            })
                            .count()
                })
                .sum::<usize>()
        })
        .sum::<usize>();
    assert_eq!(source_map.locations().len(), expected_locations);

    for reason in [
        VirGeneratedReason::ControlFlowBlock,
        VirGeneratedReason::BlockParameter,
        VirGeneratedReason::ControlFlowEdge,
        VirGeneratedReason::LoopIncrement,
    ] {
        assert!(
            source_map.origins().iter().any(|origin| {
                matches!(
                    origin.kind,
                    VirOriginKind::Generated {
                        reason: found,
                        ..
                    } if found == reason
                )
            }),
            "missing generated origin {reason:?}"
        );
    }

    for entry in source_map.locations() {
        let resolved = source_map
            .source_span(entry.location)
            .expect("every registered location resolves to source");
        assert_eq!(resolved.source, VirSourceId::new(0));
        assert!(resolved.span.end() <= for_source.len());
    }
}

#[test]
fn entry_permissions_and_calls_have_distinct_stable_locations() {
    let source = include_bytes!("../spec/cases/control-flow/owned-call.nera");
    let program = accepted("owned-call.nera", source);
    let unit = program.as_unit();
    let identity = &unit.runtime.functions[1];
    let permission_location = VirLocation::BlockParameter {
        function: identity.id,
        block: identity.entry,
        ordinal: 1,
    };
    assert!(matches!(
        unit.source_map
            .origin_at(permission_location)
            .map(|origin| &origin.kind),
        Some(VirOriginKind::Generated {
            reason: VirGeneratedReason::PermissionParameter,
            ..
        })
    ));

    let caller = &unit.runtime.functions[0];
    let (block, ordinal, call_span) = caller
        .blocks
        .iter()
        .find_map(|block| {
            block
                .instructions
                .iter()
                .enumerate()
                .find(|(_, instruction)| {
                    matches!(instruction.instruction, VirInstruction::Call { .. })
                })
                .map(|(ordinal, instruction)| (block.id, ordinal as u64, instruction.source_span))
        })
        .expect("owned-call contains a direct call");
    let instruction = VirLocation::Instruction {
        function: caller.id,
        block,
        ordinal,
    };
    let call_edge = VirLocation::CallEdge {
        function: caller.id,
        block,
        instruction: ordinal,
    };
    assert_ne!(instruction, call_edge);
    assert_eq!(
        unit.source_map.source_span(instruction).unwrap().span,
        call_span
    );
    assert_eq!(
        unit.source_map.source_span(call_edge).unwrap().span,
        call_span
    );
}

#[test]
fn full_dump_tracks_source_identity_while_runtime_dump_does_not() {
    let source = b"fn main() -> u64 { return 1; }";
    let first = accepted("first.nera", source);
    let replay = accepted("first.nera", source);
    let renamed = accepted("renamed.nera", source);

    assert_eq!(first.as_unit().source_map, replay.as_unit().source_map);
    assert_eq!(first.stable_dump(), replay.stable_dump());
    assert_eq!(
        first.runtime().stable_dump(),
        renamed.runtime().stable_dump()
    );
    assert_ne!(first.stable_dump(), renamed.stable_dump());
}

#[test]
fn current_units_retain_v2_temporary_origins_and_v1_rejects_them() {
    let program = accepted(
        "surface.nera",
        include_bytes!("../spec/cases/aggregate/surface.nera"),
    );
    assert_eq!(program.as_unit().version, VirUnitVersion::V28);
    let temporary = program
        .as_unit()
        .source_map
        .origins()
        .iter()
        .find(|origin| {
            matches!(
                origin.kind,
                VirOriginKind::Generated {
                    reason: VirGeneratedReason::TemporaryStorage,
                    ..
                }
            )
        })
        .expect("aggregate lowering emits temporary storage origins");
    assert!(program.stable_dump().contains("temporary-storage"));

    let mut legacy = program.as_unit().clone();
    legacy.version = VirUnitVersion::V1;
    assert!(matches!(
        legacy.validate().unwrap_err().kind(),
        VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V1)
    ));

    let mut wrong_category = program.as_unit().clone();
    let location = wrong_category
        .source_map
        .locations()
        .iter()
        .find(|entry| entry.origin == temporary.id)
        .map(|entry| entry.location)
        .expect("temporary origin owns a runtime location");
    let sources = wrong_category.source_map.sources().to_vec();
    let mut origins = wrong_category.source_map.origins().to_vec();
    let parent = match origins[temporary.id.get() as usize].kind {
        VirOriginKind::Generated { parent, .. } => parent,
        VirOriginKind::User { .. } => unreachable!(),
    };
    origins[temporary.id.get() as usize].kind = VirOriginKind::Generated {
        parent,
        reason: VirGeneratedReason::ImplicitDrop,
    };
    let locations = wrong_category.source_map.locations().to_vec();
    replace_tables(&mut wrong_category, sources, origins, locations);
    assert_source_error(
        &wrong_category,
        VirSourceMapErrorKind::GeneratedReasonMismatch {
            location,
            reason: VirGeneratedReason::ImplicitDrop,
        },
    );
}

#[test]
fn v2_generated_reasons_cannot_be_smuggled_in_as_spec_only_origins() {
    let mut unit = simple_unit();
    let sources = unit.source_map.sources().to_vec();
    let mut origins = unit.source_map.origins().to_vec();
    let locations = unit.source_map.locations().to_vec();
    let generated = VirOriginId::new(origins.len() as u32);
    origins.push(VirOrigin {
        id: generated,
        kind: VirOriginKind::Generated {
            parent: VirOriginId::new(0),
            reason: VirGeneratedReason::ImplicitDrop,
        },
    });
    replace_tables(&mut unit, sources, origins, locations);
    unit.specs = VirSpecEnvironment::from_tables(VirSpecTables {
        contracts: unit.specs.contracts().to_vec(),
        binders: vec![VirSpecBinder {
            id: VirSpecBinderId::new(0),
            owner: VirSpecBinderOwner::Clause(VirSpecClauseId::new(0)),
            name: "forged".to_owned(),
            ty: VirSpecType::Bool,
            origin: generated,
        }],
        ..VirSpecTables::default()
    });

    assert_source_error(
        &unit,
        VirSourceMapErrorKind::GeneratedReasonWithoutRuntimeLocation {
            origin: generated,
            reason: VirGeneratedReason::ImplicitDrop,
        },
    );
}

#[test]
fn validator_rejects_location_coverage_order_and_dangling_origin_mutations() {
    let base = simple_unit();
    base.validate().expect("baseline source map validates");

    let mut missing = base.clone();
    let sources = missing.source_map.sources().to_vec();
    let origins = missing.source_map.origins().to_vec();
    let mut locations = missing.source_map.locations().to_vec();
    let removed = locations.remove(2).location;
    replace_tables(&mut missing, sources, origins, locations);
    assert_source_error(&missing, VirSourceMapErrorKind::MissingLocation(removed));

    let mut duplicate = base.clone();
    let sources = duplicate.source_map.sources().to_vec();
    let origins = duplicate.source_map.origins().to_vec();
    let mut locations = duplicate.source_map.locations().to_vec();
    locations.insert(1, locations[0]);
    replace_tables(&mut duplicate, sources, origins, locations);
    assert_source_error(
        &duplicate,
        VirSourceMapErrorKind::DuplicateLocation(duplicate.source_map.locations()[0].location),
    );

    let mut unordered = base.clone();
    let sources = unordered.source_map.sources().to_vec();
    let origins = unordered.source_map.origins().to_vec();
    let mut locations = unordered.source_map.locations().to_vec();
    locations.swap(0, 1);
    replace_tables(&mut unordered, sources, origins, locations);
    assert_source_error(&unordered, VirSourceMapErrorKind::NonCanonicalLocationOrder);

    let mut dangling = base;
    let sources = dangling.source_map.sources().to_vec();
    let origins = dangling.source_map.origins().to_vec();
    let mut locations = dangling.source_map.locations().to_vec();
    locations[0].origin = VirOriginId::new(99);
    replace_tables(&mut dangling, sources, origins, locations);
    assert_source_error(
        &dangling,
        VirSourceMapErrorKind::UnknownOrigin(VirOriginId::new(99)),
    );
}

#[test]
fn validator_rejects_source_bounds_cache_and_unused_table_entries() {
    let base = simple_unit();

    let mut unordered_origins = base.clone();
    let sources = unordered_origins.source_map.sources().to_vec();
    let mut origins = unordered_origins.source_map.origins().to_vec();
    let first = origins[1].kind.clone();
    origins[1].kind = origins[2].kind.clone();
    origins[2].kind = first;
    let locations = unordered_origins.source_map.locations().to_vec();
    replace_tables(&mut unordered_origins, sources, origins, locations);
    assert_source_error(
        &unordered_origins,
        VirSourceMapErrorKind::NonCanonicalOriginOrder,
    );

    let mut outside = base.clone();
    let mut sources = outside.source_map.sources().to_vec();
    sources[0].byte_len = 19;
    let origins = outside.source_map.origins().to_vec();
    let locations = outside.source_map.locations().to_vec();
    replace_tables(&mut outside, sources, origins, locations);
    assert_source_error(
        &outside,
        VirSourceMapErrorKind::SpanOutsideSource {
            source: VirSourceId::new(0),
            span: span(0, 20),
            source_len: 19,
        },
    );

    let mut stale_cache = base.clone();
    let sources = stale_cache.source_map.sources().to_vec();
    let mut origins = stale_cache.source_map.origins().to_vec();
    let instruction_origin = stale_cache
        .source_map
        .locations()
        .iter()
        .find(|entry| matches!(entry.location, VirLocation::Instruction { .. }))
        .expect("instruction location")
        .origin;
    origins[instruction_origin.get() as usize].kind = VirOriginKind::User {
        source: VirSourceId::new(0),
        span: span(3, 4),
    };
    let locations = stale_cache.source_map.locations().to_vec();
    replace_tables(&mut stale_cache, sources, origins, locations);
    assert_source_error(
        &stale_cache,
        VirSourceMapErrorKind::LocationSpanMismatch {
            location: VirLocation::Instruction {
                function: VirFunctionId::new(0),
                block: VirBlockId::new(0),
                ordinal: 0,
            },
            expected: span(2, 3),
            found: span(3, 4),
        },
    );

    let mut unused = base;
    let mut sources = unused.source_map.sources().to_vec();
    sources.push(VirSource {
        id: VirSourceId::new(1),
        name: "unused.nera".to_owned(),
        byte_len: 0,
    });
    let origins = unused.source_map.origins().to_vec();
    let locations = unused.source_map.locations().to_vec();
    replace_tables(&mut unused, sources, origins, locations);
    assert_source_error(
        &unused,
        VirSourceMapErrorKind::UnusedSource(VirSourceId::new(1)),
    );
}

#[test]
fn validator_rejects_generated_cycles_empty_parents_and_wrong_categories() {
    let program = accepted(
        "generated.nera",
        include_bytes!("../spec/cases/control-flow/for-range.nera"),
    );
    let base = program.as_unit();
    let generated = base
        .source_map
        .origins()
        .iter()
        .find(|origin| {
            matches!(
                origin.kind,
                VirOriginKind::Generated {
                    reason: VirGeneratedReason::ControlFlowBlock,
                    ..
                }
            )
        })
        .expect("for lowering creates generated blocks");
    let generated_id = generated.id;

    let mut cycle = base.clone();
    let sources = cycle.source_map.sources().to_vec();
    let mut origins = cycle.source_map.origins().to_vec();
    let reason = match origins[generated_id.get() as usize].kind {
        VirOriginKind::Generated { reason, .. } => reason,
        VirOriginKind::User { .. } => unreachable!(),
    };
    origins[generated_id.get() as usize].kind = VirOriginKind::Generated {
        parent: generated_id,
        reason,
    };
    let locations = cycle.source_map.locations().to_vec();
    replace_tables(&mut cycle, sources, origins, locations);
    assert_source_error(
        &cycle,
        VirSourceMapErrorKind::GeneratedParentNotEarlier {
            origin: generated_id,
            parent: generated_id,
        },
    );

    let mut empty_parent = base.clone();
    let sources = empty_parent.source_map.sources().to_vec();
    let mut origins = empty_parent.source_map.origins().to_vec();
    let parent = match origins[generated_id.get() as usize].kind {
        VirOriginKind::Generated { parent, .. } => parent,
        VirOriginKind::User { .. } => unreachable!(),
    };
    let parent_span = match origins[parent.get() as usize].kind {
        VirOriginKind::User { span, .. } => span,
        VirOriginKind::Generated { .. } => unreachable!(),
    };
    origins[parent.get() as usize].kind = VirOriginKind::User {
        source: VirSourceId::new(0),
        span: span(parent_span.start(), parent_span.start()),
    };
    let locations = empty_parent.source_map.locations().to_vec();
    replace_tables(&mut empty_parent, sources, origins, locations);
    assert_source_error(
        &empty_parent,
        VirSourceMapErrorKind::GeneratedFromEmptySpan(generated_id),
    );

    let mut wrong_category = base.clone();
    let sources = wrong_category.source_map.sources().to_vec();
    let origins = wrong_category.source_map.origins().to_vec();
    let (location_index, location, parent) = wrong_category
        .source_map
        .locations()
        .iter()
        .enumerate()
        .find_map(
            |(index, entry)| match origins[entry.origin.get() as usize].kind {
                VirOriginKind::Generated {
                    parent,
                    reason: VirGeneratedReason::ControlFlowBlock,
                } if origins.iter().any(|origin| {
                    matches!(
                        origin.kind,
                        VirOriginKind::Generated {
                            parent: candidate,
                            reason: VirGeneratedReason::BlockParameter,
                        } if candidate == parent
                    )
                }) =>
                {
                    Some((index, entry.location, parent))
                }
                _ => None,
            },
        )
        .expect("generated block and parameters share a parent");
    let block_parameter_origin = origins
        .iter()
        .find(|origin| {
            matches!(
                origin.kind,
                VirOriginKind::Generated {
                    parent: candidate,
                    reason: VirGeneratedReason::BlockParameter,
                } if candidate == parent
            )
        })
        .expect("matching generated parameter origin")
        .id;
    let mut locations = wrong_category.source_map.locations().to_vec();
    locations[location_index].origin = block_parameter_origin;
    replace_tables(&mut wrong_category, sources, origins, locations);
    assert_source_error(
        &wrong_category,
        VirSourceMapErrorKind::GeneratedReasonMismatch {
            location,
            reason: VirGeneratedReason::BlockParameter,
        },
    );

    let mut forged_user = base.clone();
    let sources = forged_user.source_map.sources().to_vec();
    let origins = forged_user.source_map.origins().to_vec();
    let mut locations = forged_user.source_map.locations().to_vec();
    let (location_index, location, parent) = locations
        .iter()
        .enumerate()
        .find_map(
            |(index, entry)| match origins[entry.origin.get() as usize].kind {
                VirOriginKind::Generated {
                    parent,
                    reason: VirGeneratedReason::ControlFlowBlock,
                } => Some((index, entry.location, parent)),
                _ => None,
            },
        )
        .expect("generated block location");
    locations[location_index].origin = parent;
    replace_tables(&mut forged_user, sources, origins, locations);
    assert_source_error(
        &forged_user,
        VirSourceMapErrorKind::ExpectedGeneratedOrigin {
            location,
            reason: VirGeneratedReason::ControlFlowBlock,
        },
    );
}
