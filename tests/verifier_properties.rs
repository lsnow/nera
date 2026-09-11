use nera::{
    AbstractByteRange, AbstractValue, ByteRange, ByteSpan, PermissionAvailability, ResourceState,
    SpannedVirInstruction, U64Interval, VirConstant, VirInstruction, VirRegionId, VirType,
    VirValue, VirValueId, transfer_instruction_sequence,
};

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("valid property-test span")
}

fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn word(id: u32) -> VirValue {
    value(id, VirType::U64)
}

fn pointer(id: u32) -> VirValue {
    value(
        id,
        VirType::Pointer {
            access: nera::VirMemoryAccess::core_u64(),
        },
    )
}

fn permission(id: u32) -> VirValue {
    value(id, VirType::Permission)
}

fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

#[test]
fn every_small_exact_permission_split_rejoins_to_the_original_range() {
    for size in 1_u64..=32 {
        for split in 0..=size {
            let instructions = [
                instruction(VirInstruction::Constant {
                    result: word(0),
                    value: VirConstant::U64(size),
                }),
                instruction(VirInstruction::Allocate {
                    pointer_result: pointer(1),
                    permission_result: permission(2),
                    size_bytes: VirValueId::new(0),
                    alignment: 8,
                    region: VirRegionId::new(0),
                    element: nera::VirMemoryAccess::core_u64(),
                }),
                instruction(VirInstruction::Constant {
                    result: word(3),
                    value: VirConstant::U64(split),
                }),
                instruction(VirInstruction::PermissionSplit {
                    left_result: permission(4),
                    right_result: permission(5),
                    source: VirValueId::new(2),
                    split_at_bytes: VirValueId::new(3),
                }),
                instruction(VirInstruction::PermissionJoin {
                    result: permission(6),
                    left: VirValueId::new(4),
                    right: VirValueId::new(5),
                }),
            ];

            let transfer = transfer_instruction_sequence(&ResourceState::new(), &instructions)
                .expect("small exact split/join transfer");
            assert!(
                transfer.all_obligations_proven(),
                "size={size}, split={split}"
            );
            let Some(AbstractValue::Permission(joined)) =
                transfer.state().value(VirValueId::new(6)).copied()
            else {
                panic!("joined permission missing for size={size}, split={split}")
            };
            assert_eq!(
                joined.range(),
                AbstractByteRange::Exact(ByteRange::new(0, size).unwrap())
            );
            assert_eq!(joined.availability(), PermissionAvailability::Available);
        }
    }
}

#[test]
fn affine_scaling_is_retained_exactly_until_interval_overflow_is_possible() {
    for upper in [0, 1, 7, u64::MAX / 2, u64::MAX / 2 + 1] {
        let mut state = ResourceState::new();
        state
            .define_value(
                VirValueId::new(0),
                AbstractValue::U64(U64Interval::new(0, upper).unwrap()),
            )
            .expect("unique word input");
        let transferred = transfer_instruction_sequence(
            &state,
            &[instruction(VirInstruction::WordAdd {
                result: word(1),
                left: VirValueId::new(0),
                right: VirValueId::new(0),
            })],
        )
        .expect("word addition transfer");

        assert_eq!(
            transferred
                .state()
                .word_expression(VirValueId::new(1))
                .is_some(),
            upper <= u64::MAX / 2,
            "upper={upper}"
        );
    }
}
