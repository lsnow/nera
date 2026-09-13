//! One scalar allocation, real writes/deinitialization/free, with Spec erased.
use nera::*;

pub fn unit() -> VirUnit {
    let span = ByteSpan::new(0, 1).unwrap();
    let id = VirValueId::new;
    let v = |id, ty| VirValue {
        id: VirValueId::new(id),
        ty,
    };
    let access = VirMemoryAccess::core_u64();
    let instructions = vec![
        VirInstruction::Constant {
            result: v(0, VirType::U64),
            value: VirConstant::U64(16),
        },
        VirInstruction::Allocate {
            pointer_result: v(1, VirType::Pointer { access }),
            permission_result: v(2, VirType::Permission),
            size_bytes: id(0),
            alignment: 8,
            region: VirRegionId::new(0),
            element: access,
        },
        VirInstruction::Constant {
            result: v(3, VirType::U64),
            value: VirConstant::U64(42),
        },
        VirInstruction::Initialize {
            pointer: id(1),
            value: id(3),
            permission: id(2),
            access,
        },
        VirInstruction::Constant {
            result: v(4, VirType::U64),
            value: VirConstant::U64(7),
        },
        VirInstruction::Store {
            pointer: id(1),
            value: id(4),
            permission: id(2),
            access,
        },
        VirInstruction::Load {
            result: v(5, VirType::U64),
            pointer: id(1),
            permission: id(2),
            access,
        },
        VirInstruction::ObjectDeinitialize {
            pointer: id(1),
            permission: id(2),
            access,
        },
        VirInstruction::Initialize {
            pointer: id(1),
            value: id(4),
            permission: id(2),
            access,
        },
        VirInstruction::Free {
            pointer: id(1),
            permission: id(2),
        },
    ];
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "main".into(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            source_span: span,
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![],
                instructions: instructions
                    .into_iter()
                    .map(|instruction| SpannedVirInstruction {
                        instruction,
                        source_span: span,
                    })
                    .collect(),
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![id(5)],
                    },
                    source_span: span,
                },
                source_span: span,
            }],
        }],
    )
}

pub fn location(ordinal: u32) -> VirLocation {
    if ordinal == 10 {
        VirLocation::Terminator {
            function: VirFunctionId::new(0),
            block: VirBlockId::new(0),
        }
    } else {
        VirLocation::Instruction {
            function: VirFunctionId::new(0),
            block: VirBlockId::new(0),
            ordinal: ordinal.into(),
        }
    }
}

pub fn add(
    unit: &mut VirUnit,
    location: VirLocation,
    make: impl FnOnce([VirSpecTermId; 3]) -> VirSpecAssertionKind,
) {
    let origin = unit.source_map.origin_at(location).unwrap().id;
    let clause = VirSpecClauseId::new(unit.specs.clauses().len() as u32);
    let prove = VirSpecProveId::new(unit.specs.proves().len() as u32);
    let assertion = VirSpecAssertionId::new(unit.specs.assertions().len() as u32);
    let first = unit.specs.terms().len() as u32;
    let terms = [
        VirSpecTermId::new(first),
        VirSpecTermId::new(first + 1),
        VirSpecTermId::new(first + 2),
    ];
    for (id, value) in terms.into_iter().zip([0, 8, 42]) {
        unit.specs.terms_mut().push(VirSpecTerm {
            id,
            clause,
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::U64(value),
            origin,
        });
    }
    unit.specs.assertions_mut().push(VirSpecAssertion {
        id: assertion,
        clause,
        kind: make(terms),
        origin,
    });
    unit.specs.clauses_mut().push(VirSpecClause {
        id: clause,
        owner: VirSpecClauseOwner::Prove(prove),
        location: VirSpecLocation::Runtime(location),
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Assertion { root: assertion },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: prove,
        function: location.function(),
        location: VirSpecLocation::Runtime(location),
        clause,
        origin,
    });
}

pub fn snapshot(id: u32) -> VirSpecSnapshot {
    VirSpecSnapshot::Value {
        function: VirFunctionId::new(0),
        value: VirValueId::new(id),
    }
}

pub fn claim(
    terms: [VirSpecTermId; 3],
) -> SpecMemoryClaim<VirSpecSnapshot, VirSpecTermId, VirMemoryAccess> {
    SpecMemoryClaim {
        pointer: snapshot(1),
        authority: snapshot(2),
        start_bytes: terms[0],
        end_bytes: terms[1],
        layout: VirMemoryAccess::core_u64(),
        access: SpecAccess::Write,
    }
}

pub fn checked_unit() -> VirUnit {
    let mut unit = unit();
    add(&mut unit, location(2), |t| {
        SpecAssertionKind::Permission(claim(t))
    });
    add(&mut unit, location(6), |t| SpecAssertionKind::PointsTo {
        memory: claim(t),
        value: None,
    });
    unit
}
