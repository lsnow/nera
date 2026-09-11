//! Typed-VIR-only conditional enum resource interface. Surface/target ABI
//! support is deliberately not expanded by this verifier fixture.
use nera::*;

pub fn unit(flag: bool, wrong_tag: bool, missing_payload: bool) -> VirUnit {
    let source = "enum Item { Empty, Full(Own<u64>, u64), }
        fn main()->u64 { return run(true); } fn run(flag:bool)->u64 { return 42; }
        fn make(flag:bool)->u64 { let p=alloc<Item>(1);
        if flag { let q=alloc<u64>(1); *q=42; *p=Item::Full(q,42); }
        else { *p=Item::Empty; } free(p); return 42; }";
    let out = analyze(&SourceFile::from_text("conditional-enum.nera", source));
    let original = out.vir().expect("local enum fixture lowers").as_unit();
    let mut functions = original.runtime.functions.clone();
    let make = functions.iter_mut().find(|f| f.name == "make").unwrap();
    let block = make
        .blocks
        .iter_mut()
        .find(|b| {
            b.instructions
                .iter()
                .any(|i| matches!(i.instruction, VirInstruction::Free { .. }))
        })
        .unwrap();
    let (pointer, permission) = block
        .instructions
        .iter()
        .find_map(|i| match i.instruction {
            VirInstruction::Free {
                pointer,
                permission,
            } => Some((pointer, permission)),
            _ => None,
        })
        .unwrap();
    let drop = block.instructions.iter().position(|i| matches!(i.instruction, VirInstruction::ObjectDrop { pointer: p, .. } if p == pointer)).unwrap();
    let VirInstruction::ObjectDrop { access, .. } = block.instructions[drop].instruction else {
        unreachable!()
    };
    block.instructions.truncate(drop);
    let span = block.source_span;
    let value = |id, ty| VirValue {
        id: VirValueId::new(id),
        ty,
    };
    let tag = value(100000, VirType::U64);
    block.instructions.push(SpannedVirInstruction {
        instruction: VirInstruction::EnumDiscriminant {
            result: tag,
            pointer,
            permission,
            access,
        },
        source_span: span,
    });
    block.terminator.terminator = VirTerminator::Return {
        values: vec![pointer, permission, tag.id],
    };
    make.signature.results = vec![
        VirType::Pointer { access },
        VirType::Permission,
        VirType::U64,
    ];
    let mut reachable = std::collections::BTreeSet::from([make.entry]);
    loop {
        let count = reachable.len();
        for b in &make.blocks {
            if !reachable.contains(&b.id) {
                continue;
            }
            match &b.terminator.terminator {
                VirTerminator::Jump { target } => {
                    reachable.insert(target.block);
                }
                VirTerminator::Branch {
                    then_target,
                    else_target,
                    ..
                } => {
                    reachable.insert(then_target.block);
                    reachable.insert(else_target.block);
                }
                _ => {}
            }
        }
        if reachable.len() == count {
            break;
        }
    }
    make.blocks.retain(|b| reachable.contains(&b.id));
    if missing_payload {
        for b in &mut make.blocks {
            b.instructions
                .retain(|i| !matches!(i.instruction, VirInstruction::ResourceInitialize { .. }));
        }
    }
    let target = VirCallTarget {
        symbol: make.name.clone(),
        signature: make.signature.clone(),
        contract: make.contract,
        abi: None,
    };
    let run = functions.iter_mut().find(|f| f.name == "run").unwrap();
    let input = run.blocks[0].parameters[0].id;
    let (p, q, returned_tag) = (
        value(100, VirType::Pointer { access }),
        value(101, VirType::Permission),
        value(102, VirType::U64),
    );
    let actual_tag = value(103, VirType::U64);
    let condition = value(104, VirType::Bool);
    let yes = value(105, VirType::Bool);
    let result = value(106, VirType::U64);
    run.blocks[0].instructions = vec![
        VirInstruction::Call {
            results: vec![p, q, returned_tag],
            target,
            arguments: vec![input],
        },
        VirInstruction::EnumDiscriminant {
            result: actual_tag,
            pointer: p.id,
            permission: q.id,
            access,
        },
        VirInstruction::Compare {
            result: condition,
            predicate: if wrong_tag {
                VirIntegerPredicate::NotEqual
            } else {
                VirIntegerPredicate::Equal
            },
            left: actual_tag.id,
            right: returned_tag.id,
        },
        VirInstruction::Check {
            condition: condition.id,
        },
        VirInstruction::Constant {
            result: yes,
            value: VirConstant::Bool(true),
        },
        VirInstruction::ObjectDrop {
            pointer: p.id,
            permission: q.id,
            access,
            condition: yes.id,
        },
        VirInstruction::Free {
            pointer: p.id,
            permission: q.id,
        },
        VirInstruction::Constant {
            result,
            value: VirConstant::U64(42),
        },
    ]
    .into_iter()
    .map(|instruction| SpannedVirInstruction {
        instruction,
        source_span: span,
    })
    .collect();
    run.blocks[0].terminator.terminator = VirTerminator::Return {
        values: vec![result.id],
    };
    for function in &mut functions {
        function.source_span = ByteSpan::new(0, 1).unwrap();
        for b in &mut function.blocks {
            b.source_span = function.source_span;
            b.terminator.source_span = function.source_span;
            for i in &mut b.instructions {
                i.source_span = function.source_span;
                if let VirInstruction::Call { target, .. } = &mut i.instruction {
                    target.abi = None;
                }
                if function.name == "main"
                    && let VirInstruction::Constant {
                        value: VirConstant::Bool(v),
                        ..
                    } = &mut i.instruction
                {
                    *v = flag;
                }
            }
        }
    }
    VirUnit::from_runtime(original.memory.clone(), original.runtime.entry, functions)
}
