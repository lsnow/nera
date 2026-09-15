use nera::*;

fn inspect(source: &str) -> (FrontendOutput, ProgramVerification) {
    let out = analyze(&SourceFile::from_text("loop-control.nera", source));
    assert_eq!(
        out.status(),
        FrontendStatus::AcceptedProposal,
        "{source}: {:?}",
        out.issues()
    );
    let report =
        verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default()).unwrap();
    (out, report)
}

fn checked(source: &str, answer: u64) {
    let (out, report) = inspect(source);
    assert!(
        report.is_memory_checked_core0(),
        "{source}: {:?}",
        report
            .diagnostics()
            .iter()
            .map(|d| d.message())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        interpret(out.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(answer)]
    );
}

#[test]
fn for_checks_actual_increment_after_every_continue() {
    checked(
        "fn main()->u64 {let p=alloc<[u64;4]>(1);
        for i in 0usize..4usize {invariant i<=4usize; invariant initialized(p,0usize..i);
            p[i]=42; if i==0usize {continue;} if i==2usize {continue;}
        } let v=p[3]; free(p); return v;}",
        42,
    );
    let (_, report) = inspect(
        "fn main(){let p=alloc<[u64;4]>(1);
        for i in 0usize..4usize {invariant i<=4usize; invariant initialized(p,0usize..i);
            if i==2usize {continue;} p[i]=42;
        } free(p); return;}",
    );
    assert!(!report.is_memory_checked_core0());
}

#[test]
fn nested_loops_have_separate_entry_backedge_and_scalar_frames() {
    checked(
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3;
        let mut j=0; while j<4 {invariant j<=4; j=j+1;} assert j==4; if j!=4 {return 99;} i=i+1;
    } assert i==3; return i;}",
        3,
    );
    checked(
        "fn main()->u64 {for i in 0..3 {invariant i<=3;
        for j in 0..4 {invariant j<=4; if j==1 {continue;} if i==2 {break;}}
    } return 42;}",
        42,
    );
    let (_, report) = inspect(
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3;
        let mut j=0; while j<2 {invariant j<=2; if j==1 {i=i+1;} j=j+1;}
        assert i==0; if i!=0 {return i;} i=i+1;
    } return i;}",
    );
    assert!(
        !report.is_memory_checked_core0(),
        "a phi that changes the outer counter must not inherit its entry value"
    );
}

#[test]
fn exits_use_actual_partial_initialization_and_cleanup_state() {
    checked(
        "fn main()->u64 {let p=alloc<[u64;4]>(1); let mut i=0usize;
        while i<4usize {invariant i<=4usize; invariant initialized(p,0usize..i);
            p[i]=42; if i==1usize {free(p); return 42;} i=i+1usize;
        } free(p); return 0;}",
        42,
    );
    checked(
        "fn main()->u64 {let p=alloc<[u64;4]>(1);
        for i in 0usize..4usize {invariant initialized(p,0usize..i); invariant i<=4usize;
            p[i]=42; break;
        } free(p); return 42;}",
        42,
    );
    for body in ["break;", "continue;"] {
        let source = format!("fn main()->u64 {{let p=alloc<[u64;4]>(1);
            for i in 0usize..4usize {{invariant i<=4usize; invariant initialized(p,0usize..i); {body}}}
            let v=p[3]; free(p); return v;}}");
        assert!(!inspect(&source).1.is_memory_checked_core0());
    }
}

#[test]
fn scoped_loans_end_on_continue_break_and_return() {
    for tail in ["continue;", "break;", "return *r;"] {
        let source = format!(
            "fn main()->u64 {{let mut x=7;
            for i in 0..3 {{invariant i<=3; let r=&mut x; *r=42; {tail}}}
            return x;}}"
        );
        checked(&source, 42);
    }
    checked(
        "fn main()->u64 {let x=42; for i in 0..3 {invariant i<=3;
        let r=&x; let s=r; let v=*s; let w=*r; if v!=w {return 99;}
    } return x;}",
        42,
    );
}

#[test]
fn raw_loan_cleanup_cannot_be_omitted_or_executed_twice() {
    let (out, report) = inspect(
        "fn main()->u64 {let mut x=7; for i in 0..3 {invariant i<=3;
        let r=&mut x; *r=42; if i==1 {continue;} continue;} return x;}",
    );
    assert!(report.is_memory_checked_core0());
    for duplicate in [false, true] {
        let mut unit = out.vir().unwrap().as_unit().clone();
        let function = VirFunctionId::new(0);
        let (bid, index) = unit.runtime.functions[0]
            .blocks
            .iter()
            .find_map(|b| {
                b.instructions
                    .iter()
                    .position(|i| matches!(i.instruction, VirInstruction::LoanEnd { .. }))
                    .map(|i| (b.id, i))
            })
            .unwrap();
        let block = unit.runtime.functions[0]
            .blocks
            .iter_mut()
            .find(|b| b.id == bid)
            .unwrap();
        let instruction = block.instructions[index].clone();
        let mut locations = unit.source_map.locations().to_vec();
        let mut origins = unit.source_map.origins().to_vec();
        if duplicate {
            let origin = unit
                .source_map
                .origin_at(VirLocation::Instruction {
                    function,
                    block: bid,
                    ordinal: index as u64,
                })
                .unwrap()
                .id;
            let ordinal = block.instructions.len() as u64;
            block.instructions.push(instruction);
            locations.push(VirLocationOrigin {
                location: VirLocation::Instruction {
                    function,
                    block: bid,
                    ordinal,
                },
                origin,
            });
        } else {
            let removed = unit
                .source_map
                .origin_at(VirLocation::Instruction {
                    function,
                    block: bid,
                    ordinal: index as u64,
                })
                .unwrap()
                .id;
            block.instructions.remove(index);
            locations.retain(|l| {
                l.location
                    != VirLocation::Instruction {
                        function,
                        block: bid,
                        ordinal: index as u64,
                    }
            });
            for l in &mut locations {
                if let VirLocation::Instruction {
                    function: f,
                    block: b,
                    ordinal,
                } = &mut l.location
                    && *f == function
                    && *b == bid
                    && *ordinal > index as u64
                {
                    *ordinal -= 1;
                }
            }
            // Removing a generated origin leaves all earlier user/spec origins
            // unchanged. Compact the runtime origin suffix, including effects.
            assert!(matches!(
                origins[removed.get() as usize].kind,
                VirOriginKind::Generated { .. }
            ));
            origins.remove(removed.get() as usize);
            let compact = |id: &mut VirOriginId| {
                assert_ne!(*id, removed);
                if id.get() > removed.get() {
                    *id = VirOriginId::new(id.get() - 1);
                }
            };
            for origin in &mut origins {
                compact(&mut origin.id);
                if let VirOriginKind::Generated { parent, .. } = &mut origin.kind {
                    compact(parent);
                }
            }
            for location in &mut locations {
                compact(&mut location.origin);
            }
            for block in &mut unit.runtime.functions[0].blocks {
                for instruction in &mut block.instructions {
                    match &mut instruction.instruction {
                        VirInstruction::LoanBegin { effect, .. }
                        | VirInstruction::LoanReborrow { effect, .. }
                        | VirInstruction::LoanAliasShared { effect, .. }
                        | VirInstruction::LoanEnd { effect } => compact(&mut effect.origin),
                        VirInstruction::LoanAliasAuthority { effect, .. }
                        | VirInstruction::LoanReborrowAuthority { effect, .. }
                        | VirInstruction::LoanEndAuthority { effect } => {
                            compact(&mut effect.origin)
                        }
                        _ => {}
                    }
                }
            }
        }
        locations.sort_by_key(|l| l.location);
        unit.source_map =
            VirSourceMap::from_tables(unit.source_map.sources().to_vec(), origins, locations);
        let unit = unit.into_validated().unwrap();
        let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
        assert!(!report.is_memory_checked_core0(), "duplicate={duplicate}");
    }
}

#[test]
fn false_inner_invariant_and_bad_early_return_do_not_publish_summary() {
    let (_, report) = inspect(
        "fn main()->u64 {return f();} fn f()->u64 ensures result==42; {
        let mut i=0; while i<3 {invariant i<=3;
            let mut j=0; while j<2 {invariant j==0; j=j+1;}
            i=i+1;
        } return 42;}",
    );
    assert!(!report.is_memory_checked_core0());
    assert!(
        !inspect(
            "fn main()->u64 {return f();} fn f()->u64 ensures result==42; {
        for i in 0..3 {invariant i<=3; return 0;} return 42;}"
        )
        .1
        .is_memory_checked_core0()
    );
}

#[test]
fn nested_audit_keeps_inner_obligations_and_work_is_not_iteration_count() {
    use nera::verifier::{relation::audit::RelationReplayCache, summary::audit::SummaryAudit};
    let source = "fn main()->u64 {return f();} fn f()->u64 ensures result==42; {
        let mut i=0; while i<3 {invariant i<=3; let mut j=0;
            while j<2 {invariant j<=2; j=j+1;} i=i+1;
        } return 42;}";
    let (out, report) = inspect(source);
    assert!(report.is_memory_checked_core0());
    let resolved = out.vir().unwrap().resolve().unwrap();
    let cache = RelationReplayCache::new(&resolved, Default::default()).unwrap();
    let audit = SummaryAudit::from_report(&report);
    assert!(cache.accepts_summary_audit(&audit));
    let mut bad = audit.clone();
    let f = bad
        .functions
        .iter_mut()
        .find(|f| f.function == VirFunctionId::new(1))
        .unwrap();
    let inner = out
        .vir()
        .unwrap()
        .as_unit()
        .specs
        .loop_invariants()
        .iter()
        .min_by_key(|i| i.boundary.as_ref().unwrap().blocks.len())
        .unwrap()
        .clause;
    let index=f.requirements.iter().position(|(_,finding)|matches!(finding.site(),VerifierFindingSite::Spec{entity:VerifierSpecEntity::Clause(id),..} if id==inner)).unwrap();
    f.requirements.remove(index);
    assert!(!cache.accepts_summary_audit(&bad));
    for n in [3, 1_000_000] {
        let source = format!(
            "fn main(){{let mut i=0; while i<{n} {{invariant i<={n};
            let mut j=0; while j<{n} {{invariant j<={n}; j=j+1;}} i=i+1;
        }} return;}}"
        );
        let (out, report) = inspect(&source);
        assert!(report.is_memory_checked_core0());
        let cfg = analyze_function_cfg_with_config(
            &out.vir().unwrap().resolve().unwrap(),
            VirFunctionId::new(0),
            CfgAnalysisConfig {
                max_block_visits: 32,
                ..Default::default()
            },
        )
        .unwrap();
        assert!(cfg.all_obligations_proven());
    }
}

#[test]
fn conditions_use_transfer_and_unannotated_inner_cycles_remain_gated() {
    checked(
        "fn main()->u64 {let p=alloc<u64>(1); *p=0;
        while *p<3 {invariant initialized(p); *p=*p+1;} free(p); return 42;}",
        42,
    );
    assert!(
        !inspect(
            "fn main()->u64 {let p=alloc<u64>(1);
        while *p<3 {invariant initialized(p); *p=*p+1;} free(p); return 42;}"
        )
        .1
        .is_memory_checked_core0()
    );
    checked(
        "fn main()->u64 {while test() {invariant true; break;} return 42;} fn test()->bool{return true;}",
        42,
    );
    // Acyclic inner regions need no induction hypothesis.
    checked(
        "fn main()->u64 {while true {invariant true; while true {break;} break;} return 42;}",
        42,
    );
    let out = analyze(&SourceFile::from_text(
        "gated-loop.nera",
        "fn main(){while true {invariant true; while true {continue;} break;} return;}",
    ));
    assert_eq!(out.status(), FrontendStatus::Unsupported);
}

#[test]
fn bounds_execute_once_and_zero_iterations_never_initialize_storage() {
    checked(
        "fn main()->u64 {let mut end=4; let mut count=0;
        for i in 0..end {invariant i<=4; invariant count==i; end=0; count=count+1;}
        return count+end;}",
        4,
    );
    checked(
        "fn main()->u64 {for i in 0..bound() {invariant i<=3;} return 42;}
        fn bound()->u64 {return 3;}",
        42,
    );
    checked(
        "fn main()->u64 {let p=alloc<[u64;4]>(1);
        for i in 0usize..0usize {invariant i<=0usize; p[i]=42;} free(p); return 42;}",
        42,
    );
    assert!(
        !inspect(
            "fn main()->u64 {let p=alloc<[u64;4]>(1);
        for i in 0usize..0usize {invariant i<=0usize; p[i]=42;}
        let v=p[0]; free(p); return v;}"
        )
        .1
        .is_memory_checked_core0()
    );
}

#[test]
fn nested_memory_updates_and_each_exit_use_actual_state() {
    checked(
        "fn main()->u64 {let mut values=[0,0,0,0];
        for i in 0usize..3usize {invariant i<=3usize;
            for j in 0usize..4usize {invariant j<=4usize; values[j]=42; if j==1usize {continue;}}
        } return values[3];}",
        42,
    );
    let (_, report) = inspect(
        "fn main(){let p=alloc<u64>(1); *p=0; let mut i=0;
        while i<3 {invariant i<=3; let mut j=0;
            while j<2 {invariant j<=2; *p=j; j=j+1;}
            let value=*p; assert value==0; i=i+1;
        } free(p); return;}",
    );
    assert!(!report.is_memory_checked_core0());
}

#[test]
fn raw_latch_free_cannot_reset_liveness_or_permission_on_next_iteration() {
    let (out, report) = inspect(
        "fn main(){let p=alloc<u64>(1);
        for i in 0..3 {invariant i<=3; *p=i;} free(p); return;}",
    );
    assert!(report.is_memory_checked_core0());
    let mut unit = out.vir().unwrap().as_unit().clone();
    let latch = unit.specs.loop_invariants()[0]
        .boundary
        .as_ref()
        .unwrap()
        .latch
        .unwrap();
    let block = unit.runtime.functions[0]
        .blocks
        .iter_mut()
        .find(|b| b.id == latch)
        .unwrap();
    let pointer = block
        .parameters
        .iter()
        .find(|p| matches!(p.ty, VirType::Pointer { .. }))
        .unwrap()
        .id;
    let permission = block
        .parameters
        .iter()
        .find(|p| p.ty == VirType::Permission)
        .unwrap()
        .id;
    block.instructions.push(SpannedVirInstruction {
        instruction: VirInstruction::Free {
            pointer,
            permission,
        },
        source_span: block.terminator.source_span,
    });
    let ordinal = (block.instructions.len() - 1) as u64;
    let source_span = block.terminator.source_span;
    let mut origins = unit.source_map.origins().to_vec();
    let kind = VirOriginKind::User {
        source: VirSourceId::new(0),
        span: source_span,
    };
    let origin = if let Some(existing) = origins.iter().find(|o| o.kind == kind) {
        existing.id
    } else {
        let id = VirOriginId::new(origins.len() as u32);
        origins.push(VirOrigin { id, kind });
        id
    };
    let mut locations = unit.source_map.locations().to_vec();
    locations.push(VirLocationOrigin {
        location: VirLocation::Instruction {
            function: VirFunctionId::new(0),
            block: latch,
            ordinal,
        },
        origin,
    });
    locations.sort_by_key(|l| l.location);
    unit.source_map =
        VirSourceMap::from_tables(unit.source_map.sources().to_vec(), origins, locations);
    let unit = unit.into_validated().unwrap();
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::LoopResourcesPreserved { .. }
            ) && !o.obligation().is_proven())
    );
}
