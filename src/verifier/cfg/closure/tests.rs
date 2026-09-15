use super::*;
use crate::{SourceFile, analyze};

const RELEASE: &str = "fn main()->u64 {
    let memory=alloc<u64>(1); let mut i=0;
    while i<2 {if i==0 {free(memory);} i=i+1;} return i;
}";

fn recheck(
    source: &str,
    mutate: impl FnOnce(&mut FunctionCfgAnalysis),
) -> Result<(), CfgAnalysisError> {
    let output = analyze(&SourceFile::from_text("closure.nera", source));
    let program = output.vir().unwrap().resolve().unwrap();
    let function = &program.runtime().functions[0];
    // Disable candidate selection to test the actual partition fixpoint. Explicit
    // invariants are still active and receive a fresh frame in the replay.
    let config = CfgAnalysisConfig {
        max_loop_candidates: 0,
        max_loop_partition_cuts: 0,
        ..Default::default()
    };
    let mut result = analyze_function_cfg_with_config(&program, function.id, config).unwrap();
    assert!(result.all_obligations_proven());
    assert!(result.closure_audited());
    mutate(&mut result);
    let blocks = function.blocks.iter().map(|b| (b.id, b)).collect();
    let sites = assign_instruction_sites(&blocks)?;
    let sources = super::super::super::relation::audit::SourceIndex::new(&program, function);
    let journal = std::cell::RefCell::new(result.summary_events.clone());
    let anchors =
        loops::Induction::new(&program, function, config, &BTreeSet::new(), None)?.anchors();
    let context = BlockEvaluationContext {
        loop_blocks: &result.loop_blocks,
        scalar_anchors: &anchors,
        summary_context: super::super::super::summary::SummaryTransferContext {
            site: None,
            case_ordinal: 0,
            audit_limit: config.max_summary_evidence,
            registry: None,
            journal: &journal,
            limit: config.max_relation_evidence,
        },
        program: &program,
        function,
        blocks: &blocks,
        contracts: None,
        relation_sources: &sources,
        instruction_sites: &sites,
        loan_limits: config.loan_limits(),
        config,
    };
    let mut obligations = BTreeMap::<_, Vec<_>>::new();
    for o in &result.obligations {
        obligations.entry(o.block()).or_default().push(*o);
    }
    let mut returns = BTreeMap::<_, Vec<_>>::new();
    for r in &result.returns {
        returns.entry(r.block()).or_default().push(r.clone());
    }
    audit(
        context,
        &BTreeSet::new(),
        &ConditionalResourceState::singleton(result.function_entry_state.clone()),
        &result.blocks,
        &result.refined_blocks,
        &obligations,
        &returns,
    )
}

#[test]
fn frozen_replay_rejects_missing_phase_exit_return_and_obligations() {
    recheck(RELEASE, |_| {}).unwrap();
    for mutation in 0..5 {
        let result = recheck(RELEASE, |cfg| match mutation {
            0 => {
                let block = cfg
                    .blocks
                    .values_mut()
                    .find(|b| b.loop_block && b.entry_conditional_state.cases().len() > 1)
                    .unwrap();
                block.entry_conditional_state = ConditionalResourceState::singleton(
                    block.entry_conditional_state.cases()[0].clone(),
                );
            }
            1 => {
                let id = cfg.returns[0].block;
                cfg.blocks.get_mut(&id).unwrap().entry_conditional_state =
                    ConditionalResourceState::unreachable();
            }
            2 => cfg.returns.clear(),
            3 => cfg.obligations.clear(),
            4 => {
                cfg.blocks.pop_last();
            }
            _ => unreachable!(),
        });
        assert!(
            matches!(result, Err(CfgAnalysisError::ClosureAuditFailed { .. })),
            "{mutation}: {result:?}"
        );
    }
}

#[test]
fn explicit_cut_obligations_are_regenerated_not_trusted() {
    let source = "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+1;} return i;}";
    recheck(source, |_| {}).unwrap();
    assert!(
        recheck(source, |cfg| {
            cfg.obligations.retain(|o| {
                !matches!(
                    o.obligation().kind(),
                    ResourceObligationKind::LoopInvariantEstablished {
                        back_edge: true,
                        ..
                    }
                )
            });
        })
        .is_err()
    );
}

#[test]
fn conditional_observations_remain_subject_to_backedge_replay() {
    let source = "fn main()->u64 {let p=alloc<u64>(1); let mut i=0; while i<3 {
        invariant i!=0 || alive(p.region); if i==0 {free(p);} i=i+1;} return i;}";
    recheck(source, |_| {}).unwrap();
    assert!(
        recheck(source, |cfg| cfg.obligations.retain(|o| !matches!(
            o.obligation().kind(),
            ResourceObligationKind::LoopInvariantEstablished {
                back_edge: true,
                ..
            }
        )))
        .is_err()
    );
}

#[test]
fn all_proven_obligations_without_closure_are_not_success() {
    recheck(RELEASE, |cfg| {
        cfg.closure_audited = false;
        assert!(!cfg.all_obligations_proven());
    })
    .unwrap();
}

#[test]
fn coverage_cannot_revive_permission_or_reuse_old_scalar_and_drop_flag() {
    use crate::verifier::resource::*;
    let id = VirValueId::new;
    let mut live = ResourceState::new();
    let allocation = AbstractAllocationId::new(0);
    live.define_allocation(
        allocation,
        AbstractAllocation::new(crate::VirRegionId::new(0), 8, 8).unwrap(),
    )
    .unwrap();
    let mut permission = AbstractPermission::new(
        AbstractProvenance::Known(allocation),
        AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
        AccessPermission::Write,
        FreeCapability::Yes,
    );
    live.define_value(id(0), AbstractValue::Permission(permission))
        .unwrap();
    live.define_value(id(1), AbstractValue::U64(U64Interval::exact(0)))
        .unwrap();
    live.define_value(id(2), AbstractValue::Bool(AbstractBool::True))
        .unwrap();
    let mut dead = live.clone();
    dead.allocation_mut(allocation).unwrap().mark_dead();
    permission.mark_consumed();
    *dead.value_mut(id(0)).unwrap() = AbstractValue::Permission(permission);
    *dead.value_mut(id(1)).unwrap() = AbstractValue::U64(U64Interval::exact(1));
    *dead.value_mut(id(2)).unwrap() = AbstractValue::Bool(AbstractBool::False);
    assert!(live.covers_cfg_case(&live));
    assert!(dead.covers_cfg_case(&dead));
    assert!(!live.covers_cfg_case(&dead));
    assert!(!dead.covers_cfg_case(&live));
    for field in [1, 2] {
        let mut stale = dead.clone();
        *stale.value_mut(id(field)).unwrap() = *live.value(id(field)).unwrap();
        assert!(!stale.covers_cfg_case(&dead));
    }
    let mut stale = dead.clone();
    *stale.value_mut(id(0)).unwrap() = *live.value(id(0)).unwrap();
    assert!(!stale.covers_cfg_case(&dead));
}
