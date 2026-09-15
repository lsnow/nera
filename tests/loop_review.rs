use nera::*;
#[path = "support/loop_review.rs"]
mod fixture;
#[path = "support/runtime_origins.rs"]
mod runtime_origins;

fn inspect(source: &str) -> FrontendOutput {
    let out = analyze(&SourceFile::from_text("loop-review.nera", source));
    assert!(out.vir().is_some(), "{:?}", out.issues());
    out
}
fn checked(source: &str) -> FrontendOutput {
    let out = inspect(source);
    let report =
        verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    out
}
fn unproved(source: &str) {
    let out = inspect(source);
    assert!(
        !verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default())
            .is_ok_and(|r| r.is_memory_checked_core0())
    );
}

#[test]
fn explicit_automatic_and_carrier_mappings_preserve_runtime() {
    for source in [fixture::MIXED, fixture::FOR_BOUND, fixture::READ_ONLY] {
        let out = checked(source);
        let erased = checked(&fixture::erase_invariants(source));
        assert_eq!(
            runtime_origins::runtime_with_resolved_origins(out.vir().unwrap()),
            runtime_origins::runtime_with_resolved_origins(erased.vir().unwrap())
        );
    }
}

#[test]
fn nested_interfaces_mix_in_both_directions_but_explicit_failures_remain() {
    for clauses in ["invariant i<=3;", ""] {
        let inner = if clauses.is_empty() {
            "invariant j<=2;"
        } else {
            ""
        };
        let source = format!(
            "fn main()->u64 {{let mut i=0; while i<3 {{{clauses}
            let mut j=0; while j<2 {{{inner} j=j+1;}} i=i+1;}} return i;}}"
        );
        checked(&source);
        unproved(
            &source
                .replace("invariant i<=3;", "invariant i==0;")
                .replace("invariant j<=2;", "invariant j==0;"),
        );
    }
}

#[test]
fn non_admitted_sibling_does_not_disable_a_separate_inductive_loop() {
    let source = fixture::MIXED.replace(
        "while j<3 {j=j+1;}",
        "while j<3 {let p=alloc<u64>(1); free(p); j=j+1;}",
    );
    checked(&source);
    checked(&fixture::erase_invariants(&source));
    // The same unsupported cycle *inside* an inductive region is still gated.
    let out = analyze(&SourceFile::from_text(
        "nested-gate.nera",
        "fn main(){let mut i=0; while i<3 {invariant i<=3; while true {continue;} i=i+1;} return;}",
    ));
    assert_eq!(out.status(), FrontendStatus::Unsupported);
}

#[test]
fn mutable_bound_is_not_replaced_by_its_once_evaluated_carrier() {
    let source = "fn main()->u64 {let mut n=3usize; for i in 0usize..n {
        invariant i<=n;
        n=0usize;
    } return 0;}";
    let out = analyze(&SourceFile::from_text("mutable-bound.nera", source));
    if let Some(unit) = out.vir() {
        assert!(
            !verify_program(&unit.resolve().unwrap(), Default::default())
                .is_ok_and(|r| r.is_memory_checked_core0())
        );
    } else {
        assert_eq!(out.status(), FrontendStatus::Unsupported);
    }
}

#[test]
fn only_closed_actual_effects_preserve_the_loop_frame() {
    // False declaration cannot suppress actual writes. Without that declaration,
    // the callee closes but the caller must still forget the old value.
    let write = fixture::READ_ONLY
        .replace("observe(&*p)", "observe(&mut *p)")
        .replace("p:&u64", "p:&mut u64")
        .replace("{return;}", "{*p=9; return;}");
    unproved(&write);
    unproved(&write.replace("writes ();", ""));
    unproved(&fixture::READ_ONLY.replace("{return;}", "{assert false; return;}"));
    // Pure read effects also preserve contents; no explicit writes declaration
    // is required when the actual closed summary has no write/free effects.
    checked(
        &fixture::READ_ONLY.replace("reads (); writes (); {return;}", "{let value=*p; return;}"),
    );
}

#[test]
fn closed_frame_evidence_is_invalidated_by_callee_changes() {
    use nera::verifier::{relation::audit::RelationReplayCache, summary::audit::SummaryAudit};
    let out = checked(fixture::READ_ONLY);
    let unit = out.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, Default::default()).unwrap();
    let audit = SummaryAudit::from_report(&report);
    assert!(
        RelationReplayCache::new(&unit, Default::default())
            .unwrap()
            .accepts_summary_audit(&audit)
    );
    let changed = inspect(&fixture::READ_ONLY.replace("{return;}", "{assert false; return;}"));
    let changed = changed.vir().unwrap().resolve().unwrap();
    assert!(
        !RelationReplayCache::new(&changed, Default::default())
            .unwrap()
            .accepts_summary_audit(&audit)
    );
    // An explicit failed interface is mandatory even if automatic discovery or
    // all automatic attempts are disabled for sibling loops.
    let bad = inspect(&fixture::MIXED.replace("invariant i<=3;", "invariant i==0;"));
    assert!(
        !verify_program(
            &bad.vir().unwrap().resolve().unwrap(),
            CfgAnalysisConfig {
                max_loop_candidates: 0,
                max_loop_candidate_rounds: 0,
                ..Default::default()
            }
        )
        .unwrap()
        .is_memory_checked_core0()
    );
}
