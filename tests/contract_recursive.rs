use nera::verifier::summary::{SccOutcome, SummaryState};
use nera::*;

fn inspect(source: &str, config: CfgAnalysisConfig) -> ProgramVerification {
    let output = analyze(&SourceFile::from_text("contract-recursive.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("{:?}", output.issues()));
    verify_program(&unit.resolve().unwrap(), config).unwrap()
}

const SCALAR: &str = "fn main()->u64 {return wrapper();}
    fn wrapper()->u64 {return recurse(0);}
    fn recurse(n:u64)->u64 requires n<=3; ensures result==42; reads (); writes ();
    {if n==3 {return 42;} return recurse(n+1);}";

#[test]
fn explicit_scalar_recursion_uses_final_component_replay() {
    let report = inspect(SCALAR, Default::default());
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let recursive = report
        .functions()
        .values()
        .find(|f| f.summary().recursion.is_some())
        .unwrap();
    let audit = recursive.summary().recursion.as_ref().unwrap();
    assert_eq!(audit.outcome, SccOutcome::Closed);
    assert!(audit.final_recheck);
    assert!(matches!(recursive.summary().state, SummaryState::Closed));
    assert!(
        !inspect(
            &SCALAR.replace("return 42;", "return 41;"),
            Default::default()
        )
        .is_memory_checked_core0()
    );
    assert!(
        !inspect(
            &SCALAR.replace("recurse(n+1)", "recurse(4)"),
            Default::default()
        )
        .is_memory_checked_core0()
    );
}

#[test]
fn mixed_mutual_component_is_published_atomically() {
    let source = "fn main()->u64 {return even(0);}
        fn even(n:u64)->u64 ensures result==42; reads (); writes ();
        {if n==4 {return 42;} return odd(n+1);}
        fn odd(n:u64)->u64 {if n==3 {return 42;} return even(n+1);}";
    let report = inspect(source, Default::default());
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let bad = inspect(
        &source.replace("n==3 {return 42", "n==3 {return 7"),
        Default::default(),
    );
    assert!(!bad.is_memory_checked_core0());
    assert!(
        bad.functions()
            .values()
            .filter(|f| f.summary().recursion.is_some())
            .all(|f| !matches!(f.summary().state, SummaryState::Closed))
    );
}

#[test]
fn resource_and_frame_contracts_are_rechecked_inside_recursion() {
    let source = "fn main()->u64 {let mut n=1; fill(&mut n,0); return n;}
        fn fill(p:&mut u64,n:u64) requires writable(p,0..1); ensures readable(p,0..1);
        reads p[0..1]; writes p[0..1];
        {if n==3 {*p=42; return;} fill(p,n+1); return;}";
    let report = inspect(source, Default::default());
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert!(
        !inspect(
            &source.replace("writes p[0..1]", "writes ()"),
            Default::default()
        )
        .is_memory_checked_core0()
    );
    assert!(
        !inspect(
            &source.replace("ensures readable(p,0..1)", "ensures readable(p,0..2)"),
            Default::default()
        )
        .is_memory_checked_core0()
    );
}

#[test]
fn budgets_and_unsupported_return_hypotheses_never_close() {
    let config = CfgAnalysisConfig {
        summary_limits: nera::verifier::summary::SccLimits {
            max_body_analyses: 0,
            ..Default::default()
        },
        ..Default::default()
    };
    assert!(!inspect(SCALAR, config).is_memory_checked_core0());
    assert!(
        !inspect(
            "fn main()->u64 {return f();} fn f()->u64 ensures result==42; {return f();}",
            Default::default()
        )
        .is_memory_checked_core0()
    );
}

#[test]
fn contract_config_and_final_replay_evidence_are_content_bound() {
    use nera::verifier::relation::audit::RelationReplayCache;
    use nera::verifier::summary::audit::SummaryAudit;
    let output = analyze(&SourceFile::from_text("contract-recursive.nera", SCALAR));
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, Default::default()).unwrap();
    let audit = SummaryAudit::from_report(&report);
    let cache = RelationReplayCache::new(&unit, Default::default()).unwrap();
    assert!(cache.accepts_summary_audit(&audit));
    let mut forged = audit.clone();
    forged
        .functions
        .iter_mut()
        .find(|f| f.summary.recursion.is_some())
        .unwrap()
        .summary
        .recursion
        .as_mut()
        .unwrap()
        .final_recheck = false;
    assert!(!cache.accepts_summary_audit(&forged));
    for source in [
        SCALAR.replace("result==42", "result==41"),
        SCALAR.replace("reads ()", "writes ()"),
        SCALAR.replace("return 42;", "return 41;"),
    ] {
        let changed = analyze(&SourceFile::from_text("contract-recursive.nera", &source));
        let changed = changed.vir().unwrap().resolve().unwrap();
        assert!(
            !RelationReplayCache::new(&changed, Default::default())
                .unwrap()
                .accepts_summary_audit(&audit)
        );
    }
    assert!(
        !RelationReplayCache::new(
            &unit,
            CfgAnalysisConfig {
                max_summary_evidence: 32,
                ..Default::default()
            }
        )
        .unwrap()
        .accepts_summary_audit(&audit)
    );
}
