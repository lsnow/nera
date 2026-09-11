use nera::verification::*;
use nera::*;

fn preview(text: &str) -> VerificationPreview {
    verify_source(
        &SourceFile::from_text("report.nera", text),
        Default::default(),
    )
}

#[test]
fn both_modes_are_deterministic_read_only_and_counts_match_canonical_records() {
    let report = preview(include_str!("../spec/cases/verify/summary-calls.nera"));
    assert!(report.is_checked());
    let saved = report.clone();
    let short = render_text(&report, TextReportMode::Summary);
    let long = render_text(&report, TextReportMode::Explain);
    assert_eq!(report, saved);
    assert_eq!(short, render_text(&report, TextReportMode::Summary));
    assert_eq!(long, render_text(&report, TextReportMode::Explain));
    assert!(!short.contains("[CFG/Proven]"));
    let counts = report.counts().unwrap();
    assert_eq!(long.matches("[CFG/").count(), counts.cfg.total());
    assert_eq!(
        long.matches("[postcondition/").count(),
        counts.postconditions.total()
    );
    assert_eq!(long.matches("[Spec/").count(), counts.proofs.total());
    assert_eq!(
        long.matches("[historical/not-additional/").count(),
        counts.historical.total()
    );
    for text in [&short, &long] {
        assert!(text.starts_with("verification preview (experimental): Checked\n"));
        assert!(text.contains(&format!("obligations: total={}", counts.total())));
        assert!(text.contains("external solver: none"));
        assert!(text.contains("budgets/config: CfgAnalysisConfig"));
        assert!(text.contains("explicit trust entries: 0"));
        assert!(text.contains("implementation TCB:"));
        assert!(text.contains("native execution boundary (not invoked)"));
    }
    assert!(long.contains("mapping world:"));
    assert!(long.contains("guard="));
    assert!(counts.postconditions.total() > 0);
    assert!(long.contains("related return occurrence:"));
}

#[test]
fn explain_names_generated_borrow_sources_guards_and_projections() {
    let source = "struct Pair{left:u64,right:u64,}
         fn main()->u64{let pair=Pair{left:1,right:42};let r=right(&pair);return *r;}
         fn right(value:&Pair)->&u64{return &value.right;}
         fn choose(flag:bool,a:&u64,b:&u64)->&u64{if flag{return a;}else{return b;}}";
    let report = preview(source);
    assert!(report.is_checked(), "{report:#?}");
    let counts = report.counts().unwrap();
    assert_eq!(counts.borrow_interfaces, 2);
    assert_eq!(counts.borrow_worlds, 3);
    let summary = render_text(&report, TextReportMode::Summary);
    let explain = render_text(&report, TextReportMode::Explain);
    assert!(summary.contains("inferred borrow interfaces: functions=2; complete result worlds=3"));
    assert!(!summary.contains("[borrow-interface/generated]"));
    assert!(explain.contains("not user contracts or trusted assumptions"));
    assert!(explain.contains("`right` when always: result #0 borrows Shared from parameter #0"));
    assert!(explain.contains("projection=fixed bytes 8..16 (alignment 8)"));
    assert!(explain.contains("`choose` when parameter #0 == true"));
    assert!(explain.contains("`choose` when parameter #0 == false"));
    assert!(explain.contains("from parameter #1"));
    assert!(explain.contains("from parameter #2"));
    assert_eq!(report, preview(source));
}

#[test]
fn raw_unit_interfaces_are_not_misreported_as_source_inference() {
    let source = "fn main()->u64{let value=42;let r=id(&value);return *r;} fn id(value:&u64)->&u64{return value;}";
    let unit = analyze(&SourceFile::from_text("raw-interface.nera", source))
        .vir()
        .unwrap()
        .as_unit()
        .clone();
    let report = verify_unit(unit, Default::default());
    assert!(report.is_checked());
    let explain = render_text(&report, TextReportMode::Explain);
    assert!(explain.contains("[borrow-interface/validated-unit]"));
    assert!(explain.contains("does not classify them as source inference or user contracts"));
    assert!(!explain.contains("[borrow-interface/generated]"));
}

#[test]
fn ordinary_failures_use_source_and_conditions_not_ssa_names_or_witness_claims() {
    for (source, reason) in [
        (
            include_str!("../spec/cases/verify/uaf.nera"),
            "allocation is live",
        ),
        (
            include_str!("../spec/cases/verify/loop-initialization-skipped.nera"),
            "value bytes are initialized",
        ),
        (
            "fn main()->u64 { let a=[42]; let i=2usize; return a[i]; }",
            "index is below array length 1",
        ),
        (
            "fn main()->u64 { let mut x=42; let p=&x; x=3; return *p; }",
            "access is compatible with outstanding loans",
        ),
    ] {
        let report = preview(source);
        assert_eq!(report.outcome(), PreviewOutcome::Unproved, "{report:?}");
        let text = render_text(&report, TextReportMode::Summary);
        assert!(text.contains(reason), "{text}");
        assert!(text.contains("--> report.nera:"), "{text}");
        assert!(text.contains(" | "));
        assert!(
            !text.contains('%'),
            "ordinary view must not require SSA: {text}"
        );
        assert!(text.contains("not an executable counterexample"));
        let failed = report
            .obligations()
            .unwrap()
            .filter(|o| !o.status().is_proven())
            .count();
        let rendered = text
            .lines()
            .filter(|l| {
                l.starts_with("[CFG/")
                    || l.starts_with("[postcondition/")
                    || l.starts_with("[Spec/")
            })
            .count();
        assert_eq!(rendered, failed, "do not drop same-source obligations");
    }
}

#[test]
fn call_precision_links_caller_callee_and_keeps_each_case_without_claiming_causality() {
    let report = preview(
        "fn main()->u64 { bad(); return 42; }\nfn bad() { let p=alloc<u64>(1); let x=*p; free(p); return; }",
    );
    assert_eq!(report.outcome(), PreviewOutcome::Unproved);
    for mode in [TextReportMode::Summary, TextReportMode::Explain] {
        let text = render_text(&report, mode);
        assert!(text.contains("`main` -> `bad`: NotClosed"), "{text}");
        assert!(text.contains("related callee definition (not by itself the failure cause)"));
        assert!(text.contains("report.nera:1:"));
        assert!(text.contains("report.nera:2:"));
        if mode == TextReportMode::Explain {
            let calls: usize = report
                .summaries()
                .unwrap()
                .map(|(_, s)| s.call_uses.len())
                .sum();
            assert_eq!(
                text.matches("[call/precision-not-obligation]").count(),
                calls
            );
            assert!(text.contains("case="));
            assert!(text.contains("arguments="));
            assert!(text.contains("mapping loss:"));
        }
    }
}

#[test]
fn generated_cleanup_and_loan_end_retain_parent_source_origins() {
    for source in [
        include_str!("../spec/cases/verify/drop-scope.nera"),
        include_str!("../spec/cases/verify/local-nll.nera"),
    ] {
        let report = preview(source);
        assert!(report.verification().is_some(), "{report:?}");
        let text = render_text(&report, TextReportMode::Explain);
        assert!(
            text.contains("generated ImplicitDrop:") || text.contains("generated LoanEffect:"),
            "{text}"
        );
        assert!(text.contains("attributed to the enclosing source construct"));
        assert!(!text.contains("source text unavailable"));
    }
}

#[test]
fn same_call_site_keeps_distinct_cases_and_return_occurrences() {
    let source = include_str!("../spec/cases/verify/summary-conditional.nera").replace(
        "return *returned;",
        "let answer=pass(returned); return *answer;",
    ) + "\nfn pass(p:Own<u64>)->Own<u64> { return p; }";
    let report = preview(&source);
    assert!(report.is_checked());
    let mut sites = std::collections::BTreeMap::new();
    for (_, summary) in report.summaries().unwrap() {
        for call in &summary.call_uses {
            sites
                .entry(call.observation.finding)
                .or_insert_with(Vec::new)
                .push(&call.observation);
        }
    }
    assert!(
        sites.values().any(|cases| cases.len() > 1
            && cases
                .windows(2)
                .any(|c| c[0].case_ordinal != c[1].case_ordinal)),
        "{sites:#?}"
    );
    let text = render_text(&report, TextReportMode::Explain);
    assert_eq!(
        text.matches("  case=").count(),
        sites.values().map(Vec::len).sum::<usize>()
    );
    // Distinct resource worlds can have the same projected (even empty) guard.
    // Render both cases and exactly the retained guard, never reconstruct one.
    for observation in sites.values().flatten() {
        assert!(text.contains(&format!(
            "case={}; instance_site={}; guard={:?}",
            observation.case_ordinal, observation.instance_site, observation.guard
        )));
    }

    let report =
        preview("fn choose(flag:bool,p:Own<u64>)->Own<u64> { if flag { return p; } return p; }");
    assert!(report.is_checked());
    let mut positions = std::collections::BTreeMap::new();
    for o in report.obligations().unwrap() {
        if let ObligationEvidence::Postcondition(_) = o.evidence {
            positions
                .entry(o.finding().source_span())
                .or_insert_with(std::collections::BTreeSet::new)
                .insert(o.finding().occurrence());
        }
    }
    assert!(positions.values().any(|returns| returns.len() > 1));
    let text = render_text(&report, TextReportMode::Explain);
    assert_eq!(
        text.matches("related return occurrence:").count(),
        report.counts().unwrap().postconditions.total()
    );
}

#[test]
fn unknown_numeric_queries_are_auxiliary_not_a_new_verdict() {
    let report = preview("fn get(i:usize)->u64 { let a=[42]; return a[i]; }");
    assert_eq!(report.outcome(), PreviewOutcome::Unproved);
    let short = render_text(&report, TextReportMode::Summary);
    let long = render_text(&report, TextReportMode::Explain);
    assert!(short.contains("[CFG/Unknown]"));
    assert!(short.contains("insufficient facts to establish condition"));
    assert!(
        long.contains("query-local evidence (auxiliary attempts, not necessarily the sole cause)"),
        "{long}"
    );
    assert!(long.contains("MissingRelation"));
    assert_eq!(report.outcome(), PreviewOutcome::Unproved);
}

#[test]
fn rejected_unsupported_budget_and_raw_inputs_never_fabricate_zero_or_locations() {
    for input in [
        SourceFile::from_text("empty.nera", ""),
        SourceFile::from_text("unicode.nera", "fn 名字()->u64 {\n return 42;\n}"),
        SourceFile::from_text("multiline.nera", "fn main(\n {"),
        SourceFile::new("invalid.nera", vec![0xff]),
    ] {
        let report = verify_source(&input, Default::default());
        let text = render_text(&report, TextReportMode::Summary);
        assert!(
            text.contains("obligations/statistics: unavailable"),
            "{text}"
        );
        assert!(text.contains("explicit trust: unavailable"));
        assert!(!text.contains("total=0"));
        assert!(text.contains("[frontend/"));
        if report.frontend_status() == Some(FrontendStatus::Unsupported) {
            assert!(text.contains("Unsupported { stage: Frontend"));
        }
    }
    let source = SourceFile::from_text("budget.nera", "fn main()->u64 { return 42; }");
    let report = verify_source(
        &source,
        CfgAnalysisConfig {
            max_block_visits: 0,
            ..Default::default()
        },
    );
    let text = render_text(&report, TextReportMode::Summary);
    assert!(text.contains("BudgetAborted"));
    assert!(text.contains("budget.nera:1:1"));
    assert!(text.contains("obligations/statistics: unavailable"));

    let raw_source = SourceFile::from_text(
        "budget.nera",
        "fn main()->u64 { let a=[42]; return a[0usize]; }",
    );
    let unit = analyze(&raw_source).vir().unwrap().as_unit().clone();
    let report = verify_unit(unit.clone(), Default::default());
    let text = render_text(&report, TextReportMode::Explain);
    assert!(text.contains("source text unavailable; line/column unavailable"));
    assert!(
        !text.contains("budget.nera:1:1"),
        "raw route must not reopen source paths"
    );
    let mut invalid = unit;
    invalid.runtime.entry = VirFunctionId::new(999);
    let text = render_text(
        &verify_unit(invalid, Default::default()),
        TextReportMode::Summary,
    );
    assert!(text.contains("Rejected(Validation)"));
    assert!(text.contains("[validation]"));
}

#[test]
fn unknown_summary_can_coexist_with_checked_skeleton_and_explain_does_not_change_it() {
    let source = SourceFile::from_text(
        "skeleton.nera",
        "fn main()->u64 { return f(0); } fn f(n:u64)->u64 { if n==3 { return 42; } return f(n+1); }",
    );
    let mut config = CfgAnalysisConfig::default();
    config.summary_limits.max_iterations = 0;
    let report = verify_source(&source, config);
    assert!(report.is_checked());
    for mode in [TextReportMode::Summary, TextReportMode::Explain] {
        let text = render_text(&report, mode);
        assert!(text.starts_with("verification preview (experimental): Checked"));
        assert!(text.contains("[summary/precision-not-obligation] `f`: Unknown"));
        assert!(!text.contains("[CFG/Unknown]"));
    }
}
