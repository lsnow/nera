//! Historical borrow baseline, checked against the current supported profile.
use nera::verification::{TextReportMode, render_text, verify_source};
use nera::{
    FrontendStatus, ObligationStatus, ResourceObligationKind, SourceFile,
    VirContractInitialization, VirSpecClauseKind, VirSpecClauseOrigin, analyze,
};

#[test]
fn conditional_source_interfaces_check_both_shared_and_mutable_paths() {
    for borrow in ["&", "&mut"] {
        let function = format!(
            "fn choose(flag:bool,a:{borrow} u64,b:{borrow} u64)->{borrow} u64{{if flag{{return a;}}return b;}}"
        );
        for (body, expected) in [
            ("return 42;".to_owned(), 42),
            (
                format!(
                    "let mut a=42;let mut b=7;let r=choose(true,{borrow} a,{borrow} b);return *r;"
                ),
                42,
            ),
            (
                format!(
                    "let mut a=42;let mut b=7;let r=choose(false,{borrow} a,{borrow} b);return *r;"
                ),
                7,
            ),
        ] {
            let source =
                SourceFile::from_text("choose", format!("fn main()->u64{{{body}}}{function}"));
            let report = verify_source(&source, Default::default());
            assert!(
                report.is_checked(),
                "{}",
                render_text(&report, TextReportMode::Explain)
            );
            assert_eq!(
                nera::interpret(
                    report
                        .validated_unit()
                        .unwrap()
                        .resolve()
                        .unwrap()
                        .runtime()
                )
                .unwrap()
                .values(),
                [nera::VirRuntimeValue::U64(expected)]
            );
        }
    }
}

#[test]
fn stored_shared_field_projection_checks_and_executes() {
    let source = SourceFile::from_text(
        "stored-reference-field",
        "struct Holder { value:&u64, } fn main()->u64{let value=42; let holder=Holder{value:&value}; let view=extract(&holder);return *view;} fn extract(holder:&Holder)->&u64{return holder.value;}",
    );
    let report = verify_source(&source, Default::default());
    assert!(
        report.is_checked(),
        "{}",
        render_text(&report, TextReportMode::Explain)
    );
    assert_eq!(
        nera::interpret(
            report
                .validated_unit()
                .unwrap()
                .resolve()
                .unwrap()
                .runtime()
        )
        .unwrap()
        .values(),
        [nera::VirRuntimeValue::U64(42)]
    );
}

#[test]
fn unsupported_projection_shapes_are_not_misclassified_as_supported_views() {
    {
        let (name, source, status, message) = (
            "tail",
            "fn tail(p:&[u64])->&[u64]{if len(p)>0usize{return &p[1..];}return p;} fn main()->u64{return 42;}",
            FrontendStatus::Unsupported,
            "multiple path-dependent input sources",
        );
        let file = SourceFile::from_text(name, source);
        let output = analyze(&file);
        assert_eq!(output.status(), status, "{name}: {:?}", output.issues());
        assert!(
            output
                .issues()
                .iter()
                .any(|issue| issue.diagnostic().message().contains(message)),
            "{name}: {:?}",
            output.issues()
        );
        assert!(output.vir().is_none());
        assert!(!verify_source(&file, Default::default()).is_checked());
    }
}

#[test]
fn owning_entry_initialization_is_not_inferred_away_for_write_only_bodies() {
    // A write-only implementation does not weaken the current owning ABI.
    for initialize in ["*p=1;", ""] {
        let source = SourceFile::from_text(
            "owning-entry.nera",
            format!(
                "fn main()->u64{{let p=alloc<u64>(1);{initialize}fill(p);return 42;}} fn fill(p:Own<u64>){{*p=42;free(p);return;}}"
            ),
        );
        let report = verify_source(&source, Default::default());
        assert_eq!(
            report.frontend_status(),
            Some(FrontendStatus::AcceptedProposal)
        );
        assert_eq!(
            report.is_checked(),
            !initialize.is_empty(),
            "{}",
            render_text(&report, TextReportMode::Explain)
        );
        if initialize.is_empty() {
            let unit = report.validated_unit().unwrap().as_unit();
            assert!(
                report
                    .verification()
                    .unwrap()
                    .functions()
                    .values()
                    .any(|function| {
                        function.cfg().obligations().iter().any(|record| {
                            let obligation = record.obligation();
                            let ResourceObligationKind::CallContractPrecondition { clause, .. } = obligation.kind() else {
                                return false;
                            };
                            let clause = unit.specs.clause(clause).unwrap();
                            matches!(&clause.kind, VirSpecClauseKind::Resource(resource)
                                if resource.initialization == VirContractInitialization::Initialized)
                                && matches!(clause.origin, VirSpecClauseOrigin::InferredType { .. })
                                && obligation.status() == ObligationStatus::Refuted
                        })
                    }),
                "{}",
                render_text(&report, TextReportMode::Explain)
            );
        }
    }
}
