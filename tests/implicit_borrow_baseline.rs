//! Stage 7.8.3.1 pins current boundaries; it does not implement inference.
use nera::verification::{TextReportMode, render_text, verify_source};
use nera::{
    FrontendStatus, ObligationStatus, ResourceObligationKind, SourceFile,
    VirContractInitialization, VirSpecClauseKind, VirSpecClauseOrigin, analyze,
};

#[test]
fn future_path_dependent_source_interfaces_are_rejected_before_execution() {
    // 7.8.3.3 admits a unique source among several inputs. Conditional source
    // alternatives remain gated until 7.8.3.4, even in uncalled functions.
    for (name, function) in [
        (
            "choose",
            "fn choose(flag:bool,a:&u64,b:&u64)->&u64{if flag{return a;}return b;}",
        ),
        (
            "choose_mut",
            "fn choose_mut(flag:bool,a:&mut u64,b:&mut u64)->&mut u64{if flag{return a;}return b;}",
        ),
    ] {
        let mutable = name.ends_with("mut");
        let borrow = if mutable { "&mut" } else { "&" };
        let flag = if name.starts_with("choose") {
            "true,"
        } else {
            ""
        };
        let call = format!(
            "let mut a=42;let mut b=7;let r={name}({flag}{borrow} a,{borrow} b);return *r;"
        );
        for body in ["return 42;", call.as_str()] {
            let source = SourceFile::from_text(name, format!("fn main()->u64{{{body}}}{function}"));
            let output = analyze(&source);
            assert_eq!(
                output.status(),
                FrontendStatus::Unsupported,
                "{name}: {:?}",
                output.issues()
            );
            assert!(
                output.issues().iter().any(|issue| issue
                    .diagnostic()
                    .message()
                    .contains("multiple path-dependent input sources")),
                "{name}: {:?}",
                output.issues()
            );
            assert!(output.hir().is_none());
            assert!(output.vir().is_none());
            let report = verify_source(&source, Default::default());
            assert!(!report.is_checked());
            assert!(report.validated_unit().is_none());
        }
    }
}

#[test]
fn unsupported_projection_shapes_are_not_misclassified_as_supported_views() {
    for (name, source, status, message) in [
        (
            "stored-reference-field",
            "struct Holder { value:&u64, } fn extract(holder:&Holder)->&u64{return holder.value;} fn main()->u64{return 42;}",
            FrontendStatus::Unsupported,
            "projection",
        ),
        (
            "tail",
            "fn tail(p:&[u64])->&[u64]{if len(p)>0usize{return &p[1..];}return p;} fn main()->u64{return 42;}",
            FrontendStatus::Unsupported,
            "multiple path-dependent input sources",
        ),
    ] {
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
