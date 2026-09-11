//! Measurements use the production phases; time/RSS never enter canonical reports.
use super::*;
use std::{cell::Cell, time::Instant};
#[path = "../../tests/support/summary_scale.rs"]
mod scale;

thread_local! { static RENDERING: Cell<bool> = const { Cell::new(false) }; }
pub(crate) fn assert_not_rendering() {
    RENDERING.with(|active| {
        assert!(
            !active.get(),
            "rendering must not verify/replay or construct SummaryAudit"
        )
    });
}
struct Rendering;
impl Rendering {
    fn begin() -> Self {
        RENDERING.with(|active| assert!(!active.replace(true)));
        Self
    }
}
impl Drop for Rendering {
    fn drop(&mut self) {
        RENDERING.with(|active| active.set(false));
    }
}
fn peak_rss_kib() -> Option<usize> {
    std::fs::read_to_string("/proc/self/status")
        .ok()?
        .lines()
        .find(|line| line.starts_with("VmHWM:"))?
        .split_whitespace()
        .nth(1)?
        .parse()
        .ok()
}

#[test]
fn scale_phases_and_rendering_keep_the_canonical_verdict() {
    let dimension = std::env::var("NERA_VERIFY_SCALE").ok();
    let size = std::env::var("NERA_VERIFY_SCALE_SIZE")
        .ok()
        .map(|v| v.parse::<usize>().expect("numeric scale size"));
    let mode = std::env::var("NERA_VERIFY_SCALE_MODE").ok();
    assert!(
        dimension
            .as_deref()
            .is_none_or(|d| scale::DIMENSIONS.contains(&d)),
        "unknown dimension"
    );
    assert!(
        size.is_none_or(|s| scale::SIZES.contains(&s)),
        "unsupported size"
    );
    assert!(
        mode.as_deref()
            .is_none_or(|m| ["summary", "explain"].contains(&m)),
        "unknown mode"
    );
    for d in scale::DIMENSIONS {
        if dimension.as_deref().is_some_and(|selected| selected != d) {
            continue;
        }
        for n in scale::SIZES {
            if size.is_some_and(|selected| selected != n) {
                continue;
            }
            let input = SourceFile::from_text("verify-scale.nera", scale::source(d, n));
            let start = Instant::now();
            let mut preview = prepare_source(&input, Default::default());
            let frontend_us = start.elapsed().as_micros();
            assert_eq!(
                preview.frontend_status(),
                Some(FrontendStatus::AcceptedProposal)
            );
            let start = Instant::now();
            preview.analyze_unit();
            let verify_us = start.elapsed().as_micros();
            assert!(preview.is_checked(), "{d}/{n}: {:?}", preview.failure());
            let counts = preview.counts().unwrap();
            if d == "alternatives" && n == 8 {
                assert_eq!(
                    counts.summaries_closed, 0,
                    "retain known skeleton precision boundary"
                );
                assert_eq!(counts.summaries_unknown, 2);
            } else {
                assert_eq!(counts.summaries_closed, counts.functions);
            }
            for (label, report_mode) in [
                ("summary", TextReportMode::Summary),
                ("explain", TextReportMode::Explain),
            ] {
                if mode.as_deref().is_some_and(|selected| selected != label) {
                    continue;
                }
                let scope = Rendering::begin();
                let start = Instant::now();
                let text = render_text(&preview, report_mode);
                let render_us = start.elapsed().as_micros();
                drop(scope);
                // Sample before extra assertions or later modes raise the high-water mark.
                let rss = peak_rss_kib();
                assert!(text.starts_with("verification preview (experimental): Checked\n"));
                assert!(!text.contains("elapsed_us=") && !text.contains("peak_rss_kib="));
                if report_mode == TextReportMode::Summary {
                    for detail in [
                        "  evidence:",
                        "  mapping world:",
                        "summary return alternatives:",
                        "[CFG/Proven]",
                    ] {
                        assert!(
                            !text.contains(detail),
                            "default view expanded evidence: {detail}"
                        );
                    }
                    assert!(
                        text.len() < 16 * 1024,
                        "bounded fixtures must not dump whole audits"
                    );
                } else {
                    let obligations = text
                        .lines()
                        .filter(|line| {
                            ["[CFG/", "[postcondition/", "[Spec/"]
                                .iter()
                                .any(|p| line.starts_with(p))
                        })
                        .count();
                    assert_eq!(obligations, counts.total());
                }
                if counts.summaries_unknown > 0 {
                    assert!(text.contains("Unknown") && text.contains("NotClosed"));
                }
                eprintln!(
                    "verify-scale dimension={d} size={n} mode={label} functions={} closed={} obligations={} source_bytes={} frontend_us={frontend_us} verify_us={verify_us} render_us={render_us} output_bytes={} peak_rss_kib={rss:?}",
                    counts.functions,
                    counts.summaries_closed,
                    counts.total(),
                    input.len(),
                    text.len()
                );
            }
            assert_eq!(preview.counts(), Some(counts));
            assert!(preview.is_checked());
        }
    }
}

#[test]
fn rendering_tripwire_rejects_hidden_reverification_and_audit_materialization() {
    let input = SourceFile::from_text("tripwire.nera", "fn main()->u64 { return 42; }");
    let preview = verify_source(&input, Default::default());
    let resolved = preview.validated_unit().unwrap().resolve().unwrap();
    let scope = Rendering::begin();
    assert!(
        std::panic::catch_unwind(|| crate::verify_program(&resolved, Default::default())).is_err()
    );
    assert!(
        std::panic::catch_unwind(
            || crate::verifier::summary::audit::SummaryAudit::from_report(
                preview.verification().unwrap()
            )
        )
        .is_err()
    );
    drop(scope);
    assert_not_rendering();
}
