//! Report/CLI observation assertions shared by existing semantic and replay suites.
use nera::verification::*;

pub fn observe(preview: &VerificationPreview) {
    let expected_code = match preview.outcome() {
        PreviewOutcome::Checked => 0,
        PreviewOutcome::Unproved
        | PreviewOutcome::Unsupported {
            stage: PreviewStage::Verification,
            ..
        } => 1,
        _ => 2,
    };
    let before = preview.clone();
    for mode in [TextReportMode::Summary, TextReportMode::Explain] {
        let mut bytes = Vec::new();
        assert_eq!(
            write_report(preview, mode, &mut bytes).unwrap(),
            expected_code
        );
        let text = String::from_utf8(bytes).unwrap();
        assert_eq!(text, render_text(preview, mode));
        assert!(text.starts_with(&format!(
            "verification preview (experimental): {:?}\n",
            preview.outcome()
        )));
        let count = preview.obligations().map(|os| {
            os.filter(|o| mode == TextReportMode::Explain || !o.status().is_proven())
                .count()
        });
        assert_eq!(
            text.lines()
                .filter(|l| ["[CFG/", "[Spec/", "[postcondition/"]
                    .iter()
                    .any(|prefix| l.starts_with(prefix)))
                .count(),
            count.unwrap_or(0),
            "cannot omit failed obligations"
        );
        if let Some(trust) = preview.trust_report() {
            assert_eq!(
                text.matches("[trust] registered assumption:").count(),
                trust.entries().len()
            );
        } else {
            assert!(text.contains("explicit trust: unavailable"));
        }
        if preview.verification().is_none() {
            assert_ne!(expected_code, 0);
            assert!(preview.counts().is_none());
            assert!(text.contains("obligations/statistics: unavailable"));
        }
        if mode == TextReportMode::Explain
            && let Some(report) = preview.verification()
        {
            for function in report.functions().values() {
                for losses in function.cfg().guarded_precision_losses().values() {
                    if !losses.is_empty() {
                        assert!(
                            text.contains(&format!("{losses:?}")),
                            "lost precision must remain visible"
                        );
                    }
                }
            }
        }
    }
    assert_eq!(*preview, before, "rendering cannot mutate proof state");
}
