#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{CfgAnalysisConfig, ResourceObligationKind, verify_program};

const SOURCE: &str = include_str!("../spec/cases/verify/provenance-instance.nera");

#[test]
fn repeated_heap_summary_aggregate_and_recursive_frame_instances_are_checked() {
    frontend_checks::checked("provenance-instance.nera", SOURCE, 42);
}

#[test]
fn overlapping_instances_at_one_site_keep_the_old_owner_and_fail_closed() {
    // This is a safe concrete construction, but needs a multi-instance heap
    // domain. A single-slot model must not silently overwrite the first owner.
    for producer in ["alloc<u64>(1)", "make()"] {
        let source = format!(
            "fn main() -> u64 {{
        let mut values: [Own<u64>; 2];
        for i in 0usize..2usize {{ values[i] = {producer}; }}
        return 42;
    }} fn make() -> Own<u64> {{ let p = alloc<u64>(1); *p = 7; return p; }}"
        );
        let output = frontend_checks::accepted("overlapping-instances.nera", &source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!verification.is_memory_checked_core0());
        assert!(
            verification
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(|o| {
                    matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::AllocationInstanceFresh { .. }
                    ) && !o.obligation().is_proven()
                })
        );
        assert!(
            verification
                .diagnostics()
                .iter()
                .any(|d| d.message().contains("fresh instance"))
        );
    }
}
