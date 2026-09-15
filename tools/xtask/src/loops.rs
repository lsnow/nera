//! One deduplicated union: extend the contract command plan, never invoke its gate.
use std::{error::Error, path::Path};

fn test_commands() -> Vec<Vec<&'static str>> {
    let mut commands = super::contracts::test_commands();
    commands[0].extend(["verifier::cfg", "verifier::resource", "verifier::transfer"]);
    for target in [
        "loop_baseline",
        "loop_induction",
        "loop_resources",
        "loop_control",
        "loop_candidates",
        "loop_composition",
        "loop_arena",
        "loop_acceptance",
        "loop_review",
        "loop_partitions",
        "frontend_loops",
        "frontend_loop_initialization",
        "frontend_for_match",
        "frontend_control_flow",
        "frontend_nll",
        "frontend_reborrow",
        "verifier_cfg",
        "verifier_guarded",
        "verifier_loans",
        "relation_cfg",
        "vir_corpus",
    ] {
        assert!(!commands[1].contains(&target));
        commands[1].extend(["--test", target]);
    }
    commands[2].extend([
        "scalar_loop_induction_preserves_native_runtime",
        "stable_resource_loop_invariants_preserve_native_runtime",
        "structured_loop_control_and_cleanup_match_native",
        "inferred_loop_candidates_preserve_native_execution_and_cleanup",
        "loop_contract_composition_matches_native_and_resource_ledger",
        "loop_arena_initialization_and_views_preserve_native_resource_ledger",
        "loop_initialization_matches_native_and_preserves_resource_cleanup",
        "loop_review_fixes_preserve_native_execution_and_cleanup",
    ]);
    commands
}

pub(super) fn run(root: &Path) -> Result<(), Box<dyn Error>> {
    super::require_native_acceptance_host()?;
    super::run_cargo(root, &["fmt", "--all", "--", "--check"])?;
    super::stage4::check(root)?;
    for args in test_commands() {
        println!("==> cargo {}", args.join(" "));
        super::run_cargo(root, &args)?;
    }
    super::run_cargo(root, &["check", "--workspace", "--all-targets"])?;
    super::run_cargo(
        root,
        &[
            "clippy",
            "--workspace",
            "--all-targets",
            "--",
            "-D",
            "warnings",
        ],
    )
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    #[test]
    fn loop_union_executes_each_target_once_without_full_gate() {
        let commands = super::test_commands();
        assert_eq!(commands.len(), 4);
        let targets: Vec<_> = commands[1]
            .windows(2)
            .filter(|p| p[0] == "--test")
            .map(|p| p[1])
            .collect();
        assert_eq!(targets.len(), targets.iter().collect::<BTreeSet<_>>().len());
        assert!(targets.contains(&"loop_arena") && targets.contains(&"loop_acceptance"));
        assert!(targets.contains(&"loop_partitions"));
        let native = &commands[2][7..];
        assert_eq!(native.len(), native.iter().collect::<BTreeSet<_>>().len());
        for command in commands {
            assert!(!command.iter().any(|s| s.contains("fuzz")
                || *s == "lean"
                || s.starts_with("check-lean")
                || *s == "--workspace"
                || s.starts_with("check-")));
        }
    }
}
