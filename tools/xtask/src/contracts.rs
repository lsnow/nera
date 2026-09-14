//! Stage 8.2 extends the 8.1 union without rerunning overlapping targets.
use std::{error::Error, path::Path};

fn test_commands() -> Vec<Vec<&'static str>> {
    let mut commands = super::spec_local::test_commands();
    commands[1].push("--no-fail-fast");
    commands[0].extend([
        "verifier::contract",
        "verifier::summary",
        "verifier::verify",
        "verifier::transfer::call",
        "frontend::hir::validation::spec",
        "vir::validate::spec",
    ]);
    for target in [
        "contract_baseline",
        "contract_schema",
        "pure_contracts",
        "memory_contracts",
        "resource_contracts",
        "frame_contracts",
        "contract_recursive",
        "contract_composition",
        "contract_arena",
        "contract_acceptance",
        "scalar_memory",
        "summary_audit",
        "summary_calls",
        "summary_recursive",
        "summary_borrows",
        "summary_conditional",
        "summary_projection",
        "summary_architecture",
        "summary_baseline",
        "module_program",
        "borrow_interface_mapping",
        "borrow_source_scc",
        "implicit_borrow_acceptance",
        "vir_contracts",
        "verifier_contracts",
    ] {
        assert!(!commands[1].contains(&target));
        commands[1].extend(["--test", target]);
    }
    commands[2].extend([
        "contract_baseline_runtime_and_raw_scalar_match_native",
        "entry_contract_snapshots_are_checked_and_erased_by_native",
        "pure_source_contracts_share_interpreter_and_native_execution",
        "heap_contract_observations_preserve_native_execution",
        "arena_contracts_restore_backing_and_match_the_resource_ledger",
        "composed_module_contracts_and_erasure_preserve_native_execution",
        "recursive_contracts_use_the_ordinary_native_call_path",
        "frame_contracts_are_erased_before_native_execution",
        "resource_contracts_preserve_interpreter_and_native_execution",
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
    #[test]
    fn union_has_unique_targets_and_does_not_invoke_full_gate() {
        let commands = super::test_commands();
        let targets: Vec<_> = commands[1]
            .windows(2)
            .filter(|pair| pair[0] == "--test")
            .map(|pair| pair[1])
            .collect();
        assert_eq!(
            targets.len(),
            targets
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len()
        );
        assert!(targets.contains(&"contract_arena"));
        assert!(targets.contains(&"spec_diagnostics"));
        for command in commands {
            assert!(!command.contains(&"--workspace"));
            assert!(
                !command
                    .iter()
                    .any(|arg| arg.contains("fuzz") || arg.contains("lean"))
            );
        }
    }
}
