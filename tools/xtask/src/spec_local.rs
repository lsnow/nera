//! 8.1 acceptance union, not the full stage-8 gate. These are concrete test
//! identities, deliberately independent of historical stage gate aliases.
use std::{error::Error, path::Path};

const LIBRARY_FILTERS: &[&str] = &[
    "frontend::tests",
    "frontend::lower::tests",
    "frontend::lower::post_cfg",
    "verifier::vc",
    "verifier::transfer::spec",
    "verifier::spec::separation",
];

const INTEGRATIONS: &[&str] = &[
    "borrow_baseline",
    "compilation_session",
    "conditional_borrow_inference",
    "difference_relations",
    "frontend_borrow_calls",
    "frontend_calls",
    "frontend_copy_move",
    "frontend_deferred_local",
    "frontend_partial_construction",
    "generic_instances",
    "hir_regions",
    "hir_spec",
    "initialization_baseline",
    "local_assert",
    "provenance_instance",
    "relation_audit",
    "relation_baseline",
    "relation_bounds",
    "resource_payload",
    "spec_arithmetic",
    "spec_baseline",
    "spec_diagnostics",
    "spec_exists",
    "spec_local_arena",
    "spec_memory",
    "spec_separation",
    "symbolic_footprint",
    "typed_spec_ir",
    "verification_report",
    "verification_text",
    "verifier_cases",
    "verify_cli",
    "vir_loan_schema",
    "vir_source_map",
    "vir_unit_baseline",
    "vir_v0",
];

const NATIVE_FILTERS: &[&str] = &[
    "spec_arena_source_baseline_preserves_native_storage_and_release_ledger",
    "resource_assertion_schema_is_erased_by_interpreter_and_native",
    "checked_spec_arithmetic_preserves_native_arena_execution",
    "checked_spec_memory_preserves_native_execution",
    "checked_spec_separation_preserves_native_execution",
    "checked_spec_exists_preserves_native_execution",
    "source_local_assertions_preserve_native_execution",
    "spec_local_arena_preserves_native_storage_and_release_ledger",
];

fn test_commands() -> Vec<Vec<&'static str>> {
    let mut library = vec!["test", "--quiet", "--lib", "--"];
    library.extend(LIBRARY_FILTERS);
    let mut integrations = vec!["test", "--quiet"];
    for target in INTEGRATIONS {
        integrations.extend(["--test", target]);
    }
    // libtest combines multiple filters with OR, executing each matched test once.
    let mut native = vec![
        "test",
        "--quiet",
        "--test",
        "native_acceptance",
        "--",
        "--exact",
    ];
    native.extend(NATIVE_FILTERS);
    vec![
        library,
        integrations,
        native,
        vec!["test", "--quiet", "-p", "xtask"],
    ]
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
        &["clippy", "--lib", "--tests", "--", "-D", "warnings"],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn focused_union_is_unique_and_has_no_full_gate_or_fuzz() {
        for entries in [LIBRARY_FILTERS, INTEGRATIONS, NATIVE_FILTERS] {
            assert_eq!(entries.iter().collect::<BTreeSet<_>>().len(), entries.len());
        }
        assert!(INTEGRATIONS.contains(&"spec_local_arena"));
        assert!(INTEGRATIONS.contains(&"spec_baseline"));
        assert!(INTEGRATIONS.contains(&"spec_exists"));
        let commands = test_commands();
        assert_eq!(commands.len(), 4);
        for args in commands {
            assert!(!args.contains(&"--workspace"));
            assert!(!args.contains(&"check-rust"));
            assert!(!args.iter().any(|s| s.contains("fuzz")));
        }
        assert_eq!(NATIVE_FILTERS.len(), 8);
    }
}
