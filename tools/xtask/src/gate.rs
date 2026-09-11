//! Plan concrete tasks before running commands. Stage names are not execution
//! identities: many distinct stages request the same library/integration tests.

use std::{collections::BTreeSet, error::Error, path::Path};

#[cfg(test)]
use super::STAGE7_GATE;
use super::{GateStep, regression};

/// Checks that define the standalone release gate. Historical stage metadata is
/// retained for focused developer commands, but release validation must not
/// depend on archived design documents.
const RELEASE_GATE: &[GateStep] = &[
    GateStep::VirSnapshots,
    GateStep::Format,
    GateStep::WorkspaceTests,
    GateStep::FrontendFuzz,
    GateStep::VerifierFuzz,
    GateStep::Clippy,
    GateStep::Rustdoc,
];

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct TestSelection {
    workspace: bool,
    library: bool,
    binaries: BTreeSet<&'static str>,
    integrations: BTreeSet<&'static str>,
}

impl TestSelection {
    fn cargo_args(&self) -> Vec<&'static str> {
        if self.workspace {
            return vec!["test", "--workspace"];
        }
        let mut args = vec!["test"];
        if self.library {
            args.push("--lib");
        }
        for target in &self.binaries {
            args.extend(["--bin", *target]);
        }
        for target in &self.integrations {
            args.extend(["--test", *target]);
        }
        args
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Task {
    Check(GateStep),
    Tests(TestSelection),
}

#[derive(Debug, PartialEq, Eq)]
struct GatePlan {
    native: bool,
    tasks: Vec<Task>,
}

impl GatePlan {
    fn new(steps: &[GateStep]) -> Self {
        let workspace = steps.contains(&GateStep::WorkspaceTests);
        let mut selection = TestSelection {
            workspace,
            ..TestSelection::default()
        };
        let mut native = workspace;
        for step in steps {
            if let Some(regression) = regression::get(*step) {
                native |= regression.native;
                if !workspace {
                    selection.library |= regression.library;
                    selection
                        .binaries
                        .extend(regression::binaries(*step).iter().copied());
                    selection
                        .integrations
                        .extend(regression.tests.iter().copied());
                }
            }
        }

        let mut checks = BTreeSet::new();
        let mut tasks = Vec::new();
        let mut tests_scheduled = false;
        for step in steps {
            let regression = regression::get(*step);
            if regression.as_ref().is_some_and(|entry| entry.snapshots)
                && checks.insert(GateStep::VirSnapshots)
            {
                tasks.push(Task::Check(GateStep::VirSnapshots));
            }
            if *step != GateStep::WorkspaceTests && checks.insert(*step) {
                tasks.push(Task::Check(*step));
            }
            // With a workspace pass, focused stages only contribute checks.
            // Without one, union their targets into a single focused cargo run.
            if !tests_scheduled
                && (*step == GateStep::WorkspaceTests || (!workspace && regression.is_some()))
            {
                tasks.push(Task::Tests(selection.clone()));
                tests_scheduled = true;
            }
        }
        Self { native, tasks }
    }
}

pub(super) fn rust_steps() -> Vec<GateStep> {
    RELEASE_GATE.to_vec()
}

pub(super) fn run(root: &Path, steps: &[GateStep]) -> Result<(), Box<dyn Error>> {
    let plan = GatePlan::new(steps);
    if plan.native {
        super::require_native_acceptance_host()?;
    }
    for task in plan.tasks {
        match task {
            Task::Tests(selection) => {
                let args = selection.cargo_args();
                println!("==> cargo {}", args.join(" "));
                super::run_cargo(root, &args)?;
            }
            Task::Check(step) => {
                println!("==> {step:?}");
                run_check(root, step)?;
            }
        }
    }
    Ok(())
}

fn run_check(root: &Path, step: GateStep) -> Result<(), Box<dyn Error>> {
    match step {
        GateStep::VirSnapshots => super::stage4::check(root),
        GateStep::Format => super::run_cargo(root, &["fmt", "--all", "--", "--check"]),
        GateStep::FrontendFuzz => super::run_frontend_fuzz(root),
        GateStep::VerifierFuzz => super::run_verifier_fuzz(root),
        GateStep::Clippy => super::run_cargo(
            root,
            &[
                "clippy",
                "--workspace",
                "--all-targets",
                "--all-features",
                "--",
                "-D",
                "warnings",
            ],
        ),
        GateStep::Rustdoc => super::run_rustdoc(root),
        _ => {
            let entry =
                regression::get(step).ok_or_else(|| format!("missing check for {step:?}"))?;
            (entry.check)(root)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complete_gate_runs_tests_once_without_losing_stage_checks() {
        let plan = GatePlan::new(STAGE7_GATE);
        assert!(plan.native);
        assert_eq!(
            plan.tasks
                .iter()
                .filter(|task| matches!(task, Task::Tests(_)))
                .count(),
            1
        );
        assert!(plan.tasks.contains(&Task::Tests(TestSelection {
            workspace: true,
            ..Default::default()
        })));
        for step in STAGE7_GATE {
            if *step != GateStep::WorkspaceTests {
                assert_eq!(
                    plan.tasks
                        .iter()
                        .filter(|task| **task == Task::Check(*step))
                        .count(),
                    1,
                    "{step:?}"
                );
            }
        }
        assert_eq!(plan, GatePlan::new(STAGE7_GATE));
    }

    #[test]
    fn focused_gate_keeps_its_checks_snapshots_and_exact_test_targets() {
        for step in STAGE7_GATE {
            let Some(regression) = regression::get(*step) else {
                continue;
            };
            let plan = GatePlan::new(&[*step]);
            assert!(plan.tasks.contains(&Task::Check(*step)));
            assert_eq!(plan.native, regression.native);
            assert_eq!(
                plan.tasks.contains(&Task::Check(GateStep::VirSnapshots)),
                regression.snapshots
            );
            assert!(plan.tasks.contains(&Task::Tests(TestSelection {
                workspace: false,
                library: regression.library,
                binaries: regression::binaries(*step).iter().copied().collect(),
                integrations: regression.tests.iter().copied().collect(),
            })));
        }
    }

    #[test]
    fn overlapping_focused_selections_are_unioned_and_workspace_dominates_in_any_order() {
        let focused = [
            GateStep::Place,
            GateStep::Phase736EnumConstruction,
            GateStep::Place,
            GateStep::Phase773VerifyPreview,
            GateStep::Phase773VerifyPreview,
            GateStep::Phase774AutoMemoryCorpus,
            GateStep::Phase774AutoMemoryCorpus,
            GateStep::Phase775VerifyFailClosed,
            GateStep::Phase775VerifyFailClosed,
        ];
        let plan = GatePlan::new(&focused);
        let selections: Vec<_> = plan
            .tasks
            .iter()
            .filter_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .collect();
        assert_eq!(selections.len(), 1);
        let args = selections[0].cargo_args();
        assert_eq!(args.iter().filter(|arg| **arg == "--lib").count(), 1);
        assert_eq!(
            args.iter()
                .filter(|arg| **arg == "native_acceptance")
                .count(),
            1
        );
        assert!(args.contains(&"hir_place") && args.contains(&"frontend_enum_construction"));
        assert_eq!(
            args.iter()
                .filter(|arg| **arg == "auto_memory_corpus")
                .count(),
            1
        );
        assert_eq!(args.iter().filter(|arg| **arg == "--bin").count(), 1);
        assert_eq!(
            args.iter()
                .filter(|arg| **arg == "verification_fail_closed")
                .count(),
            1
        );
        assert_eq!(args.iter().filter(|arg| **arg == "nera").count(), 1);
        for steps in [
            [GateStep::Place, GateStep::WorkspaceTests],
            [GateStep::WorkspaceTests, GateStep::Place],
            [GateStep::Phase773VerifyPreview, GateStep::WorkspaceTests],
            [GateStep::WorkspaceTests, GateStep::Phase773VerifyPreview],
            [GateStep::Phase774AutoMemoryCorpus, GateStep::WorkspaceTests],
            [GateStep::WorkspaceTests, GateStep::Phase774AutoMemoryCorpus],
            [GateStep::Phase775VerifyFailClosed, GateStep::WorkspaceTests],
            [GateStep::WorkspaceTests, GateStep::Phase775VerifyFailClosed],
        ] {
            let plan = GatePlan::new(&steps);
            let tests: Vec<_> = plan
                .tasks
                .iter()
                .filter_map(|task| match task {
                    Task::Tests(selection) => Some(selection.cargo_args()),
                    _ => None,
                })
                .collect();
            assert_eq!(tests, [vec!["test", "--workspace"]]);
        }
    }

    #[test]
    fn rust_ci_uses_the_documentation_free_release_gate() {
        assert_eq!(rust_steps().as_slice(), RELEASE_GATE);
        assert!(rust_steps().contains(&GateStep::WorkspaceTests));
        assert!(rust_steps().contains(&GateStep::FrontendFuzz));
        assert!(rust_steps().contains(&GateStep::VerifierFuzz));
        assert!(rust_steps().contains(&GateStep::Clippy));
        assert!(rust_steps().contains(&GateStep::Rustdoc));
        assert!(!rust_steps().contains(&GateStep::Phase743RelationCfg));
        assert!(GatePlan::new(&[]).tasks.is_empty());
    }

    #[test]
    fn preview_acceptance_is_the_union_of_previous_observers_not_six_test_runs() {
        let previous = GatePlan::new(&[
            GateStep::Phase771VerifyReport,
            GateStep::Phase772SourceDiagnostics,
            GateStep::Phase773VerifyPreview,
            GateStep::Phase774AutoMemoryCorpus,
            GateStep::Phase775VerifyFailClosed,
        ]);
        let final_plan = GatePlan::new(&[GateStep::Phase776VerifyAcceptance]);
        let selections = |p: &GatePlan| {
            p.tasks
                .iter()
                .filter_map(|t| match t {
                    Task::Tests(s) => Some(s.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(selections(&final_plan).len(), 1);
        assert_eq!(selections(&final_plan), selections(&previous));
        assert_eq!(final_plan.native, previous.native);
    }

    #[test]
    fn catalog_targets_exist_even_when_workspace_subsumes_their_execution() {
        let root = super::super::workspace_root();
        for step in STAGE7_GATE {
            let Some(regression) = regression::get(*step) else {
                continue;
            };
            assert!(
                regression.library || !regression.tests.is_empty(),
                "{step:?}: empty focused selection"
            );
            let mut targets = BTreeSet::new();
            for target in regression.tests {
                assert!(
                    targets.insert(target),
                    "{step:?}: duplicate target {target}"
                );
                assert!(
                    root.join("tests").join(format!("{target}.rs")).is_file(),
                    "{step:?}: missing target {target}"
                );
            }
        }
    }

    #[test]
    fn a_stage_specific_check_still_fails_without_its_required_document() {
        // No command is executed: the metadata check must report its own error.
        let missing_root = super::super::workspace_root().join("Cargo.toml");
        assert!(run_check(&missing_root, GateStep::Phase736EnumConstruction).is_err());
        assert!(run_check(&missing_root, GateStep::Phase7831ImplicitBorrowBaseline).is_err());
    }

    #[test]
    fn implicit_borrow_baseline_remains_available_outside_the_release_gate() {
        let step = GateStep::Phase7831ImplicitBorrowBaseline;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert_eq!(plan.tasks.len(), 2);
        assert_eq!(plan.tasks[0], Task::Check(step));
        let Task::Tests(selection) = &plan.tasks[1] else {
            panic!("baseline must execute tests, not just document checks");
        };
        assert!(!selection.workspace && !selection.library);
        assert!(selection.binaries.is_empty());
        assert_eq!(selection.integrations.len(), 8);
        assert!(selection.integrations.contains("implicit_borrow_baseline"));
        assert!(!STAGE7_GATE[..super::super::STAGE7_8_3_GATE_END].contains(&step));
        assert!(STAGE7_GATE.contains(&step));
        assert!(!rust_steps().contains(&step));
    }

    #[test]
    fn borrow_mapping_gate_covers_schema_consumers_without_workspace_or_fuzz() {
        let step = GateStep::Phase7832BorrowInterfaceMapping;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert_eq!(plan.tasks.len(), 3);
        assert!(plan.tasks.contains(&Task::Check(GateStep::VirSnapshots)));
        assert!(plan.tasks.contains(&Task::Check(step)));
        let selection = plan
            .tasks
            .iter()
            .find_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .unwrap();
        assert!(!selection.workspace);
        assert!(selection.library);
        for target in [
            "borrow_interface_mapping",
            "hir_regions",
            "aggregate_abi",
            "loan_consumers",
            "stage7_borrow_acceptance",
            "generic_instances",
        ] {
            assert!(selection.integrations.contains(target), "{target}");
        }
    }

    #[test]
    fn implicit_borrow_inference_gate_is_focused_and_native() {
        let step = GateStep::Phase7833ImplicitBorrowInference;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert_eq!(plan.tasks.len(), 2);
        assert!(plan.tasks.contains(&Task::Check(step)));
        let selection = plan
            .tasks
            .iter()
            .find_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .unwrap();
        assert!(!selection.workspace);
        assert!(selection.library);
        for target in [
            "implicit_borrow_inference",
            "implicit_borrow_baseline",
            "borrow_interface_mapping",
            "summary_borrows",
            "loan_consumers",
            "generic_instances",
            "module_program",
        ] {
            assert!(selection.integrations.contains(target), "{target}");
        }
    }

    #[test]
    fn conditional_borrow_inference_gate_is_focused_and_versioned() {
        let step = GateStep::Phase7834ConditionalBorrowInference;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert!(plan.tasks.contains(&Task::Check(GateStep::VirSnapshots)));
        assert!(plan.tasks.contains(&Task::Check(step)));
        let selection = plan
            .tasks
            .iter()
            .find_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .unwrap();
        assert!(!selection.workspace);
        assert!(selection.library);
        assert!(
            selection
                .integrations
                .contains("conditional_borrow_inference")
        );
        assert!(selection.integrations.contains("summary_borrows"));
    }

    #[test]
    fn borrow_projection_gate_is_focused_versioned_and_native() {
        let step = GateStep::Phase7835BorrowProjection;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert!(plan.tasks.contains(&Task::Check(GateStep::VirSnapshots)));
        assert!(plan.tasks.contains(&Task::Check(step)));
        let selection = plan
            .tasks
            .iter()
            .find_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .unwrap();
        assert!(!selection.workspace);
        assert!(selection.library);
        for target in [
            "borrow_projection",
            "borrow_interface_mapping",
            "frontend_safe_slice",
            "summary_borrows",
            "vir_unit_baseline",
        ] {
            assert!(selection.integrations.contains(target), "{target}");
        }
    }

    #[test]
    fn borrow_source_scc_gate_reuses_recursive_and_loop_consumers() {
        let step = GateStep::Phase7836BorrowSourceScc;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert!(!plan.tasks.contains(&Task::Check(GateStep::VirSnapshots)));
        assert!(plan.tasks.contains(&Task::Check(step)));
        let selection = plan
            .tasks
            .iter()
            .find_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .unwrap();
        assert!(selection.library);
        for target in [
            "borrow_source_scc",
            "implicit_borrow_inference",
            "summary_recursive",
            "frontend_loops",
        ] {
            assert!(selection.integrations.contains(target), "{target}");
        }
    }

    #[test]
    fn implicit_lifetime_syntax_gate_keeps_internal_borrow_consumers() {
        let step = GateStep::Phase7837ImplicitLifetimeSyntax;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert!(plan.tasks.contains(&Task::Check(step)));
        let selection = plan
            .tasks
            .iter()
            .find_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .unwrap();
        assert!(selection.library);
        for target in [
            "implicit_lifetime_syntax",
            "generic_instances",
            "module_program",
            "hir_regions",
            "summary_borrows",
        ] {
            assert!(selection.integrations.contains(target), "{target}");
        }
    }

    #[test]
    fn implicit_borrow_acceptance_unifies_consumers_without_workspace_or_fuzz() {
        let step = GateStep::Phase7838ImplicitBorrowAcceptance;
        let plan = GatePlan::new(&[step]);
        assert!(plan.native);
        assert!(plan.tasks.contains(&Task::Check(GateStep::VirSnapshots)));
        assert!(plan.tasks.contains(&Task::Check(step)));
        let selection = plan
            .tasks
            .iter()
            .find_map(|task| match task {
                Task::Tests(selection) => Some(selection),
                _ => None,
            })
            .unwrap();
        assert!(!selection.workspace);
        assert!(selection.library);
        for target in [
            "implicit_borrow_acceptance",
            "borrow_projection",
            "borrow_source_scc",
            "verification_text",
            "module_program",
            "ghost_non_interference",
            "native_acceptance",
        ] {
            assert!(selection.integrations.contains(target), "{target}");
        }
        assert!(!plan.tasks.contains(&Task::Check(GateStep::FrontendFuzz)));
        assert!(!plan.tasks.contains(&Task::Check(GateStep::VerifierFuzz)));
    }
}
