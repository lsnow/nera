//! Smoke-test the public walkthrough, not a second semantic regression matrix.
#[path = "support/cli_process.rs"]
mod cli_process;

use cli_process::{Fixture, run};

#[test]
fn examples_match_the_documented_cli_results() {
    let fixture = Fixture::new();
    for (name, source, valid) in [
        ("memory", include_str!("../examples/memory.nera"), true),
        ("frontend", include_str!("../examples/frontend.nera"), true),
        (
            "core-subset",
            include_str!("../examples/core-subset.nera"),
            true,
        ),
        (
            "execution",
            include_str!("../examples/execution.nera"),
            true,
        ),
        (
            "use-after-free",
            include_str!("../examples/use-after-free.nera"),
            false,
        ),
        (
            "structured-data",
            include_str!("../examples/structured-data.nera"),
            true,
        ),
        (
            "inferred-borrows",
            include_str!("../examples/inferred-borrows.nera"),
            true,
        ),
        (
            "loop-contracts",
            include_str!("../examples/loop-contracts.nera"),
            true,
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), source);
        let frontend = run(fixture.command().arg("frontend").arg(&path));
        assert!(frontend.status.success(), "{name}: {frontend:?}");
        let verification = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(
            verification.status.code(),
            Some(if valid { 0 } else { 1 }),
            "{name}: {verification:?}"
        );
        let text = String::from_utf8_lossy(&verification.stdout);
        assert!(
            text.contains(if valid { "Checked" } else { "Unproved" }),
            "{name}: {text}"
        );
        if valid {
            let execution = run(fixture.command().arg("run").arg(&path));
            assert!(execution.status.success(), "{name}: {execution:?}");
            assert!(
                String::from_utf8_lossy(&execution.stdout)
                    .lines()
                    .any(|line| line == "return: 42"),
                "{name}: {execution:?}"
            );
        }
    }
}
