//! Real process policy tests; semantic fixtures remain owned by the existing suites.
use std::fs;
use std::process::Stdio;

use nera::SourceFile;
use nera::verification::{PreviewOutcome, TextReportMode, render_text, verify_source};

#[path = "support/cli_process.rs"]
mod cli_process;
use cli_process::{Fixture, run};

#[test]
fn loop_arena_cli_distinguishes_initialization_from_remaining_storage() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/loop-arena-initialize.nera");
    for (text, code) in [
        (source.to_owned(), 0),
        (source.replace("let value = p[1];", "let value = p[6];"), 1),
    ] {
        let path = fixture.file("loop-arena.nera", text);
        let output = run(fixture.command().arg("verify").arg("--explain").arg(path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        let text = String::from_utf8_lossy(&output.stdout);
        assert!(text.contains("loop-arena.nera"), "{text}");
        assert!(
            text.contains(if code == 0 { "Checked" } else { "initialized" }),
            "{text}"
        );
    }
}

#[test]
fn loop_contract_cli_reports_callee_and_iteration_obligations() {
    #[path = "support/loop_composition.rs"]
    mod cases;
    let fixture = Fixture::new();
    let args = [
        "--module",
        "app=app.nera",
        "--module",
        "ops=ops.nera",
        "--entry",
        "app::main",
    ];
    for (app, ops, code, explicit_invariants) in [
        (cases::APP.to_owned(), cases::OPS.to_owned(), 0, true),
        (
            cases::erase_invariants(cases::APP),
            cases::OPS.to_owned(),
            0,
            false,
        ),
        (
            cases::APP.to_owned(),
            cases::OPS.replace("readable(result,0..1)", "readable(result,0..2)"),
            1,
            true,
        ),
    ] {
        assert_eq!(
            cases::session(&app, &ops)
                .verify("app")
                .unwrap()
                .is_checked(),
            code == 0
        );
        fixture.file("app.nera", app);
        fixture.file("ops.nera", ops);
        let out = run(fixture.command().arg("verify").arg("--explain").args(args));
        assert_eq!(out.status.code(), Some(code), "{out:?}");
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(
            text.contains(if code == 0 { "Checked" } else { "ops.nera" }),
            "{text}"
        );
        if code == 0 {
            assert!(text.contains("callee precondition holds for these arguments"));
            // Automatic analysis may prove the loop without selecting invariant
            // candidates. Explicit clauses must still report both proof sites.
            if explicit_invariants {
                assert!(text.contains("loop invariant holds on entry"));
                assert!(text.contains("loop invariant is preserved on the back edge"));
            }
        }
    }
}

#[test]
fn arena_contract_cli_distinguishes_normal_capacity_failure_from_bad_contracts() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/contract-arena.nera");
    for (name, text, code) in [
        ("arena", source.to_owned(), 0),
        (
            "arena-bad",
            source.replace("return false;", "return true;"),
            1,
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), text);
        let output = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains(if code == 0 {
                "Checked"
            } else {
                "postcondition"
            }),
            "{output:?}"
        );
        if code == 0 {
            let execution = run(fixture.command().arg("run").arg(&path));
            assert!(execution.status.success(), "{execution:?}");
            assert!(String::from_utf8_lossy(&execution.stdout).contains("49"));
        }
    }
}

#[test]
fn composed_contract_cli_keeps_module_diagnostics_and_exit_status() {
    #[path = "support/contract_composition.rs"]
    mod cases;
    let fixture = Fixture::new();
    // Also exercises the same source-snapshot builder used by verifier/native tests.
    assert!(
        cases::session(&[
            ("app", cases::APP),
            ("left", cases::LEFT),
            ("right", cases::RIGHT)
        ])
        .verify("app")
        .unwrap()
        .is_checked()
    );
    fixture.file("app.nera", cases::APP);
    fixture.file("left.nera", cases::LEFT);
    let args = [
        "--module",
        "app=app.nera",
        "--module",
        "left=left.nera",
        "--module",
        "right=right.nera",
        "--entry",
        "app::main",
    ];
    for (right, code) in [
        (cases::RIGHT.to_owned(), 0),
        (
            cases::RIGHT.replace("len(result)==N", "len(result)==2usize"),
            1,
        ),
    ] {
        fixture.file("right.nera", right);
        let output = run(fixture.command().arg("verify").args(args));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains(if code == 0 { "Checked" } else { "right.nera" }),
            "{output:?}"
        );
        let execution = run(fixture.command().arg("run").args(args));
        assert!(execution.status.success(), "{execution:?}");
        assert!(String::from_utf8_lossy(&execution.stdout).contains("42"));
    }
}

#[test]
fn recursive_contract_cli_requires_closed_component_evidence() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/contract-recursive.nera");
    for (name, text, code) in [
        ("recursive-ok", source.to_owned(), 0),
        ("recursive-bad", source.replace("return 42", "return 41"), 1),
    ] {
        let path = fixture.file(format!("{name}.nera"), text);
        let output = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains(if code == 0 {
                "Checked"
            } else {
                "Unproved"
            }),
            "{output:?}"
        );
    }
}

#[test]
fn frame_contract_cli_reports_declared_effect_failures() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/contract-frame.nera");
    for (name, text, code, message) in [
        ("frame-ok", source.to_owned(), 0, "Checked"),
        (
            "frame-bad",
            source.replace("writes p[1..2];", "writes ();"),
            1,
            "writes` frame",
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), text);
        let output = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains(message),
            "{output:?}"
        );
        let execution = run(fixture.command().arg("run").arg(&path));
        assert!(execution.status.success(), "{execution:?}");
        assert!(String::from_utf8_lossy(&execution.stdout).contains("unverified"));
    }
}

#[test]
fn resource_contract_cli_checks_calls_and_returns_without_runtime_checks() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/contract-resources.nera");
    for (name, text, code, message) in [
        ("resources-ok", source.to_owned(), 0, "Checked"),
        (
            "resources-call",
            source.replace("[0..2]", "[0..1]"),
            1,
            "requires",
        ),
        (
            "resources-return",
            source.replace("0usize..len(p)", "0usize..3usize"),
            1,
            "postcondition",
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), text);
        let output = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains(message),
            "{output:?}"
        );
        if code != 0 {
            let execution = run(fixture.command().arg("run").arg(&path));
            assert!(execution.status.success(), "{execution:?}");
            assert!(String::from_utf8_lossy(&execution.stdout).contains("unverified"));
        }
    }
}

#[test]
fn memory_contract_cli_reports_source_call_and_return_failures() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/contract-memory.nera");
    for (name, text, code, message) in [
        ("memory-ok", source.to_owned(), 0, "Checked"),
        (
            "memory-caller",
            source.replace("value = 41", "value = 40"),
            1,
            "requires",
        ),
        (
            "memory-callee",
            source.replace("before + 1", "before + 2"),
            1,
            "postcondition",
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), text);
        let output = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains(message) && stdout.contains(name),
            "{output:?}"
        );
    }
}

#[test]
fn pure_contract_cli_checks_calls_and_bodies_but_run_build_remain_unverified() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/contract-pure.nera");
    for (name, text, code, message) in [
        ("valid", source.to_owned(), 0, "Checked"),
        (
            "caller",
            source.replace("successor(40)", "successor(42)"),
            1,
            "requires",
        ),
        (
            "callee",
            source.replace("return value + 1;", "return value;"),
            1,
            "postcondition",
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), text);
        let output = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains(message), "{output:?}");
        assert!(stdout.contains(&format!("{name}.nera")), "{output:?}");
        if name == "callee" {
            let output = run(fixture.command().arg("run").arg(&path));
            assert!(output.status.success(), "{output:?}");
            assert!(String::from_utf8_lossy(&output.stdout).contains("unverified"));
            let output = run(fixture
                .command()
                .args(["build", "--emit", "asm"])
                .arg(&path)
                .arg("-o")
                .arg(fixture.0.join("contract.s")));
            assert!(output.status.success(), "{output:?}");
            assert!(String::from_utf8_lossy(&output.stdout).contains("built (unverified)"));
        }
    }
}

#[test]
fn local_arena_cli_checks_the_whole_program_not_just_prove_status() {
    let fixture = Fixture::new();
    let source = include_str!("../spec/cases/verify/spec-arena-local.nera");
    for (name, source, expected) in [
        ("checked", source.to_owned(), 0),
        (
            "false",
            source.replace("assert second < 6usize;", "assert second > 6usize;"),
            1,
        ),
        (
            "uaf",
            source.replace(
                "return answer;",
                "let p=alloc<u64>(1); free(p); return *p + answer;",
            ),
            1,
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), source);
        let output = run(fixture.command().arg("verify").arg(path));
        assert_eq!(output.status.code(), Some(expected), "{output:?}");
    }
}

#[test]
fn local_assertions_have_real_exit_codes_and_execution_remains_unverified() {
    let fixture = Fixture::new();
    for (name, source, code, message) in [
        (
            "ok",
            "fn main()->u64 { assert 1<2; return 7; }",
            0,
            "Spec: Proven=1",
        ),
        (
            "false",
            "fn main()->u64 { assert false; return 7; }",
            1,
            "logical predicate is false",
        ),
        (
            "unknown",
            "fn main()->u64 { return f(1); } fn f(x:u64)->u64 { assert x<8; return x; }",
            1,
            "insufficient current-state facts",
        ),
        (
            "effect",
            "fn main()->u64 { assert f()==7; return 7; } fn f()->u64{return 7;}",
            2,
            "unsupported static assertion",
        ),
    ] {
        let path = fixture.file(format!("{name}.nera"), source);
        let output = run(fixture.command().arg("verify").arg(&path));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains(message),
            "{output:?}"
        );
        if name == "false" {
            let assembly = fixture.0.join("false-assert.s");
            let built = run(fixture
                .command()
                .args(["build", "--emit", "asm"])
                .arg(&path)
                .arg("-o")
                .arg(&assembly));
            assert!(built.status.success(), "{built:?}");
            assert!(
                String::from_utf8_lossy(&built.stdout).contains("built (unverified)"),
                "{built:?}"
            );
            let output = run(fixture.command().arg("run").arg(&path));
            assert!(output.status.success(), "{output:?}");
            assert!(
                String::from_utf8_lossy(&output.stdout).contains("unverified"),
                "{output:?}"
            );
        }
    }
}

#[test]
fn source_process_reports_equal_the_library_for_success_failures_and_unsupported() {
    let fixture = Fixture::new();
    let cases: &[(&[u8], u8)] = &[
        (b"fn main()->u64 { return 42; }", 0),
        (include_bytes!("../spec/cases/verify/summary-calls.nera"), 0),
        (include_bytes!("../spec/cases/verify/uaf.nera"), 1),
        (b"fn get(i:usize)->u64 { let a=[42]; return a[i]; }", 1),
        // Uncalled functions still participate in the whole-unit verdict.
        (b"fn main()->u64 { return 42; } fn bad()->u64 { let a=[42]; let i=2usize; return a[i]; }", 1),
        ("fn 名字()->u64 { return 42; }".as_bytes(), 2),
        (b"fn main( {", 2),
        (b"", 2),
        (&[0xff], 2),
    ];
    for (i, &(bytes, code)) in cases.iter().enumerate() {
        let path = fixture.file(format!("case {i}.nera"), bytes);
        let source = SourceFile::load(&path).unwrap();
        let preview = verify_source(&source, Default::default());
        assert_eq!(preview.outcome() == PreviewOutcome::Checked, code == 0);
        for mode in [TextReportMode::Summary, TextReportMode::Explain] {
            let mut command = fixture.command();
            command.arg("verify");
            if mode == TextReportMode::Explain {
                command.arg("--explain");
            }
            let output = run(command.arg(&path));
            assert_eq!(output.status.code(), Some(i32::from(code)), "{output:?}");
            assert_eq!(output.stdout, render_text(&preview, mode).as_bytes());
            assert!(
                output.stderr.is_empty(),
                "reports, including rejection, belong to stdout"
            );
        }
        assert_eq!(fs::read(&path).unwrap(), bytes);
    }
}

#[test]
fn help_and_invalid_arguments_have_unambiguous_streams_and_exit_codes() {
    let fixture = Fixture::new();
    for args in [
        vec!["--help"],
        vec!["verify", "--help"],
        vec!["verify", "-h"],
    ] {
        let output = run(fixture.command().args(args));
        assert_eq!(output.status.code(), Some(0));
        assert!(String::from_utf8_lossy(&output.stdout).contains("nera verify"));
        assert!(output.stderr.is_empty());
    }
    for args in [
        vec![],
        vec!["--explain"],
        vec!["--"],
        vec![""],
        vec!["--explain", "--explain", "missing.nera"],
        vec!["one.nera", "two.nera"],
        vec!["--unknown", "missing.nera"],
        vec!["--help", "missing.nera"],
        vec!["--help", "--help"],
        vec!["--explain", "--help"],
        vec!["missing.nera", "--help"],
        vec!["--ignore-unknown", "missing.nera"],
        vec!["--trust", "missing.nera"],
        vec!["--max-block-visits", "0", "missing.nera"],
    ] {
        let output = run(fixture.command().arg("verify").args(&args));
        assert_eq!(output.status.code(), Some(2), "{args:?}: {output:?}");
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.starts_with("error:"));
        assert!(
            !stderr.contains("cannot read"),
            "validate arguments before I/O"
        );
    }
}

#[test]
fn input_io_failures_have_no_fabricated_analysis_report() {
    let fixture = Fixture::new();
    for path in [fixture.0.join("not present.nera"), fixture.0.clone()] {
        let output = run(fixture.command().arg("verify").arg(path));
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("cannot read"));
    }
}

#[test]
fn argument_order_and_end_of_options_preserve_source_path_identity() {
    let fixture = Fixture::new();
    for (name, args, mode) in [
        (
            "space name.nera",
            vec!["space name.nera", "--explain"],
            TextReportMode::Explain,
        ),
        (
            "--explain",
            vec!["--", "--explain"],
            TextReportMode::Summary,
        ),
        (
            "--help",
            vec!["--explain", "--", "--help"],
            TextReportMode::Explain,
        ),
    ] {
        let bytes = b"fn main()->u64 { return 7; }";
        fixture.file(name, bytes);
        let source = SourceFile::new(name, bytes);
        let expected = render_text(&verify_source(&source, Default::default()), mode);
        let output = run(fixture.command().arg("verify").args(args));
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, expected.as_bytes());
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn divergent_source_is_analyzed_without_execution_or_external_tools() {
    let fixture = Fixture::new();
    let path = fixture.file("divergent.nera", "fn main()->u64 { return main(); }");
    let empty_path = fixture.0.join("empty-path");
    fs::create_dir(&empty_path).unwrap();
    let source = SourceFile::load(&path).unwrap();
    let preview = verify_source(&source, Default::default());
    assert!(
        preview.is_checked(),
        "memory safety does not require termination: {preview:?}"
    );
    for mode in [TextReportMode::Summary, TextReportMode::Explain] {
        let mut command = fixture.command();
        command.arg("verify").env("PATH", &empty_path);
        for key in ["CC", "AS", "LD", "LEAN", "LAKE"] {
            command.env(key, empty_path.join("unavailable-tool"));
        }
        if mode == TextReportMode::Explain {
            command.arg("--explain");
        }
        let output = run(command.arg(&path));
        assert_eq!(output.status.code(), Some(0), "{output:?}");
        assert_eq!(output.stdout, render_text(&preview, mode).as_bytes());
        assert!(output.stderr.is_empty());
    }
    assert_eq!(
        fs::read_dir(&fixture.0).unwrap().count(),
        2,
        "no generated artifact"
    );
    assert_eq!(fs::read_dir(empty_path).unwrap().count(), 0);
    assert_eq!(fs::read(path).unwrap(), source.bytes());
}

#[test]
fn frontend_and_run_remain_untrusted_and_unverified() {
    let fixture = Fixture::new();
    let path = fixture.file("legacy.nera", "fn main()->u64 { return 42; }");
    let frontend = run(fixture.command().arg("frontend").arg(&path));
    assert_eq!(frontend.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&frontend.stdout).contains("accepted-proposal (untrusted)"));
    let execution = run(fixture.command().arg("run").arg(path));
    assert_eq!(execution.status.code(), Some(0));
    let text = String::from_utf8_lossy(&execution.stdout);
    assert!(text.contains("status: executed (unverified)"));
    assert!(text.contains("return: 42"));
    assert!(!text.contains("verification preview"));
}

#[cfg(unix)]
#[test]
fn non_utf8_source_paths_are_not_lossily_reinterpreted() {
    use std::os::unix::ffi::OsStringExt;
    let fixture = Fixture::new();
    let path = fixture.file(
        std::ffi::OsString::from_vec(b"name\xff.nera".to_vec()),
        b"fn main()->u64 { return 42; }",
    );
    let source = SourceFile::load(&path).unwrap();
    let output = run(fixture.command().arg("verify").arg(&path));
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        output.stdout,
        render_text(
            &verify_source(&source, Default::default()),
            TextReportMode::Summary
        )
        .as_bytes()
    );
    assert!(output.stderr.is_empty());
}

#[cfg(unix)]
#[test]
fn broken_stdout_is_an_io_failure_not_a_panic_or_success() {
    use std::os::fd::OwnedFd;
    use std::os::unix::net::UnixStream;
    let fixture = Fixture::new();
    let path = fixture.file("output.nera", "fn main()->u64 { return 42; }");
    let (writer, reader) = UnixStream::pair().unwrap();
    drop(reader);
    let output = fixture
        .command()
        .arg("verify")
        .arg(path)
        .stdout(Stdio::from(OwnedFd::from(writer)))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("cannot write verification output"));
    assert!(!stderr.contains("panicked"));
}
