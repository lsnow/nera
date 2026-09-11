//! Real process policy tests; semantic fixtures remain owned by the existing suites.
use std::fs;
use std::process::Stdio;

use nera::SourceFile;
use nera::verification::{PreviewOutcome, TextReportMode, render_text, verify_source};

#[path = "support/cli_process.rs"]
mod cli_process;
use cli_process::{Fixture, run};

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
