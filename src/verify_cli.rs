//! Single-file preview driver. No interpreter/backend/toolchain dependency here.
use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use nera::SourceFile;
use nera::verification::{TextReportMode, verify_source, write_report};

const HELP: &str = "Nera experimental verification preview

Usage:
  nera verify [--explain] <SOURCE>
  nera verify [--explain] -- <SOURCE>
  nera verify -h | --help
  nera verify [--explain] --module NAME=PATH ... --entry MODULE::FUNCTION

Options:
  --explain  Include all obligations and diagnostic evidence
  --         End options (for source paths starting with '-')

Verifies every function using the current default profile and budgets.
Does not execute the program, invoke system tools or Lean, or produce an artifact.
No flags can disable checks, ignore Unknown, override budgets, or add trust.

Exit codes:
  0  Checked, relative to the reported profile and registered assumptions
  1  Unproved (Refuted/Unknown) or verification-unsupported
  2  Bad arguments, input/front-end/resolution failure, analysis abort/error, or I/O failure

Source analysis reports go to stdout, including rejected/incomplete reports.
Argument, file-read and report-write errors go to stderr.
Text is experimental, not a stable machine format or proof certificate.
";

#[derive(Debug, PartialEq, Eq)]
enum Options {
    Help,
    Source { path: PathBuf, mode: TextReportMode },
}

fn parse(arguments: impl Iterator<Item = OsString>) -> Result<Options, String> {
    let arguments: Vec<_> = arguments.collect();
    if arguments.len() == 1 && matches!(arguments[0].to_str(), Some("--help" | "-h")) {
        return Ok(Options::Help);
    }
    let mut path = None;
    let mut explain = false;
    let mut options = true;
    for argument in arguments {
        if options && argument == OsStr::new("--") {
            options = false;
        } else if options && argument == OsStr::new("--explain") {
            if explain {
                return Err("`--explain` may only be specified once".into());
            }
            explain = true;
        } else if options && argument.to_string_lossy().starts_with('-') {
            return Err(format!("unknown or misplaced verify option {argument:?}"));
        } else if argument.is_empty() {
            return Err("source path must not be empty".into());
        } else if path.replace(PathBuf::from(&argument)).is_some() {
            return Err(format!("unexpected second source path {argument:?}"));
        }
    }
    Ok(Options::Source {
        path: path.ok_or("`nera verify` requires a source path")?,
        mode: if explain {
            TextReportMode::Explain
        } else {
            TextReportMode::Summary
        },
    })
}

pub(super) fn run(arguments: impl Iterator<Item = OsString>) -> ExitCode {
    let mut output = io::stdout().lock();
    match command(arguments, &mut output) {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            let _ = writeln!(
                io::stderr().lock(),
                "error: {error}\ntry 'nera verify --help' for more information"
            );
            ExitCode::from(2)
        }
    }
}

fn command(
    arguments: impl Iterator<Item = OsString>,
    output: &mut impl Write,
) -> Result<u8, String> {
    let (text, code) = match parse(arguments)? {
        Options::Help => (HELP.to_owned(), 0),
        Options::Source { path, mode } => {
            let source =
                SourceFile::load(&path).map_err(|e| format!("cannot read {path:?}: {e}"))?;
            let preview = verify_source(&source, Default::default());
            return write_report(&preview, mode, output)
                .map_err(|e| format!("cannot write verification output: {e}"));
        }
    };
    output
        .write_all(text.as_bytes())
        .and_then(|()| output.flush())
        .map_err(|e| format!("cannot write verification output: {e}"))?;
    Ok(code)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn output_errors_do_not_panic_or_report_success() {
        struct BrokenOutput;
        impl Write for BrokenOutput {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                Err(io::ErrorKind::BrokenPipe.into())
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        assert!(
            command(["--help".into()].into_iter(), &mut BrokenOutput)
                .unwrap_err()
                .contains("cannot write verification output")
        );
        struct FlushFailure;
        impl Write for FlushFailure {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                Ok(bytes.len())
            }
            fn flush(&mut self) -> io::Result<()> {
                Err(io::ErrorKind::BrokenPipe.into())
            }
        }
        assert!(command(["--help".into()].into_iter(), &mut FlushFailure).is_err());
    }
}
