use std::env;
use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64SystemToolchain};
use nera::{
    FrontendOutput, FrontendStatus, SourceFile, VirRuntimeValue, analyze,
    current_capability_profile, interpret,
};

mod module_cli;
mod verify_cli;

const HELP: &str = "Nera compiler

Usage:
  nera frontend <SOURCE>
  nera verify [--explain] <SOURCE>
  nera run <SOURCE>
  nera build --emit <asm|obj|exe> <SOURCE> -o <OUTPUT>
  nera <frontend|verify|run|build> --module NAME=PATH ... --entry MODULE::FUNCTION
  nera [OPTIONS]

Commands:
  frontend <SOURCE>  Produce AST, typed HIR and validated VIR
  verify             Experimental memory-verification preview (does not execute code)
  run <SOURCE>       Resolve and interpret validated VIR (execution remains unverified)
  build              Build an x86_64 Linux artifact (artifact remains unverified)

Options:
  -h, --help         Print help
  -V, --version      Print version

Module inputs are explicit and closed; no discovery or downloads. Build still
requires --emit and -o. Positional source input cannot be mixed with --module.

The `frontend` result is not a memory-safety result. `run` and `build` remain unverified.
`verify` reports profile-relative analysis, not a checked native artifact or a
compiler soundness theorem. See `nera verify --help` for preview exit codes.
";

fn main() -> ExitCode {
    let mut args = env::args_os();
    let _program = args.next();

    let Some(command) = args.next() else {
        print!("{HELP}");
        return ExitCode::SUCCESS;
    };
    if command == OsStr::new("-h") || command == OsStr::new("--help") {
        print!("{HELP}");
        return ExitCode::SUCCESS;
    }
    if command == OsStr::new("-V") || command == OsStr::new("--version") {
        println!("nera {}", env!("CARGO_PKG_VERSION"));
        return ExitCode::SUCCESS;
    }
    let args: Vec<_> = args.collect();
    match module_cli::extract(args) {
        Ok((Some(input), remaining)) => module_cli::run(&command, input, remaining),
        Ok((None, remaining)) => single_command(command, remaining.into_iter()),
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(2)
        }
    }
}

fn single_command(command: OsString, mut args: impl Iterator<Item = OsString>) -> ExitCode {
    if command == OsStr::new("build") {
        let options = match parse_build_options(args) {
            Ok(options) => options,
            Err(error) => {
                eprintln!("error: {error}");
                eprintln!("try 'nera --help' for more information");
                return ExitCode::from(2);
            }
        };
        return build_source(options);
    }
    if command == OsStr::new("verify") {
        return verify_cli::run(args);
    }
    if command == OsStr::new("frontend") || command == OsStr::new("run") {
        let Some(path) = args.next().map(PathBuf::from) else {
            eprintln!(
                "error: `nera {}` requires a source path",
                command.to_string_lossy()
            );
            return ExitCode::from(2);
        };
        if args.next().is_some() {
            eprintln!("error: unexpected argument after source path");
            return ExitCode::from(2);
        }
        return if command == OsStr::new("frontend") {
            run_frontend(path)
        } else {
            interpret_source(path)
        };
    }

    eprintln!("error: unknown command `{}`", command.to_string_lossy());
    eprintln!("try 'nera --help' for more information");
    ExitCode::from(2)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BuildEmit {
    Assembly,
    Object,
    Executable,
}

impl BuildEmit {
    fn parse(value: &OsStr) -> Option<Self> {
        if value == OsStr::new("asm") {
            Some(Self::Assembly)
        } else if value == OsStr::new("obj") {
            Some(Self::Object)
        } else if value == OsStr::new("exe") {
            Some(Self::Executable)
        } else {
            None
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::Assembly => "asm",
            Self::Object => "obj",
            Self::Executable => "exe",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BuildOptions {
    emit: BuildEmit,
    source: PathBuf,
    output: PathBuf,
}

fn parse_build_options(
    mut arguments: impl Iterator<Item = OsString>,
) -> Result<BuildOptions, String> {
    let mut emit = None;
    let mut source = None;
    let mut output = None;
    while let Some(argument) = arguments.next() {
        if argument == OsStr::new("--emit") {
            if emit.is_some() {
                return Err("`--emit` may only be specified once".to_owned());
            }
            let value = arguments
                .next()
                .ok_or_else(|| "`--emit` requires asm, obj or exe".to_owned())?;
            emit = Some(BuildEmit::parse(&value).ok_or_else(|| {
                format!(
                    "unsupported emit kind `{}`; expected asm, obj or exe",
                    value.to_string_lossy()
                )
            })?);
        } else if argument == OsStr::new("-o") {
            if output.is_some() {
                return Err("`-o` may only be specified once".to_owned());
            }
            output = Some(PathBuf::from(
                arguments
                    .next()
                    .ok_or_else(|| "`-o` requires an output path".to_owned())?,
            ));
        } else if argument.to_string_lossy().starts_with('-') {
            return Err(format!(
                "unknown build option `{}`",
                argument.to_string_lossy()
            ));
        } else if source.replace(PathBuf::from(&argument)).is_some() {
            return Err(format!(
                "unexpected second source path `{}`",
                argument.to_string_lossy()
            ));
        }
    }
    Ok(BuildOptions {
        emit: emit.ok_or_else(|| "`nera build` requires `--emit asm|obj|exe`".to_owned())?,
        source: source.ok_or_else(|| "`nera build` requires a source path".to_owned())?,
        output: output.ok_or_else(|| "`nera build` requires `-o OUTPUT`".to_owned())?,
    })
}

fn build_source(options: BuildOptions) -> ExitCode {
    if paths_refer_to_same_file(&options.source, &options.output) {
        eprintln!("error: source and output paths refer to the same file");
        return ExitCode::from(2);
    }
    let source = match SourceFile::load(&options.source) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("error: cannot read {}: {error}", options.source.display());
            return ExitCode::FAILURE;
        }
    };
    let frontend = analyze(&source);
    build_frontend(options, &frontend)
}

fn build_frontend(options: BuildOptions, frontend: &FrontendOutput) -> ExitCode {
    if frontend.status() != FrontendStatus::AcceptedProposal {
        eprintln!("status: {}", status_name(frontend.status()));
        print_frontend_issues(&options.source, frontend);
        return ExitCode::from(2);
    }
    let Some(vir) = frontend.vir() else {
        eprintln!("error: accepted frontend output did not contain validated VIR");
        return ExitCode::FAILURE;
    };
    let resolved = match vir.resolve() {
        Ok(resolved) => resolved,
        Err(error) => {
            let span = error.source_span();
            eprintln!(
                "resolution fault (unverified) {}:{}..{}: {error}",
                runtime_source_path(frontend, Some(error.function()), &options.source).display(),
                span.start(),
                span.end()
            );
            return ExitCode::FAILURE;
        }
    };
    let machine = match X86_64_UNKNOWN_LINUX_GNU.codegen_program(resolved.runtime()) {
        Ok(machine) => machine,
        Err(error) => {
            let category = if error.capability_failure_kind()
                == Some(nera::CapabilityFailureKind::TargetUnsupported)
            {
                "target-unsupported"
            } else {
                "native codegen fault"
            };
            if let Some(span) = error.source_span() {
                eprintln!(
                    "{category} (unverified) {}:{}..{}: {error}",
                    runtime_source_path(frontend, error.function(), &options.source).display(),
                    span.start(),
                    span.end()
                );
            } else {
                eprintln!("{category} (unverified): {error}");
            }
            return ExitCode::FAILURE;
        }
    };
    let assembly = match X86_64_UNKNOWN_LINUX_GNU.emit_assembly(&machine) {
        Ok(assembly) => assembly,
        Err(error) => {
            eprintln!("assembly emission fault (unverified): {error}");
            return ExitCode::FAILURE;
        }
    };

    let tools = X86_64SystemToolchain::default();
    let build = match options.emit {
        BuildEmit::Assembly => tools.write_assembly(&assembly, &options.output),
        BuildEmit::Object => tools.assemble(&assembly, &options.output),
        BuildEmit::Executable => tools.build_executable(&assembly, &options.output),
    };
    if let Err(error) = build {
        eprintln!("native tool failure (unverified): {error}");
        print_tool_stderr(error.stderr());
        return ExitCode::FAILURE;
    }
    println!("status: built (unverified)");
    print_capability_profile();
    println!("emit: {}", options.emit.name());
    println!("output: {}", options.output.display());
    ExitCode::SUCCESS
}

fn paths_refer_to_same_file(left: &Path, right: &Path) -> bool {
    left == right
        || match (left.canonicalize(), right.canonicalize()) {
            (Ok(left), Ok(right)) => left == right,
            _ => false,
        }
}

fn print_tool_stderr(stderr: &[u8]) {
    if stderr.is_empty() {
        return;
    }
    let mut terminal = io::stderr().lock();
    let _ = terminal.write_all(stderr);
    if !stderr.ends_with(b"\n") {
        let _ = terminal.write_all(b"\n");
    }
}

fn run_frontend(path: PathBuf) -> ExitCode {
    let source = match SourceFile::load(&path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("error: cannot read {}: {error}", path.display());
            return ExitCode::FAILURE;
        }
    };
    let output = analyze(&source);
    print_frontend(&path, source.len(), &output)
}

fn print_frontend(path: &Path, source_len: usize, output: &FrontendOutput) -> ExitCode {
    println!("status: {}", status_name(output.status()));
    print_capability_profile();
    println!("source-bytes: {}", source_len);
    println!("tokens: {}", output.lexed().tokens().len());

    print_frontend_issues(path, output);

    if let Some(ast) = output.ast() {
        println!("ast: {ast:#?}");
    }
    if let Some(hir) = output.hir() {
        println!("typed-hir: {hir:#?}");
    }
    if let Some(vir) = output.vir() {
        println!("validated-vir:\n{vir}");
    }
    match output.status() {
        FrontendStatus::AcceptedProposal => ExitCode::SUCCESS,
        FrontendStatus::Invalid | FrontendStatus::Unsupported => ExitCode::from(2),
    }
}

fn interpret_source(path: PathBuf) -> ExitCode {
    let source = match SourceFile::load(&path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("error: cannot read {}: {error}", path.display());
            return ExitCode::FAILURE;
        }
    };
    let output = analyze(&source);
    interpret_frontend(&path, &output)
}

fn interpret_frontend(path: &Path, output: &FrontendOutput) -> ExitCode {
    if output.status() != FrontendStatus::AcceptedProposal {
        eprintln!("status: {}", status_name(output.status()));
        print_frontend_issues(path, output);
        return ExitCode::from(2);
    }
    let Some(vir) = output.vir() else {
        eprintln!("error: accepted frontend output did not contain validated VIR");
        return ExitCode::FAILURE;
    };
    let resolved = match vir.resolve() {
        Ok(resolved) => resolved,
        Err(error) => {
            let span = error.source_span();
            eprintln!(
                "resolution fault (unverified) {}:{}..{}: {error}",
                runtime_source_path(output, Some(error.function()), path).display(),
                span.start(),
                span.end()
            );
            return ExitCode::FAILURE;
        }
    };
    match interpret(resolved.runtime()) {
        Ok(execution) => {
            println!("status: executed (unverified)");
            print_capability_profile();
            println!("steps: {}", execution.steps());
            match execution.values() {
                [] => println!("return: ()"),
                [value] => println!("return: {}", runtime_value(value)),
                values => {
                    let values = values
                        .iter()
                        .map(runtime_value)
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!("return: ({values})");
                }
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            let span = error.source_span();
            eprintln!(
                "execution fault (unverified) {}:{}..{}: {error}",
                runtime_source_path(
                    output,
                    error.trace().last().map(|event| event.function),
                    path
                )
                .display(),
                span.start(),
                span.end()
            );
            ExitCode::FAILURE
        }
    }
}

fn print_capability_profile() {
    let profile = current_capability_profile().expect("frontend resolved production profile");
    println!("capability-profile: {}", profile.profile());
}

fn print_frontend_issues(path: &Path, output: &FrontendOutput) {
    for issue in output.issues() {
        if let Some(span) = issue.diagnostic().primary_span() {
            eprintln!(
                "{:?} {}:{}..{}: {}",
                issue.kind(),
                path.display(),
                span.start(),
                span.end(),
                issue.diagnostic().message()
            );
        } else {
            eprintln!(
                "{:?} {}: {}",
                issue.kind(),
                path.display(),
                issue.diagnostic().message()
            );
        }
    }
}

fn runtime_source_path(
    output: &FrontendOutput,
    function: Option<nera::VirFunctionId>,
    fallback: &Path,
) -> PathBuf {
    let Some(unit) = output.vir() else {
        return fallback.to_owned();
    };
    let map = &unit.as_unit().source_map;
    function
        .and_then(|function| map.source_span(nera::VirLocation::FunctionEntry { function }))
        .and_then(|span| map.source(span.source))
        .map(|source| PathBuf::from(&source.name))
        .unwrap_or_else(|| fallback.to_owned())
}

fn runtime_value(value: &VirRuntimeValue) -> String {
    match value {
        VirRuntimeValue::U64(value) => value.to_string(),
        VirRuntimeValue::Bool(value) => value.to_string(),
        VirRuntimeValue::Pointer(pointer) => {
            format!(
                "ptr(alloc{}, +{})",
                pointer.allocation, pointer.offset_bytes
            )
        }
        VirRuntimeValue::Permission(permission) => format!(
            "permission(alloc{}, {}..{})",
            permission.allocation, permission.start_bytes, permission.end_bytes
        ),
    }
}

const fn status_name(status: FrontendStatus) -> &'static str {
    match status {
        FrontendStatus::AcceptedProposal => "accepted-proposal (untrusted)",
        FrontendStatus::Invalid => "invalid",
        FrontendStatus::Unsupported => "unsupported",
    }
}
