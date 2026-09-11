//! Explicit closed source-set input, shared by all production consumers.
use nera::{
    FrontendStatus, SourceFile,
    session::CompilerSession,
    source::{SourceDatabase, SourceInput},
};
use std::{
    ffi::{OsStr, OsString},
    path::PathBuf,
    process::ExitCode,
};

pub(super) struct ModuleOptions {
    mappings: Vec<(String, PathBuf)>,
    entry: String,
}

pub(super) fn extract(
    arguments: Vec<OsString>,
) -> Result<(Option<ModuleOptions>, Vec<OsString>), String> {
    let mut remaining = Vec::new();
    let mut mappings = Vec::new();
    let mut entry = None;
    let mut args = arguments.into_iter();
    while let Some(arg) = args.next() {
        if arg == "--" {
            remaining.push(arg);
            remaining.extend(args);
            break;
        }
        if arg == "--module" {
            let value = args.next().ok_or("--module requires NAME=PATH")?;
            let text = value.to_str().ok_or("module mapping must be UTF-8")?;
            let (name, path) = text.split_once('=').ok_or("--module requires NAME=PATH")?;
            if path.is_empty() {
                return Err("module path must not be empty".into());
            }
            mappings.push((name.replace("::", "/"), PathBuf::from(path)));
        } else if arg == "--entry" {
            let value = args.next().ok_or("--entry requires MODULE::FUNCTION")?;
            if entry
                .replace(value.into_string().map_err(|_| "entry must be UTF-8")?)
                .is_some()
            {
                return Err("--entry may only be specified once".into());
            }
        } else {
            remaining.push(arg);
        }
    }
    if mappings.is_empty() && entry.is_none() {
        return Ok((None, remaining));
    }
    if mappings.is_empty() {
        return Err("--entry requires explicit --module inputs".into());
    }
    Ok((
        Some(ModuleOptions {
            mappings,
            entry: entry.ok_or("module inputs require --entry MODULE::FUNCTION")?,
        }),
        remaining,
    ))
}

pub(super) fn run(command: &OsStr, options: ModuleOptions, remaining: Vec<OsString>) -> ExitCode {
    match execute(command, options, remaining) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(2)
        }
    }
}

fn execute(
    command: &OsStr,
    options: ModuleOptions,
    remaining: Vec<OsString>,
) -> Result<ExitCode, String> {
    if !matches!(
        command.to_str(),
        Some("frontend" | "verify" | "run" | "build")
    ) {
        return Err("module inputs require frontend, verify, run or build".into());
    }
    // Reject all positional paths and unknown options before loading any input.
    let mut build = None;
    let explain = if command == "verify" {
        match remaining.as_slice() {
            [] => false,
            [arg] if arg == "--explain" => true,
            _ => {
                return Err("module verify only accepts --explain besides --module/--entry".into());
            }
        }
    } else if command == "build" {
        // Reuse the existing emit/output parser and target pipeline.
        let mut args = remaining;
        args.push("<module-entry>".into());
        build = Some(super::parse_build_options(args.into_iter())?);
        false
    } else {
        if !remaining.is_empty() {
            return Err(
                "module input cannot be mixed with positional paths or extra options".into(),
            );
        }
        false
    };
    if let Some(build) = &build {
        for (_, path) in &options.mappings {
            if super::paths_refer_to_same_file(path, &build.output) {
                return Err("source and output paths refer to the same file".into());
            }
        }
    }
    // The CLI loader rejects physical aliases as well as duplicate logical keys.
    let mut physical = std::collections::BTreeSet::new();
    let sources = options
        .mappings
        .into_iter()
        .map(|(name, path)| {
            let canonical = path
                .canonicalize()
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            if !physical.insert(canonical) {
                return Err("two module inputs refer to the same physical file".into());
            }
            let file = SourceFile::load(&path)
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            Ok(SourceInput::new(name, file))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let sources = SourceDatabase::new(sources).map_err(|e| e.to_string())?;
    let session = CompilerSession::modules(sources, Default::default(), options.entry)
        .map_err(|e| e.to_string())?;
    let root = session.entry_source().unwrap();
    if command == "verify" {
        let preview = session.verify(&root).map_err(|e| e.to_string())?;
        let mode = if explain {
            nera::verification::TextReportMode::Explain
        } else {
            nera::verification::TextReportMode::Summary
        };
        return nera::verification::write_report(&preview, mode, &mut std::io::stdout().lock())
            .map(ExitCode::from)
            .map_err(|e| format!("cannot write verification output: {e}"));
    }
    let analysis = session.analyze(&root).map_err(|e| e.to_string())?;
    let frontend = analysis.frontend();
    if frontend.status() != FrontendStatus::AcceptedProposal {
        eprintln!("status: {:?}", frontend.status());
        for issue in analysis.issues() {
            let source = issue
                .location
                .and_then(|location| session.sources().source(location.source))
                .unwrap_or(analysis.input().source());
            if let Some(span) = issue.issue.diagnostic().primary_span() {
                eprintln!(
                    "{}:{}..{}: {}",
                    source.path().display(),
                    span.start(),
                    span.end(),
                    issue.issue.diagnostic().message()
                );
            }
        }
        return Ok(ExitCode::from(2));
    }
    let source = analysis.input().source();
    Ok(if let Some(mut build) = build {
        build.source = source.path().to_owned();
        super::build_frontend(build, frontend)
    } else if command == "run" {
        super::interpret_frontend(source.path(), frontend)
    } else {
        super::print_frontend(source.path(), source.len(), frontend)
    })
}
