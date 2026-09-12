mod core;
mod stage7_1;
mod stage7_2;
mod stage7_3;
mod stage7_4;
mod stage7_5;
mod stage7_6;
mod stage7_7;
mod stage7_8;

use std::{error::Error, fs, path::Path};

fn missing_marker<'a>(source: &str, markers: &'a [&'a str]) -> Option<&'a str> {
    markers
        .iter()
        .copied()
        .find(|marker| !source.contains(*marker))
}

/// Reads a Rust module facade and all of its split implementation files.
///
/// Regression checks use this view when they care about a module's semantic
/// implementation rather than the current physical file layout.
fn read_rust_module(root: &Path, module: &str) -> Result<String, Box<dyn Error>> {
    let mut paths = vec![root.join(format!("{module}.rs"))];
    collect_rust_files(&root.join(module), &mut paths)?;
    paths.sort();

    let mut source = String::new();
    for path in paths {
        source.push_str(&fs::read_to_string(path)?);
        source.push('\n');
    }
    Ok(source)
}

fn collect_rust_files(
    directory: &Path,
    paths: &mut Vec<std::path::PathBuf>,
) -> Result<(), Box<dyn Error>> {
    if !directory.is_dir() {
        return Ok(());
    }
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_rust_files(&path, paths)?;
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            paths.push(path);
        }
    }
    Ok(())
}

pub(super) use core::*;
pub(super) use stage7_1::*;
pub(super) use stage7_2::*;
pub(super) use stage7_3::*;
pub(super) use stage7_4::*;
pub(super) use stage7_5::*;
pub(super) use stage7_6::*;
pub(super) use stage7_7::*;
pub(super) use stage7_8::*;

#[cfg(test)]
mod tests {
    use super::missing_marker;

    #[test]
    fn marker_check_reports_the_first_missing_marker() {
        assert_eq!(
            missing_marker("alpha gamma", &["alpha", "beta", "gamma"]),
            Some("beta")
        );
        assert_eq!(missing_marker("alpha beta", &["alpha", "beta"]), None);
    }
}
