//! Immutable, deterministic input snapshot. No filesystem discovery or reload.
use std::{
    collections::BTreeSet,
    error::Error,
    fmt,
    path::{Component, PathBuf},
};

use super::SourceFile;
use crate::{ByteSpan, VirSourceId, VirSourceSpan};

/// An explicit logical key, independent of the path displayed in diagnostics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceInput {
    logical_name: String,
    file: SourceFile,
}

impl SourceInput {
    pub fn new(logical_name: impl Into<String>, file: SourceFile) -> Self {
        Self {
            logical_name: logical_name.into(),
            file,
        }
    }
    pub fn logical_name(&self) -> &str {
        &self.logical_name
    }
    pub fn file(&self) -> &SourceFile {
        &self.file
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceDatabaseError {
    Empty,
    TooManySources,
    InvalidLogicalName(String),
    DuplicateLogicalName(String),
    DuplicateDisplayPath(PathBuf),
}
impl fmt::Display for SourceDatabaseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid source snapshot: {self:?}")
    }
}
impl Error for SourceDatabaseError {}

/// IDs are dense and local to this snapshot, assigned by logical-name order.
/// They are NOT persistent identities or interchangeable with a unit's source IDs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceDatabase {
    entries: Vec<SourceInput>,
}
impl SourceDatabase {
    pub fn new(mut entries: Vec<SourceInput>) -> Result<Self, SourceDatabaseError> {
        if entries.is_empty() {
            return Err(SourceDatabaseError::Empty);
        }
        if u32::try_from(entries.len()).is_err() {
            return Err(SourceDatabaseError::TooManySources);
        }
        entries.sort_by(|a, b| a.logical_name.cmp(&b.logical_name));
        let mut paths = BTreeSet::new();
        for (index, entry) in entries.iter().enumerate() {
            let name = &entry.logical_name;
            if name
                .chars()
                .any(|c| c.is_control() || c == '\\' || c == ':')
                || name
                    .split('/')
                    .any(|s| s.is_empty() || matches!(s, "." | ".."))
            {
                return Err(SourceDatabaseError::InvalidLogicalName(name.clone()));
            }
            if index > 0 && entries[index - 1].logical_name == *name {
                return Err(SourceDatabaseError::DuplicateLogicalName(name.clone()));
            }
            // Lexical components remove redundant separators and '.', not '..'
            // or symlinks. Never consult the live filesystem to identify bytes.
            let path: PathBuf = entry
                .file
                .path()
                .components()
                .filter(|component| !matches!(component, Component::CurDir))
                .collect();
            if !paths.insert(path.clone()) {
                return Err(SourceDatabaseError::DuplicateDisplayPath(path));
            }
        }
        Ok(Self { entries })
    }
    pub(crate) fn single(source: SourceFile) -> Self {
        Self {
            entries: vec![SourceInput::new("input.nera", source)],
        }
    }
    pub fn entries(&self) -> &[SourceInput] {
        &self.entries
    }
    pub fn id(&self, logical_name: &str) -> Option<VirSourceId> {
        self.entries
            .binary_search_by(|e| e.logical_name.as_str().cmp(logical_name))
            .ok()
            .map(|i| VirSourceId::new(i as u32))
    }
    pub fn entry(&self, id: VirSourceId) -> Option<&SourceInput> {
        self.entries.get(id.get() as usize)
    }
    pub fn source(&self, id: VirSourceId) -> Option<&SourceFile> {
        self.entry(id).map(SourceInput::file)
    }
    /// Qualify an inherited file-local span, checking the exact snapshot bytes.
    pub fn locate(&self, source: VirSourceId, span: ByteSpan) -> Option<VirSourceSpan> {
        (span.end() <= self.source(source)?.len()).then_some(VirSourceSpan { source, span })
    }
}
