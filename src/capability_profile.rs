//! Closed, machine-readable description of the one production profile.
//!
//! This registry classifies support; it never substitutes for frontend,
//! verifier, interpreter, or backend semantic checks.

use std::{error::Error, fmt, sync::OnceLock};

const MANIFEST: &str = include_str!("../spec/capability-profile-v1.txt");
const MAGIC: &str = "nera-capability-profile-v1";
const COLUMNS: &str =
    "columns|feature|surface|runtime|hir|vir|verifier|interpreter|backend|formal|limit|check";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapabilityAxis {
    Surface,
    Runtime,
    Hir,
    Vir,
    Verifier,
    Interpreter,
    Backend,
    Formal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapabilityStatus {
    Supported,
    RejectedWithDiagnostic,
    SchemaOnly,
    ErasedAfterValidation,
    ArchivedSubset,
    Unsupported,
    NotApplicable,
}

impl CapabilityStatus {
    fn parse(value: &str) -> Option<Self> {
        Some(match value {
            "supported" => Self::Supported,
            "rejected-with-diagnostic" => Self::RejectedWithDiagnostic,
            "schema-only" => Self::SchemaOnly,
            "erased-after-validation" => Self::ErasedAfterValidation,
            "archived-subset" => Self::ArchivedSubset,
            "unsupported" => Self::Unsupported,
            "not-applicable" => Self::NotApplicable,
            _ => return None,
        })
    }

    pub const fn name(self) -> &'static str {
        match self {
            Self::Supported => "supported",
            Self::RejectedWithDiagnostic => "rejected-with-diagnostic",
            Self::SchemaOnly => "schema-only",
            Self::ErasedAfterValidation => "erased-after-validation",
            Self::ArchivedSubset => "archived-subset",
            Self::Unsupported => "unsupported",
            Self::NotApplicable => "not-applicable",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityFeature {
    id: String,
    statuses: [CapabilityStatus; 8],
    limit: String,
    check: String,
}

impl CapabilityFeature {
    pub fn id(&self) -> &str {
        &self.id
    }

    pub const fn status(&self, axis: CapabilityAxis) -> CapabilityStatus {
        self.statuses[axis as usize]
    }

    pub fn limit(&self) -> &str {
        &self.limit
    }

    pub fn check(&self) -> &str {
        &self.check
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityProfile {
    profile: String,
    language: String,
    runtime: String,
    hir_schema: u32,
    vir_schema: u32,
    verifier: String,
    interpreter: String,
    target: String,
    backend: String,
    formal_checker: String,
    features: Vec<CapabilityFeature>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityProfileError {
    line: Option<usize>,
    message: String,
}

impl CapabilityProfileError {
    fn at(line: usize, message: impl Into<String>) -> Self {
        Self {
            line: Some(line),
            message: message.into(),
        }
    }

    fn incompatible(message: impl Into<String>) -> Self {
        Self {
            line: None,
            message: message.into(),
        }
    }
}

impl fmt::Display for CapabilityProfileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(line) = self.line {
            write!(f, "capability profile line {line}: {}", self.message)
        } else {
            write!(f, "capability profile: {}", self.message)
        }
    }
}

impl Error for CapabilityProfileError {}

impl CapabilityProfile {
    pub fn parse(input: &str) -> Result<Self, CapabilityProfileError> {
        let records: Vec<(usize, &str)> = input
            .lines()
            .enumerate()
            .filter_map(|(index, line)| {
                let line = line.trim();
                (!line.is_empty() && !line.starts_with('#')).then_some((index + 1, line))
            })
            .collect();
        let Some(&(magic_line, magic)) = records.first() else {
            return Err(CapabilityProfileError::at(1, "missing format marker"));
        };
        if magic != MAGIC {
            return Err(CapabilityProfileError::at(
                magic_line,
                "unknown format marker",
            ));
        }

        let header_names = [
            "profile",
            "language",
            "runtime",
            "hir-schema",
            "vir-schema",
            "verifier",
            "interpreter",
            "target",
            "backend",
            "formal-checker",
        ];
        if records.len() < header_names.len() + 2 {
            return Err(CapabilityProfileError::at(magic_line, "incomplete header"));
        }
        let mut values = Vec::with_capacity(header_names.len());
        for (offset, expected) in header_names.iter().enumerate() {
            let (line, record) = records[offset + 1];
            let Some((name, value)) = record.split_once('|') else {
                return Err(CapabilityProfileError::at(line, "malformed header record"));
            };
            if name != *expected || value.is_empty() || value.contains('|') {
                return Err(CapabilityProfileError::at(
                    line,
                    format!("expected one nonempty '{expected}' value"),
                ));
            }
            values.push(value);
        }
        let (columns_line, columns) = records[header_names.len() + 1];
        if columns != COLUMNS {
            return Err(CapabilityProfileError::at(
                columns_line,
                "feature columns do not match schema v1",
            ));
        }

        let hir_schema = parse_schema(records[4].0, "hir-schema", values[3])?;
        let vir_schema = parse_schema(records[5].0, "vir-schema", values[4])?;
        let mut features = Vec::new();
        let mut previous: Option<&str> = None;
        for &(line, record) in &records[header_names.len() + 2..] {
            let fields: Vec<_> = record.split('|').collect();
            if fields.len() != 12 || fields[0] != "feature" {
                return Err(CapabilityProfileError::at(
                    line,
                    "feature records require exactly 12 fields",
                ));
            }
            let id = fields[1];
            if id.is_empty()
                || !id
                    .bytes()
                    .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
            {
                return Err(CapabilityProfileError::at(line, "invalid feature id"));
            }
            if previous.is_some_and(|old| old >= id) {
                return Err(CapabilityProfileError::at(
                    line,
                    "feature ids must be unique and sorted",
                ));
            }
            previous = Some(id);
            let mut statuses = [CapabilityStatus::Unsupported; 8];
            for (slot, value) in statuses.iter_mut().zip(&fields[2..10]) {
                *slot = CapabilityStatus::parse(value).ok_or_else(|| {
                    CapabilityProfileError::at(line, format!("unknown status '{value}'"))
                })?;
            }
            if fields[10].is_empty() || !fields[11].starts_with("cargo run -p xtask -- check-") {
                return Err(CapabilityProfileError::at(
                    line,
                    "feature limit and focused check are required",
                ));
            }
            features.push(CapabilityFeature {
                id: id.into(),
                statuses,
                limit: fields[10].into(),
                check: fields[11].into(),
            });
        }
        if features.is_empty() {
            return Err(CapabilityProfileError::at(
                columns_line,
                "at least one feature is required",
            ));
        }
        Ok(Self {
            profile: values[0].into(),
            language: values[1].into(),
            runtime: values[2].into(),
            hir_schema,
            vir_schema,
            verifier: values[5].into(),
            interpreter: values[6].into(),
            target: values[7].into(),
            backend: values[8].into(),
            formal_checker: values[9].into(),
            features,
        })
    }

    pub fn profile(&self) -> &str {
        &self.profile
    }
    pub fn language(&self) -> &str {
        &self.language
    }
    pub fn runtime(&self) -> &str {
        &self.runtime
    }
    pub const fn hir_schema(&self) -> u32 {
        self.hir_schema
    }
    pub const fn vir_schema(&self) -> u32 {
        self.vir_schema
    }
    pub fn verifier(&self) -> &str {
        &self.verifier
    }
    pub fn interpreter(&self) -> &str {
        &self.interpreter
    }
    pub fn target(&self) -> &str {
        &self.target
    }
    pub fn backend(&self) -> &str {
        &self.backend
    }
    pub fn formal_checker(&self) -> &str {
        &self.formal_checker
    }
    pub fn features(&self) -> &[CapabilityFeature] {
        &self.features
    }
    pub fn feature(&self, id: &str) -> Option<&CapabilityFeature> {
        self.features
            .binary_search_by_key(&id, |feature| feature.id())
            .ok()
            .map(|index| &self.features[index])
    }

    /// Reject a manifest that describes a combination this compiler binary
    /// does not implement. This does not decide whether any source is valid.
    pub fn check_implementation(&self) -> Result<(), CapabilityProfileError> {
        let expected = [
            ("profile", self.profile(), "system-v1"),
            ("language", self.language(), "0.3-draft"),
            ("runtime", self.runtime(), "system-v2"),
            ("verifier", self.verifier(), "automatic-memory-v1"),
            (
                "interpreter",
                self.interpreter(),
                "system-v2-interpreter-v1",
            ),
            (
                "target",
                self.target(),
                crate::backend::X86_64_UNKNOWN_LINUX_GNU.triple(),
            ),
            ("backend", self.backend(), "direct-x86_64-system-tools-v1"),
            ("formal-checker", self.formal_checker(), "none"),
        ];
        for (field, actual, supported) in expected {
            if actual != supported {
                return Err(CapabilityProfileError::incompatible(format!(
                    "unsupported {field} '{actual}'"
                )));
            }
        }
        if self.hir_schema != 12 || self.vir_schema != 18 {
            return Err(CapabilityProfileError::incompatible(format!(
                "unsupported HIR/VIR schema {}/{}",
                self.hir_schema, self.vir_schema
            )));
        }
        Ok(())
    }
}

fn parse_schema(line: usize, name: &str, value: &str) -> Result<u32, CapabilityProfileError> {
    value.parse::<u32>().map_err(|_| {
        CapabilityProfileError::at(line, format!("'{name}' must be an unsigned integer"))
    })
}

static CURRENT: OnceLock<Result<CapabilityProfile, CapabilityProfileError>> = OnceLock::new();

pub fn current_capability_profile()
-> Result<&'static CapabilityProfile, &'static CapabilityProfileError> {
    CURRENT
        .get_or_init(|| {
            CapabilityProfile::parse(MANIFEST).and_then(|p| {
                p.check_implementation()?;
                Ok(p)
            })
        })
        .as_ref()
}
