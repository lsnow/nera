//! Compilation input ownership and orchestration. No module discovery, cache,
//! generic instantiation, or second frontend/verifier implementation.
mod config;
pub use config::{CompilationConfig, SessionRequest};

use crate::{
    ByteSpan, CfgAnalysisConfig, FrontendIssue, FrontendOutput, SourceFile, VirSourceId,
    VirSourceSpan, source::SourceDatabase, verification::VerificationPreview,
};
use std::{error::Error, fmt, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SessionError {
    UnknownSource(String),
    UnsupportedConfiguration {
        field: &'static str,
        requested: String,
    },
    InvalidCapabilityProfile(String),
    /// An implementation error, never an accepted output under a different profile.
    ProducerConfigurationMismatch,
    ProducerSourceMismatch,
    InvalidModuleInput(String),
}
impl fmt::Display for SessionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "compilation session: {self:?}")
    }
}
impl Error for SessionError {}

/// Exact analysis input, not a hash, serialized certificate, or cache permission.
/// Even unselected files participate in identity. Coverage is one selected file
/// for independent inputs, or the complete closed set for a module program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompilationInput {
    sources: Arc<SourceDatabase>,
    source_id: VirSourceId,
    request: SessionRequest,
    config: CompilationConfig,
    entry: Option<String>,
    unit_sources: Vec<VirSourceId>,
}
impl CompilationInput {
    pub fn sources(&self) -> &SourceDatabase {
        &self.sources
    }
    pub fn source_id(&self) -> VirSourceId {
        self.source_id
    }
    pub fn source(&self) -> &SourceFile {
        self.sources
            .source(self.source_id)
            .expect("session-bound source")
    }
    pub fn logical_name(&self) -> &str {
        self.sources
            .entry(self.source_id)
            .expect("session-bound source")
            .logical_name()
    }
    pub fn requested(&self) -> &SessionRequest {
        &self.request
    }
    pub fn effective(&self) -> CompilationConfig {
        self.config
    }
    /// Omitted versus explicit defaults are the same effective analysis input.
    /// Display paths are included (diagnostics), independently of logical names.
    pub fn same_analysis_input(&self, other: &Self) -> bool {
        self.sources == other.sources
            && self.source_id == other.source_id
            && self.config == other.config
            && self.entry == other.entry
    }
    /// Locate a span in the selected entry file. Module-owned HIR spans use
    /// `SourceAnalysis::locate_hir_span` instead.
    pub fn locate(&self, span: ByteSpan) -> Option<VirSourceSpan> {
        self.sources.locate(self.source_id, span)
    }
    /// Explicit unit-local source -> snapshot source mapping. This is
    /// only exposed through source-produced results, never attached to raw VIR.
    pub(crate) fn locate_unit_span(&self, span: VirSourceSpan) -> Option<VirSourceSpan> {
        self.sources.locate(
            *self.unit_sources.get(span.source.get() as usize)?,
            span.span,
        )
    }
    pub fn is_module_program(&self) -> bool {
        self.entry.is_some()
    }
    pub fn entry(&self) -> Option<&str> {
        self.entry.as_deref()
    }
}

/// Own a closed input snapshot and analyze explicitly selected files.
/// `new` keeps entries independent; `modules` selects closed-program analysis.
///
/// ```
/// use nera::{SourceFile, source::{SourceDatabase, SourceInput}};
/// use nera::session::CompilerSession;
/// let inputs = SourceDatabase::new(vec![SourceInput::new(
///     "main.nera", SourceFile::from_text("example.nera", "fn main()->u64 { return 42; }")
/// )]).unwrap();
/// let session = CompilerSession::new(inputs, Default::default()).unwrap();
/// let report = session.verify("main.nera").unwrap();
/// assert!(report.is_checked());
/// assert!(report.matches_session(&session, "main.nera"));
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompilerSession {
    sources: Arc<SourceDatabase>,
    request: SessionRequest,
    config: CompilationConfig,
    entry: Option<String>,
}
impl CompilerSession {
    pub fn new(sources: SourceDatabase, request: SessionRequest) -> Result<Self, SessionError> {
        let config = CompilationConfig::resolve(&request)?;
        Ok(Self {
            sources: Arc::new(sources),
            request,
            config,
            entry: None,
        })
    }
    /// Explicit file-to-module mapping: logical source key `a/b` means module
    /// `a::b`. All files are analyzed, including unreachable private functions.
    pub fn modules(
        sources: SourceDatabase,
        request: SessionRequest,
        entry: impl Into<String>,
    ) -> Result<Self, SessionError> {
        let entry = entry.into();
        for input in sources.entries() {
            if !input.logical_name().split('/').all(valid_module_segment) {
                return Err(SessionError::InvalidModuleInput(
                    input.logical_name().into(),
                ));
            }
        }
        let Some((module, function)) = entry.rsplit_once("::") else {
            return Err(SessionError::InvalidModuleInput(entry));
        };
        if !valid_module_segment(function) || sources.id(&module.replace("::", "/")).is_none() {
            return Err(SessionError::InvalidModuleInput(entry));
        }
        let mut session = Self::new(sources, request)?;
        session.entry = Some(entry);
        Ok(session)
    }
    pub fn entry_source(&self) -> Option<String> {
        self.entry
            .as_ref()?
            .rsplit_once("::")
            .map(|(module, _)| module.replace("::", "/"))
    }
    /// Compatibility input. Does no I/O and admits any original path/bytes.
    pub fn single(source: SourceFile, analysis: CfgAnalysisConfig) -> Self {
        Self::new(
            SourceDatabase::single(source),
            SessionRequest {
                analysis,
                ..Default::default()
            },
        )
        .expect("known default production configuration")
    }
    pub fn sources(&self) -> &SourceDatabase {
        &self.sources
    }
    pub fn requested(&self) -> &SessionRequest {
        &self.request
    }
    pub fn effective(&self) -> CompilationConfig {
        self.config
    }
    pub fn input(&self, logical_name: &str) -> Result<CompilationInput, SessionError> {
        if self
            .entry_source()
            .is_some_and(|entry| entry != logical_name)
        {
            return Err(SessionError::InvalidModuleInput(
                "select the configured entry source for a module program".into(),
            ));
        }
        let source_id = self
            .sources
            .id(logical_name)
            .ok_or_else(|| SessionError::UnknownSource(logical_name.to_owned()))?;
        Ok(CompilationInput {
            sources: Arc::clone(&self.sources),
            source_id,
            request: self.request.clone(),
            config: self.config,
            entry: self.entry.clone(),
            unit_sources: vec![source_id],
        })
    }
    /// Analyze a selected independent source, or the configured entry of a
    /// closed module program. Both modes share the production frontend.
    pub fn analyze(&self, logical_name: &str) -> Result<SourceAnalysis, SessionError> {
        let mut input = self.input(logical_name)?;
        let frontend = if let Some(entry) = &self.entry {
            let sources: Vec<_> = self.sources.entries().iter().map(|s| s.file()).collect();
            let paths: Vec<_> = self
                .sources
                .entries()
                .iter()
                .map(|s| s.logical_name().replace('/', "::"))
                .collect();
            crate::frontend::analyze_sources(
                &sources,
                &paths,
                input.source_id.get() as usize,
                Some(entry),
            )
        } else {
            crate::frontend::analyze_single_source(input.source())
        };
        if self.entry.is_some() {
            input.unit_sources = frontend
                .hir()
                .map(|hir| {
                    hir.functions()
                        .iter()
                        .map(|f| VirSourceId::new(f.module.get()))
                        .collect::<std::collections::BTreeSet<_>>()
                        .into_iter()
                        .collect()
                })
                .unwrap_or_default();
        }
        if frontend.vir().is_some_and(|unit| {
            unit.as_unit().runtime.semantic_profile != self.config.runtime()
                || unit.as_unit().version != crate::VirUnitVersion::V27
        }) || frontend.hir().is_some_and(|hir| {
            hir.data_layout() != crate::HirTargetDataLayout::x86_64()
                || hir.version() != crate::HirVersion::CURRENT
        }) {
            return Err(SessionError::ProducerConfigurationMismatch);
        }
        if frontend.vir().is_some_and(|unit| {
            let entries = unit.as_unit().source_map.sources();
            entries.len() != input.unit_sources.len()
                || entries.iter().enumerate().any(|(i, entry)| {
                    let source = input
                        .sources
                        .source(input.unit_sources[i])
                        .expect("producer source mapping");
                    entry.id != VirSourceId::new(i as u32)
                        || entry.name != source.path().to_string_lossy()
                        || entry.byte_len != source.len()
                })
        }) {
            return Err(SessionError::ProducerSourceMismatch);
        }
        Ok(SourceAnalysis { input, frontend })
    }
    pub fn verify(&self, logical_name: &str) -> Result<VerificationPreview, SessionError> {
        crate::verification::verify_session_source(self, logical_name)
    }
}

/// The file binding travels alongside all local CST/AST/HIR spans. A source
/// analysis cannot be constructed from an unrelated frontend output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceAnalysis {
    input: CompilationInput,
    frontend: FrontendOutput,
}
#[derive(Clone, Copy, Debug)]
pub struct LocatedFrontendIssue<'a> {
    pub issue: &'a FrontendIssue,
    pub location: Option<VirSourceSpan>,
}
impl SourceAnalysis {
    pub fn input(&self) -> &CompilationInput {
        &self.input
    }
    pub fn frontend(&self) -> &FrontendOutput {
        &self.frontend
    }
    pub fn issues(&self) -> impl Iterator<Item = LocatedFrontendIssue<'_>> {
        self.frontend
            .issues()
            .iter()
            .map(|issue| LocatedFrontendIssue {
                issue,
                location: issue.diagnostic().primary_span().and_then(|span| {
                    self.input
                        .sources
                        .locate(issue.source_id().unwrap_or(self.input.source_id), span)
                }),
            })
    }
    pub fn locate_vir_span(&self, span: VirSourceSpan) -> Option<VirSourceSpan> {
        self.frontend
            .vir()?
            .as_unit()
            .source_map
            .source(span.source)?;
        self.input.locate_unit_span(span)
    }
    /// HIR local spans inherit the canonical module owner. Type/field callers
    /// obtain that owner from the HIR module declaration table.
    pub fn locate_hir_span(
        &self,
        module: crate::HirModuleId,
        span: ByteSpan,
    ) -> Option<VirSourceSpan> {
        self.frontend
            .hir()?
            .modules()
            .get(module.index())
            .filter(|m| m.id == module)?;
        self.locate_file_span(VirSourceId::new(module.get()), span)
    }
    /// Qualify a frontend file's local span against the input snapshot. This
    /// also handles independent analysis of a nonzero selected snapshot source.
    pub fn locate_file_span(&self, file: VirSourceId, span: ByteSpan) -> Option<VirSourceSpan> {
        self.frontend
            .files()
            .get(file.get() as usize)
            .filter(|entry| entry.source == file)?;
        let source = if self.input.is_module_program() {
            file
        } else {
            self.input.source_id
        };
        self.input.sources.locate(source, span)
    }
    pub(crate) fn into_frontend(self) -> FrontendOutput {
        self.frontend
    }
    pub(crate) fn into_parts(self) -> (CompilationInput, FrontendOutput) {
        (self.input, self.frontend)
    }
}

fn valid_module_segment(segment: &str) -> bool {
    let mut chars = segment.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}
