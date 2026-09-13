use std::collections::{BTreeMap, BTreeSet};

use super::{
    RuntimeVirProgram, VirBlockId, VirFunction, VirFunctionId, VirInstruction, VirOriginId,
    VirSourceId, VirType, VirUnitVersion,
};
use crate::ByteSpan;
use crate::diagnostic::span_contains;

/// One source file named by the canonical VIR source table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSource {
    pub id: VirSourceId,
    pub name: String,
    pub byte_len: usize,
}

/// A stable runtime program point independent from its source span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirLocation {
    FunctionEntry {
        function: VirFunctionId,
    },
    BlockEntry {
        function: VirFunctionId,
        block: VirBlockId,
    },
    BlockParameter {
        function: VirFunctionId,
        block: VirBlockId,
        ordinal: u64,
    },
    Instruction {
        function: VirFunctionId,
        block: VirBlockId,
        ordinal: u64,
    },
    CallEdge {
        function: VirFunctionId,
        block: VirBlockId,
        instruction: u64,
    },
    Terminator {
        function: VirFunctionId,
        block: VirBlockId,
    },
}

impl VirLocation {
    #[must_use]
    pub const fn function(self) -> VirFunctionId {
        match self {
            Self::FunctionEntry { function }
            | Self::BlockEntry { function, .. }
            | Self::BlockParameter { function, .. }
            | Self::Instruction { function, .. }
            | Self::CallEdge { function, .. }
            | Self::Terminator { function, .. } => function,
        }
    }

    #[must_use]
    pub const fn block(self) -> Option<VirBlockId> {
        match self {
            Self::FunctionEntry { .. } => None,
            Self::BlockEntry { block, .. }
            | Self::BlockParameter { block, .. }
            | Self::Instruction { block, .. }
            | Self::CallEdge { block, .. }
            | Self::Terminator { block, .. } => Some(block),
        }
    }
}

/// Why a runtime location exists without a one-to-one source node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirGeneratedReason {
    ControlFlowBlock,
    BlockParameter,
    PermissionParameter,
    ControlFlowEdge,
    ImplicitReturn,
    LoopIncrement,
    TemporaryStorage,
    ImplicitCopy,
    ImplicitMove,
    ImplicitDrop,
    ScopeCleanup,
    BranchCleanup,
    CallTransfer,
    ReturnTransfer,
    LoanEffect,
}

/// Canonical origin payload. Generated origins always delegate their span to
/// an earlier origin and never fabricate an empty source span.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirOriginKind {
    User {
        source: VirSourceId,
        span: ByteSpan,
    },
    Generated {
        parent: VirOriginId,
        reason: VirGeneratedReason,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirOrigin {
    pub id: VirOriginId,
    pub kind: VirOriginKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VirLocationOrigin {
    pub location: VirLocation,
    pub origin: VirOriginId,
}

/// Resolved source position returned by source-map queries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VirSourceSpan {
    pub source: VirSourceId,
    pub span: ByteSpan,
}

/// Canonical source, origin and location tables for one VIR unit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VirSourceMap {
    sources: Vec<VirSource>,
    origins: Vec<VirOrigin>,
    locations: Vec<VirLocationOrigin>,
}

impl VirSourceMap {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            sources: Vec::new(),
            origins: Vec::new(),
            locations: Vec::new(),
        }
    }

    /// Constructs raw source-map tables. Unit validation remains responsible
    /// for all density, coverage, origin and span invariants.
    #[must_use]
    pub fn from_tables(
        sources: Vec<VirSource>,
        origins: Vec<VirOrigin>,
        locations: Vec<VirLocationOrigin>,
    ) -> Self {
        Self {
            sources,
            origins,
            locations,
        }
    }

    /// Builds a canonical single-source map for a runtime table whose nodes
    /// already carry their diagnostic span cache.
    #[must_use]
    pub fn from_runtime_source(
        source_name: impl Into<String>,
        source_len: usize,
        runtime: &RuntimeVirProgram,
    ) -> Self {
        let source = VirSource {
            id: VirSourceId::new(0),
            name: source_name.into(),
            byte_len: source_len,
        };
        let intents = runtime_location_intents(runtime);
        build_single_source_map(source, intents, Vec::new())
    }

    /// Builds the source map from locations registered by the HIR lowerer as
    /// it creates runtime nodes. Unit validation checks the resulting draft
    /// against the completed runtime table before it can reach a consumer.
    #[must_use]
    pub(crate) fn from_lowering(
        source_name: impl Into<String>,
        source_len: usize,
        entries: Vec<VirSourceMapEntry>,
        additional_user_spans: Vec<ByteSpan>,
    ) -> Self {
        let source = VirSource {
            id: VirSourceId::new(0),
            name: source_name.into(),
            byte_len: source_len,
        };
        build_single_source_map(source, entries, additional_user_spans)
    }

    /// Source-aware lowering uses the same per-file origin canonicalization.
    /// Only origin tables are combined here, never separately lowered VIR units.
    pub(crate) fn from_module_lowering(files: Vec<(VirSource, Vec<VirSourceMapEntry>)>) -> Self {
        let mut sources = Vec::new();
        let mut origins = Vec::new();
        let mut locations = Vec::new();
        for (source, entries) in files {
            let map = build_single_source_map(source, entries, Vec::new());
            let base = origins.len() as u32;
            sources.extend(map.sources);
            origins.extend(map.origins.into_iter().map(|mut origin| {
                origin.id = VirOriginId::new(base + origin.id.get());
                if let VirOriginKind::Generated { parent, .. } = &mut origin.kind {
                    *parent = VirOriginId::new(base + parent.get());
                }
                origin
            }));
            locations.extend(map.locations.into_iter().map(|mut entry| {
                entry.origin = VirOriginId::new(base + entry.origin.get());
                entry
            }));
        }
        // User origins precede all generated origins across the complete unit.
        // Per-file builders only generate direct user parents, so sorting the
        // old parent IDs preserves their order after this dense remap.
        origins.sort_by(|a, b| a.kind.cmp(&b.kind));
        let remap: BTreeMap<_, _> = origins
            .iter()
            .enumerate()
            .map(|(i, origin)| (origin.id, VirOriginId::new(i as u32)))
            .collect();
        for origin in &mut origins {
            origin.id = remap[&origin.id];
            if let VirOriginKind::Generated { parent, .. } = &mut origin.kind {
                *parent = remap[parent];
            }
        }
        for entry in &mut locations {
            entry.origin = remap[&entry.origin];
        }
        locations.sort_by_key(|entry| entry.location);
        Self::from_tables(sources, origins, locations)
    }

    #[must_use]
    pub fn sources(&self) -> &[VirSource] {
        &self.sources
    }

    #[must_use]
    pub fn origins(&self) -> &[VirOrigin] {
        &self.origins
    }

    #[must_use]
    pub fn locations(&self) -> &[VirLocationOrigin] {
        &self.locations
    }

    #[must_use]
    pub fn source(&self, id: VirSourceId) -> Option<&VirSource> {
        self.sources
            .get(id.get() as usize)
            .filter(|source| source.id == id)
    }

    #[must_use]
    pub fn origin(&self, id: VirOriginId) -> Option<&VirOrigin> {
        self.origins
            .get(id.get() as usize)
            .filter(|origin| origin.id == id)
    }

    #[must_use]
    pub fn origin_at(&self, location: VirLocation) -> Option<&VirOrigin> {
        let origin = self
            .locations
            .binary_search_by_key(&location, |entry| entry.location)
            .ok()
            .and_then(|index| self.locations.get(index))?
            .origin;
        self.origin(origin)
    }

    #[must_use]
    pub fn source_span(&self, location: VirLocation) -> Option<VirSourceSpan> {
        let origin = self.origin_at(location)?;
        self.resolve_origin(origin.id)
    }

    /// Resolves an origin-table entry without requiring a runtime location.
    #[must_use]
    pub fn source_span_for_origin(&self, origin: VirOriginId) -> Option<VirSourceSpan> {
        self.resolve_origin(origin)
    }

    /// Finds the canonical user origin assigned to an exact source span.
    #[must_use]
    pub(crate) fn user_origin(&self, source: VirSourceId, span: ByteSpan) -> Option<VirOriginId> {
        self.origins.iter().find_map(|origin| match origin.kind {
            VirOriginKind::User {
                source: candidate,
                span: candidate_span,
            } if candidate == source && candidate_span == span => Some(origin.id),
            VirOriginKind::User { .. } | VirOriginKind::Generated { .. } => None,
        })
    }

    pub(super) fn validate(
        &self,
        version: VirUnitVersion,
        runtime: &RuntimeVirProgram,
        additional_origins: impl IntoIterator<Item = VirOriginId>,
    ) -> Result<(), VirSourceMapErrorKind> {
        self.validate_sources()?;
        self.validate_origins(version)?;
        self.validate_locations(runtime, additional_origins)
    }

    fn resolve_origin(&self, mut id: VirOriginId) -> Option<VirSourceSpan> {
        for _ in 0..self.origins.len() {
            match &self.origin(id)?.kind {
                VirOriginKind::User { source, span } => {
                    return Some(VirSourceSpan {
                        source: *source,
                        span: *span,
                    });
                }
                VirOriginKind::Generated { parent, .. } => id = *parent,
            }
        }
        None
    }

    fn validate_sources(&self) -> Result<(), VirSourceMapErrorKind> {
        if self.sources.is_empty() {
            return Err(VirSourceMapErrorKind::EmptySourceTable);
        }
        let mut names = BTreeSet::new();
        for (index, source) in self.sources.iter().enumerate() {
            let expected = VirSourceId::new(index as u32);
            if source.id != expected {
                return Err(VirSourceMapErrorKind::NonDenseSourceId {
                    expected,
                    found: source.id,
                });
            }
            if !names.insert(source.name.clone()) {
                return Err(VirSourceMapErrorKind::DuplicateSourceName(
                    source.name.clone(),
                ));
            }
        }
        Ok(())
    }

    fn validate_origins(&self, version: VirUnitVersion) -> Result<(), VirSourceMapErrorKind> {
        if self.origins.is_empty() {
            return Err(VirSourceMapErrorKind::EmptyOriginTable);
        }
        let mut kinds = BTreeSet::new();
        let mut previous = None;
        for (index, origin) in self.origins.iter().enumerate() {
            let expected = VirOriginId::new(index as u32);
            if origin.id != expected {
                return Err(VirSourceMapErrorKind::NonDenseOriginId {
                    expected,
                    found: origin.id,
                });
            }
            if !kinds.insert(origin.kind.clone()) {
                return Err(VirSourceMapErrorKind::DuplicateOrigin(origin.kind.clone()));
            }
            if previous.as_ref().is_some_and(|kind| kind > &origin.kind) {
                return Err(VirSourceMapErrorKind::NonCanonicalOriginOrder);
            }
            previous = Some(origin.kind.clone());
            match &origin.kind {
                VirOriginKind::User { source, span } => {
                    let Some(source) = self.source(*source) else {
                        return Err(VirSourceMapErrorKind::UnknownSource(*source));
                    };
                    if span.end() > source.byte_len {
                        return Err(VirSourceMapErrorKind::SpanOutsideSource {
                            source: source.id,
                            span: *span,
                            source_len: source.byte_len,
                        });
                    }
                }
                VirOriginKind::Generated { parent, .. } => {
                    if parent.get() as usize >= index {
                        return Err(VirSourceMapErrorKind::GeneratedParentNotEarlier {
                            origin: origin.id,
                            parent: *parent,
                        });
                    }
                    let Some(parent_span) = self.resolve_origin(*parent) else {
                        return Err(VirSourceMapErrorKind::UnknownOrigin(*parent));
                    };
                    if parent_span.span.is_empty() {
                        return Err(VirSourceMapErrorKind::GeneratedFromEmptySpan(origin.id));
                    }
                }
            }
            if let VirOriginKind::Generated { reason, .. } = origin.kind
                && reason == VirGeneratedReason::LoanEffect
                && !matches!(
                    version,
                    VirUnitVersion::V6
                        | VirUnitVersion::V7
                        | VirUnitVersion::V8
                        | VirUnitVersion::V9
                        | VirUnitVersion::V10
                        | VirUnitVersion::V11
                        | VirUnitVersion::V12
                        | VirUnitVersion::V13
                        | VirUnitVersion::V14
                        | VirUnitVersion::V15
                        | VirUnitVersion::V16
                        | VirUnitVersion::V17
                        | VirUnitVersion::V18
                        | VirUnitVersion::V19
                        | VirUnitVersion::V20
                        | VirUnitVersion::V21
                )
            {
                return Err(VirSourceMapErrorKind::GeneratedReasonRequiresV6 {
                    origin: origin.id,
                    reason,
                });
            }
            if let VirOriginKind::Generated { reason, .. } = origin.kind
                && version == VirUnitVersion::V1
                && reason.requires_v2()
            {
                return Err(VirSourceMapErrorKind::GeneratedReasonRequiresV2 {
                    origin: origin.id,
                    reason,
                });
            }
        }
        Ok(())
    }

    fn validate_locations(
        &self,
        runtime: &RuntimeVirProgram,
        additional_origins: impl IntoIterator<Item = VirOriginId>,
    ) -> Result<(), VirSourceMapErrorKind> {
        let required = required_runtime_locations(runtime);
        let mut previous = None;
        for entry in &self.locations {
            if let Some(previous) = previous {
                if previous == entry.location {
                    return Err(VirSourceMapErrorKind::DuplicateLocation(entry.location));
                }
                if previous > entry.location {
                    return Err(VirSourceMapErrorKind::NonCanonicalLocationOrder);
                }
            }
            previous = Some(entry.location);
        }

        let mut required_index = 0;
        let mut found_index = 0;
        while required_index < required.len() || found_index < self.locations.len() {
            match (
                required.get(required_index),
                self.locations.get(found_index),
            ) {
                (Some(required), Some(found)) if required.location == found.location => {
                    required_index += 1;
                    found_index += 1;
                }
                (Some(required), Some(found)) if required.location < found.location => {
                    return Err(VirSourceMapErrorKind::MissingLocation(required.location));
                }
                (Some(_), Some(found)) => {
                    return Err(VirSourceMapErrorKind::UnexpectedLocation(found.location));
                }
                (Some(required), None) => {
                    return Err(VirSourceMapErrorKind::MissingLocation(required.location));
                }
                (None, Some(found)) => {
                    return Err(VirSourceMapErrorKind::UnexpectedLocation(found.location));
                }
                (None, None) => break,
            }
        }

        let functions = runtime
            .functions
            .iter()
            .map(|function| (function.id, function))
            .collect::<BTreeMap<_, _>>();
        let mut function_sources = BTreeMap::new();
        let mut used_origins = vec![false; self.origins.len()];
        let mut used_sources = vec![false; self.sources.len()];
        let mut runtime_origins = BTreeSet::new();

        for required in &required {
            let entry = self
                .locations
                .binary_search_by_key(&required.location, |entry| entry.location)
                .ok()
                .and_then(|index| self.locations.get(index))
                .expect("coverage was checked above");
            let origin = self
                .origin(entry.origin)
                .ok_or(VirSourceMapErrorKind::UnknownOrigin(entry.origin))?;
            runtime_origins.insert(origin.id);
            let resolved = self
                .resolve_origin(origin.id)
                .ok_or(VirSourceMapErrorKind::UnknownOrigin(origin.id))?;
            mark_origin_chain(self, origin.id, &mut used_origins, &mut used_sources)?;

            let function = functions
                .get(&required.location.function())
                .copied()
                .ok_or(VirSourceMapErrorKind::UnexpectedLocation(required.location))?;
            if !span_contains(function.source_span, resolved.span) {
                return Err(VirSourceMapErrorKind::SpanOutsideFunction {
                    location: required.location,
                    function_span: function.source_span,
                    found: resolved.span,
                });
            }
            if let Some(block_id) = required.location.block() {
                let block = function
                    .blocks
                    .iter()
                    .find(|block| block.id == block_id)
                    .ok_or(VirSourceMapErrorKind::UnexpectedLocation(required.location))?;
                if !span_contains(block.source_span, resolved.span) {
                    return Err(VirSourceMapErrorKind::SpanOutsideBlock {
                        location: required.location,
                        block_span: block.source_span,
                        found: resolved.span,
                    });
                }
            }
            if required.expected_span != resolved.span {
                return Err(VirSourceMapErrorKind::LocationSpanMismatch {
                    location: required.location,
                    expected: required.expected_span,
                    found: resolved.span,
                });
            }

            let function_source = function_sources
                .entry(function.id)
                .or_insert(resolved.source);
            if *function_source != resolved.source {
                return Err(VirSourceMapErrorKind::FunctionUsesMultipleSources(
                    function.id,
                ));
            }
            match origin.kind {
                VirOriginKind::User { .. } => {
                    if let Some(reason) = required.generated_reason {
                        return Err(VirSourceMapErrorKind::ExpectedGeneratedOrigin {
                            location: required.location,
                            reason,
                        });
                    }
                }
                VirOriginKind::Generated { reason, .. } => {
                    if required
                        .generated_reason
                        .is_some_and(|expected| expected != reason)
                        || !generated_reason_matches(required.location, reason, function)
                    {
                        return Err(VirSourceMapErrorKind::GeneratedReasonMismatch {
                            location: required.location,
                            reason,
                        });
                    }
                }
            }
        }

        for origin in &self.origins {
            if let VirOriginKind::Generated { reason, .. } = origin.kind
                && reason.requires_v2()
                && !runtime_origins.contains(&origin.id)
            {
                return Err(
                    VirSourceMapErrorKind::GeneratedReasonWithoutRuntimeLocation {
                        origin: origin.id,
                        reason,
                    },
                );
            }
        }

        for origin in additional_origins {
            mark_origin_chain(self, origin, &mut used_origins, &mut used_sources)?;
        }

        if let Some(index) = used_origins.iter().position(|used| !used) {
            return Err(VirSourceMapErrorKind::UnusedOrigin(VirOriginId::new(
                index as u32,
            )));
        }
        if let Some(index) = used_sources.iter().position(|used| !used) {
            return Err(VirSourceMapErrorKind::UnusedSource(VirSourceId::new(
                index as u32,
            )));
        }
        Ok(())
    }
}

/// Machine-readable source-map validation failures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirSourceMapErrorKind {
    EmptySourceTable,
    NonDenseSourceId {
        expected: VirSourceId,
        found: VirSourceId,
    },
    DuplicateSourceName(String),
    EmptyOriginTable,
    NonDenseOriginId {
        expected: VirOriginId,
        found: VirOriginId,
    },
    DuplicateOrigin(VirOriginKind),
    NonCanonicalOriginOrder,
    UnknownSource(VirSourceId),
    UnknownOrigin(VirOriginId),
    GeneratedReasonRequiresV2 {
        origin: VirOriginId,
        reason: VirGeneratedReason,
    },
    GeneratedReasonRequiresV6 {
        origin: VirOriginId,
        reason: VirGeneratedReason,
    },
    GeneratedReasonWithoutRuntimeLocation {
        origin: VirOriginId,
        reason: VirGeneratedReason,
    },
    SpanOutsideSource {
        source: VirSourceId,
        span: ByteSpan,
        source_len: usize,
    },
    GeneratedParentNotEarlier {
        origin: VirOriginId,
        parent: VirOriginId,
    },
    GeneratedFromEmptySpan(VirOriginId),
    NonCanonicalLocationOrder,
    DuplicateLocation(VirLocation),
    MissingLocation(VirLocation),
    UnexpectedLocation(VirLocation),
    ExpectedGeneratedOrigin {
        location: VirLocation,
        reason: VirGeneratedReason,
    },
    GeneratedReasonMismatch {
        location: VirLocation,
        reason: VirGeneratedReason,
    },
    SpanOutsideFunction {
        location: VirLocation,
        function_span: ByteSpan,
        found: ByteSpan,
    },
    SpanOutsideBlock {
        location: VirLocation,
        block_span: ByteSpan,
        found: ByteSpan,
    },
    LocationSpanMismatch {
        location: VirLocation,
        expected: ByteSpan,
        found: ByteSpan,
    },
    FunctionUsesMultipleSources(VirFunctionId),
    UnusedOrigin(VirOriginId),
    UnusedSource(VirSourceId),
}

#[derive(Clone, Copy)]
enum OriginIntent {
    User(ByteSpan),
    Generated {
        parent_span: ByteSpan,
        reason: VirGeneratedReason,
    },
}

#[derive(Clone, Copy)]
pub(crate) struct VirSourceMapEntry {
    location: VirLocation,
    origin: OriginIntent,
}

impl VirSourceMapEntry {
    #[must_use]
    pub(crate) const fn user(location: VirLocation, span: ByteSpan) -> Self {
        Self {
            location,
            origin: OriginIntent::User(span),
        }
    }

    #[must_use]
    pub(crate) const fn generated(
        location: VirLocation,
        parent_span: ByteSpan,
        reason: VirGeneratedReason,
    ) -> Self {
        Self {
            location,
            origin: OriginIntent::Generated {
                parent_span,
                reason,
            },
        }
    }

    #[must_use]
    pub(crate) const fn location(self) -> VirLocation {
        self.location
    }

    pub(crate) fn set_location(&mut self, location: VirLocation) {
        self.location = location;
    }
}

#[derive(Clone, Copy)]
struct RequiredLocation {
    location: VirLocation,
    expected_span: ByteSpan,
    generated_reason: Option<VirGeneratedReason>,
}

fn runtime_location_intents(runtime: &RuntimeVirProgram) -> Vec<VirSourceMapEntry> {
    required_runtime_locations(runtime)
        .into_iter()
        .map(|required| {
            required.generated_reason.map_or_else(
                || VirSourceMapEntry::user(required.location, required.expected_span),
                |reason| {
                    VirSourceMapEntry::generated(required.location, required.expected_span, reason)
                },
            )
        })
        .collect()
}

fn required_runtime_locations(runtime: &RuntimeVirProgram) -> Vec<RequiredLocation> {
    let mut required = Vec::new();
    for function in &runtime.functions {
        required.push(RequiredLocation {
            location: VirLocation::FunctionEntry {
                function: function.id,
            },
            expected_span: function.source_span,
            generated_reason: None,
        });
        for block in &function.blocks {
            required.push(RequiredLocation {
                location: VirLocation::BlockEntry {
                    function: function.id,
                    block: block.id,
                },
                expected_span: block.source_span,
                generated_reason: (block.id != function.entry)
                    .then_some(VirGeneratedReason::ControlFlowBlock),
            });
            for ordinal in 0..block.parameters.len() {
                required.push(RequiredLocation {
                    location: VirLocation::BlockParameter {
                        function: function.id,
                        block: block.id,
                        ordinal: ordinal as u64,
                    },
                    expected_span: block.source_span,
                    generated_reason: if block.id != function.entry {
                        Some(VirGeneratedReason::BlockParameter)
                    } else if block.parameters[ordinal].ty == VirType::Permission {
                        Some(VirGeneratedReason::PermissionParameter)
                    } else {
                        None
                    },
                });
            }
            for (ordinal, instruction) in block.instructions.iter().enumerate() {
                let ordinal = ordinal as u64;
                required.push(RequiredLocation {
                    location: VirLocation::Instruction {
                        function: function.id,
                        block: block.id,
                        ordinal,
                    },
                    expected_span: instruction.source_span,
                    generated_reason: matches!(
                        instruction.instruction,
                        VirInstruction::LoanBegin { .. }
                            | VirInstruction::LoanAliasShared { .. }
                            | VirInstruction::LoanReborrow { .. }
                            | VirInstruction::LoanEnd { .. }
                            | VirInstruction::LoanAliasAuthority { .. }
                            | VirInstruction::LoanReborrowAuthority { .. }
                            | VirInstruction::LoanEndAuthority { .. }
                    )
                    .then_some(VirGeneratedReason::LoanEffect),
                });
                if matches!(instruction.instruction, VirInstruction::Call { .. }) {
                    required.push(RequiredLocation {
                        location: VirLocation::CallEdge {
                            function: function.id,
                            block: block.id,
                            instruction: ordinal,
                        },
                        expected_span: instruction.source_span,
                        generated_reason: None,
                    });
                }
            }
            required.push(RequiredLocation {
                location: VirLocation::Terminator {
                    function: function.id,
                    block: block.id,
                },
                expected_span: block.terminator.source_span,
                generated_reason: None,
            });
        }
    }
    required.sort_by_key(|required| required.location);
    required
}

fn build_single_source_map(
    source: VirSource,
    mut locations: Vec<VirSourceMapEntry>,
    additional_user_spans: Vec<ByteSpan>,
) -> VirSourceMap {
    let mut user_spans = additional_user_spans.into_iter().collect::<BTreeSet<_>>();
    let mut generated = BTreeSet::new();
    for location in &locations {
        match location.origin {
            OriginIntent::User(span) => {
                user_spans.insert(span);
            }
            OriginIntent::Generated {
                parent_span,
                reason,
            } => {
                user_spans.insert(parent_span);
                generated.insert((parent_span, reason));
            }
        }
    }

    let mut origins = Vec::new();
    let mut users = BTreeMap::new();
    for span in user_spans {
        let id = VirOriginId::new(origins.len() as u32);
        users.insert(span, id);
        origins.push(VirOrigin {
            id,
            kind: VirOriginKind::User {
                source: source.id,
                span,
            },
        });
    }
    let mut generated_origins = BTreeMap::new();
    for (parent_span, reason) in generated {
        let id = VirOriginId::new(origins.len() as u32);
        let parent = users[&parent_span];
        generated_origins.insert((parent_span, reason), id);
        origins.push(VirOrigin {
            id,
            kind: VirOriginKind::Generated { parent, reason },
        });
    }

    let mut entries = locations
        .drain(..)
        .map(|pending| VirLocationOrigin {
            location: pending.location,
            origin: match pending.origin {
                OriginIntent::User(span) => users[&span],
                OriginIntent::Generated {
                    parent_span,
                    reason,
                } => generated_origins[&(parent_span, reason)],
            },
        })
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.location);
    VirSourceMap::from_tables(vec![source], origins, entries)
}

fn mark_origin_chain(
    source_map: &VirSourceMap,
    mut id: VirOriginId,
    used_origins: &mut [bool],
    used_sources: &mut [bool],
) -> Result<(), VirSourceMapErrorKind> {
    for _ in 0..source_map.origins.len() {
        let index = id.get() as usize;
        let Some(used) = used_origins.get_mut(index) else {
            return Err(VirSourceMapErrorKind::UnknownOrigin(id));
        };
        *used = true;
        match &source_map.origins[index].kind {
            VirOriginKind::User { source, .. } => {
                let Some(used) = used_sources.get_mut(source.get() as usize) else {
                    return Err(VirSourceMapErrorKind::UnknownSource(*source));
                };
                *used = true;
                return Ok(());
            }
            VirOriginKind::Generated { parent, .. } => id = *parent,
        }
    }
    Err(VirSourceMapErrorKind::UnknownOrigin(id))
}

fn generated_reason_matches(
    location: VirLocation,
    reason: VirGeneratedReason,
    function: &VirFunction,
) -> bool {
    match (location, reason) {
        (VirLocation::BlockEntry { block, .. }, VirGeneratedReason::ControlFlowBlock) => {
            block != function.entry
        }
        (VirLocation::BlockParameter { block, .. }, VirGeneratedReason::BlockParameter) => {
            block != function.entry
        }
        (
            VirLocation::BlockParameter { block, ordinal, .. },
            VirGeneratedReason::PermissionParameter,
        ) => {
            block == function.entry
                && function
                    .blocks
                    .iter()
                    .find(|candidate| candidate.id == block)
                    .and_then(|block| block.parameters.get(ordinal as usize))
                    .is_some_and(|parameter| parameter.ty == VirType::Permission)
        }
        (VirLocation::Terminator { block, .. }, VirGeneratedReason::ControlFlowEdge) => function
            .blocks
            .iter()
            .find(|candidate| candidate.id == block)
            .is_some_and(|block| {
                matches!(
                    block.terminator.terminator,
                    super::VirTerminator::Jump { .. } | super::VirTerminator::Branch { .. }
                )
            }),
        (VirLocation::Terminator { block, .. }, VirGeneratedReason::ImplicitReturn) => function
            .blocks
            .iter()
            .find(|candidate| candidate.id == block)
            .is_some_and(|block| {
                matches!(
                    block.terminator.terminator,
                    super::VirTerminator::Return { .. }
                )
            }),
        (VirLocation::Instruction { block, ordinal, .. }, VirGeneratedReason::LoopIncrement) => {
            function
                .blocks
                .iter()
                .find(|candidate| candidate.id == block)
                .and_then(|block| block.instructions.get(ordinal as usize))
                .is_some_and(|instruction| {
                    matches!(
                        instruction.instruction,
                        VirInstruction::Constant {
                            value: super::VirConstant::U64(1),
                            ..
                        } | VirInstruction::WordAdd { .. }
                    )
                })
        }
        (VirLocation::Instruction { block, ordinal, .. }, VirGeneratedReason::TemporaryStorage) => {
            function
                .blocks
                .iter()
                .find(|candidate| candidate.id == block)
                .and_then(|block| block.instructions.get(ordinal as usize))
                .is_some_and(|instruction| {
                    matches!(instruction.instruction, VirInstruction::LocalStorage { .. })
                })
        }
        (VirLocation::Instruction { block, ordinal, .. }, VirGeneratedReason::ImplicitCopy) => {
            function
                .blocks
                .iter()
                .find(|candidate| candidate.id == block)
                .and_then(|block| block.instructions.get(ordinal as usize))
                .is_some_and(|instruction| {
                    matches!(
                        instruction.instruction,
                        VirInstruction::ObjectTransfer {
                            source_mode: super::VirObjectSourceMode::Copy,
                            ..
                        }
                    )
                })
        }
        (VirLocation::Instruction { block, ordinal, .. }, VirGeneratedReason::ImplicitMove) => {
            function
                .blocks
                .iter()
                .find(|candidate| candidate.id == block)
                .and_then(|block| block.instructions.get(ordinal as usize))
                .is_some_and(|instruction| {
                    matches!(
                        instruction.instruction,
                        VirInstruction::ObjectTransfer {
                            source_mode: super::VirObjectSourceMode::Move,
                            ..
                        }
                    )
                })
        }
        (VirLocation::Instruction { block, ordinal, .. }, VirGeneratedReason::ImplicitDrop) => {
            function
                .blocks
                .iter()
                .find(|candidate| candidate.id == block)
                .and_then(|block| block.instructions.get(ordinal as usize))
                .is_some_and(|instruction| {
                    matches!(
                        instruction.instruction,
                        VirInstruction::DropOwn { .. }
                            | VirInstruction::ObjectDrop { .. }
                            | VirInstruction::Constant {
                                value: super::VirConstant::Bool(_),
                                ..
                            }
                    )
                })
        }
        (VirLocation::Instruction { block, ordinal, .. }, VirGeneratedReason::LoanEffect) => {
            function
                .blocks
                .iter()
                .find(|candidate| candidate.id == block)
                .and_then(|block| block.instructions.get(ordinal as usize))
                .is_some_and(|instruction| {
                    matches!(
                        instruction.instruction,
                        VirInstruction::LoanBegin { .. }
                            | VirInstruction::LoanAliasShared { .. }
                            | VirInstruction::LoanReborrow { .. }
                            | VirInstruction::LoanEnd { .. }
                            | VirInstruction::LoanAliasAuthority { .. }
                            | VirInstruction::LoanReborrowAuthority { .. }
                            | VirInstruction::LoanEndAuthority { .. }
                    )
                })
        }
        (
            VirLocation::CallEdge {
                block, instruction, ..
            },
            VirGeneratedReason::CallTransfer,
        ) => function
            .blocks
            .iter()
            .find(|candidate| candidate.id == block)
            .and_then(|block| block.instructions.get(instruction as usize))
            .is_some_and(|instruction| {
                matches!(instruction.instruction, VirInstruction::Call { .. })
            }),
        (VirLocation::Terminator { block, .. }, VirGeneratedReason::ReturnTransfer) => function
            .blocks
            .iter()
            .find(|candidate| candidate.id == block)
            .is_some_and(|block| {
                matches!(
                    block.terminator.terminator,
                    super::VirTerminator::Return { .. }
                )
            }),
        _ => false,
    }
}

impl VirGeneratedReason {
    const fn requires_v2(self) -> bool {
        matches!(
            self,
            Self::TemporaryStorage
                | Self::ImplicitCopy
                | Self::ImplicitMove
                | Self::ImplicitDrop
                | Self::ScopeCleanup
                | Self::BranchCleanup
                | Self::CallTransfer
                | Self::ReturnTransfer
                | Self::LoanEffect
        )
    }
}

fn inferred_source_len(runtime: &RuntimeVirProgram) -> usize {
    runtime
        .functions
        .iter()
        .flat_map(|function| {
            std::iter::once(function.source_span.end()).chain(function.blocks.iter().flat_map(
                |block| {
                    std::iter::once(block.source_span.end())
                        .chain(
                            block
                                .instructions
                                .iter()
                                .map(|instruction| instruction.source_span.end()),
                        )
                        .chain(std::iter::once(block.terminator.source_span.end()))
                },
            ))
        })
        .max()
        .unwrap_or(0)
}

pub(super) fn hand_authored_source_map(runtime: &RuntimeVirProgram) -> VirSourceMap {
    VirSourceMap::from_runtime_source("<hand-authored-vir>", inferred_source_len(runtime), runtime)
}
