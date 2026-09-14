mod recursive;
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use crate::{ByteSpan, ResolvedVirUnit, Severity, VirFunctionId, VirLocation};

use super::cfg::{
    CfgAnalysisConfig, CfgAnalysisError, CfgObligation, FunctionCfgAnalysis,
    analyze_function_cfg_with_summaries,
};
use super::contract::{ContractCheck, check_postconditions, instantiate_contracts};
use super::finding::VerifierFinding;
use super::spec::{SpecProof, TrustReportEntry, collect_trust_entries, prove_function_specs};
use super::transfer::{ObligationStatus, ResourceObligation, ResourceObligationKind};

fn analyze_one(
    program: &ResolvedVirUnit<'_>,
    id: VirFunctionId,
    contracts: &super::contract::InstantiatedContracts,
    config: CfgAnalysisConfig,
    summaries: &super::summary::SummaryRegistry,
    summary_unit: &std::sync::Arc<str>,
) -> Result<FunctionVerification, VerificationError> {
    let function = program
        .runtime()
        .functions
        .iter()
        .find(|f| f.id == id)
        .unwrap();
    let contract = contracts
        .get(function.contract)
        .ok_or(VerificationError::ContractInstantiation)?;
    let cfg = analyze_function_cfg_with_summaries(
        program,
        function.id,
        contracts,
        config,
        Some(summaries),
    )
    .map_err(|error| VerificationError::Cfg {
        function: function.id,
        error,
    })?;
    let mut postconditions = Vec::new();
    let parameters = function
        .blocks
        .iter()
        .find(|b| b.id == function.entry)
        .unwrap()
        .parameters
        .iter()
        .map(|p| p.id)
        .collect::<Vec<_>>();
    if function.id == program.runtime().entry {
        let (_, checks) = super::contract::check_preconditions(
            cfg.function_entry_state(),
            &parameters,
            contract,
            config,
        );
        for check in checks {
            postconditions.push(FunctionPostconditionCheck {
                finding: VerifierFinding::clause(program, check.clause, None)
                    .ok_or(VerificationError::InvalidFinding)?,
                check,
            });
        }
    }
    for check in super::contract::frame::check(program, function, &cfg, &parameters, config) {
        postconditions.push(FunctionPostconditionCheck {
            finding: VerifierFinding::clause(program, check.clause, None)
                .ok_or(VerificationError::InvalidFinding)?,
            check,
        });
    }
    for returned in cfg.returns() {
        let mut checks = check_postconditions(returned.state(), returned.values(), contract);
        if let Some(resources) = &contract.resources {
            let block = function
                .blocks
                .iter()
                .find(|b| b.id == returned.block())
                .unwrap();
            if let crate::VirTerminator::Return { values } = &block.terminator.terminator {
                checks.extend(resources.check(
                    returned.observation_state(),
                    cfg.function_entry_state(),
                    &parameters,
                    values,
                    crate::VirContractPosition::Ensures,
                    config,
                ));
            }
        }
        if let Some(pure) = &contract.pure {
            let block = function
                .blocks
                .iter()
                .find(|b| b.id == returned.block())
                .unwrap();
            if let crate::VirTerminator::Return { values } = &block.terminator.terminator {
                checks.extend(pure.check(
                    returned.observation_state(),
                    cfg.function_entry_state(),
                    &parameters,
                    values,
                    crate::VirContractPosition::Ensures,
                    config.relation_limits,
                ));
            }
        }
        for check in checks {
            let occurrence = VirLocation::Terminator {
                function: function.id,
                block: returned.block(),
            };
            postconditions.push(FunctionPostconditionCheck {
                finding: VerifierFinding::clause(program, check.clause, Some(occurrence))
                    .ok_or(VerificationError::InvalidFinding)?,
                check,
            });
        }
    }
    let proofs = prove_function_specs(program, function, &cfg, config)
        .ok_or(VerificationError::InvalidFinding)?;

    let summary = super::summary::project(
        program,
        function,
        &cfg,
        &postconditions,
        &proofs,
        super::summary::SummaryBinding::new(summary_unit.clone(), function.id, config),
    )
    .map_err(|error| VerificationError::Summary {
        function: function.id,
        error,
    })?;

    Ok(FunctionVerification {
        summary,
        cfg,
        postconditions,
        proofs,
    })
}

/// Stable diagnostic classification for verifier failures.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VerifierDiagnosticKind {
    RefutedObligation,
    MissingFact,
    RefutedPostcondition,
    MissingPostconditionFact,
    RefutedProof,
    UnknownProof,
}

/// User-facing memory-verifier diagnostic with an optional contract edit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifierDiagnostic {
    provenance_notes: Vec<super::provenance::ProvenanceNote>,
    kind: VerifierDiagnosticKind,
    severity: Severity,
    finding: VerifierFinding,
    message: String,
    suggestion: Option<String>,
    relation_queries: Vec<super::relation::audit::QueryEvidence>,
}

impl VerifierDiagnostic {
    #[must_use]
    pub fn provenance_notes(&self) -> &[super::provenance::ProvenanceNote] {
        &self.provenance_notes
    }
    /// Query-local outcomes at this access. These may be auxiliary attempts;
    /// an Unknown query alone does not identify the cause of every obligation.
    #[must_use]
    pub fn relation_queries(&self) -> &[super::relation::audit::QueryEvidence] {
        &self.relation_queries
    }
    #[must_use]
    pub const fn kind(&self) -> VerifierDiagnosticKind {
        self.kind
    }

    #[must_use]
    pub const fn severity(&self) -> Severity {
        self.severity
    }

    #[must_use]
    pub const fn function(&self) -> VirFunctionId {
        self.finding.site().function()
    }

    #[must_use]
    pub const fn source_span(&self) -> ByteSpan {
        self.finding.source_span()
    }

    #[must_use]
    pub const fn finding(&self) -> VerifierFinding {
        self.finding
    }

    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    #[must_use]
    pub fn suggestion(&self) -> Option<&str> {
        self.suggestion.as_deref()
    }
}

/// One checked `ensures` clause at a concrete return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunctionPostconditionCheck {
    finding: VerifierFinding,
    check: ContractCheck,
}

impl FunctionPostconditionCheck {
    #[must_use]
    pub const fn source_span(&self) -> ByteSpan {
        self.finding.source_span()
    }

    #[must_use]
    pub const fn finding(&self) -> VerifierFinding {
        self.finding
    }

    #[must_use]
    pub const fn check(&self) -> ContractCheck {
        self.check
    }
}

/// Complete modular result for one function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionVerification {
    summary: super::summary::FunctionSummary,
    cfg: FunctionCfgAnalysis,
    postconditions: Vec<FunctionPostconditionCheck>,
    proofs: Vec<SpecProof>,
}

impl FunctionVerification {
    /// Diagnostic interface observations, not an importable call-authorizing certificate.
    pub const fn summary(&self) -> &super::summary::FunctionSummary {
        &self.summary
    }
    #[must_use]
    pub const fn cfg(&self) -> &FunctionCfgAnalysis {
        &self.cfg
    }

    #[must_use]
    pub fn postconditions(&self) -> &[FunctionPostconditionCheck] {
        &self.postconditions
    }

    #[must_use]
    pub fn proofs(&self) -> &[SpecProof] {
        &self.proofs
    }

    #[must_use]
    pub fn is_verified(&self) -> bool {
        self.cfg.all_obligations_proven()
            && self
                .postconditions
                .iter()
                .all(|check| check.check.status.is_proven())
            && self.proofs.iter().all(|proof| proof.status().is_proven())
    }
}

/// Registered assumptions imported into the proof, retained as an explicit
/// report rather than being flattened into anonymous facts.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VerifierTrustReport {
    entries: Vec<TrustReportEntry>,
}

impl VerifierTrustReport {
    #[must_use]
    pub fn entries(&self) -> &[TrustReportEntry] {
        &self.entries
    }
}

/// Stage-5 whole-program verifier result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramVerification {
    functions: BTreeMap<VirFunctionId, FunctionVerification>,
    diagnostics: Vec<VerifierDiagnostic>,
    trust_report: VerifierTrustReport,
}

impl ProgramVerification {
    #[must_use]
    pub const fn functions(&self) -> &BTreeMap<VirFunctionId, FunctionVerification> {
        &self.functions
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[VerifierDiagnostic] {
        &self.diagnostics
    }

    #[must_use]
    pub const fn trust_report(&self) -> &VerifierTrustReport {
        &self.trust_report
    }

    /// Internal stage-5 result. This deliberately does not claim the later
    /// `memory-checked-by-rust` publication status.
    #[must_use]
    pub fn is_memory_checked_core0(&self) -> bool {
        self.functions
            .values()
            .all(FunctionVerification::is_verified)
            && self.diagnostics.is_empty()
    }
}

/// Verifies every function body against its contract, then reports all final
/// CFG and postcondition failures in deterministic order.
pub fn verify_program(
    program: &ResolvedVirUnit<'_>,
    config: CfgAnalysisConfig,
) -> Result<ProgramVerification, VerificationError> {
    #[cfg(test)]
    crate::verification::scale_tests::assert_not_rendering();
    let contracts =
        instantiate_contracts(program).map_err(|_| VerificationError::ContractInstantiation)?;

    let mut functions = BTreeMap::new();
    let summary_unit = super::summary::SummaryBinding::unit(program);
    let mut diagnostics = Vec::new();
    let mut summaries = super::summary::SummaryRegistry::new(super::summary::SummaryBinding::new(
        summary_unit.clone(),
        program.runtime().entry,
        config,
    ));
    for component in super::summary::components(program) {
        if component.recursive {
            functions.extend(recursive::analyze(
                program,
                &component.members,
                &contracts,
                config,
                &mut summaries,
                &summary_unit,
            )?);
        } else {
            let id = component.members[0];
            let mut verification =
                analyze_one(program, id, &contracts, config, &summaries, &summary_unit)?;
            let function = program
                .runtime()
                .functions
                .iter()
                .find(|f| f.id == id)
                .unwrap();
            summaries.close(&function.name, &mut verification.summary);
            functions.insert(id, verification);
        }
    }
    // Provisional SCC findings never escape. Diagnostics belong only to the
    // final closed replay or the untouched published-registry fallback.
    for verification in functions.values() {
        diagnostics.extend(
            verification
                .cfg
                .obligations()
                .iter()
                .filter(|record| !record.obligation().is_proven())
                .map(|record| {
                    diagnostic_for_obligation(
                        record,
                        verification.cfg.relation_queries(),
                        verification.cfg.provenance_evidence(),
                    )
                }),
        );
        diagnostics.extend(
            verification
                .postconditions
                .iter()
                .filter(|record| !record.check.status.is_proven())
                .map(|record| diagnostic_for_postcondition(*record, program)),
        );
        diagnostics.extend(
            verification
                .proofs
                .iter()
                .filter(|proof| !proof.status().is_proven())
                .map(diagnostic_for_proof),
        );
    }

    diagnostics.sort_by(|left, right| {
        let left_span = left.finding.source_span();
        let right_span = right.finding.source_span();
        (
            left.finding.source(),
            left_span.start(),
            left_span.end(),
            left.finding.site(),
            left.finding.origin(),
            left.kind,
            left.message.as_str(),
            left.suggestion.as_deref(),
        )
            .cmp(&(
                right.finding.source(),
                right_span.start(),
                right_span.end(),
                right.finding.site(),
                right.finding.origin(),
                right.kind,
                right.message.as_str(),
                right.suggestion.as_deref(),
            ))
    });
    let mut trust_entries =
        collect_trust_entries(program).ok_or(VerificationError::InvalidFinding)?;
    trust_entries.sort_by_key(|entry| (entry.finding(), entry.id()));

    Ok(ProgramVerification {
        functions,
        diagnostics,
        trust_report: VerifierTrustReport {
            entries: trust_entries,
        },
    })
}

fn diagnostic_for_proof(proof: &SpecProof) -> VerifierDiagnostic {
    let unknown = proof.status() == ObligationStatus::Unknown;
    VerifierDiagnostic {
        relation_queries: proof.relation_queries().to_vec(),
        provenance_notes: Vec::new(),
        kind: if unknown {
            VerifierDiagnosticKind::UnknownProof
        } else {
            VerifierDiagnosticKind::RefutedProof
        },
        severity: Severity::Error,
        finding: proof.finding(),
        message: if unknown {
            format!(
                "cannot prove specification obligation {}: {}",
                proof.prove().get(),
                proof
                    .failure()
                    .map_or("unknown reason", super::spec::SpecFailure::description)
            )
        } else {
            format!(
                "specification obligation {} is false: {}",
                proof.prove().get(),
                proof
                    .failure()
                    .map_or("unknown reason", super::spec::SpecFailure::description)
            )
        },
        suggestion: Some(
            "strengthen dominating facts, provide a valid witness, or weaken the `prove` clause"
                .to_owned(),
        ),
    }
}

fn diagnostic_for_obligation(
    record: &CfgObligation,
    queries: &[super::relation::audit::QueryEvidence],
    evidence: &[super::provenance::ProvenanceEvidence],
) -> VerifierDiagnostic {
    let obligation = record.obligation();
    let missing = obligation.status() == ObligationStatus::Unknown;
    let subject = describe_obligation(obligation);
    let relation_queries: Vec<_> = queries
        .iter()
        .filter(|q| q.finding == record.finding())
        .cloned()
        .collect();
    let mut message = if missing {
        format!("cannot prove {subject}")
    } else {
        format!("required memory-safety condition is false: {subject}")
    };
    if !relation_queries.is_empty() {
        use super::relation::audit::QueryOutcome;
        let mut notes = Vec::new();
        for (outcome, note) in [
            (
                QueryOutcome::RefutedCondition,
                "negated numeric condition proved (not an execution counterexample)",
            ),
            (
                QueryOutcome::MissingRelation,
                "insufficient range relations",
            ),
            (
                QueryOutcome::BudgetExhausted,
                "deterministic relation budget exhausted",
            ),
            (
                QueryOutcome::UnsupportedTheory,
                "unsupported relation theory",
            ),
            (
                QueryOutcome::InconsistentPremises,
                "inconsistent arithmetic premises; no resource unreachability inferred",
            ),
        ] {
            if relation_queries.iter().any(|q| q.query.outcome == outcome) {
                notes.push(note);
            }
        }
        if !notes.is_empty() {
            message.push_str(&format!("; queries at this access: {}", notes.join(", ")));
        }
    }
    let provenance_notes: Vec<_> = evidence
        .iter()
        .filter(|e| e.finding == record.finding())
        .flat_map(|e| {
            e.obligations
                .iter()
                .filter(|o| o.kind() == obligation.kind())
                .filter_map(|o| {
                    e.issue(*o).map(|issue| super::provenance::ProvenanceNote {
                        case_ordinal: e.case_ordinal,
                        issue,
                        sources: e.sources.clone(),
                        sources_truncated: e.sources_truncated,
                    })
                })
        })
        .collect();
    let issues: std::collections::BTreeSet<_> = provenance_notes.iter().map(|n| n.issue).collect();
    for issue in issues {
        message.push_str("; ");
        message.push_str(issue.description());
    }
    VerifierDiagnostic {
        provenance_notes,
        relation_queries,
        kind: if missing {
            VerifierDiagnosticKind::MissingFact
        } else {
            VerifierDiagnosticKind::RefutedObligation
        },
        severity: Severity::Error,
        finding: record.finding(),
        message,
        suggestion: contract_suggestion(obligation.kind()),
    }
}

fn diagnostic_for_postcondition(
    record: FunctionPostconditionCheck,
    program: &ResolvedVirUnit<'_>,
) -> VerifierDiagnostic {
    let missing = record.check.status == ObligationStatus::Unknown;
    if let Some(crate::VirSpecClause {
        kind: crate::VirSpecClauseKind::Assertion { root },
        ..
    }) = program.as_unit().specs.clause(record.check.clause)
        && let crate::SpecAssertionKind::Footprint { write, .. } =
            program.as_unit().specs.assertions()[root.get() as usize].kind
    {
        let name = if write { "writes" } else { "reads" };
        return VerifierDiagnostic {
            relation_queries: Vec::new(), provenance_notes: Vec::new(),
            kind: if missing { VerifierDiagnosticKind::MissingFact } else { VerifierDiagnosticKind::RefutedObligation },
            severity: Severity::Error, finding: record.finding,
            message: format!("{} `{name}` frame for clause {}", if missing { "cannot prove" } else { "actual effects exceed" }, record.check.clause.get()),
            suggestion: Some("cover actual entry-bound effects, or omit this upper bound to use automatic effect inference; declarations do not grant memory access".into()),
        };
    }
    if record.check.origin.position() == crate::VirContractPosition::Requires {
        return VerifierDiagnostic {
            relation_queries: Vec::new(), provenance_notes: Vec::new(),
            kind: if missing { VerifierDiagnosticKind::MissingFact } else { VerifierDiagnosticKind::RefutedObligation },
            severity: Severity::Error, finding: record.finding,
            message: format!("whole-program entry cannot establish `requires` clause {} without a caller", record.check.clause.get()),
            suggestion: Some("remove the entry assumption or establish the condition in the entry body before calling a contracted function".into()),
        };
    }
    VerifierDiagnostic {
        relation_queries: Vec::new(),
        provenance_notes: Vec::new(),
        kind: if missing {
            VerifierDiagnosticKind::MissingPostconditionFact
        } else {
            VerifierDiagnosticKind::RefutedPostcondition
        },
        severity: Severity::Error,
        finding: record.finding,
        message: if missing {
            format!(
                "cannot prove function postcondition clause {}",
                record.check.clause.get()
            )
        } else {
            format!(
                "function return violates postcondition clause {}",
                record.check.clause.get()
            )
        },
        suggestion: Some(format!(
            "strengthen the implementation or weaken `ensures` clause {}",
            record.check.clause.get()
        )),
    }
}

fn describe_obligation(obligation: ResourceObligation) -> String {
    match obligation.kind() {
        ResourceObligationKind::PointerProvenanceKnown { pointer } => {
            format!("pointer %{} has known provenance", pointer.get())
        }
        ResourceObligationKind::PointerMemoryAccessMatches {
            pointer, expected, ..
        } => format!(
            "pointer %{} denotes canonical type{}/layout{}",
            pointer.get(),
            expected.ty.get(),
            expected.layout.get()
        ),
        ResourceObligationKind::IndexWithinBounds { index, length, .. } => {
            format!("index %{} is below array length {length}", index.get())
        }
        ResourceObligationKind::IndexStrideNoOverflow {
            index,
            stride_bytes,
            ..
        } => format!(
            "index %{} multiplied by stride {stride_bytes} does not overflow",
            index.get()
        ),
        ResourceObligationKind::SliceIndexWithinBounds { index, length, .. } => format!(
            "slice index %{} is below runtime length %{}",
            index.get(),
            length.get()
        ),
        ResourceObligationKind::SliceRangeOrdered { start, end, .. } => {
            format!("slice start %{} is at most end %{}", start.get(), end.get())
        }
        ResourceObligationKind::SliceRangeWithinBounds { end, .. } => {
            format!("slice end %{} is within its source length", end.get())
        }
        ResourceObligationKind::SliceRangeStrideNoOverflow { stride_bytes, .. } => {
            format!("slice length multiplied by stride {stride_bytes} does not overflow")
        }
        ResourceObligationKind::BorrowProjectionRangeOrdered { source_parameter } => {
            format!("borrow-result slice range for parameter {source_parameter} has start <= end")
        }
        ResourceObligationKind::BorrowProjectionRangeWithinSource { source_parameter } => format!(
            "borrow-result slice range for parameter {source_parameter} ends within the caller source view"
        ),
        ResourceObligationKind::AddressCalculationNoOverflow { base, .. } => format!(
            "address calculation from pointer %{} does not overflow",
            base.get()
        ),
        ResourceObligationKind::AddressObjectWithinBounds { .. } => {
            "projected object is within allocation bounds".to_owned()
        }
        ResourceObligationKind::AddressObjectAligned {
            pointer,
            required_alignment,
        } => format!(
            "projected pointer %{} is aligned to {required_alignment} bytes",
            pointer.get()
        ),
        ResourceObligationKind::AllocationLive { allocation } => {
            format!("allocation {allocation} is live")
        }
        ResourceObligationKind::AllocationInstanceFresh {
            allocation: Some(allocation),
        } => {
            format!(
                "allocation slot {allocation} can represent a fresh instance without discarding an outstanding owner or loan"
            )
        }
        ResourceObligationKind::AllocationInstanceFresh { allocation: None } => {
            "a fresh allocation instance fits the identity slot budget".to_owned()
        }
        ResourceObligationKind::AccessWithinBounds { .. } => {
            "memory access is within allocation bounds".to_owned()
        }
        ResourceObligationKind::MemoryInitialized { .. } => {
            "loaded memory is initialized".to_owned()
        }
        ResourceObligationKind::ObjectValueBytesInitialized { object, .. } => format!(
            "all active value bytes of type{}/layout{} are initialized",
            object.ty.get(),
            object.layout.get()
        ),
        ResourceObligationKind::ObjectValueBytesUninitialized { object, .. } => format!(
            "all destination value bytes of type{}/layout{} are uninitialized",
            object.ty.get(),
            object.layout.get()
        ),
        ResourceObligationKind::ObjectRepresentationValid { object, .. } => format!(
            "type{}/layout{} has a valid active representation",
            object.ty.get(),
            object.layout.get()
        ),
        ResourceObligationKind::ObjectActiveVariantKnown { access, .. } => format!(
            "enum type{}/layout{} has a known finite active variant",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::ActiveVariantAllowsAccess {
            pointer,
            enum_access,
            ..
        } => format!(
            "pointer %{} addresses the active payload of enum type{}/layout{}",
            pointer.get(),
            enum_access.ty.get(),
            enum_access.layout.get()
        ),
        ResourceObligationKind::ObjectAllocationLive { pointer, .. } => {
            format!("object addressed by pointer %{} is live", pointer.get())
        }
        ResourceObligationKind::ObjectWithinBounds {
            pointer,
            size_bytes,
            ..
        } => format!(
            "the {size_bytes}-byte object addressed by pointer %{} is within allocation bounds",
            pointer.get()
        ),
        ResourceObligationKind::ObjectAligned {
            pointer,
            required_alignment,
        } => format!(
            "object pointer %{} is aligned to {required_alignment} bytes",
            pointer.get()
        ),
        ResourceObligationKind::ObjectStateWithinBudget { allocation } => format!(
            "enum subobject metadata for allocation {allocation} remains within the verifier precision budget"
        ),
        ResourceObligationKind::ObjectNonOverlapping {
            destination,
            source,
            ..
        } => format!(
            "object ranges at destination %{} and source %{} do not overlap",
            destination.get(),
            source.get()
        ),
        ResourceObligationKind::ObjectTriviallyCopyable { access } => format!(
            "type{}/layout{} is in the verifier's trivially-copyable object subset",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::ObjectMoveSupported { access } => format!(
            "type{}/layout{} has a supported canonical move representation",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::ObjectTriviallyDroppable { access } => format!(
            "type{}/layout{} is in the verifier's trivially-droppable object subset",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::ObjectBuiltinDroppable { access } => format!(
            "type{}/layout{} has canonical builtin drop glue",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::ObjectResourcePayloadEmpty {
            allocation,
            offset_bytes,
            access,
        } => format!(
            "object type{}/layout{} at allocation {allocation:?} offset {offset_bytes:?} has no remaining resource payload before representation construction",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::ObjectDropPayloadValid {
            allocation,
            offset_bytes,
            access,
        } => format!(
            "owner payload type{}/layout{} at allocation {allocation:?} offset {offset_bytes:?} is valid for exactly-once drop",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::AggregateAbiPayloadValid {
            allocation,
            offset_bytes,
            access,
        } => format!(
            "aggregate ABI owner payload type{}/layout{} at allocation {allocation:?} offset {offset_bytes:?} is available for exactly-once transfer",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::DropFlagKnown { condition } => format!(
            "drop flag %{} is determined on this guarded path",
            condition.get()
        ),
        ResourceObligationKind::ResourcePayloadLocationExact {
            pointer, access, ..
        } => format!(
            "resource pointer %{} selects one exact type{}/layout{} move path",
            pointer.get(),
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::ResourcePayloadAvailable { access, .. } => format!(
            "type{}/layout{} move path contains one available typed owner payload",
            access.ty.get(),
            access.layout.get()
        ),
        ResourceObligationKind::AllocationResourcePayloadEmpty { allocation } => {
            format!("allocation {allocation} contains no live nested owner payload")
        }
        ResourceObligationKind::PermissionAvailable { permission } => {
            format!("permission %{} is still available", permission.get())
        }
        ResourceObligationKind::PermissionWritable { permission } => {
            format!("permission %{} permits mutation", permission.get())
        }
        ResourceObligationKind::PermissionCoversAccess { permission, .. } => {
            format!(
                "permission %{} covers the accessed byte range",
                permission.get()
            )
        }
        ResourceObligationKind::PermissionSplitPointInRange { permission, .. } => {
            format!("split point lies within permission %{}", permission.get())
        }
        ResourceObligationKind::LoanRangeContained {
            loan,
            permission,
            range,
        } => format!(
            "loan l{} byte range {}..{} is covered by pointer provenance and permission %{}",
            loan.get(),
            range.start(),
            range.end(),
            permission.get()
        ),
        ResourceObligationKind::LoanCompatible {
            loan,
            permission,
            required,
            ..
        } => format!(
            "permission %{} has authority compatible with {required:?} access{}",
            permission.get(),
            loan.map_or_else(String::new, |loan| format!(" through loan l{}", loan.get()))
        ),
        ResourceObligationKind::LoanPairQueriesWithinBudget { queries, limit } => {
            format!("loan-pair query count {queries} is within per-instruction budget {limit}")
        }
        ResourceObligationKind::LoanParentActive { loan, parent } => format!(
            "parent loan l{} has a live reborrow authority containing child loan l{}",
            parent.get(),
            loan.get()
        ),
        ResourceObligationKind::LoanRegionIncluded { loan, parent } => format!(
            "child loan l{} region is included in parent loan l{} region",
            loan.get(),
            parent.get()
        ),
        ResourceObligationKind::LoanEndedExactlyOnce { loan } => {
            format!(
                "loan l{} and all of its authorities end exactly once",
                loan.get()
            )
        }
        ResourceObligationKind::LoanWithinBudget { loan, limit } => format!(
            "loan l{} fits the per-case active-loan limit {limit}",
            loan.get()
        ),
        ResourceObligationKind::LoanAliasWithinBudget { loan, limit } => format!(
            "loan l{} fits the per-loan authority limit {limit}",
            loan.get()
        ),
        ResourceObligationKind::LoanReborrowDepthWithinBudget { loan, limit } => {
            format!("loan l{} fits the reborrow-depth limit {limit}", loan.get())
        }
        ResourceObligationKind::OwnershipConserved { allocation } => format!(
            "owned allocation {allocation} is dropped, freed, or transferred exactly once at this return"
        ),
        ResourceObligationKind::CallContractAvailable { contract } => {
            format!(
                "contract{} is signature-checked and explicit guarantees have a closed or scoped inductive interface",
                contract.get()
            )
        }
        ResourceObligationKind::CallContractPrecondition {
            contract, clause, ..
        } => format!(
            "call satisfies contract{} `requires` clause {}",
            contract.get(),
            clause.get()
        ),
        _ => format!("{:?}", obligation.kind()),
    }
}

fn contract_suggestion(kind: ResourceObligationKind) -> Option<String> {
    match kind {
        ResourceObligationKind::PointerProvenanceKnown { pointer } => Some(format!(
            "add a checked pointer/`Own<T>` precondition for %{}",
            pointer.get()
        )),
        ResourceObligationKind::PointerMemoryAccessMatches { pointer, .. } => Some(format!(
            "preserve the canonical object type while deriving pointer %{}",
            pointer.get()
        )),
        ResourceObligationKind::IndexWithinBounds { index, length, .. } => Some(format!(
            "add a dominating check that %{} is below {length}",
            index.get()
        )),
        ResourceObligationKind::IndexStrideNoOverflow { index, .. } => Some(format!(
            "bound index %{} before scaling it by the element stride",
            index.get()
        )),
        ResourceObligationKind::SliceIndexWithinBounds { index, length, .. } => Some(format!(
            "prove that slice index %{} is below length %{}",
            index.get(),
            length.get()
        )),
        ResourceObligationKind::SliceRangeOrdered { start, end, .. } => Some(format!(
            "prove that range start %{} does not exceed end %{}",
            start.get(),
            end.get()
        )),
        ResourceObligationKind::SliceRangeWithinBounds { end, .. } => Some(format!(
            "prove that range end %{} does not exceed the source length",
            end.get()
        )),
        ResourceObligationKind::SliceRangeStrideNoOverflow { .. } => {
            Some("bound the slice length before scaling it by the element stride".to_owned())
        }
        ResourceObligationKind::BorrowProjectionRangeOrdered { .. } => Some(
            "establish that the projected range start does not exceed its end before this call"
                .to_owned(),
        ),
        ResourceObligationKind::BorrowProjectionRangeWithinSource { .. } => Some(
            "establish that the projected range end does not exceed the source slice length before this call"
                .to_owned(),
        ),
        ResourceObligationKind::AddressCalculationNoOverflow { base, .. } => Some(format!(
            "bound the offset derived from pointer %{}",
            base.get()
        )),
        ResourceObligationKind::AddressObjectWithinBounds { .. } => {
            Some("prove that the complete projected object fits the allocation".to_owned())
        }
        ResourceObligationKind::AddressObjectAligned { .. } => {
            Some("preserve the alignment required by the projected layout".to_owned())
        }
        ResourceObligationKind::AllocationLive { .. } => {
            Some("require the referenced allocation to be live at this point".to_owned())
        }
        ResourceObligationKind::AllocationInstanceFresh { allocation: Some(_) } => {
            Some("retire the previous instance and its loans before reusing this site; simultaneous instances at one site require a richer heap model".to_owned())
        }
        ResourceObligationKind::AllocationInstanceFresh { allocation: None } => {
            Some("reduce simultaneously tracked allocation sites or split the function proof; identity budget exhaustion cannot evict outstanding resources".to_owned())
        }
        ResourceObligationKind::AccessWithinBounds { .. } => {
            Some("add a range precondition or a dominating bounds check".to_owned())
        }
        ResourceObligationKind::MemoryInitialized { .. } => {
            Some("initialize this range or require it to be initialized".to_owned())
        }
        ResourceObligationKind::ObjectValueBytesInitialized { .. } => Some(
            "initialize every active field before copying, moving, replacing, or deinitializing the object"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectValueBytesUninitialized { .. } => Some(
            "use initialize only for fresh storage; use replace for a complete old value"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectRepresentationValid { .. } => Some(
            "construct the object through typed writes and establish its active enum variant"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectActiveVariantKnown { .. }
        | ResourceObligationKind::ActiveVariantAllowsAccess { .. } => Some(
            "refine the enum with a dominating match/discriminant check before accessing its payload"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectAllocationLive { .. } => {
            Some("keep the complete source/destination object alive for this effect".to_owned())
        }
        ResourceObligationKind::ObjectWithinBounds { .. } => Some(
            "prove that the complete canonical object shape fits its allocation".to_owned(),
        ),
        ResourceObligationKind::ObjectAligned { .. } => Some(
            "derive the object address with the alignment required by its canonical layout"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectStateWithinBudget { .. } => Some(
            "reduce simultaneously tracked enum subobjects or split the function/module proof"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectNonOverlapping { .. } => Some(
            "derive disjoint source and destination ranges or split their permissions"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectTriviallyCopyable { .. }
        | ResourceObligationKind::ObjectTriviallyDroppable { .. } => Some(
            "copy only Copy values, and drop/replace owning values through the future cleanup effect"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectBuiltinDroppable { .. } => Some(
            "use a sized type with compiler-derived builtin drop glue; user destructors remain gated"
                .to_owned(),
        ),
        ResourceObligationKind::ObjectResourcePayloadEmpty { .. } => Some(
            "clean the old active payload before establishing a new enum representation".to_owned(),
        ),
        ResourceObligationKind::ObjectDropPayloadValid { .. } => Some(
            "preserve each active owner payload and move or drop it exactly once before object cleanup"
                .to_owned(),
        ),
        ResourceObligationKind::AggregateAbiPayloadValid { .. } => Some(
            "initialize every owning aggregate payload before the call/return and transfer it through the canonical indirect ABI buffer"
                .to_owned(),
        ),
        ResourceObligationKind::DropFlagKnown { condition } => Some(format!(
            "preserve the branch fact that determines drop flag %{} or split the cleanup edge",
            condition.get()
        )),
        ResourceObligationKind::ObjectMoveSupported { .. } => Some(
            "move only sized objects whose resource leaves have a supported ownership policy"
                .to_owned(),
        ),
        ResourceObligationKind::ResourcePayloadLocationExact { pointer, .. } => Some(format!(
            "refine resource pointer %{} to one canonical move path before moving its owner",
            pointer.get()
        )),
        ResourceObligationKind::ResourcePayloadAvailable { .. } => Some(
            "initialize this owner path exactly once and do not use it after a move".to_owned(),
        ),
        ResourceObligationKind::AllocationResourcePayloadEmpty { .. } => Some(
            "move out or drop every nested owner before freeing its containing allocation"
                .to_owned(),
        ),
        ResourceObligationKind::PermissionAvailable { permission } => Some(format!(
            "move one available permission into %{} and do not reuse its source",
            permission.get()
        )),
        ResourceObligationKind::PermissionWritable { permission } => Some(format!(
            "request a mutable borrow/write permission for %{}",
            permission.get()
        )),
        ResourceObligationKind::PermissionCoversAccess { permission, .. } => Some(format!(
            "split or join permissions so %{} covers this access without overlap",
            permission.get()
        )),
        ResourceObligationKind::PermissionSplitPointInRange { permission, .. } => Some(format!(
            "prove that the split offset lies within permission %{}",
            permission.get()
        )),
        ResourceObligationKind::LoanRangeContained { loan, .. } => Some(format!(
            "derive loan l{} from a live pointer and a permission covering its complete byte range",
            loan.get()
        )),
        ResourceObligationKind::LoanCompatible { loan, .. } => Some(loan.map_or_else(
            || "end or narrow every overlapping loan before using the owner authority".to_owned(),
            |loan| {
                format!(
                    "use an active authority belonging to loan l{} with compatible mutability and range",
                    loan.get()
                )
            },
        )),
        ResourceObligationKind::LoanParentActive { parent, .. } => Some(format!(
            "use a valid Active or Suspended parent loan l{} with compatible mutability and a contained child range",
            parent.get()
        )),
        ResourceObligationKind::LoanRegionIncluded { loan, parent } => Some(format!(
            "constrain child loan l{} to a region no longer than parent loan l{}",
            loan.get(),
            parent.get()
        )),
        ResourceObligationKind::LoanEndedExactlyOnce { loan } => Some(format!(
            "end every authority and child of loan l{} exactly once before restoring its owner or returning",
            loan.get()
        )),
        ResourceObligationKind::LoanWithinBudget { .. }
        | ResourceObligationKind::LoanPairQueriesWithinBudget { .. }
        | ResourceObligationKind::LoanAliasWithinBudget { .. }
        | ResourceObligationKind::LoanReborrowDepthWithinBudget { .. } => Some(
            "reduce simultaneous borrow state, split the proof, or raise the explicit verifier budget"
                .to_owned(),
        ),
        ResourceObligationKind::OwnershipConserved { .. } => Some(
            "drop or free the owner before returning, or move its permission through the function result/call interface"
                .to_owned(),
        ),
        ResourceObligationKind::CallContractAvailable { contract } => Some(format!(
            "register and verify contract{} before this call",
            contract.get()
        )),
        ResourceObligationKind::CallContractPrecondition {
            contract, clause, ..
        } => Some(format!(
            "establish contract{} `requires` clause {} before this call",
            contract.get(),
            clause.get()
        )),
        _ => None,
    }
}

/// Failure of verifier orchestration or its closed modular environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationError {
    Summary {
        function: VirFunctionId,
        error: super::summary::SummaryValidationError,
    },
    /// Runtime semantics are defined, but this verifier profile has no rule.
    UnsupportedCapability(&'static str),
    ContractInstantiation,
    InvalidFinding,
    Cfg {
        function: VirFunctionId,
        error: CfgAnalysisError,
    },
}

impl VerificationError {
    #[must_use]
    pub const fn capability_failure_kind(&self) -> Option<crate::CapabilityFailureKind> {
        match self {
            Self::UnsupportedCapability(_) => {
                Some(crate::CapabilityFailureKind::VerificationUnsupported)
            }
            Self::ContractInstantiation
            | Self::InvalidFinding
            | Self::Cfg { .. }
            | Self::Summary { .. } => None,
        }
    }
}

impl fmt::Display for VerificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Summary { function, error } => {
                write!(formatter, "cannot project fn{}: {error}", function.get())
            }
            Self::UnsupportedCapability(capability) => write!(
                formatter,
                "verification profile does not support runtime capability `{capability}`"
            ),
            Self::ContractInstantiation => formatter
                .write_str("validated VIR contract table could not be instantiated by verifier"),
            Self::InvalidFinding => formatter.write_str(
                "verifier finding does not match the validated canonical VIR source identity",
            ),
            Self::Cfg { function, error } => {
                write!(formatter, "cannot verify fn{}: {error}", function.get())
            }
        }
    }
}

impl Error for VerificationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Summary { error, .. } => Some(error),
            Self::Cfg { error, .. } => Some(error),
            Self::UnsupportedCapability(_) | Self::ContractInstantiation | Self::InvalidFinding => {
                None
            }
        }
    }
}
