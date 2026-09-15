use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
mod loops;
pub use loops::LoopCandidateAttempt;

use crate::{
    ByteSpan, ResolvedVirUnit, VirBasicBlock, VirBlockId, VirBlockTarget, VirFunction,
    VirFunctionId, VirInstruction, VirIntegerPredicate, VirLocation, VirMemorySchema,
    VirTerminator, VirType, VirValueId,
};

use super::contract::{
    ContractApplicationError, InstantiatedContracts, entry_state, instantiate_contracts,
};
use super::finding::{VerifierFinding, VerifierFindingSite};
use super::guarded::{
    ConditionalResourceState, GuardedReduction, GuardedStateLimits, GuardedStatePrecisionLoss,
};
use super::resource::{
    AbstractAllocationId, AbstractBool, AbstractProvenance, AbstractValue, ActiveVariantState,
    EnumDiscriminantFact, LoanActivity, ObjectStateKey, PathFact, PermissionAvailability,
    ResourceJoinError, ResourceState, ResourceStateDefinitionError, U64Interval,
    VERIFIER_MAX_ACTIVE_LOANS_PER_CASE, VERIFIER_MAX_ALIASES_PER_LOAN, VERIFIER_MAX_REBORROW_DEPTH,
    VERIFIER_MAX_REGION_CONSTRAINTS_PER_FUNCTION,
};
use super::transfer::{
    LoanTransferContext, LoanTransferLimits, ObligationStatus, ResourceObligation,
    ResourceObligationKind, TransferError, abstract_value_matches_type, abstract_value_type,
    aggregate_abi_payload_status, install_aggregate_abi_payloads, permission_availability_status,
    transfer_instruction_with_contracts_and_memory, transfer_instruction_with_loans_and_memory,
    unknown_permission, unknown_value,
};

/// Deterministic limits and widening policy for CFG analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CfgAnalysisConfig {
    /// Maximum untrusted loop candidates selected for one function.
    pub max_loop_candidates: usize,
    /// Bounded induction/elimination attempts after ordinary analysis fails.
    pub max_loop_candidate_rounds: u32,
    /// Total block-transfer budget across candidate attempts, separate from baseline.
    pub max_loop_candidate_block_visits: u64,
    /// Weighted call evidence per body, including provisional CFG evaluations.
    /// Exhaustion prevents summary publication, never grants missing effects.
    pub max_summary_evidence: usize,
    /// Joint recursive-summary work limits, separate from one body's CFG limits.
    pub summary_limits: super::summary::SccLimits,
    /// Shared audit weight per function: relation observations plus provenance
    /// events and their pointer/instance/obligation/query-link entries.
    /// Independent of closure work; exhaustion fails analysis, not just logging.
    pub max_relation_evidence: usize,
    /// Numeric closure/query limits, also bounding each guarded relation case.
    pub relation_limits: super::relation::difference::DifferenceLimits,
    /// Maximum number of block transfers before analysis fails closed.
    pub max_block_visits: u64,
    /// Number of ordinary cyclic-entry expansions allowed before widening.
    pub widen_after_updates: u32,
    /// Maximum whole resource cases retained at one block program point.
    pub max_guarded_cases_per_block: usize,
    /// Maximum canonical guard atoms retained by one resource case.
    pub max_guard_atoms_per_case: usize,
    /// Maximum number of obligation-directed block replays per function.
    pub max_refinement_passes: u32,
    /// Maximum case-block transfers spent by obligation-directed replay.
    pub max_refinement_block_visits: u64,
    /// Maximum live or maybe-live loans retained by one resource case.
    pub max_active_loans_per_case: usize,
    /// Maximum available authorities retained for one shared loan.
    pub max_aliases_per_loan: usize,
    /// Maximum canonical constraints consulted for this function.
    pub max_region_constraints_per_function: usize,
    /// Maximum reborrow parent-chain depth.
    pub max_reborrow_depth: usize,
    /// Total loan-pair comparisons across all accesses in one instruction.
    pub max_region_pairs_per_instruction: usize,
}

impl Default for CfgAnalysisConfig {
    fn default() -> Self {
        Self {
            max_loop_candidates: 32,
            max_loop_candidate_rounds: 4,
            max_loop_candidate_block_visits: 2_000,
            max_summary_evidence: 65_536,
            summary_limits: super::summary::SccLimits::default(),
            max_relation_evidence: 65_536,
            relation_limits: super::relation::difference::DifferenceLimits::default(),
            max_block_visits: 10_000,
            widen_after_updates: 2,
            max_guarded_cases_per_block: 16,
            max_guard_atoms_per_case: 16,
            max_refinement_passes: 64,
            max_refinement_block_visits: 2_000,
            max_active_loans_per_case: VERIFIER_MAX_ACTIVE_LOANS_PER_CASE,
            max_aliases_per_loan: VERIFIER_MAX_ALIASES_PER_LOAN,
            max_region_constraints_per_function: VERIFIER_MAX_REGION_CONSTRAINTS_PER_FUNCTION,
            max_reborrow_depth: VERIFIER_MAX_REBORROW_DEPTH,
            max_region_pairs_per_instruction: 256,
        }
    }
}

impl CfgAnalysisConfig {
    const fn guarded_limits(self) -> GuardedStateLimits {
        GuardedStateLimits {
            max_cases: self.max_guarded_cases_per_block,
            max_guard_atoms: self.max_guard_atoms_per_case,
        }
    }

    const fn loan_limits(self) -> LoanTransferLimits {
        LoanTransferLimits {
            max_active_loans: self.max_active_loans_per_case,
            max_aliases_per_loan: self.max_aliases_per_loan,
            max_region_constraints: self.max_region_constraints_per_function,
            max_reborrow_depth: self.max_reborrow_depth,
            max_region_pairs: self.max_region_pairs_per_instruction,
        }
    }
}

/// Exact CFG construct responsible for one resource obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CfgObligationOrigin {
    Instruction { index: usize },
    Jump { target: VirBlockId },
    BranchThen { target: VirBlockId },
    BranchElse { target: VirBlockId },
    Return,
}

/// One final fixed-point obligation with its block and CFG origin.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CfgObligation {
    block: VirBlockId,
    origin: CfgObligationOrigin,
    finding: VerifierFinding,
    obligation: ResourceObligation,
}

impl CfgObligation {
    #[must_use]
    pub const fn block(&self) -> VirBlockId {
        self.block
    }

    #[must_use]
    pub const fn origin(&self) -> CfgObligationOrigin {
        self.origin
    }

    #[must_use]
    pub const fn obligation(&self) -> ResourceObligation {
        self.obligation
    }

    /// Returns the exact runtime program point responsible for this obligation.
    #[must_use]
    pub const fn location(&self) -> VirLocation {
        match self.finding.site() {
            VerifierFindingSite::Runtime(location) => location,
            VerifierFindingSite::Spec {
                occurrence: Some(location),
                ..
            } => location,
            VerifierFindingSite::Spec { .. } => unreachable!(),
        }
    }

    #[must_use]
    pub const fn site(&self) -> VerifierFindingSite {
        self.finding.site()
    }

    /// Returns the canonical source-backed finding captured when the
    /// obligation was formed.
    #[must_use]
    pub const fn finding(&self) -> VerifierFinding {
        self.finding
    }
}

/// Fixed-point entry and post-instruction state for one basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CfgBlockAnalysis {
    entry_state: ResourceState,
    instruction_states: Vec<ResourceState>,
    exit_state: ResourceState,
    entry_conditional_state: ConditionalResourceState,
    instruction_conditional_states: Vec<ConditionalResourceState>,
    exit_conditional_state: ConditionalResourceState,
    loop_block: bool,
}

impl CfgBlockAnalysis {
    #[must_use]
    pub const fn entry_state(&self) -> &ResourceState {
        &self.entry_state
    }

    #[must_use]
    pub const fn exit_state(&self) -> &ResourceState {
        &self.exit_state
    }

    /// Abstract state immediately after each instruction in source order.
    #[must_use]
    pub fn instruction_states(&self) -> &[ResourceState] {
        &self.instruction_states
    }

    #[must_use]
    pub const fn entry_conditional_state(&self) -> &ConditionalResourceState {
        &self.entry_conditional_state
    }

    /// Guarded state immediately after each instruction in source order.
    #[must_use]
    pub fn instruction_conditional_states(&self) -> &[ConditionalResourceState] {
        &self.instruction_conditional_states
    }

    #[must_use]
    pub const fn exit_conditional_state(&self) -> &ConditionalResourceState {
        &self.exit_conditional_state
    }

    /// Whether this block belongs to a non-trivial or self-loop CFG cycle.
    #[must_use]
    pub const fn is_loop_block(&self) -> bool {
        self.loop_block
    }
}

/// One reachable successful return after the final fixed point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionReturnState {
    case_ordinal: usize,
    finding: VerifierFinding,
    block: VirBlockId,
    source_span: ByteSpan,
    state: ResourceState,
    /// Logical observation before the checked ABI return consumes authorities.
    observation_state: Option<ResourceState>,
    values: Vec<AbstractValue>,
}

impl FunctionReturnState {
    pub(super) fn observation_state(&self) -> &ResourceState {
        self.observation_state.as_ref().unwrap_or(&self.state)
    }
    /// Ordinal within this final block evaluation, not a cross-iteration ID.
    pub const fn case_ordinal(&self) -> usize {
        self.case_ordinal
    }

    pub const fn finding(&self) -> VerifierFinding {
        self.finding
    }
    #[must_use]
    pub const fn block(&self) -> VirBlockId {
        self.block
    }

    #[must_use]
    pub const fn source_span(&self) -> ByteSpan {
        self.source_span
    }

    #[must_use]
    pub const fn state(&self) -> &ResourceState {
        &self.state
    }

    #[must_use]
    pub fn values(&self) -> &[AbstractValue] {
        &self.values
    }
}

/// Final CFG result for one structurally validated VIR function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionCfgAnalysis {
    loop_candidate_attempts: Vec<LoopCandidateAttempt>,
    pub(crate) summary_events: super::summary::EffectJournal,
    /// Historical non-Proven observations cannot justify summary closure just
    /// because a later transfer removed their path. Not used as new premises.
    summary_pending: Vec<CfgObligation>,
    provenance_evidence: Vec<super::provenance::ProvenanceEvidence>,
    function: VirFunctionId,
    function_entry_state: ResourceState,
    blocks: BTreeMap<VirBlockId, CfgBlockAnalysis>,
    obligations: Vec<CfgObligation>,
    relation_evidence: Vec<super::relation::RelationEvidence>,
    relation_queries: Vec<super::relation::audit::QueryEvidence>,
    returns: Vec<FunctionReturnState>,
    loop_blocks: BTreeSet<VirBlockId>,
    widened_blocks: BTreeSet<VirBlockId>,
    refined_blocks: BTreeSet<VirBlockId>,
    guarded_precision_losses: BTreeMap<VirBlockId, BTreeSet<GuardedStatePrecisionLoss>>,
    refinement_passes: u32,
    refinement_block_visits: u64,
    block_visits: u64,
}

impl FunctionCfgAnalysis {
    /// Discovery failures are diagnostics, never assumptions or trusted evidence.
    pub fn loop_candidate_attempts(&self) -> &[LoopCandidateAttempt] {
        &self.loop_candidate_attempts
    }
    pub fn summary_pending(&self) -> &[CfgObligation] {
        &self.summary_pending
    }
    #[must_use]
    pub fn provenance_evidence(&self) -> &[super::provenance::ProvenanceEvidence] {
        &self.provenance_evidence
    }
    #[must_use]
    pub fn relation_queries(&self) -> &[super::relation::audit::QueryEvidence] {
        &self.relation_queries
    }
    /// Final per-case numeric observations; not merged across guards and not
    /// accepted as permissions or initialization facts.
    #[must_use]
    pub fn relation_evidence(&self) -> &[super::relation::RelationEvidence] {
        &self.relation_evidence
    }
    #[must_use]
    pub const fn function(&self) -> VirFunctionId {
        self.function
    }

    #[must_use]
    pub const fn function_entry_state(&self) -> &ResourceState {
        &self.function_entry_state
    }

    #[must_use]
    pub const fn blocks(&self) -> &BTreeMap<VirBlockId, CfgBlockAnalysis> {
        &self.blocks
    }

    #[must_use]
    pub fn block(&self, id: VirBlockId) -> Option<&CfgBlockAnalysis> {
        self.blocks.get(&id)
    }

    #[must_use]
    pub fn obligations(&self) -> &[CfgObligation] {
        &self.obligations
    }

    #[must_use]
    pub fn returns(&self) -> &[FunctionReturnState] {
        &self.returns
    }

    /// Inferred inductive states are exactly the entry states of these cyclic
    /// blocks. They are computed, never assumed.
    #[must_use]
    pub const fn loop_blocks(&self) -> &BTreeSet<VirBlockId> {
        &self.loop_blocks
    }

    #[must_use]
    pub const fn widened_blocks(&self) -> &BTreeSet<VirBlockId> {
        &self.widened_blocks
    }

    #[must_use]
    pub const fn refined_blocks(&self) -> &BTreeSet<VirBlockId> {
        &self.refined_blocks
    }

    #[must_use]
    pub const fn guarded_precision_losses(
        &self,
    ) -> &BTreeMap<VirBlockId, BTreeSet<GuardedStatePrecisionLoss>> {
        &self.guarded_precision_losses
    }

    #[must_use]
    pub const fn refinement_passes(&self) -> u32 {
        self.refinement_passes
    }

    #[must_use]
    pub const fn refinement_block_visits(&self) -> u64 {
        self.refinement_block_visits
    }

    #[must_use]
    pub const fn block_visits(&self) -> u64 {
        self.block_visits
    }

    #[must_use]
    pub fn all_obligations_proven(&self) -> bool {
        self.obligations
            .iter()
            .all(|record| record.obligation.is_proven())
    }
}

/// Unsupported boundary, internal inconsistency or resource limit reached
/// during CFG analysis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgAnalysisError {
    LoopInvariantResourceStateUnsupported,
    LoopInvariantBudgetExceeded(crate::VirSpecLoopInvariantId),
    MissingFunction(VirFunctionId),
    MissingBlock(VirBlockId),
    InvalidEdgeShape {
        source: VirBlockId,
        target: VirBlockId,
        arguments: usize,
        parameters: usize,
    },
    InvalidReturnShape {
        block: VirBlockId,
        values: usize,
        results: usize,
    },
    AbstractValueTypeMismatch {
        block: VirBlockId,
        value: VirValueId,
        expected: VirType,
        found: VirType,
    },
    StateDefinition {
        block: VirBlockId,
        error: ResourceStateDefinitionError,
    },
    InstructionTransfer {
        block: VirBlockId,
        error: TransferError,
    },
    ResourceJoin {
        block: VirBlockId,
        error: ResourceJoinError,
    },
    BlockVisitLimitExceeded {
        limit: u64,
    },
    ContractInstantiation,
    ContractApplication(ContractApplicationError),
    InstructionSiteLimitExceeded,
    MissingInstructionSite {
        block: VirBlockId,
        index: usize,
    },
    InvalidFinding {
        location: VirLocation,
    },
    RelationEvidenceBudgetExceeded {
        block: VirBlockId,
        limit: usize,
    },
    RelationEvidenceMismatch {
        location: VirLocation,
    },
}

impl fmt::Display for CfgAnalysisError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LoopInvariantResourceStateUnsupported => write!(
                formatter,
                "loop induction requires stable allocation identities, fixed resource ranges and supported entry state"
            ),
            Self::LoopInvariantBudgetExceeded(id) => {
                write!(formatter, "loop invariant {id:?} proof budget exhausted")
            }
            Self::RelationEvidenceBudgetExceeded { block, limit } => write!(
                formatter,
                "relation evidence budget {limit} exhausted in {block:?}"
            ),
            Self::RelationEvidenceMismatch { location } => write!(
                formatter,
                "numeric derivation disagrees with obligation at {location:?}"
            ),
            Self::MissingFunction(function) => {
                write!(
                    formatter,
                    "validated VIR has no function fn{}",
                    function.get()
                )
            }
            Self::MissingBlock(block) => {
                write!(formatter, "validated VIR has no block bb{}", block.get())
            }
            Self::InvalidEdgeShape {
                source,
                target,
                arguments,
                parameters,
            } => write!(
                formatter,
                "validated edge bb{} -> bb{} has {arguments} arguments for {parameters} parameters",
                source.get(),
                target.get()
            ),
            Self::InvalidReturnShape {
                block,
                values,
                results,
            } => write!(
                formatter,
                "validated return in bb{} has {values} values for {results} results",
                block.get()
            ),
            Self::AbstractValueTypeMismatch {
                block,
                value,
                expected,
                found,
            } => write!(
                formatter,
                "abstract value %{} in bb{} has type {found:?}; expected {expected:?}",
                value.get(),
                block.get()
            ),
            Self::StateDefinition { block, error } => {
                write!(
                    formatter,
                    "cannot define CFG state for bb{}: {error}",
                    block.get()
                )
            }
            Self::InstructionTransfer { block, error } => write!(
                formatter,
                "instruction transfer failed in bb{}: {error}",
                block.get()
            ),
            Self::ResourceJoin { block, error } => write!(
                formatter,
                "resource join failed at bb{}: {error}",
                block.get()
            ),
            Self::BlockVisitLimitExceeded { limit } => {
                write!(
                    formatter,
                    "CFG analysis exceeded its {limit}-block visit limit"
                )
            }
            Self::ContractInstantiation => formatter.write_str(
                "validated VIR contract table could not be instantiated for CFG analysis",
            ),
            Self::ContractApplication(error) => error.fmt(formatter),
            Self::InstructionSiteLimitExceeded => {
                formatter.write_str("CFG has more instruction sites than the verifier can name")
            }
            Self::MissingInstructionSite { block, index } => write!(
                formatter,
                "CFG instruction bb{}[{index}] has no stable analysis-site identity",
                block.get()
            ),
            Self::InvalidFinding { location } => write!(
                formatter,
                "CFG obligation at {location:?} does not match the canonical source map",
            ),
        }
    }
}

impl Error for CfgAnalysisError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::StateDefinition { error, .. } => Some(error),
            Self::InstructionTransfer { error, .. } => Some(error),
            Self::ResourceJoin { error, .. } => Some(error),
            Self::ContractApplication(error) => Some(error),
            Self::LoopInvariantResourceStateUnsupported
            | Self::LoopInvariantBudgetExceeded(_)
            | Self::MissingFunction(_)
            | Self::MissingBlock(_)
            | Self::InvalidEdgeShape { .. }
            | Self::InvalidReturnShape { .. }
            | Self::AbstractValueTypeMismatch { .. }
            | Self::BlockVisitLimitExceeded { .. }
            | Self::ContractInstantiation
            | Self::InstructionSiteLimitExceeded
            | Self::MissingInstructionSite { .. }
            | Self::InvalidFinding { .. }
            | Self::RelationEvidenceBudgetExceeded { .. }
            | Self::RelationEvidenceMismatch { .. } => None,
        }
    }
}

/// Analyzes one validated function with unknown-but-well-typed entry values.
pub fn analyze_function_cfg(
    program: &ResolvedVirUnit<'_>,
    function: VirFunctionId,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    analyze_function_cfg_with_config(program, function, CfgAnalysisConfig::default())
}

/// Analyzes one function using the checked contracts owned by the same unit.
pub fn analyze_function_cfg_with_config(
    program: &ResolvedVirUnit<'_>,
    function: VirFunctionId,
    config: CfgAnalysisConfig,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    let contracts =
        instantiate_contracts(program).map_err(|_| CfgAnalysisError::ContractInstantiation)?;
    analyze_function_cfg_with_contracts(program, function, &contracts, config)
}

/// Analyzes one validated function from an explicit entry resource state.
///
/// The supplied entry state replaces only this function's `requires`; calls
/// still use contracts instantiated from the same validated unit.
pub fn analyze_function_cfg_with_entry(
    program: &ResolvedVirUnit<'_>,
    function_id: VirFunctionId,
    supplied_entry: &ResourceState,
    config: CfgAnalysisConfig,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    let contracts =
        instantiate_contracts(program).map_err(|_| CfgAnalysisError::ContractInstantiation)?;
    analyze_function_cfg_internal(
        program,
        function_id,
        supplied_entry,
        config,
        Some(&contracts),
        None,
    )
}

/// Analyzes one function from its checked `requires` facts and uses the same
/// registry to instantiate every call summary.
pub(super) fn analyze_function_cfg_with_contracts(
    program: &ResolvedVirUnit<'_>,
    function_id: VirFunctionId,
    contracts: &InstantiatedContracts,
    config: CfgAnalysisConfig,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    analyze_function_cfg_with_summaries(program, function_id, contracts, config, None)
}

pub(super) fn analyze_function_cfg_with_summaries(
    program: &ResolvedVirUnit<'_>,
    function_id: VirFunctionId,
    contracts: &InstantiatedContracts,
    config: CfgAnalysisConfig,
    registry: Option<&super::summary::SummaryRegistry>,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    let function = program
        .runtime()
        .functions
        .iter()
        .find(|function| function.id == function_id)
        .ok_or(CfgAnalysisError::MissingFunction(function_id))?;
    let contract = contracts
        .get(function.contract)
        .ok_or(CfgAnalysisError::ContractInstantiation)?;
    if contract.signature() != &function.signature {
        return Err(CfgAnalysisError::ContractInstantiation);
    }
    let entry_block = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)
        .ok_or(CfgAnalysisError::MissingBlock(function.entry))?;
    let parameters = entry_block
        .parameters
        .iter()
        .map(|parameter| (parameter.id, parameter.ty))
        .collect::<Vec<_>>();
    let mut supplied =
        entry_state(contract, &parameters).map_err(CfgAnalysisError::ContractApplication)?;
    let abi = program
        .runtime()
        .abis
        .function(function_id)
        .ok_or(CfgAnalysisError::ContractInstantiation)?;
    super::borrow_interface::install_entry(
        &mut supplied,
        function,
        &abi.signature,
        program.runtime().borrows,
        program.runtime().memory,
    )
    .ok_or(CfgAnalysisError::ContractInstantiation)?;
    if function_id != program.runtime().entry
        && let Some(resources) = &contract.resources
    {
        let ids = parameters.iter().map(|(id, _)| *id).collect::<Vec<_>>();
        if !resources
            .check(
                &supplied,
                &supplied,
                &ids,
                &[],
                crate::VirContractPosition::Requires,
                config,
            )
            .iter()
            .all(|c| c.status.is_proven())
        {
            return Err(CfgAnalysisError::ContractInstantiation);
        }
    }
    if let Some(pure) = &contract.pure {
        pure.install_memory_entry(
            &mut supplied,
            &parameters.iter().map(|(id, _)| *id).collect::<Vec<_>>(),
        )
        .ok_or(CfgAnalysisError::ContractInstantiation)?;
    }
    if supplied.loans().len() > config.max_active_loans_per_case || config.max_aliases_per_loan == 0
    {
        let loans = supplied.loans().keys().copied().collect::<Vec<_>>();
        for loan in loans {
            if let Some(loan) = supplied.loan_mut(loan) {
                loan.set_activity(LoanActivity::MaybeActive);
            }
        }
        supplied.mark_loan_precision_loss(super::resource::LoanPrecisionLoss::ActiveLoanBudget);
    }
    for (parameter_index, binding) in abi.signature.parameters().iter().enumerate() {
        if binding.interface().transfer != crate::VirInterfaceTransfer::Move {
            continue;
        }
        let crate::VirAbiValue::IndirectAggregate { access } = binding.value() else {
            continue;
        };
        let [pointer_slot, _permission_slot] = binding.parameter_slots() else {
            return Err(CfgAnalysisError::ContractInstantiation);
        };
        let pointer = entry_block
            .parameters
            .get(*pointer_slot as usize)
            .ok_or(CfgAnalysisError::ContractInstantiation)?
            .id;
        let parameter =
            u32::try_from(parameter_index).map_err(|_| CfgAnalysisError::ContractInstantiation)?;
        let installed = install_aggregate_abi_payloads(
            &mut supplied,
            program.runtime().memory,
            pointer,
            *access,
            |leaf| AbstractAllocationId::abi_entry_payload(function_id.get(), parameter, leaf),
        )
        .map_err(|error| CfgAnalysisError::InstructionTransfer {
            block: entry_block.id,
            error,
        })?;
        if !installed {
            return Err(CfgAnalysisError::ContractInstantiation);
        }
    }
    analyze_function_cfg_internal(
        program,
        function_id,
        &supplied,
        config,
        Some(contracts),
        registry,
    )
}

fn analyze_function_cfg_internal(
    program: &ResolvedVirUnit<'_>,
    function_id: VirFunctionId,
    supplied_entry: &ResourceState,
    config: CfgAnalysisConfig,
    contracts: Option<&InstantiatedContracts>,
    registry: Option<&super::summary::SummaryRegistry>,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    loops::candidates::analyze(
        program,
        function_id,
        supplied_entry,
        config,
        contracts,
        registry,
    )
}

fn analyze_function_cfg_attempt(
    program: &ResolvedVirUnit<'_>,
    function_id: VirFunctionId,
    supplied_entry: &ResourceState,
    config: CfgAnalysisConfig,
    contracts: Option<&InstantiatedContracts>,
    registry: Option<&super::summary::SummaryRegistry>,
    selected: &BTreeSet<crate::VirSpecLoopInvariantId>,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    let function = program
        .runtime()
        .functions
        .iter()
        .find(|function| function.id == function_id)
        .ok_or(CfgAnalysisError::MissingFunction(function_id))?;
    let blocks: BTreeMap<_, _> = function
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect();
    let loop_blocks = find_loop_blocks(&blocks);
    let mut induction = loops::Induction::new(program, function, config, selected, registry)?;
    let scalar_anchors = induction.anchors();
    let instruction_sites = assign_instruction_sites(&blocks)?;
    let entry = initialize_entry_state(function, supplied_entry)?;
    let function_entry_state = entry.clone();
    let entry_seed = ConditionalResourceState::singleton(entry);

    let mut entries = BTreeMap::from([(function.entry, entry_seed.clone())]);
    let mut incoming_edges = BTreeMap::<CfgEdgeKey, (VirBlockId, ConditionalResourceState)>::new();
    let mut entry_updates = BTreeMap::<VirBlockId, u32>::new();
    let mut pending = BTreeSet::from([function.entry]);
    let mut block_results = BTreeMap::new();
    let mut obligations_by_block = BTreeMap::new();
    let mut summary_pending = Vec::new();
    let mut queries_by_block = BTreeMap::new();
    let mut relations_by_block = BTreeMap::new();
    let mut provenance_by_block = BTreeMap::new();
    let mut returns_by_block = BTreeMap::new();
    let mut widened_blocks = BTreeSet::new();
    let mut refined_blocks = BTreeSet::new();
    let mut guarded_precision_losses =
        BTreeMap::<VirBlockId, BTreeSet<GuardedStatePrecisionLoss>>::new();
    let mut refinement_passes = 0_u32;
    let mut refinement_block_visits = 0_u64;
    let mut block_visits = 0_u64;
    let relation_sources = super::relation::audit::SourceIndex::new(program, function);
    let summary_events = std::cell::RefCell::new(super::summary::EffectJournal::default());
    let evaluation_context = BlockEvaluationContext {
        loop_blocks: &loop_blocks,
        scalar_anchors: &scalar_anchors,
        summary_context: super::summary::SummaryTransferContext {
            site: None,
            case_ordinal: 0,
            audit_limit: config.max_summary_evidence,
            registry,
            journal: &summary_events,
            limit: config.max_relation_evidence,
        },
        relation_sources: &relation_sources,
        program,
        function,
        blocks: &blocks,
        contracts,
        instruction_sites: &instruction_sites,
        loan_limits: config.loan_limits(),
        config,
    };

    while let Some(block_id) = pending.iter().next().copied() {
        if block_visits >= config.max_block_visits {
            return Err(CfgAnalysisError::BlockVisitLimitExceeded {
                limit: config.max_block_visits,
            });
        }
        pending.remove(&block_id);
        block_visits += 1;

        let block = blocks
            .get(&block_id)
            .copied()
            .ok_or(CfgAnalysisError::MissingBlock(block_id))?;
        let entry_conditional_state = entries
            .get(&block_id)
            .cloned()
            .unwrap_or_else(ConditionalResourceState::unreachable);
        let mut evaluated = evaluate_conditional_block(
            &evaluation_context,
            block,
            &entry_conditional_state,
            config.guarded_limits(),
            GuardedReduction::Selective,
        )?;
        retain_summary_pending(
            &mut summary_pending,
            &evaluated.obligations,
            block_id,
            config,
        )?;

        if !loop_blocks.contains(&block_id) && has_refinement_candidate(&evaluated.obligations) {
            let precise_entry = combine_block_inputs(
                block_id,
                function.entry,
                &entry_seed,
                &incoming_edges,
                config.guarded_limits(),
                GuardedReduction::PreserveGuards,
            )?;
            if precise_entry.cases().len() > entry_conditional_state.cases().len() {
                let visit_cost = u64::try_from(precise_entry.cases().len()).unwrap_or(u64::MAX);
                if refinement_passes >= config.max_refinement_passes {
                    guarded_precision_losses
                        .entry(block_id)
                        .or_default()
                        .insert(GuardedStatePrecisionLoss::RefinementPassBudget);
                } else if refinement_block_visits.saturating_add(visit_cost)
                    > config.max_refinement_block_visits
                {
                    guarded_precision_losses
                        .entry(block_id)
                        .or_default()
                        .insert(GuardedStatePrecisionLoss::RefinementVisitBudget);
                } else {
                    refinement_passes = refinement_passes.saturating_add(1);
                    refinement_block_visits = refinement_block_visits.saturating_add(visit_cost);
                    evaluated = evaluate_conditional_block(
                        &evaluation_context,
                        block,
                        &precise_entry,
                        config.guarded_limits(),
                        GuardedReduction::PreserveGuards,
                    )?;
                    refined_blocks.insert(block_id);
                }
            }
        }

        induction.cut_edges(block, &mut evaluated)?;
        collect_guarded_precision_losses(block_id, &evaluated, &mut guarded_precision_losses);

        let mut affected_targets = incoming_edges
            .iter()
            .filter_map(|(edge, (target, _))| (edge.source == block_id).then_some(*target))
            .collect::<BTreeSet<_>>();
        incoming_edges.retain(|edge, _| edge.source != block_id);
        for successor in evaluated.successors {
            affected_targets.insert(successor.block);
            incoming_edges.insert(
                CfgEdgeKey {
                    source: block_id,
                    ordinal: successor.edge_ordinal,
                },
                (successor.block, successor.state),
            );
        }
        for target in affected_targets {
            let incoming = combine_block_inputs(
                target,
                function.entry,
                &entry_seed,
                &incoming_edges,
                config.guarded_limits(),
                GuardedReduction::Selective,
            )?;
            if merge_successor(
                target,
                incoming,
                &loop_blocks,
                config,
                &mut entries,
                &mut entry_updates,
                &mut widened_blocks,
            )? {
                pending.insert(target);
            }
        }

        if evaluated.returns.is_empty() {
            returns_by_block.remove(&block_id);
        } else {
            returns_by_block.insert(block_id, evaluated.returns);
        }
        retain_summary_pending(
            &mut summary_pending,
            &evaluated.obligations,
            block_id,
            config,
        )?;
        obligations_by_block.insert(block_id, evaluated.obligations);
        relations_by_block.insert(block_id, evaluated.relation_evidence);
        provenance_by_block.insert(block_id, evaluated.provenance_evidence);
        queries_by_block.insert(block_id, evaluated.relation_queries);
        let evidence_count: usize = queries_by_block
            .values()
            .map(Vec::len)
            .sum::<usize>()
            .saturating_add(relations_by_block.values().map(Vec::len).sum::<usize>())
            .saturating_add(
                provenance_by_block
                    .values()
                    .flatten()
                    .map(|e| e.weight())
                    .sum::<usize>(),
            );
        if evidence_count > config.max_relation_evidence {
            return Err(CfgAnalysisError::RelationEvidenceBudgetExceeded {
                block: block_id,
                limit: config.max_relation_evidence,
            });
        }
        let entry_state =
            evaluated
                .entry
                .collapsed()
                .map_err(|error| CfgAnalysisError::ResourceJoin {
                    block: block_id,
                    error,
                })?;
        let instruction_states = evaluated
            .instruction_states
            .iter()
            .map(ConditionalResourceState::collapsed)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| CfgAnalysisError::ResourceJoin {
                block: block_id,
                error,
            })?;
        let exit_state =
            evaluated
                .exit_state
                .collapsed()
                .map_err(|error| CfgAnalysisError::ResourceJoin {
                    block: block_id,
                    error,
                })?;
        block_results.insert(
            block_id,
            CfgBlockAnalysis {
                entry_state,
                instruction_states,
                exit_state,
                entry_conditional_state: evaluated.entry,
                instruction_conditional_states: evaluated.instruction_states,
                exit_conditional_state: evaluated.exit_state,
                loop_block: loop_blocks.contains(&block_id),
            },
        );
    }

    for &block_id in blocks.keys() {
        block_results
            .entry(block_id)
            .or_insert_with(|| CfgBlockAnalysis {
                entry_state: ResourceState::unreachable(),
                instruction_states: Vec::new(),
                exit_state: ResourceState::unreachable(),
                entry_conditional_state: ConditionalResourceState::unreachable(),
                instruction_conditional_states: Vec::new(),
                exit_conditional_state: ConditionalResourceState::unreachable(),
                loop_block: loop_blocks.contains(&block_id),
            });
    }

    Ok(FunctionCfgAnalysis {
        loop_candidate_attempts: Vec::new(),
        summary_events: summary_events.into_inner(),
        summary_pending,
        provenance_evidence: provenance_by_block.into_values().flatten().collect(),
        function: function_id,
        function_entry_state,
        blocks: block_results,
        obligations: obligations_by_block.into_values().flatten().collect(),
        relation_evidence: relations_by_block.into_values().flatten().collect(),
        relation_queries: queries_by_block.into_values().flatten().collect(),
        returns: returns_by_block.into_values().flatten().collect(),
        loop_blocks,
        widened_blocks,
        refined_blocks,
        guarded_precision_losses,
        refinement_passes,
        refinement_block_visits,
        block_visits,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CfgEdgeKey {
    source: VirBlockId,
    ordinal: u8,
}

fn retain_summary_pending(
    pending: &mut Vec<CfgObligation>,
    records: &[CfgObligation],
    block: VirBlockId,
    config: CfgAnalysisConfig,
) -> Result<(), CfgAnalysisError> {
    for record in records {
        if !record.obligation().is_proven() && !pending.contains(record) {
            if pending.len() >= config.max_relation_evidence {
                return Err(CfgAnalysisError::RelationEvidenceBudgetExceeded {
                    block,
                    limit: config.max_relation_evidence,
                });
            }
            pending.push(*record);
        }
    }
    Ok(())
}

struct ConditionalBlockEvaluation {
    provenance_evidence: Vec<super::provenance::ProvenanceEvidence>,
    entry: ConditionalResourceState,
    instruction_states: Vec<ConditionalResourceState>,
    exit_state: ConditionalResourceState,
    successors: Vec<ConditionalSuccessorState>,
    obligations: Vec<CfgObligation>,
    relation_evidence: Vec<super::relation::RelationEvidence>,
    relation_queries: Vec<super::relation::audit::QueryEvidence>,
    returns: Vec<FunctionReturnState>,
}

struct ConditionalSuccessorState {
    edge_ordinal: u8,
    block: VirBlockId,
    state: ConditionalResourceState,
}

struct BlockStepEvaluation {
    provenance_evidence: Vec<super::provenance::ProvenanceEvidence>,
    outcomes: Vec<ResourceState>,
    successors: Vec<SuccessorState>,
    obligations: Vec<CfgObligation>,
    relation_evidence: Vec<super::relation::RelationEvidence>,
    relation_queries: Vec<super::relation::audit::QueryEvidence>,
    returned: Option<FunctionReturnState>,
}

struct SuccessorState {
    edge_ordinal: u8,
    block: VirBlockId,
    state: ResourceState,
    guard_projection_lost: bool,
}

#[derive(Clone, Copy)]
struct BlockEvaluationContext<'analysis, 'unit> {
    loop_blocks: &'analysis BTreeSet<VirBlockId>,
    scalar_anchors: &'analysis [VirValueId],
    summary_context: super::summary::SummaryTransferContext<'analysis>,
    program: &'analysis ResolvedVirUnit<'unit>,
    function: &'analysis VirFunction,
    blocks: &'analysis BTreeMap<VirBlockId, &'analysis VirBasicBlock>,
    contracts: Option<&'analysis InstantiatedContracts>,
    relation_sources: &'analysis super::relation::audit::SourceIndex,
    instruction_sites: &'analysis BTreeMap<(VirBlockId, usize), u64>,
    loan_limits: LoanTransferLimits,
    config: CfgAnalysisConfig,
}

fn evaluate_conditional_block(
    context: &BlockEvaluationContext<'_, '_>,
    block: &VirBasicBlock,
    entry: &ConditionalResourceState,
    limits: GuardedStateLimits,
    reduction: GuardedReduction,
) -> Result<ConditionalBlockEvaluation, CfgAnalysisError> {
    let config = context.config;
    let mut instruction_states = Vec::new();
    let mut current = entry.clone();
    let mut successor_cases = BTreeMap::<(u8, VirBlockId), (Vec<ResourceState>, bool)>::new();
    let mut obligations = Vec::new();
    let mut returns = Vec::new();
    let mut provenance_evidence: Vec<super::provenance::ProvenanceEvidence> = Vec::new();
    let mut relation_evidence = Vec::new();
    let mut relation_queries = Vec::new();
    // A call splits whole states inside a block. Each subsequent instruction
    // and the terminator see every surviving outcome, never a favorable world.
    for step in 0..=block.instructions.len() {
        if step == block.instructions.len() {
            current = classify_boolean_returns(context, block, current, limits)?;
        }
        let mut next_cases = Vec::new();
        for (case_ordinal, case) in current.cases().iter().enumerate() {
            let evaluated = evaluate_block_step(context, block, case, case_ordinal, step)?;
            relation_evidence.extend(evaluated.relation_evidence);
            relation_queries.extend(evaluated.relation_queries);
            provenance_evidence.extend(evaluated.provenance_evidence);
            if relation_evidence
                .len()
                .saturating_add(relation_queries.len())
                .saturating_add(
                    provenance_evidence
                        .iter()
                        .map(|e| e.weight())
                        .sum::<usize>(),
                )
                > config.max_relation_evidence
            {
                return Err(CfgAnalysisError::RelationEvidenceBudgetExceeded {
                    block: block.id,
                    limit: config.max_relation_evidence,
                });
            }
            next_cases.extend(evaluated.outcomes);
            for successor in evaluated.successors {
                let (cases, projection_lost) = successor_cases
                    .entry((successor.edge_ordinal, successor.block))
                    .or_default();
                cases.push(successor.state);
                *projection_lost |= successor.guard_projection_lost;
            }
            for obligation in evaluated.obligations {
                merge_case_obligation(&mut obligations, obligation);
            }
            if let Some(returned) = evaluated.returned {
                returns.push(returned);
            }
        }
        if step < block.instructions.len() {
            current = ConditionalResourceState::from_cases(
                next_cases,
                current.precision_losses().clone(),
                limits,
                // Keep scalar return alternatives until a real branch or CFG
                // merge can consume them. The same case/atom budgets still apply.
                GuardedReduction::PreserveGuards,
            )
            .map_err(|error| CfgAnalysisError::ResourceJoin {
                block: block.id,
                error,
            })?;
            instruction_states.push(current.clone());
        }
    }
    let exit_state = current;
    let inherited_losses = exit_state.precision_losses().clone();
    let successors = successor_cases
        .into_iter()
        .map(|((edge_ordinal, target), (cases, projection_lost))| {
            let mut losses = inherited_losses.clone();
            if projection_lost {
                losses.insert(GuardedStatePrecisionLoss::GuardProjection);
            }
            ConditionalResourceState::from_cases(cases, losses, limits, reduction)
                .map(|state| ConditionalSuccessorState {
                    edge_ordinal,
                    block: target,
                    state,
                })
                .map_err(|error| CfgAnalysisError::ResourceJoin {
                    block: target,
                    error,
                })
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(ConditionalBlockEvaluation {
        provenance_evidence,
        entry: entry.clone(),
        instruction_states,
        exit_state,
        successors,
        obligations,
        relation_evidence,
        relation_queries,
        returns,
    })
}

/// Classify boolean normal results using the SAME branch refinement as a VIR
/// branch. This exposes `return i < n` and forwarded booleans as complete return
/// cases, without teaching the summary projector a second symbolic evaluator.
fn classify_boolean_returns(
    context: &BlockEvaluationContext<'_, '_>,
    block: &VirBasicBlock,
    mut state: ConditionalResourceState,
    limits: GuardedStateLimits,
) -> Result<ConditionalResourceState, CfgAnalysisError> {
    if context.summary_context.registry.is_none() {
        return Ok(state);
    }
    let VirTerminator::Return { values } = &block.terminator.terminator else {
        return Ok(state);
    };
    for value in values {
        let mut cases = Vec::new();
        for case in state.cases() {
            if case.value(*value) != Some(&AbstractValue::Bool(AbstractBool::Unknown)) {
                cases.push(case.clone());
                continue;
            }
            for expected in [false, true] {
                let mut refined = refine_branch(
                    block.id,
                    case,
                    *value,
                    expected,
                    direct_comparison_definition(block, *value),
                    context.program.runtime().memory,
                )?;
                if refined.path_condition().is_reachable() {
                    *refined.value_mut(*value).expect("return value exists") =
                        AbstractValue::Bool(if expected {
                            AbstractBool::True
                        } else {
                            AbstractBool::False
                        });
                }
                cases.push(refined);
            }
        }
        state = ConditionalResourceState::from_cases(
            cases,
            state.precision_losses().clone(),
            limits,
            GuardedReduction::PreserveGuards,
        )
        .map_err(|error| CfgAnalysisError::ResourceJoin {
            block: block.id,
            error,
        })?;
    }
    Ok(state)
}

fn evaluate_block_step(
    context: &BlockEvaluationContext<'_, '_>,
    block: &VirBasicBlock,
    entry: &ResourceState,
    case_ordinal: usize,
    step: usize,
) -> Result<BlockStepEvaluation, CfgAnalysisError> {
    let BlockEvaluationContext {
        summary_context,
        relation_sources,
        program,
        function,
        blocks,
        contracts,
        instruction_sites,
        loan_limits,
        config,
        ..
    } = *context;
    let memory = program.runtime().memory;
    let mut provenance_evidence = Vec::new();
    let mut provenance_weight = 0usize;
    let mut state = entry.clone();
    state.limit_relations(config.relation_limits);
    state.reduce_relation_intervals();
    // Widening may discard numeric bounds inside an SCC while retaining the
    // branch predicates. Reapply those independently established predicates
    // before using intervals (including initialized-prefix reduction).
    for fact in entry.path_condition().facts().into_iter().flatten() {
        refine_integer_comparison(&mut state, *fact);
    }
    state.reduce_initialization_prefixes();
    let mut outcomes = Vec::with_capacity(block.instructions.len());
    let mut obligations = Vec::new();
    let mut relation_evidence = Vec::new();
    let mut relation_queries = Vec::new();
    for (index, instruction) in block.instructions.iter().enumerate().skip(step).take(1) {
        let call_site = *instruction_sites.get(&(block.id, index)).ok_or(
            CfgAnalysisError::MissingInstructionSite {
                block: block.id,
                index,
            },
        )?;
        let transferred = contracts
            .map_or_else(
                || {
                    transfer_instruction_with_loans_and_memory(
                        &state,
                        instruction,
                        memory,
                        config.relation_limits,
                        LoanTransferContext {
                            borrows: program.runtime().borrows,
                            function: function.id,
                            limits: loan_limits,
                        },
                    )
                },
                |contracts| {
                    transfer_instruction_with_contracts_and_memory(
                        &state,
                        instruction,
                        super::transfer::ContractTransferContext {
                            contracts,
                            call_site,
                            summary: Some(super::summary::SummaryTransferContext {
                                site: VerifierFinding::runtime(
                                    program,
                                    VirLocation::Instruction {
                                        function: function.id,
                                        block: block.id,
                                        ordinal: index as u64,
                                    },
                                    instruction.source_span,
                                ),
                                case_ordinal,
                                ..summary_context
                            }),
                        },
                        memory,
                        config.relation_limits,
                        LoanTransferContext {
                            borrows: program.runtime().borrows,
                            function: function.id,
                            limits: loan_limits,
                        },
                    )
                },
            )
            .map_err(|error| CfgAnalysisError::InstructionTransfer {
                block: block.id,
                error,
            })?;
        append_queries(
            program,
            relation_sources,
            block.id,
            instruction.source_span,
            VirLocation::Instruction {
                function: function.id,
                block: block.id,
                ordinal: index as u64,
            },
            case_ordinal,
            None,
            transferred.queries.clone(),
            &mut relation_queries,
            config,
        )?;
        let instruction_obligations = transferred
            .obligations()
            .iter()
            .copied()
            .map(|obligation| {
                let location = match obligation.kind() {
                    ResourceObligationKind::CallContractAvailable { .. }
                    | ResourceObligationKind::CallContractPrecondition { .. } => {
                        VirLocation::CallEdge {
                            function: function.id,
                            block: block.id,
                            instruction: index as u64,
                        }
                    }
                    _ => VirLocation::Instruction {
                        function: function.id,
                        block: block.id,
                        ordinal: index as u64,
                    },
                };
                cfg_obligation(
                    program,
                    block.id,
                    CfgObligationOrigin::Instruction { index },
                    location,
                    obligation,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (ordinal, record) in instruction_obligations.iter().enumerate() {
            if let Some(evidence) = super::relation::capture(
                record.finding(),
                config,
                case_ordinal,
                ordinal,
                &instruction.instruction,
                memory,
                &state,
                transferred.state(),
                record.obligation(),
            )
            .map_err(|()| CfgAnalysisError::RelationEvidenceMismatch {
                location: record.location(),
            })? {
                relation_evidence.push(evidence);
            }
        }
        obligations.extend(instruction_obligations);
        let location = VirLocation::Instruction {
            function: function.id,
            block: block.id,
            ordinal: index as u64,
        };
        let finding = VerifierFinding::runtime(program, location, instruction.source_span)
            .ok_or(CfgAnalysisError::InvalidFinding { location })?;
        if let Some(evidence) = (super::provenance::Capture {
            finding,
            config,
            case_ordinal,
            instruction: &instruction.instruction,
            before: &state,
            after: transferred.state(),
            obligations: transferred.obligations(),
            query_count: transferred.queries.as_ref().map_or(0, Vec::len),
            sources: relation_sources,
        })
        .record()
        {
            provenance_weight = provenance_weight.saturating_add(evidence.weight());
            provenance_evidence.push(evidence);
            if provenance_weight
                .saturating_add(relation_evidence.len())
                .saturating_add(relation_queries.len())
                > config.max_relation_evidence
            {
                return Err(CfgAnalysisError::RelationEvidenceBudgetExceeded {
                    block: block.id,
                    limit: config.max_relation_evidence,
                });
            }
        }
        state = transferred.state().clone();
        outcomes.extend(transferred.cases.unwrap_or_else(|| vec![state.clone()]));
    }

    if step < block.instructions.len() || !state.path_condition().is_reachable() {
        return Ok(BlockStepEvaluation {
            provenance_evidence,
            outcomes,
            successors: Vec::new(),
            obligations,
            relation_evidence,
            relation_queries,
            returned: None,
        });
    }

    let span = block.terminator.source_span;
    let mut successors = Vec::new();
    let mut returned = None;
    match &block.terminator.terminator {
        VirTerminator::Jump { target } => {
            let target_block = target_block(target, blocks)?;
            let edge = transfer_edge(block.id, &state, target, target_block, span, context)?;
            append_queries(
                program,
                relation_sources,
                block.id,
                span,
                VirLocation::Terminator {
                    function: function.id,
                    block: block.id,
                },
                case_ordinal,
                Some(0),
                edge.queries.clone(),
                &mut relation_queries,
                config,
            )?;
            obligations.extend(wrap_edge_obligations(
                program,
                function.id,
                block.id,
                CfgObligationOrigin::Jump {
                    target: target.block,
                },
                edge.obligations,
            )?);
            successors.push(SuccessorState {
                edge_ordinal: 0,
                block: target.block,
                state: edge.state,
                guard_projection_lost: edge.guard_projection_lost,
            });
        }
        VirTerminator::Branch {
            condition,
            then_target,
            else_target,
        } => {
            let comparison = direct_comparison_definition(block, *condition);
            for (edge_ordinal, expected, target, origin) in [
                (
                    0,
                    true,
                    then_target,
                    CfgObligationOrigin::BranchThen {
                        target: then_target.block,
                    },
                ),
                (
                    1,
                    false,
                    else_target,
                    CfgObligationOrigin::BranchElse {
                        target: else_target.block,
                    },
                ),
            ] {
                let mut refined =
                    refine_branch(block.id, &state, *condition, expected, comparison, memory)?;
                if !refined.path_condition().is_reachable() {
                    continue;
                }
                if let Some(fact) = comparison {
                    let effective = if expected { fact } else { fact.negated() };
                    if let Some(premise) =
                        super::relation::state::comparison_premise(&refined, effective)
                    {
                        refined.learn_relations(&[premise], config.relation_limits);
                    }
                }
                let destination = target_block(target, blocks)?;
                let edge = transfer_edge(block.id, &refined, target, destination, span, context)?;
                append_queries(
                    program,
                    relation_sources,
                    block.id,
                    span,
                    VirLocation::Terminator {
                        function: function.id,
                        block: block.id,
                    },
                    case_ordinal,
                    Some(edge_ordinal),
                    edge.queries.clone(),
                    &mut relation_queries,
                    config,
                )?;
                obligations.extend(wrap_edge_obligations(
                    program,
                    function.id,
                    block.id,
                    origin,
                    edge.obligations,
                )?);
                successors.push(SuccessorState {
                    edge_ordinal,
                    block: target.block,
                    state: edge.state,
                    guard_projection_lost: edge.guard_projection_lost,
                });
            }
        }
        VirTerminator::Return { values } => {
            let abi = program
                .runtime()
                .abis
                .function(function.id)
                .ok_or(CfgAnalysisError::ContractInstantiation)?;
            let transfer = transfer_return(
                block.id,
                &state,
                values,
                &function.signature.results,
                &abi.signature,
                memory,
                span,
            )?;
            let location = VirLocation::Terminator {
                function: function.id,
                block: block.id,
            };
            for obligation in transfer.obligations {
                obligations.push(cfg_obligation(
                    program,
                    block.id,
                    CfgObligationOrigin::Return,
                    location,
                    obligation,
                )?);
            }
            if transfer.successful {
                returned = Some(FunctionReturnState {
                    case_ordinal,
                    finding: VerifierFinding::runtime(program, location, span)
                        .ok_or(CfgAnalysisError::InvalidFinding { location })?,
                    block: block.id,
                    source_span: span,
                    state: transfer.state,
                    observation_state: contracts
                        .and_then(|cs| cs.get(function.contract))
                        .filter(|c| c.observes_memory())
                        .map(|_| state.clone()),
                    values: transfer.values,
                });
            }
        }
    }

    Ok(BlockStepEvaluation {
        provenance_evidence,
        outcomes,
        successors,
        obligations,
        relation_evidence,
        relation_queries,
        returned,
    })
}

fn assign_instruction_sites(
    blocks: &BTreeMap<VirBlockId, &VirBasicBlock>,
) -> Result<BTreeMap<(VirBlockId, usize), u64>, CfgAnalysisError> {
    let mut sites = BTreeMap::new();
    let mut next = 0_u64;
    for (&block, body) in blocks {
        for index in 0..body.instructions.len() {
            sites.insert((block, index), next);
            next = next
                .checked_add(1)
                .ok_or(CfgAnalysisError::InstructionSiteLimitExceeded)?;
        }
    }
    Ok(sites)
}

fn initialize_entry_state(
    function: &VirFunction,
    supplied: &ResourceState,
) -> Result<ResourceState, CfgAnalysisError> {
    if !supplied.path_condition().is_reachable() {
        return Ok(ResourceState::unreachable());
    }
    let entry = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)
        .ok_or(CfgAnalysisError::MissingBlock(function.entry))?;
    let renames: Vec<_> = entry
        .parameters
        .iter()
        .map(|parameter| (parameter.id, parameter.id))
        .collect();
    let mut projected = supplied.project_cfg_edge(&renames);
    for parameter in &entry.parameters {
        let fact = supplied
            .value(parameter.id)
            .copied()
            .unwrap_or_else(|| unknown_value(parameter.ty));
        ensure_type(entry.id, parameter.id, parameter.ty, fact)?;
        projected
            .define_value(parameter.id, fact)
            .map_err(|error| CfgAnalysisError::StateDefinition {
                block: entry.id,
                error,
            })?;
        if matches!(parameter.ty, VirType::U64) && projected.word_expression(parameter.id).is_none()
        {
            projected.set_word_expression(
                parameter.id,
                super::resource::AffineExpression::identity(parameter.id),
            );
        }
    }
    Ok(projected)
}

struct EdgeTransfer {
    queries: Option<Vec<super::relation::audit::QueryObservation>>,
    state: ResourceState,
    obligations: Vec<ResourceObligation>,
    guard_projection_lost: bool,
}

fn transfer_edge(
    source_block: VirBlockId,
    source: &ResourceState,
    target: &VirBlockTarget,
    destination: &VirBasicBlock,
    source_span: ByteSpan,
    context: &BlockEvaluationContext<'_, '_>,
) -> Result<EdgeTransfer, CfgAnalysisError> {
    let relation_limits = context.config.relation_limits;
    let scalar_anchors = context.scalar_anchors;
    if target.arguments.len() != destination.parameters.len() {
        return Err(CfgAnalysisError::InvalidEdgeShape {
            source: source_block,
            target: target.block,
            arguments: target.arguments.len(),
            parameters: destination.parameters.len(),
        });
    }
    let mut renames: Vec<_> = target
        .arguments
        .iter()
        .copied()
        .zip(destination.parameters.iter().map(|parameter| parameter.id))
        .collect();
    // Immutable function-entry scalars are verification-only anchors for loop
    // activation/exit observations, not additional runtime block parameters.
    let anchors: Vec<_> = scalar_anchors
        .iter()
        .copied()
        .filter(|id| {
            source.value(*id).is_some() && !destination.parameters.iter().any(|p| p.id == *id)
        })
        .collect();
    renames.extend(anchors.iter().map(|id| (*id, *id)));
    let mut state = source.project_cfg_edge(&renames);
    let queries = super::relation::audit::QueryLog::default();
    source.project_initialization_prefix_relations(
        &renames,
        &mut state,
        relation_limits,
        &queries,
        context.loop_blocks.contains(&destination.id),
    );
    let queries = queries.finish();
    let guard_projection_lost =
        state.path_condition().atom_count() < source.path_condition().atom_count();
    if !state.path_condition().is_reachable() {
        return Ok(EdgeTransfer {
            queries,
            state,
            obligations: Vec::new(),
            guard_projection_lost,
        });
    }

    let mut obligations = Vec::new();
    let mut permission_arguments = Vec::new();
    for (&argument, parameter) in target.arguments.iter().zip(&destination.parameters) {
        let mut fact = source
            .project_value_for_cfg(argument, &renames)
            .unwrap_or_else(|| missing_value(parameter.ty));
        ensure_type(source_block, argument, parameter.ty, fact)?;
        if let AbstractValue::Permission(permission) = fact {
            for &previous in &permission_arguments {
                obligations.push(ResourceObligation::new(
                    ResourceObligationKind::PermissionOperandsDistinct {
                        left: previous,
                        right: argument,
                    },
                    if previous == argument {
                        ObligationStatus::Refuted
                    } else {
                        ObligationStatus::Proven
                    },
                    source_span,
                ));
            }
            permission_arguments.push(argument);
            // A CFG edge renames the permission token together with its
            // availability state.  In particular, a consumed token may cross
            // a join as a tombstone so a guarded alternative can retain the
            // correlation between the drop flag and the remaining authority.
            // Calls, returns and memory effects still require Available.
            fact = AbstractValue::Permission(permission);
        }
        state.define_value(parameter.id, fact).map_err(|error| {
            CfgAnalysisError::StateDefinition {
                block: destination.id,
                error,
            }
        })?;
    }
    for id in anchors {
        state
            .define_value(id, *source.value(id).unwrap())
            .map_err(|error| CfgAnalysisError::StateDefinition {
                block: destination.id,
                error,
            })?;
        if matches!(state.value(id), Some(AbstractValue::U64(_))) {
            state.set_word_expression(id, crate::AffineExpression::identity(id));
        }
    }
    if obligations
        .iter()
        .any(|obligation| obligation.status() == ObligationStatus::Refuted)
    {
        state = ResourceState::unreachable();
    }
    Ok(EdgeTransfer {
        queries,
        state,
        obligations,
        guard_projection_lost,
    })
}

struct ReturnTransfer {
    state: ResourceState,
    values: Vec<AbstractValue>,
    obligations: Vec<ResourceObligation>,
    successful: bool,
}

fn transfer_return(
    block: VirBlockId,
    state: &ResourceState,
    values: &[VirValueId],
    expected: &[VirType],
    abi: &crate::VirAbiSignature,
    memory: &VirMemorySchema,
    source_span: ByteSpan,
) -> Result<ReturnTransfer, CfgAnalysisError> {
    if values.len() != expected.len() {
        return Err(CfgAnalysisError::InvalidReturnShape {
            block,
            values: values.len(),
            results: expected.len(),
        });
    }
    let mut facts = Vec::with_capacity(values.len());
    let mut obligations = Vec::new();
    let mut permission_values = Vec::new();
    let mut transferred_allocations = BTreeSet::new();
    for (index, binding) in abi.parameters().iter().enumerate() {
        let loan = crate::vir::interface_loan_id(index as u32);
        if state.loan(loan).is_some()
            || matches!(binding.value(), crate::VirAbiValue::Pointer { access, .. } if matches!(memory.kind(access.ty), Some(crate::VirMemoryTypeKind::Pointer { kind: crate::VirPointerKind::Reference, .. })))
        {
            obligations.push(ResourceObligation::new(
                ResourceObligationKind::LoanEndedExactlyOnce { loan },
                if super::borrow_interface::exported_authority(state, loan, values, abi) {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Refuted
                },
                source_span,
            ));
            obligations.extend(super::borrow_interface::export_value_obligations(
                state,
                loan,
                abi,
                memory,
                source_span,
            ));
        }
    }
    for (&loan, fact) in state.loans() {
        let status = match fact.activity() {
            LoanActivity::Ended => ObligationStatus::Proven,
            LoanActivity::Active | LoanActivity::Suspended
                if super::borrow_interface::exported_authority(state, loan, values, abi) =>
            {
                ObligationStatus::Proven
            }
            LoanActivity::Active | LoanActivity::Suspended => ObligationStatus::Refuted,
            LoanActivity::MaybeActive => ObligationStatus::Unknown,
        };
        if !status.is_proven() {
            obligations.push(ResourceObligation::new(
                ResourceObligationKind::LoanEndedExactlyOnce { loan },
                status,
                source_span,
            ));
        }
    }
    for (&value, &expected) in values.iter().zip(expected) {
        let mut fact = state
            .value(value)
            .copied()
            .unwrap_or_else(|| missing_value(expected));
        ensure_type(block, value, expected, fact)?;
        if let AbstractValue::Permission(permission) = fact {
            obligations.push(ResourceObligation::new(
                ResourceObligationKind::PermissionAvailable { permission: value },
                permission_availability_status(permission.availability()),
                source_span,
            ));
            for &previous in &permission_values {
                obligations.push(ResourceObligation::new(
                    ResourceObligationKind::PermissionOperandsDistinct {
                        left: previous,
                        right: value,
                    },
                    if previous == value {
                        ObligationStatus::Refuted
                    } else {
                        ObligationStatus::Proven
                    },
                    source_span,
                ));
            }
            permission_values.push(value);
            if let super::resource::AbstractProvenance::Known(allocation) = permission.provenance()
            {
                transferred_allocations.insert(allocation);
            }
            fact = AbstractValue::Permission(
                permission.with_availability(PermissionAvailability::Available),
            );
        }
        facts.push(fact);
    }
    for binding in abi.results() {
        if binding.interface().transfer != crate::VirInterfaceTransfer::Move {
            continue;
        }
        let crate::VirAbiValue::IndirectAggregate { access } = binding.value() else {
            continue;
        };
        let [permission_slot] = binding.result_slots() else {
            return Err(CfgAnalysisError::InvalidReturnShape {
                block,
                values: values.len(),
                results: expected.len(),
            });
        };
        let permission_value =
            *values
                .get(*permission_slot as usize)
                .ok_or(CfgAnalysisError::InvalidReturnShape {
                    block,
                    values: values.len(),
                    results: expected.len(),
                })?;
        let storage = match state.value(permission_value).copied() {
            Some(AbstractValue::Permission(permission)) => match permission.provenance() {
                AbstractProvenance::Known(allocation) => Some(allocation),
                AbstractProvenance::Unknown => None,
            },
            _ => None,
        };
        let shape = memory
            .object_shape(*access)
            .map_err(|_| CfgAnalysisError::ContractInstantiation)?;
        if !shape.variants().is_empty() {
            return Err(CfgAnalysisError::ContractInstantiation);
        }
        for leaf in shape.resource_leaves() {
            let offset = leaf.bytes().start_bytes();
            let payload = storage
                .and_then(|storage| state.allocation(storage))
                .map(|allocation| {
                    allocation.resource_payload(super::resource::ResourcePayloadKey::new(
                        offset,
                        leaf.access(),
                    ))
                });
            let status = match &payload {
                Some(super::resource::MovePathState::Available(payload)) => {
                    aggregate_abi_payload_status(state, memory, leaf.access(), payload)
                }
                Some(super::resource::MovePathState::Moved) => ObligationStatus::Refuted,
                Some(super::resource::MovePathState::Unknown) | None => ObligationStatus::Unknown,
            };
            obligations.push(ResourceObligation::new(
                ResourceObligationKind::AggregateAbiPayloadValid {
                    allocation: storage,
                    offset_bytes: storage.map(|_| offset),
                    access: leaf.access(),
                },
                status,
                source_span,
            ));
            if let Some(super::resource::MovePathState::Available(payload)) = payload
                && let AbstractProvenance::Known(allocation) = payload.pointer().provenance()
            {
                transferred_allocations.insert(allocation);
            }
        }
    }
    // A returned owning storage capability also transfers the owners actually
    // stored inside that storage, including conditional enum payloads. Follow
    // only validated, available payloads behind a full returned owner; a raw
    // pointer or a returned borrow is not an ownership root.
    let mut pending = permission_values
        .iter()
        .filter_map(|id| {
            let AbstractValue::Permission(p) = state.value(*id)? else {
                return None;
            };
            let AbstractProvenance::Known(id) = p.provenance() else {
                return None;
            };
            let allocation = state.allocation(id)?;
            (p.free_capability() == super::FreeCapability::Yes
                && p.access() == super::AccessPermission::Write
                && p.range()
                    == super::AbstractByteRange::Exact(
                        super::ByteRange::new(0, allocation.size_bytes()).ok()?,
                    ))
            .then_some(id)
        })
        .collect::<Vec<_>>();
    let mut visited = BTreeSet::new();
    while let Some(root) = pending.pop() {
        if !visited.insert(root) {
            continue;
        }
        let Some(allocation) = state.allocation(root) else {
            continue;
        };
        for (key, payload) in allocation.object_state().resource_payloads() {
            let super::MovePathState::Available(payload) = payload else {
                continue;
            };
            if payload.permission().free_capability() != super::FreeCapability::Yes {
                continue;
            }
            let status = super::transfer::object_drop_payload_status(state, payload);
            obligations.push(ResourceObligation::new(
                ResourceObligationKind::ObjectDropPayloadValid {
                    allocation: Some(root),
                    offset_bytes: Some(key.offset_bytes()),
                    access: key.access(),
                },
                status,
                source_span,
            ));
            if status.is_proven()
                && let AbstractProvenance::Known(child) = payload.pointer().provenance()
            {
                transferred_allocations.insert(child);
                pending.push(child);
            }
        }
    }
    for (&allocation_id, allocation) in state.allocations() {
        let status = match (allocation.liveness(), allocation.ownership()) {
            (super::resource::LivenessState::Dead, _)
            | (_, super::resource::OwnershipState::Unowned) => ObligationStatus::Proven,
            (super::resource::LivenessState::Live, super::resource::OwnershipState::Owned)
                if transferred_allocations.contains(&allocation_id) =>
            {
                ObligationStatus::Proven
            }
            (super::resource::LivenessState::Live, super::resource::OwnershipState::Owned) => {
                ObligationStatus::Refuted
            }
            _ => ObligationStatus::Unknown,
        };
        obligations.push(ResourceObligation::new(
            ResourceObligationKind::OwnershipConserved {
                allocation: allocation_id,
            },
            status,
            source_span,
        ));
    }
    let successful = !obligations
        .iter()
        .any(|obligation| obligation.status() == ObligationStatus::Refuted);
    let mut returned_state = state.clone();
    if successful {
        for permission in permission_values {
            if let Some(AbstractValue::Permission(fact)) = returned_state.value_mut(permission) {
                fact.mark_consumed();
            }
        }
    }
    Ok(ReturnTransfer {
        state: returned_state,
        values: facts,
        obligations,
        successful,
    })
}

fn refine_branch(
    block: VirBlockId,
    state: &ResourceState,
    condition: VirValueId,
    expected: bool,
    comparison: Option<PathFact>,
    memory: &VirMemorySchema,
) -> Result<ResourceState, CfgAnalysisError> {
    let condition_fact = state
        .value(condition)
        .copied()
        .unwrap_or(AbstractValue::Bool(AbstractBool::Unknown));
    ensure_type(block, condition, VirType::Bool, condition_fact)?;
    let AbstractValue::Bool(condition_fact) = condition_fact else {
        unreachable!("type checked above")
    };
    if matches!(
        (condition_fact, expected),
        (AbstractBool::True, false) | (AbstractBool::False, true)
    ) {
        return Ok(ResourceState::unreachable());
    }

    let mut refined = state.clone();
    refined.conjoin_path_fact(PathFact::boolean(condition, expected));
    if let Some(comparison) = comparison {
        let effective = if expected {
            comparison
        } else {
            comparison.negated()
        };
        refined.conjoin_path_fact(effective);
        refine_integer_comparison(&mut refined, effective);
        refine_enum_discriminant(&mut refined, effective, memory);
    }
    Ok(refined)
}

fn refine_integer_comparison(state: &mut ResourceState, comparison: PathFact) {
    let PathFact::Comparison {
        predicate,
        left,
        right,
    } = comparison
    else {
        return;
    };
    if left == right {
        return;
    }
    let (Some(AbstractValue::U64(left_interval)), Some(AbstractValue::U64(right_interval))) =
        (state.value(left).copied(), state.value(right).copied())
    else {
        return;
    };
    let refined = match predicate {
        VirIntegerPredicate::Equal => left_interval
            .intersection(right_interval)
            .map(|intersection| (intersection, intersection)),
        VirIntegerPredicate::NotEqual => refine_not_equal(left_interval, right_interval),
        VirIntegerPredicate::LessThan => refine_less_than(left_interval, right_interval),
        VirIntegerPredicate::LessOrEqual => refine_less_or_equal(left_interval, right_interval),
        VirIntegerPredicate::GreaterThan => {
            refine_less_than(right_interval, left_interval).map(|(right, left)| (left, right))
        }
        VirIntegerPredicate::GreaterOrEqual => {
            refine_less_or_equal(right_interval, left_interval).map(|(right, left)| (left, right))
        }
    };
    let Some((left_interval, right_interval)) = refined else {
        *state = ResourceState::unreachable();
        return;
    };
    state.narrow_word_interval(left, left_interval);
    state.narrow_word_interval(right, right_interval);
}

fn refine_less_than(left: U64Interval, right: U64Interval) -> Option<(U64Interval, U64Interval)> {
    if left.lower() >= right.upper() {
        return None;
    }
    let left_limit = U64Interval::new(0, right.upper().checked_sub(1)?).ok()?;
    let right_limit = U64Interval::new(left.lower().checked_add(1)?, u64::MAX).ok()?;
    Some((
        left.intersection(left_limit)?,
        right.intersection(right_limit)?,
    ))
}

fn refine_less_or_equal(
    left: U64Interval,
    right: U64Interval,
) -> Option<(U64Interval, U64Interval)> {
    if left.lower() > right.upper() {
        return None;
    }
    let left_limit = U64Interval::new(0, right.upper()).ok()?;
    let right_limit = U64Interval::new(left.lower(), u64::MAX).ok()?;
    Some((
        left.intersection(left_limit)?,
        right.intersection(right_limit)?,
    ))
}

fn refine_not_equal(left: U64Interval, right: U64Interval) -> Option<(U64Interval, U64Interval)> {
    match (left.exact_value(), right.exact_value()) {
        (Some(left), Some(right)) if left == right => None,
        (Some(value), _) => Some((left, exclude_interval_endpoint(right, value)?)),
        (_, Some(value)) => Some((exclude_interval_endpoint(left, value)?, right)),
        _ => Some((left, right)),
    }
}

fn exclude_interval_endpoint(interval: U64Interval, value: u64) -> Option<U64Interval> {
    if interval.exact_value() == Some(value) {
        None
    } else if interval.lower() == value {
        U64Interval::new(value.checked_add(1)?, interval.upper()).ok()
    } else if interval.upper() == value {
        U64Interval::new(interval.lower(), value.checked_sub(1)?).ok()
    } else {
        Some(interval)
    }
}

fn refine_enum_discriminant(
    state: &mut ResourceState,
    comparison: PathFact,
    memory: &VirMemorySchema,
) {
    let PathFact::Comparison {
        predicate,
        left,
        right,
    } = comparison
    else {
        return;
    };
    let equality = match predicate {
        VirIntegerPredicate::Equal => true,
        VirIntegerPredicate::NotEqual => false,
        VirIntegerPredicate::LessThan
        | VirIntegerPredicate::LessOrEqual
        | VirIntegerPredicate::GreaterThan
        | VirIntegerPredicate::GreaterOrEqual => return,
    };
    let facts = state.values();
    let (fact, discriminant) = match (facts.get(&left).copied(), facts.get(&right).copied()) {
        (Some(AbstractValue::EnumDiscriminant(fact)), Some(other)) => (fact, exact_word(other)),
        (Some(other), Some(AbstractValue::EnumDiscriminant(fact))) => (fact, exact_word(other)),
        _ => return,
    };
    let Some(discriminant) = discriminant else {
        return;
    };
    apply_enum_discriminant_refinement(state, fact, discriminant, equality, memory);
}

fn exact_word(value: AbstractValue) -> Option<u64> {
    match value {
        AbstractValue::U64(interval) => interval.exact_value(),
        AbstractValue::EnumDiscriminant(fact) => fact.interval().exact_value(),
        AbstractValue::Bool(_) | AbstractValue::Pointer(_) | AbstractValue::Permission(_) => None,
    }
}

fn apply_enum_discriminant_refinement(
    state: &mut ResourceState,
    fact: EnumDiscriminantFact,
    discriminant: u64,
    equality: bool,
    memory: &VirMemorySchema,
) {
    let pointer = fact.pointer();
    let (AbstractProvenance::Known(allocation_id), Some(offset_bytes)) =
        (pointer.provenance(), pointer.offset_bytes().exact_value())
    else {
        return;
    };
    let Ok(shape) = memory.object_shape(fact.access()) else {
        return;
    };
    let cases = shape
        .variants()
        .iter()
        .filter(|case| case.path().segments().is_empty() && case.enum_access() == fact.access())
        .collect::<Vec<_>>();
    let declared = cases
        .iter()
        .map(|case| case.variant())
        .collect::<BTreeSet<_>>();
    let selected = cases
        .iter()
        .find(|case| case.discriminant() == discriminant)
        .map(|case| case.variant());
    if equality && selected.is_none() {
        *state = ResourceState::unreachable();
        return;
    }
    let key = ObjectStateKey::new(offset_bytes, fact.access());
    let Some(allocation) = state.allocation_mut(allocation_id) else {
        return;
    };
    let mut alternatives = allocation
        .active_variant(key)
        .alternatives()
        .unwrap_or(declared);
    if equality {
        alternatives.retain(|variant| Some(*variant) == selected);
    } else if let Some(selected) = selected {
        alternatives.remove(&selected);
    }
    if alternatives.is_empty() {
        *state = ResourceState::unreachable();
        return;
    }
    let active = if alternatives.len() == 1 {
        ActiveVariantState::Exact(*alternatives.first().expect("one active variant"))
    } else {
        ActiveVariantState::Alternatives(alternatives)
    };
    let _ = allocation.set_active_variant(key, active);
}

fn direct_comparison_definition(block: &VirBasicBlock, condition: VirValueId) -> Option<PathFact> {
    block
        .instructions
        .iter()
        .rev()
        .find_map(|instruction| match instruction.instruction {
            VirInstruction::Compare {
                result,
                predicate,
                left,
                right,
            } if result.id == condition => Some(PathFact::comparison(predicate, left, right)),
            _ => None,
        })
}

fn missing_value(ty: VirType) -> AbstractValue {
    if matches!(ty, VirType::Permission) {
        AbstractValue::Permission(unknown_permission())
    } else {
        unknown_value(ty)
    }
}

fn ensure_type(
    block: VirBlockId,
    value: VirValueId,
    expected: VirType,
    fact: AbstractValue,
) -> Result<(), CfgAnalysisError> {
    let found = abstract_value_type(fact);
    if abstract_value_matches_type(fact, expected) {
        Ok(())
    } else {
        Err(CfgAnalysisError::AbstractValueTypeMismatch {
            block,
            value,
            expected,
            found,
        })
    }
}

fn target_block<'a>(
    target: &VirBlockTarget,
    blocks: &BTreeMap<VirBlockId, &'a VirBasicBlock>,
) -> Result<&'a VirBasicBlock, CfgAnalysisError> {
    blocks
        .get(&target.block)
        .copied()
        .ok_or(CfgAnalysisError::MissingBlock(target.block))
}

fn wrap_edge_obligations(
    program: &ResolvedVirUnit<'_>,
    function: VirFunctionId,
    block: VirBlockId,
    origin: CfgObligationOrigin,
    obligations: Vec<ResourceObligation>,
) -> Result<Vec<CfgObligation>, CfgAnalysisError> {
    obligations
        .into_iter()
        .map(|obligation| {
            cfg_obligation(
                program,
                block,
                origin,
                VirLocation::Terminator { function, block },
                obligation,
            )
        })
        .collect()
}

fn cfg_obligation(
    program: &ResolvedVirUnit<'_>,
    block: VirBlockId,
    origin: CfgObligationOrigin,
    location: VirLocation,
    obligation: ResourceObligation,
) -> Result<CfgObligation, CfgAnalysisError> {
    let finding = VerifierFinding::runtime(program, location, obligation.source_span())
        .ok_or(CfgAnalysisError::InvalidFinding { location })?;
    Ok(CfgObligation {
        block,
        origin,
        finding,
        obligation,
    })
}

fn merge_case_obligation(obligations: &mut Vec<CfgObligation>, incoming: CfgObligation) {
    if let Some(existing) = obligations.iter_mut().find(|existing| {
        existing.block == incoming.block
            && existing.origin == incoming.origin
            && existing.obligation.kind() == incoming.obligation.kind()
            && existing.obligation.source_span() == incoming.obligation.source_span()
    }) {
        let status =
            combine_case_status(existing.obligation.status(), incoming.obligation.status());
        existing.obligation = ResourceObligation::new(
            existing.obligation.kind(),
            status,
            existing.obligation.source_span(),
        );
    } else {
        obligations.push(incoming);
    }
}

const fn combine_case_status(left: ObligationStatus, right: ObligationStatus) -> ObligationStatus {
    match (left, right) {
        (ObligationStatus::Refuted, _) | (_, ObligationStatus::Refuted) => {
            ObligationStatus::Refuted
        }
        (ObligationStatus::Unknown, _) | (_, ObligationStatus::Unknown) => {
            ObligationStatus::Unknown
        }
        (ObligationStatus::Proven, ObligationStatus::Proven) => ObligationStatus::Proven,
    }
}

fn has_refinement_candidate(obligations: &[CfgObligation]) -> bool {
    obligations.iter().any(|record| {
        record.obligation.status() == ObligationStatus::Unknown
            && !matches!(
                record.obligation.kind(),
                ResourceObligationKind::AllocationSizeNonZero { .. }
                    | ResourceObligationKind::AllocationSizeWithinLimit { .. }
                    | ResourceObligationKind::AllocationExtentExact { .. }
                    | ResourceObligationKind::ObjectTriviallyCopyable { .. }
                    | ResourceObligationKind::ObjectMoveSupported { .. }
                    | ResourceObligationKind::ObjectTriviallyDroppable { .. }
                    | ResourceObligationKind::ObjectBuiltinDroppable { .. }
                    | ResourceObligationKind::CallContractAvailable { .. }
                    | ResourceObligationKind::CallContractPrecondition { .. }
            )
    })
}

fn combine_block_inputs(
    block: VirBlockId,
    function_entry: VirBlockId,
    entry_seed: &ConditionalResourceState,
    incoming_edges: &BTreeMap<CfgEdgeKey, (VirBlockId, ConditionalResourceState)>,
    limits: GuardedStateLimits,
    reduction: GuardedReduction,
) -> Result<ConditionalResourceState, CfgAnalysisError> {
    let mut cases = Vec::new();
    let mut losses = BTreeSet::new();
    if block == function_entry {
        cases.extend(entry_seed.cases().iter().cloned());
        losses.extend(entry_seed.precision_losses().iter().copied());
    }
    for (target, state) in incoming_edges.values() {
        if *target == block {
            cases.extend(state.cases().iter().cloned());
            losses.extend(state.precision_losses().iter().copied());
        }
    }
    ConditionalResourceState::from_cases(cases, losses, limits, reduction)
        .map_err(|error| CfgAnalysisError::ResourceJoin { block, error })
}

fn collect_guarded_precision_losses(
    block: VirBlockId,
    evaluated: &ConditionalBlockEvaluation,
    losses: &mut BTreeMap<VirBlockId, BTreeSet<GuardedStatePrecisionLoss>>,
) {
    let block_losses = losses.entry(block).or_default();
    block_losses.extend(evaluated.entry.precision_losses().iter().copied());
    block_losses.extend(evaluated.exit_state.precision_losses().iter().copied());
    for state in &evaluated.instruction_states {
        block_losses.extend(state.precision_losses().iter().copied());
    }
    for successor in &evaluated.successors {
        block_losses.extend(successor.state.precision_losses().iter().copied());
    }
    if block_losses.is_empty() {
        losses.remove(&block);
    }
}

#[allow(clippy::too_many_arguments)]
fn merge_successor(
    block: VirBlockId,
    incoming: ConditionalResourceState,
    loop_blocks: &BTreeSet<VirBlockId>,
    config: CfgAnalysisConfig,
    entries: &mut BTreeMap<VirBlockId, ConditionalResourceState>,
    entry_updates: &mut BTreeMap<VirBlockId, u32>,
    widened_blocks: &mut BTreeSet<VirBlockId>,
) -> Result<bool, CfgAnalysisError> {
    if !incoming.is_reachable() {
        return Ok(false);
    }
    let Some(current) = entries.get(&block).cloned() else {
        entries.insert(block, incoming);
        entry_updates.insert(block, 0);
        return Ok(true);
    };
    // `incoming` is already the normalized combination of every currently
    // known predecessor edge.  Keeping old acyclic entries in the join would
    // retain superseded partial predecessor sets (for example `{p}` after the
    // complete `{p, not p}` input has simplified to `true`).  Cycles still
    // need monotone join/widening for fixed-point convergence; acyclic blocks
    // can and should use the recomputed input directly.
    if !loop_blocks.contains(&block) {
        if incoming == current {
            return Ok(false);
        }
        entries.insert(block, incoming);
        return Ok(true);
    }
    let mut joined = current
        .join(
            &incoming,
            config.guarded_limits(),
            GuardedReduction::Selective,
        )
        .map_err(|error| CfgAnalysisError::ResourceJoin { block, error })?;
    if joined.cases().len() > 1 {
        joined = joined
            .collapse_for_loop(config.guarded_limits())
            .map_err(|error| CfgAnalysisError::ResourceJoin { block, error })?;
    }
    if joined == current {
        return Ok(false);
    }

    let updates = entry_updates.entry(block).or_default();
    let next = if *updates >= config.widen_after_updates {
        let widened = current
            .widen(&joined, config.guarded_limits())
            .map_err(|error| CfgAnalysisError::ResourceJoin { block, error })?;
        if widened != joined {
            widened_blocks.insert(block);
        }
        widened
    } else {
        joined
    };
    if next == current {
        return Ok(false);
    }
    *updates = updates.saturating_add(1);
    entries.insert(block, next);
    Ok(true)
}

fn find_loop_blocks(blocks: &BTreeMap<VirBlockId, &VirBasicBlock>) -> BTreeSet<VirBlockId> {
    let adjacency: BTreeMap<_, _> = blocks
        .iter()
        .map(|(&id, block)| (id, successor_ids(&block.terminator.terminator)))
        .collect();
    let mut reverse = blocks
        .keys()
        .copied()
        .map(|id| (id, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for (&source, targets) in &adjacency {
        for target in targets {
            if let Some(predecessors) = reverse.get_mut(target) {
                predecessors.push(source);
            }
        }
    }

    // Iterative Kosaraju avoids both recursive host-stack growth and the
    // quadratic per-block reachability scans that large CFGs would otherwise
    // induce.
    let mut visited = BTreeSet::new();
    let mut postorder = Vec::with_capacity(blocks.len());
    for &start in blocks.keys() {
        if visited.contains(&start) {
            continue;
        }
        let mut pending = vec![(start, false)];
        while let Some((block, expanded)) = pending.pop() {
            if expanded {
                postorder.push(block);
                continue;
            }
            if !visited.insert(block) {
                continue;
            }
            pending.push((block, true));
            if let Some(successors) = adjacency.get(&block) {
                pending.extend(
                    successors
                        .iter()
                        .rev()
                        .copied()
                        .filter(|successor| !visited.contains(successor))
                        .map(|successor| (successor, false)),
                );
            }
        }
    }

    let mut assigned = BTreeSet::new();
    let mut loop_blocks = BTreeSet::new();
    for &start in postorder.iter().rev() {
        if !assigned.insert(start) {
            continue;
        }
        let mut component = Vec::new();
        let mut pending = vec![start];
        while let Some(block) = pending.pop() {
            component.push(block);
            if let Some(predecessors) = reverse.get(&block) {
                for predecessor in predecessors.iter().rev().copied() {
                    if assigned.insert(predecessor) {
                        pending.push(predecessor);
                    }
                }
            }
        }
        if component.len() > 1
            || adjacency
                .get(&start)
                .is_some_and(|successors| successors.contains(&start))
        {
            loop_blocks.extend(component);
        }
    }
    loop_blocks
}

fn successor_ids(terminator: &VirTerminator) -> Vec<VirBlockId> {
    match terminator {
        VirTerminator::Jump { target } => vec![target.block],
        VirTerminator::Branch {
            then_target,
            else_target,
            ..
        } => vec![then_target.block, else_target.block],
        VirTerminator::Return { .. } => Vec::new(),
    }
}

#[allow(clippy::too_many_arguments)]
fn append_queries(
    program: &ResolvedVirUnit<'_>,
    sources: &super::relation::audit::SourceIndex,
    block: VirBlockId,
    span: ByteSpan,
    location: VirLocation,
    case_ordinal: usize,
    edge_ordinal: Option<u8>,
    queries: Option<Vec<super::relation::audit::QueryObservation>>,
    output: &mut Vec<super::relation::audit::QueryEvidence>,
    config: CfgAnalysisConfig,
) -> Result<(), CfgAnalysisError> {
    let queries = queries.ok_or(CfgAnalysisError::RelationEvidenceBudgetExceeded {
        block,
        limit: super::relation::audit::MAX_QUERIES_PER_SITE,
    })?;
    if queries.len().saturating_add(output.len()) > config.max_relation_evidence {
        return Err(CfgAnalysisError::RelationEvidenceBudgetExceeded {
            block,
            limit: config.max_relation_evidence,
        });
    }
    if queries.is_empty() {
        return Ok(());
    }
    let finding = VerifierFinding::runtime(program, location, span)
        .ok_or(CfgAnalysisError::InvalidFinding { location })?;
    output.extend(
        queries
            .into_iter()
            .enumerate()
            .map(|(query_ordinal, query)| {
                let (sources, sources_truncated) = sources.sources(&query);
                super::relation::audit::QueryEvidence {
                    config,
                    sources,
                    sources_truncated,
                    finding,
                    case_ordinal,
                    edge_ordinal,
                    query_ordinal,
                    query,
                }
            }),
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_comparison_refinement_tightens_both_unsigned_intervals() {
        let left = VirValueId::new(0);
        let right = VirValueId::new(1);
        let mut state = ResourceState::new();
        state
            .define_value(left, AbstractValue::U64(U64Interval::unknown()))
            .unwrap();
        state
            .define_value(right, AbstractValue::U64(U64Interval::exact(2)))
            .unwrap();

        refine_integer_comparison(
            &mut state,
            PathFact::comparison(VirIntegerPredicate::LessThan, left, right),
        );

        assert_eq!(
            state.value(left),
            Some(&AbstractValue::U64(U64Interval::new(0, 1).unwrap()))
        );
        assert_eq!(
            state.value(right),
            Some(&AbstractValue::U64(U64Interval::exact(2)))
        );
    }

    #[test]
    fn impossible_integer_comparison_makes_the_branch_unreachable() {
        let left = VirValueId::new(0);
        let right = VirValueId::new(1);
        let mut state = ResourceState::new();
        state
            .define_value(left, AbstractValue::U64(U64Interval::exact(2)))
            .unwrap();
        state
            .define_value(right, AbstractValue::U64(U64Interval::exact(2)))
            .unwrap();

        refine_integer_comparison(
            &mut state,
            PathFact::comparison(VirIntegerPredicate::LessThan, left, right),
        );

        assert!(!state.path_condition().is_reachable());
    }
}
