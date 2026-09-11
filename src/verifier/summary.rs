//! Signature-relative observations of the canonical CFG. Only the private
//! closure registry authorizes transfer; a mutable diagnostic DTO never does.
//!
//! ```compile_fail
//! fn import(dto: nera::verifier::summary::FunctionSummary) {
//!     let registry = nera::verifier::summary::SummaryRegistry::new(dto.binding.clone());
//! }
//! ```
pub mod audit;
mod borrow;
mod effects;
mod guards;
mod instantiate;
mod projection;
pub(crate) mod recursive;
mod registry;
mod validate;
pub use effects::{CallSummaryOutcome, CallSummaryUse};
pub(crate) use effects::{EffectJournal, SummaryTransferContext};
pub(crate) use instantiate::{CallInstantiation, instantiate};
pub use recursive::{SccAnalysis, SccCandidate, SccLimits, SccOutcome};
pub(crate) use registry::{SummaryRegistry, components};

use super::{
    AbstractBool, AccessPermission, ByteRange, ByteSet, CfgAnalysisConfig, FreeCapability,
    InitializationState, LivenessState, LoanActivity, ObligationStatus, OwnershipState,
    PermissionAvailability, U64Interval,
};
use crate::{
    ResolvedVirUnit, VirFunctionId, VirIntegerPredicate, VirMemoryAccess, VirObjectPathSegment,
    VirType, VirVariantId,
};
use std::{fmt, sync::Arc};

pub(crate) use projection::project;
pub use validate::SummaryValidationError;

pub const SUMMARY_SCHEMA_VERSION: u32 = 7;
pub const SUMMARY_VERIFIER_PROFILE: &str = "nera-resource-summary-v7";

/// Exact content binding, shared by all functions in a report. Debug output is
/// deliberately abbreviated; the diagnostic checksum is NEVER used for equality
/// or cache lookup. Full unit equality binds body, ABI, contracts, source, profile
/// and direct dependency bodies without a hash collision assumption.
#[derive(Clone, PartialEq, Eq)]
pub struct SummaryBinding {
    unit: Arc<str>,
    function: VirFunctionId,
    config: CfgAnalysisConfig,
}
impl SummaryBinding {
    pub(crate) fn unit(program: &ResolvedVirUnit<'_>) -> Arc<str> {
        format!("{:?}", program.as_unit()).into()
    }
    pub(crate) fn new(unit: Arc<str>, function: VirFunctionId, config: CfgAnalysisConfig) -> Self {
        Self {
            unit,
            function,
            config,
        }
    }
}
impl fmt::Debug for SummaryBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let checksum = self
            .unit
            .bytes()
            .fold(0xcbf29ce484222325_u64, |hash, byte| {
                (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3)
            });
        f.debug_struct("SummaryBinding")
            .field("diagnostic_checksum", &checksum)
            .field("function", &self.function)
            .field("config", &self.config)
            .finish()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SummaryState {
    Uncomputed,
    /// Private SCC trial only; not a well-formed exported diagnostic summary.
    Hypothesis,
    Candidate,
    /// Issued only by the private closure registry after canonical body checks.
    Closed,
    Unknown(Vec<SummaryLoss>),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SummaryLoss {
    SafetyObligation,
    GuardProjection,
    ResourceProjection,
    AnalysisPrecision,
}

/// Parameter is a VIR signature slot (including ghost permission slots), not a
/// source spelling or SSA ID. Payload paths name entry-owned nested resources.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ResourceName {
    Input {
        parameter: usize,
        payload_offsets: Vec<u64>,
    },
    /// Existential binder, scoped to one complete return world. Never reusable
    /// as a concrete allocation identity at two caller instantiations.
    Fresh(usize),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Knowledge<T> {
    Known(T),
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueEpoch {
    Pre,
    Post,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueCoordinate {
    Parameter(usize),
    Result(usize),
    Pointee {
        resource: ResourceName,
        offset: u64,
        access: VirMemoryAccess,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueReference {
    pub epoch: ValueEpoch,
    pub coordinate: ValueCoordinate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarTerm {
    Constant(u64),
    Input(usize),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryBound {
    pub terms: Vec<(usize, u64)>,
    pub addend: u64,
    pub interval: U64Interval,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SummaryRange {
    Exact(ByteRange),
    Symbolic {
        start: SummaryBound,
        end: SummaryBound,
    },
    Unknown,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SummaryDomain {
    Allocation,
    Restricted(SummaryRange),
    Unknown,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryPath {
    pub access: VirMemoryAccess,
    /// (signature pointer slot, role: object=0, incoming=1, selected=2)
    pub parameter: Option<(usize, u8)>,
    pub steps: Vec<VirObjectPathSegment>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryPointer {
    pub resource: Knowledge<ResourceName>,
    pub access: Option<VirMemoryAccess>,
    pub offset: U64Interval,
    pub offset_expression: Option<SummaryBound>,
    pub alignment: u64,
    pub domain: SummaryDomain,
    pub object_path: Option<SummaryPath>,
    pub domain_path: Option<SummaryPath>,
    pub slice_range: Option<SummaryRange>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SummaryAuthority {
    Owner,
    InputLoan(usize),
    Unknown,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryPermission {
    pub resource: Knowledge<ResourceName>,
    pub range: SummaryRange,
    pub access: AccessPermission,
    pub free: FreeCapability,
    pub availability: PermissionAvailability,
    pub authority: SummaryAuthority,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SummaryValue {
    Word {
        interval: U64Interval,
        expression: Option<SummaryBound>,
    },
    Bool(AbstractBool),
    Pointer(Box<SummaryPointer>),
    Permission(Box<SummaryPermission>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueMapping {
    pub coordinate: ValueReference,
    pub value: SummaryValue,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SummaryGuard {
    Boolean {
        parameter: usize,
        expected: bool,
    },
    Compare {
        predicate: VirIntegerPredicate,
        left: ScalarTerm,
        right: ScalarTerm,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SummaryMovePath {
    Available {
        pointer: Box<SummaryPointer>,
        permission: Box<SummaryPermission>,
    },
    Moved,
    Unknown,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PayloadState {
    pub offset: u64,
    pub access: VirMemoryAccess,
    pub state: SummaryMovePath,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantState {
    pub offset: u64,
    pub access: VirMemoryAccess,
    pub alternatives: Knowledge<Vec<VirVariantId>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResourcePostState {
    pub name: ResourceName,
    pub storage: ResourceStorage,
    pub region: Option<crate::VirRegionId>,
    pub size: u64,
    pub alignment: u64,
    pub liveness: LivenessState,
    pub ownership: OwnershipState,
    pub initialization: InitializationState,
    pub validity: ByteSet,
    pub variants: Vec<VariantState>,
    pub payloads: Vec<PayloadState>,
    pub object_precise: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceStorage {
    Input,
    Heap,
    ReturnedStorage,
    Unknown,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowRestoration {
    pub input_permission: usize,
    pub activity: LoanActivity,
    /// Actual exported endpoint, not the possibly dead entry SSA operand.
    pub permission: SummaryPermission,
}

/// Every member is a complete possible state. A consumer must establish a
/// guarantee in ALL worlds. This disjunction is the conservative merge when
/// local guards are existentially hidden, NOT independently joined fact axes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnAlternative {
    pub guard: Vec<SummaryGuard>,
    pub worlds: Vec<ReturnWorld>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnWorld {
    /// May effects in this world's resource namespace. Input effects can be
    /// overapproximated across paths; fresh binders never cross world scopes.
    pub effects: SummaryEffects,
    /// Index into cfg.returns(), which retains the source finding and case ID.
    pub return_evidence: usize,
    pub values: Vec<ValueMapping>,
    /// Post-state of physical input slots, distinct from immutable pre snapshots.
    pub post_inputs: Knowledge<Vec<ValueMapping>>,
    pub resources: Vec<ResourcePostState>,
    pub borrow_restoration: Vec<BorrowRestoration>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryFootprint {
    pub resource: ResourceName,
    pub range: SummaryRange,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryEffects {
    pub may_read: Knowledge<Vec<SummaryFootprint>>,
    pub may_write: Knowledge<Vec<SummaryFootprint>>,
    pub may_free: Knowledge<Vec<ResourceName>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvidenceKind {
    Cfg,
    Historical,
    Postcondition,
    Proof,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryFinding {
    pub kind: EvidenceKind,
    pub index: usize,
    pub status: ObligationStatus,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryFaults {
    /// All safety findings remain requirements, including those on paths that
    /// transfer made unreachable. Not a permissive "may fault" escape hatch.
    pub requirements: Vec<SummaryFinding>,
    pub runtime_faults: Knowledge<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionSummary {
    pub audit_complete: bool,
    pub recursion: Option<SccAnalysis>,
    recursion_shape: Option<SccAnalysis>,
    pub call_uses: Vec<CallSummaryUse>,
    pub local_effect_events: usize,
    pub version: u32,
    pub verifier_profile: String,
    pub binding: SummaryBinding,
    pub dependencies: Vec<SummaryDependency>,
    pub state: SummaryState,
    pub parameters: Vec<VirType>,
    pub results: Vec<VirType>,
    pub inputs: Vec<ValueMapping>,
    pub input_resources: Vec<ResourcePostState>,
    pub effects: SummaryEffects,
    pub normal_returns: Knowledge<Vec<ReturnAlternative>>,
    pub faults: SummaryFaults,
    // No deserializer or externally constructible proof/seal. Only the projector
    // records expected evidence shapes for structural mutation checking.
    return_count: usize,
    evidence_shape: Vec<SummaryFinding>,
    input_shape: Vec<ResourceName>,
    projected_state: SummaryState,
    return_guards: Vec<Vec<SummaryGuard>>,
    effects_shape: SummaryEffects,
    closed: bool,
    dependency_states: Vec<SummaryState>,
    world_shapes: Vec<ReturnWorld>,
}

/// Exact dependency identity and publication state. CallSummaryUse separately
/// records whether this caller could instantiate that closed dependency.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryDependency {
    pub binding: SummaryBinding,
    pub state: SummaryState,
}

fn dependencies(
    program: &ResolvedVirUnit<'_>,
    function: &crate::VirFunction,
    binding: &SummaryBinding,
) -> Vec<SummaryDependency> {
    function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter_map(|i| {
            if let crate::VirInstruction::Call { target, .. } = &i.instruction {
                program.runtime().call_target_id(target)
            } else {
                None
            }
        })
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .map(|id| SummaryDependency {
            binding: SummaryBinding::new(binding.unit.clone(), id, binding.config),
            state: SummaryState::Uncomputed,
        })
        .collect()
}
impl FunctionSummary {
    /// Deterministic diagnostic serialization, intentionally not an importable
    /// proof format. The binding checksum is only a display label; validation
    /// compares the private exact content, never this checksum.
    pub fn stable_dump(&self) -> String {
        format!("nera-summary-v{}\n{self:#?}\n", self.version)
    }
    pub fn validate_structure(
        &self,
        program: &ResolvedVirUnit<'_>,
        function: VirFunctionId,
        config: CfgAnalysisConfig,
    ) -> Result<(), SummaryValidationError> {
        validate::validate(self, program, function, config)
    }
}
