//! Versioned Verification IR shared by fast and verification builds.
//!
//! The runtime VIR is deliberately independent from the former Core0
//! projection. It is a typed, block-structured SSA interface with explicit
//! memory and permission operations. Since stage 6.4.2, [`VirUnit`] is the
//! sole versioned owner of the memory schema, runtime program, specification
//! environment, and source map consumed by later compiler phases.

mod aggregate_abi;
mod borrow;
mod borrow_interface;
pub(crate) use borrow::interface_loan_id;
mod dump;
mod interpreter;
mod memory;
mod object_shape;
mod provenance;
mod resolve;
mod semantics;
mod source_map;
mod spec;
mod validate;

use std::fmt;

use crate::ByteSpan;

pub use aggregate_abi::{
    VIR_AGGREGATE_ABI_MAX_DIRECT_BYTES, VIR_AGGREGATE_ABI_MAX_DIRECT_LEAVES, VirAbiBinding,
    VirAbiEnvironment, VirAbiError, VirAbiErrorKind, VirAbiLeaf, VirAbiSignature, VirAbiValue,
    VirFunctionAbi, VirInterfaceEffect, VirInterfaceStorage, VirInterfaceTransfer,
};
pub use borrow::{
    VirBorrowEnvironment, VirBorrowRegion, VirBorrowRegionConstraint, VirBorrowRegionOrigin,
    VirBorrowRegionScope, VirLoanAuthorityEffect, VirLoanEffect, VirLoanKind, VirLoanRange,
};
pub use interpreter::{
    VIR_INTERPRETER_MAX_ACTIVE_LOANS, VIR_INTERPRETER_MAX_ALIASES_PER_LOAN,
    VIR_INTERPRETER_MAX_OBJECT_ROOTS, VIR_INTERPRETER_MAX_REBORROW_DEPTH,
    VIR_INTERPRETER_MAX_RESOURCE_PAYLOADS, VirExecution, VirExecutionError, VirExecutionErrorKind,
    VirInterpreterConfig, VirRuntimePermission, VirRuntimePointer, VirRuntimeValue, VirTraceEvent,
    VirTracePoint, interpret, interpret_with_config,
};
pub use memory::{
    VirAbiClass, VirEndianness, VirField, VirFieldId, VirFieldLayout, VirIntegerType, VirLayout,
    VirLayoutId, VirMemoryAccess, VirMemorySchema, VirMemorySchemaError, VirMemorySchemaErrorKind,
    VirMemoryType, VirMemoryTypeKind, VirMutability, VirPointerKind, VirTargetDataLayout,
    VirTypeId, VirVariant, VirVariantCaseLayout, VirVariantId, VirVariantLayout,
};
pub use object_shape::{
    VIR_OBJECT_SHAPE_MAX_DEPTH, VIR_OBJECT_SHAPE_MAX_NODES, VirObjectArrayShape,
    VirObjectByteRange, VirObjectLeaf, VirObjectPath, VirObjectPathSegment, VirObjectResourceLeaf,
    VirObjectShape, VirObjectShapeError, VirObjectShapeErrorKind, VirObjectVariantShape,
};
pub use provenance::{
    VirAddressStep, VirNominalPath, VirPointerDescription, VirPointerDomain, VirPointerKey,
    VirPointerPaths, VirPointerSource, VirProvenanceCatalog, VirSequence, VirSequenceExtent,
    VirSubobject,
};
pub use resolve::{
    ResolvedRuntimeVirView, ResolvedVirUnit, VirResolutionError, VirResolutionErrorKind,
};
pub use semantics::{
    VIR_SYSTEM_SEMANTICS_V1, VIR_SYSTEM_SEMANTICS_V2, VirArithmeticSemantics,
    VirComparisonSemantics, VirDivergenceSemantics, VirFailureDisposition,
    VirPointerOffsetSemantics, VirProveSemantics, VirRuntimeSemanticProfile, VirSemanticProfileId,
};
pub(crate) use source_map::VirSourceMapEntry;
pub use source_map::{
    VirGeneratedReason, VirLocation, VirLocationOrigin, VirOrigin, VirOriginKind, VirSource,
    VirSourceMap, VirSourceMapErrorKind, VirSourceSpan,
};
pub use spec::{
    VirContract, VirContractAccess, VirContractBinder, VirContractBinderId, VirContractFree,
    VirContractInitialization, VirContractLiveness, VirContractOwnership, VirContractPermission,
    VirContractPointer, VirContractPosition, VirContractResource, VirContractResourceId,
    VirContractResourceSummary, VirPredicate, VirPredicateId, VirSpecAssertion, VirSpecAssertionId,
    VirSpecAssertionKind, VirSpecBinder, VirSpecBinderId, VirSpecBinderOwner, VirSpecClause,
    VirSpecClauseId, VirSpecClauseKind, VirSpecClauseOrigin, VirSpecClauseOwner,
    VirSpecEnvironment, VirSpecLocation, VirSpecLoopInvariant, VirSpecLoopInvariantId,
    VirSpecProve, VirSpecProveId, VirSpecSnapshot, VirSpecTables, VirSpecTerm, VirSpecTermId,
    VirSpecTermKind, VirSpecType, VirTrustEntry, VirTrustEntryId, VirTrustPolicyKind,
    VirTrustScope,
};
pub use validate::{VirValidationError, VirValidationErrorKind};

/// The serialized/dumped verification-unit schema version.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirUnitVersion {
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    /// Signature-bound borrow calls and unconditional returned-view skeletons.
    V9,
    /// Explicit retirement of possibly partial, pointer-free storage values.
    V10,
    /// Empty resource storage epochs for partial aggregate construction.
    V11,
    /// Authority-directed child creation with runtime parent identity.
    V12,
    /// Permission-neutral, typed raw address formation.
    V13,
    /// Subobject arithmetic domains and inclusive one-past formation.
    V14,
    /// Same-instance, same-domain pointer relations.
    V15,
    /// Explicit logical borrow-result relationships, separate from ABI slots.
    V16,
    /// Guarded logical borrow-result worlds with path-sensitive restoration.
    V17,
    /// Bounded fixed-field and slice borrow-result projections.
    V18,
    /// Separate resource assertion DAG, with pure terms unchanged.
    V19,
    /// Checked Spec arithmetic and byte-range relations; no runtime ABI change.
    V20,
    /// Memory observations; resource claims name physical permission snapshots.
    V21,
}

/// Stable identifier of a function within one VIR unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirFunctionId(u32);

/// Stable identifier of a basic block within one VIR function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirBlockId(u32);

/// Stable identifier of an SSA value within one VIR function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirValueId(u32);

/// Logical region named by allocation instructions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirRegionId(u32);

/// Stable identity of a reference-validity region within one VIR unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirBorrowRegionId(u32);

/// Dense identity of one borrow-region inclusion constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirBorrowRegionConstraintId(u32);

/// Function-local identity of one canonical loan/reborrow relationship.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirLoanId(u32);

/// Opaque reference to a separately checked function contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirContractId(u32);

/// Dense source-table identifier local to one snapshot or VIR unit. IDs from
/// different tables require an explicit source binding; they are not global.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirSourceId(u32);

/// Dense origin-table identifier within one VIR unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirOriginId(u32);

macro_rules! impl_id {
    ($name:ident) => {
        impl $name {
            #[must_use]
            pub const fn new(raw: u32) -> Self {
                Self(raw)
            }

            #[must_use]
            pub const fn get(self) -> u32 {
                self.0
            }
        }
    };
}

impl_id!(VirFunctionId);
impl_id!(VirBlockId);
impl_id!(VirValueId);
impl_id!(VirRegionId);
impl_id!(VirBorrowRegionId);
impl_id!(VirBorrowRegionConstraintId);
impl_id!(VirLoanId);
impl_id!(VirContractId);
impl_id!(VirSourceId);
impl_id!(VirOriginId);

/// Runtime functions and their closed entry point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeVirProgram {
    /// Explicit profile identity checked against the enclosing unit version.
    pub semantic_profile: VirRuntimeSemanticProfile,
    pub entry: VirFunctionId,
    pub functions: Vec<VirFunction>,
    pub abis: VirAbiEnvironment,
}

/// One raw, versioned verification unit.
///
/// Whole-program consumers deliberately reject this raw container. It must be
/// validated and resolved before verification or execution.
///
/// ```compile_fail
/// fn execute_raw(unit: &nera::VirUnit) {
///     let _ = nera::interpret(unit);
/// }
/// ```
///
/// ```compile_fail
/// fn verify_raw(unit: &nera::VirUnit) {
///     let _ = nera::verify_program(unit, nera::CfgAnalysisConfig::default());
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirUnit {
    pub version: VirUnitVersion,
    pub memory: VirMemorySchema,
    pub borrows: VirBorrowEnvironment,
    pub runtime: RuntimeVirProgram,
    pub specs: VirSpecEnvironment,
    pub source_map: VirSourceMap,
}

impl VirUnit {
    /// Creates the current verification unit around one runtime program.
    ///
    /// A deterministic implicit contract with canonical signature binders is
    /// created for every runtime function. A canonical single-source map is
    /// derived for the hand-authored runtime nodes; production HIR lowering
    /// records its source, generated origins and inferred type clauses
    /// directly. The returned raw unit must still pass [`Self::validate`]
    /// before downstream use.
    #[must_use]
    pub fn from_runtime(
        memory: VirMemorySchema,
        entry: VirFunctionId,
        functions: Vec<VirFunction>,
    ) -> Self {
        let abis = VirAbiEnvironment::identity(&functions);
        let mut runtime = RuntimeVirProgram {
            semantic_profile: VIR_SYSTEM_SEMANTICS_V2,
            entry,
            functions,
            abis,
        };
        let source_map = source_map::hand_authored_source_map(&runtime);
        assign_loan_effect_origins(&mut runtime, &source_map);
        let specs = VirSpecEnvironment::implicit(&runtime);
        Self {
            version: VirUnitVersion::V21,
            memory,
            borrows: VirBorrowEnvironment::empty(),
            runtime,
            specs,
            source_map,
        }
    }

    /// Checks all cross-table, structural, SSA and type invariants.
    pub fn validate(&self) -> Result<(), VirValidationError> {
        validate::validate(self)
    }

    /// Validates and seals this unit for downstream compiler phases.
    pub fn into_validated(self) -> Result<ValidatedVirUnit, VirValidationError> {
        self.validate()?;
        Ok(ValidatedVirUnit(self))
    }

    /// Returns the immutable memory/borrow/runtime portion of this raw unit.
    #[must_use]
    pub fn runtime(&self) -> RuntimeVirView<'_> {
        RuntimeVirView::new(&self.memory, &self.borrows, &self.runtime)
    }

    /// Rebuilds a single-source map after deliberately editing raw runtime VIR.
    ///
    /// This is intended for table producers and malformed-input fixtures. It
    /// does not validate the rebuilt unit or preserve a previous multi-source
    /// origin graph; production HIR lowering supplies its source directly.
    pub fn rebuild_source_map_from_runtime(
        &mut self,
        source_name: impl Into<String>,
        source_len: usize,
    ) {
        self.source_map = VirSourceMap::from_runtime_source(source_name, source_len, &self.runtime);
        assign_loan_effect_origins(&mut self.runtime, &self.source_map);
    }

    /// Replaces the raw spec table with deterministic empty contracts for the
    /// current runtime functions.
    ///
    /// Hand-authored fixture producers may call this after changing function
    /// tables. It deliberately discards every existing clause and therefore is
    /// separate from source-map rebuilding.
    pub fn rebuild_implicit_contracts_from_runtime(&mut self) {
        self.specs = VirSpecEnvironment::implicit(&self.runtime);
    }

    /// Produces the canonical, versioned full-unit text format.
    #[must_use]
    pub fn stable_dump(&self) -> String {
        dump::stable_dump(self)
    }
}

fn assign_loan_effect_origins(runtime: &mut RuntimeVirProgram, source_map: &VirSourceMap) {
    for function in &mut runtime.functions {
        for block in &mut function.blocks {
            for (ordinal, spanned) in block.instructions.iter_mut().enumerate() {
                let location = VirLocation::Instruction {
                    function: function.id,
                    block: block.id,
                    ordinal: ordinal as u64,
                };
                if let Some(origin) = source_map.origin_at(location) {
                    match &mut spanned.instruction {
                        VirInstruction::LoanBegin { effect, .. }
                        | VirInstruction::LoanAliasShared { effect, .. }
                        | VirInstruction::LoanReborrow { effect, .. }
                        | VirInstruction::LoanEnd { effect } => effect.origin = origin.id,
                        VirInstruction::LoanAliasAuthority { effect, .. }
                        | VirInstruction::LoanReborrowAuthority { effect, .. }
                        | VirInstruction::LoanEndAuthority { effect } => effect.origin = origin.id,
                        _ => {}
                    }
                }
            }
        }
    }
}

/// A shared, immutable view of the executable tables in a verification unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeVirView<'unit> {
    pub semantic_profile: VirRuntimeSemanticProfile,
    pub memory: &'unit VirMemorySchema,
    pub borrows: &'unit VirBorrowEnvironment,
    pub entry: VirFunctionId,
    pub functions: &'unit [VirFunction],
    pub abis: &'unit VirAbiEnvironment,
}

impl<'unit> RuntimeVirView<'unit> {
    fn new(
        memory: &'unit VirMemorySchema,
        borrows: &'unit VirBorrowEnvironment,
        runtime: &'unit RuntimeVirProgram,
    ) -> Self {
        Self {
            semantic_profile: runtime.semantic_profile,
            memory,
            borrows,
            entry: runtime.entry,
            functions: runtime.functions.as_slice(),
            abis: &runtime.abis,
        }
    }

    /// Produces a deterministic dump containing only memory and runtime data.
    #[must_use]
    pub fn stable_dump(self) -> String {
        dump::stable_runtime_dump(self)
    }
}

/// Owned VIR unit that has passed all checks for its version.
///
/// The inner unit is only exposed by shared reference, preventing mutation
/// between validation and its use by a backend or verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedVirUnit(VirUnit);

impl ValidatedVirUnit {
    #[must_use]
    pub const fn as_unit(&self) -> &VirUnit {
        &self.0
    }

    #[must_use]
    pub fn runtime(&self) -> RuntimeVirView<'_> {
        self.0.runtime()
    }

    /// Produces the stable dump of the validated unit.
    #[must_use]
    pub fn stable_dump(&self) -> String {
        self.0.stable_dump()
    }

    /// Resolves every call against a unique in-program function.
    pub fn resolve(&self) -> Result<ResolvedVirUnit<'_>, VirResolutionError> {
        resolve::resolve(self)
    }
}

impl AsRef<VirUnit> for ValidatedVirUnit {
    fn as_ref(&self) -> &VirUnit {
        self.as_unit()
    }
}

impl fmt::Display for ValidatedVirUnit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.stable_dump())
    }
}

impl fmt::Display for VirUnit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.stable_dump())
    }
}

/// A VIR function. Function parameters are the entry block parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirFunction {
    pub id: VirFunctionId,
    pub name: String,
    pub signature: VirSignature,
    /// Contract resolved at function entry; instructions cannot inject its facts.
    pub contract: VirContractId,
    pub entry: VirBlockId,
    pub blocks: Vec<VirBasicBlock>,
    pub source_span: ByteSpan,
}

/// Runtime and ghost parameter/result types for a VIR function or call.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirSignature {
    pub parameters: Vec<VirType>,
    pub results: Vec<VirType>,
}

/// Types admitted by the current runtime VIR schema.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirType {
    U64,
    Bool,
    Pointer {
        /// Canonical nominal type/layout of the addressed object.
        access: VirMemoryAccess,
    },
    /// A verifier-only linear resource erased before machine-code emission.
    Permission,
}

/// One typed SSA value declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirValue {
    pub id: VirValueId,
    pub ty: VirType,
}

/// A basic block with explicit parameters and exactly one terminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirBasicBlock {
    pub id: VirBlockId,
    pub parameters: Vec<VirValue>,
    pub instructions: Vec<SpannedVirInstruction>,
    pub terminator: SpannedVirTerminator,
    pub source_span: ByteSpan,
}

/// One instruction and the exact source construct responsible for it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpannedVirInstruction {
    pub instruction: VirInstruction,
    pub source_span: ByteSpan,
}

/// Integer and boolean literals are distinct in typed VIR.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirConstant {
    U64(u64),
    Bool(bool),
}

impl VirConstant {
    #[must_use]
    pub const fn ty(self) -> VirType {
        match self {
            Self::U64(_) => VirType::U64,
            Self::Bool(_) => VirType::Bool,
        }
    }
}

/// Unsigned comparisons used to produce branch/check conditions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirIntegerPredicate {
    Equal,
    NotEqual,
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual,
}

/// An external or separately compiled call and the summary used to check it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirCallTarget {
    pub symbol: String,
    pub signature: VirSignature,
    pub contract: VirContractId,
    /// Canonical logical-to-physical ABI expected by this call site. `None`
    /// is retained only for scalar hand-authored VIR compatibility fixtures.
    pub abi: Option<VirAbiSignature>,
}

/// Runtime VIR instructions. Every memory/resource action has one explicit variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirInstruction {
    /// Compare offsets only after establishing one live instance and compatible
    /// canonical arithmetic domains. Does not access the pointees.
    PointerCompare {
        result: VirValue,
        predicate: VirIntegerPredicate,
        left: VirValueId,
        right: VirValueId,
    },
    /// Nonnegative end - begin in target usize bytes, without unsigned wrap.
    /// Carries the same instance/domain premises as PointerCompare.
    PointerDistance {
        result: VirValue,
        begin: VirValueId,
        end: VirValueId,
    },
    Constant {
        result: VirValue,
        value: VirConstant,
    },
    WordAdd {
        result: VirValue,
        left: VirValueId,
        right: VirValueId,
    },
    Compare {
        result: VirValue,
        predicate: VirIntegerPredicate,
        left: VirValueId,
        right: VirValueId,
    },
    /// Creates heap storage and free authority, not an initialized pointee.
    /// Complete typed resource elements start with empty payload paths. Native
    /// consumers must establish the matching physical empty representation.
    Allocate {
        pointer_result: VirValue,
        permission_result: VirValue,
        size_bytes: VirValueId,
        alignment: u64,
        region: VirRegionId,
        /// Canonical element/object type used to seed nominal pointer facts.
        element: VirMemoryAccess,
    },
    /// Reserves one addressable object in the current function invocation.
    /// Its extent and alignment come exclusively from `access`; the storage
    /// expires on function return and never carries free authority.
    LocalStorage {
        pointer_result: VirValue,
        permission_result: VirValue,
        access: VirMemoryAccess,
    },
    /// Initializes a previously uninitialized cell. Resource analysis and the
    /// executable semantics reject an already initialized destination.
    Initialize {
        pointer: VirValueId,
        value: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Writes a trivially replaceable value regardless of whether the cell was
    /// previously initialized, leaving it initialized afterwards.
    Write {
        pointer: VirValueId,
        value: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    Load {
        result: VirValue,
        pointer: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Reads the canonical active-variant discriminant of one enum object.
    /// Invalid or uninitialized tags are execution faults rather than values.
    EnumDiscriminant {
        result: VirValue,
        pointer: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Updates a previously initialized, trivially replaceable cell. Resource
    /// analysis and the executable semantics reject an uninitialized target.
    Store {
        pointer: VirValueId,
        value: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Moves one `Own<T>` SSA pointer and its linear permission into an
    /// uninitialized canonical pointer leaf. The permission becomes part of
    /// the allocation's typed shadow payload and is consumed as an SSA value.
    ResourceInitialize {
        destination: VirValueId,
        destination_permission: VirValueId,
        value: VirValueId,
        value_permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Moves one stored `Own<T>` payload back into SSA values and leaves the
    /// source move path uninitialized. Pointer identity is recovered only from
    /// the typed payload, never from its physical bits.
    ResourceTake {
        pointer_result: VirValue,
        permission_result: VirValue,
        source: VirValueId,
        source_permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Runs compiler-generated builtin drop glue for one scalar `Own<T>`.
    /// Unlike `Free`, this effect is tied to a lexical cleanup origin and is
    /// emitted only while the lowering drop state says the value is present.
    DropOwn {
        pointer: VirValueId,
        permission: VirValueId,
        condition: VirValueId,
    },
    /// Copies or moves one complete typed object between disjoint addresses.
    ///
    /// The canonical object shape is derived from `access`; producers cannot
    /// substitute an arbitrary byte count. Verifier semantics are enabled;
    /// Interpreter/backend execution supports canonical Copy objects and
    /// initialize-only Move objects whose resource leaves are `Own`/Reference.
    ObjectTransfer {
        destination: VirValueId,
        destination_permission: VirValueId,
        source: VirValueId,
        source_permission: VirValueId,
        access: VirMemoryAccess,
        destination_mode: VirObjectDestinationMode,
        source_mode: VirObjectSourceMode,
    },
    /// Removes the initialized value bytes of one complete typed object.
    ObjectDeinitialize {
        pointer: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Forgets value bytes without reading them. Only variant-free,
    /// pointer-free shapes are admitted; live writable authority and loan
    /// exclusion remain mandatory. Does not allocate or create a value.
    StorageReset {
        pointer: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Begins a new partial-construction epoch in variant-free resource
    /// storage. Requires no payload anywhere in the allocation and uninitialized
    /// resource bytes. Establishes empty resource paths, never a readable T.
    ResourceStorageReset {
        pointer: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
    },
    /// Drops still-present Own payloads and ends stored Reference authority in
    /// the active representation, then removes initialized value state. Moved
    /// resource leaves are skipped. Variant-free drop does not read trivial
    /// siblings; tagged objects retain their tag/non-resource completeness gate.
    ObjectDrop {
        pointer: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
        condition: VirValueId,
    },
    /// Changes the active variant through the canonical enum discriminant.
    EnumSetDiscriminant {
        pointer: VirValueId,
        permission: VirValueId,
        access: VirMemoryAccess,
        variant: VirVariantId,
        mode: VirObjectDestinationMode,
    },
    /// Computes the address of one nominal field. Offset and layouts are
    /// canonical schema facts, not host-ABI calculations.
    FieldAddress {
        result: VirValue,
        base: VirValueId,
        field: VirFieldId,
        owner: VirMemoryAccess,
        field_access: VirMemoryAccess,
        offset_bytes: u64,
    },
    /// Computes the address of one positional tuple element. The element
    /// index and offset are both rechecked against the canonical tuple shape.
    TupleElementAddress {
        result: VirValue,
        base: VirValueId,
        index: u64,
        owner: VirMemoryAccess,
        element_access: VirMemoryAccess,
        offset_bytes: u64,
    },
    /// Addresses one canonical scalar leaf used by aggregate ABI packing.
    ObjectLeafAddress {
        result: VirValue,
        base: VirValueId,
        owner: VirMemoryAccess,
        leaf: VirMemoryAccess,
        offset_bytes: u64,
    },
    /// Computes one array/slice element address while retaining the canonical
    /// stride and the origin of its upper bound.
    IndexAddress {
        result: VirValue,
        base: VirValueId,
        index: VirValueId,
        source: VirMemoryAccess,
        element: VirMemoryAccess,
        stride_bytes: u64,
        bounds: VirIndexBounds,
    },
    /// Computes a checked slice pointer and length without transferring a
    /// permission. A following loan effect supplies the safe view authority.
    SliceAddress {
        pointer_result: VirValue,
        length_result: VirValue,
        base: VirValueId,
        start: VirValueId,
        end: VirValueId,
        source: VirMemoryAccess,
        slice: VirMemoryAccess,
        element: VirMemoryAccess,
        stride_bytes: u64,
        bounds: VirIndexBounds,
    },
    /// Creates one checked half-open slice view. The logical slice is expanded
    /// into an element pointer, a word length and a narrowed permission rather
    /// than becoming an addressable unsized object.
    SliceRange {
        pointer_result: VirValue,
        length_result: VirValue,
        permission_result: VirValue,
        base: VirValueId,
        permission: VirValueId,
        start: VirValueId,
        end: VirValueId,
        source: VirMemoryAccess,
        slice: VirMemoryAccess,
        element: VirMemoryAccess,
        stride_bytes: u64,
        bounds: VirIndexBounds,
    },
    /// Checks sized storage and source authority, without reading bytes,
    /// creating a loan, or transferring permission to the raw result.
    RawAddress {
        result: VirValue,
        base: VirValueId,
        /// Validates formation only; no authority is copied to the result.
        source_permission: VirValueId,
        raw_type: VirMemoryAccess,
    },
    PointerOffset {
        result: VirValue,
        base: VirValueId,
        delta_bytes: VirValueId,
    },
    Free {
        pointer: VirValueId,
        permission: VirValueId,
    },
    PermissionSplit {
        left_result: VirValue,
        right_result: VirValue,
        source: VirValueId,
        split_at_bytes: VirValueId,
    },
    PermissionJoin {
        result: VirValue,
        left: VirValueId,
        right: VirValueId,
    },
    PermissionMove {
        result: VirValue,
        source: VirValueId,
    },
    /// Creates one root shared or mutable loan and its reference authority.
    LoanBegin {
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    },
    /// Creates another authority for an existing shared loan.
    LoanAliasShared {
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    },
    /// Creates one child loan and suspends its parent while the child is live.
    LoanReborrow {
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    },
    /// Consumes one reference authority; the final authority ends the loan.
    LoanEnd {
        effect: VirLoanEffect,
    },
    /// Creates a shared alias using the loan identity carried by a permission.
    LoanAliasAuthority {
        effect: VirLoanAuthorityEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    },
    /// Creates a fresh child; its parent and range come from the source
    /// authority and evaluated selection, not guessed static loan metadata.
    LoanReborrowAuthority {
        loan: VirLoanId,
        region: VirBorrowRegionId,
        effect: VirLoanAuthorityEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    },
    /// Ends the loan authority carried by a permission.
    LoanEndAuthority {
        effect: VirLoanAuthorityEffect,
    },
    Check {
        condition: VirValueId,
    },
    Call {
        results: Vec<VirValue>,
        target: VirCallTarget,
        arguments: Vec<VirValueId>,
    },
}

impl VirInstruction {
    pub(crate) fn visit_results(&self, mut visit: impl FnMut(VirValue)) {
        match self {
            Self::Constant { result, .. }
            | Self::WordAdd { result, .. }
            | Self::Compare { result, .. }
            | Self::PointerCompare { result, .. }
            | Self::PointerDistance { result, .. }
            | Self::Load { result, .. }
            | Self::EnumDiscriminant { result, .. }
            | Self::FieldAddress { result, .. }
            | Self::TupleElementAddress { result, .. }
            | Self::ObjectLeafAddress { result, .. }
            | Self::IndexAddress { result, .. }
            | Self::PointerOffset { result, .. }
            | Self::RawAddress { result, .. }
            | Self::PermissionJoin { result, .. }
            | Self::PermissionMove { result, .. } => visit(*result),
            Self::Allocate {
                pointer_result,
                permission_result,
                ..
            }
            | Self::LocalStorage {
                pointer_result,
                permission_result,
                ..
            } => {
                visit(*pointer_result);
                visit(*permission_result);
            }
            Self::ResourceTake {
                pointer_result,
                permission_result,
                ..
            } => {
                visit(*pointer_result);
                visit(*permission_result);
            }
            Self::SliceRange {
                pointer_result,
                length_result,
                permission_result,
                ..
            } => {
                visit(*pointer_result);
                visit(*length_result);
                visit(*permission_result);
            }
            Self::SliceAddress {
                pointer_result,
                length_result,
                ..
            } => {
                visit(*pointer_result);
                visit(*length_result);
            }
            Self::PermissionSplit {
                left_result,
                right_result,
                ..
            } => {
                visit(*left_result);
                visit(*right_result);
            }
            Self::LoanBegin {
                reference_result,
                permission_result,
                ..
            }
            | Self::LoanAliasShared {
                reference_result,
                permission_result,
                ..
            }
            | Self::LoanReborrow {
                reference_result,
                permission_result,
                ..
            }
            | Self::LoanAliasAuthority {
                reference_result,
                permission_result,
                ..
            }
            | Self::LoanReborrowAuthority {
                reference_result,
                permission_result,
                ..
            } => {
                visit(*reference_result);
                visit(*permission_result);
            }
            Self::Call { results, .. } => results.iter().copied().for_each(visit),
            Self::Initialize { .. }
            | Self::Write { .. }
            | Self::Store { .. }
            | Self::ResourceInitialize { .. }
            | Self::DropOwn { .. }
            | Self::ObjectTransfer { .. }
            | Self::ObjectDeinitialize { .. }
            | Self::StorageReset { .. }
            | Self::ResourceStorageReset { .. }
            | Self::ObjectDrop { .. }
            | Self::EnumSetDiscriminant { .. }
            | Self::Free { .. }
            | Self::LoanEnd { .. }
            | Self::LoanEndAuthority { .. }
            | Self::Check { .. } => {}
        }
    }

    /// Visits every SSA operand without including instruction results.
    /// Producer analyses and validation share this exhaustive definition so
    /// post-CFG effect placement cannot silently miss a new operand shape.
    pub(crate) fn visit_operands(&self, mut visit: impl FnMut(VirValueId)) {
        match self {
            Self::Constant { .. } | Self::LocalStorage { .. } => {}
            Self::WordAdd { left, right, .. }
            | Self::Compare { left, right, .. }
            | Self::PointerCompare { left, right, .. }
            | Self::PointerDistance {
                begin: left,
                end: right,
                ..
            } => {
                visit(*left);
                visit(*right);
            }
            Self::Allocate { size_bytes, .. } => visit(*size_bytes),
            Self::Initialize {
                pointer,
                value,
                permission,
                ..
            }
            | Self::Write {
                pointer,
                value,
                permission,
                ..
            }
            | Self::Store {
                pointer,
                value,
                permission,
                ..
            } => {
                visit(*pointer);
                visit(*value);
                visit(*permission);
            }
            Self::Load {
                pointer,
                permission,
                ..
            }
            | Self::EnumDiscriminant {
                pointer,
                permission,
                ..
            }
            | Self::ObjectDeinitialize {
                pointer,
                permission,
                ..
            }
            | Self::StorageReset {
                pointer,
                permission,
                ..
            }
            | Self::ResourceStorageReset {
                pointer,
                permission,
                ..
            }
            | Self::EnumSetDiscriminant {
                pointer,
                permission,
                ..
            }
            | Self::Free {
                pointer,
                permission,
            } => {
                visit(*pointer);
                visit(*permission);
            }
            Self::ResourceInitialize {
                destination,
                destination_permission,
                value,
                value_permission,
                ..
            } => {
                visit(*destination);
                visit(*destination_permission);
                visit(*value);
                visit(*value_permission);
            }
            Self::ResourceTake {
                source,
                source_permission,
                ..
            } => {
                visit(*source);
                visit(*source_permission);
            }
            Self::DropOwn {
                pointer,
                permission,
                condition,
            }
            | Self::ObjectDrop {
                pointer,
                permission,
                condition,
                ..
            } => {
                visit(*pointer);
                visit(*permission);
                visit(*condition);
            }
            Self::ObjectTransfer {
                destination,
                destination_permission,
                source,
                source_permission,
                ..
            } => {
                visit(*destination);
                visit(*destination_permission);
                visit(*source);
                visit(*source_permission);
            }
            Self::FieldAddress { base, .. }
            | Self::TupleElementAddress { base, .. }
            | Self::ObjectLeafAddress { base, .. } => visit(*base),
            Self::IndexAddress {
                base,
                index,
                bounds,
                ..
            } => {
                visit(*base);
                visit(*index);
                if let VirIndexBounds::Slice { length } = bounds {
                    visit(*length);
                }
            }
            Self::SliceRange {
                base,
                permission,
                start,
                end,
                bounds,
                ..
            } => {
                visit(*base);
                visit(*permission);
                visit(*start);
                visit(*end);
                if let VirIndexBounds::Slice { length } = bounds {
                    visit(*length);
                }
            }
            Self::SliceAddress {
                base,
                start,
                end,
                bounds,
                ..
            } => {
                visit(*base);
                visit(*start);
                visit(*end);
                if let VirIndexBounds::Slice { length } = bounds {
                    visit(*length);
                }
            }
            Self::RawAddress {
                base,
                source_permission,
                ..
            } => {
                visit(*base);
                visit(*source_permission);
            }
            Self::PointerOffset {
                base, delta_bytes, ..
            } => {
                visit(*base);
                visit(*delta_bytes);
            }
            Self::PermissionSplit {
                source,
                split_at_bytes,
                ..
            } => {
                visit(*source);
                visit(*split_at_bytes);
            }
            Self::PermissionJoin { left, right, .. } => {
                visit(*left);
                visit(*right);
            }
            Self::PermissionMove { source, .. } => visit(*source),
            Self::LoanBegin { effect, .. }
            | Self::LoanAliasShared { effect, .. }
            | Self::LoanReborrow { effect, .. }
            | Self::LoanEnd { effect } => {
                visit(effect.source_pointer);
                visit(effect.source_permission);
            }
            Self::LoanAliasAuthority { effect, .. }
            | Self::LoanReborrowAuthority { effect, .. }
            | Self::LoanEndAuthority { effect } => {
                visit(effect.source_pointer);
                visit(effect.source_permission);
            }
            Self::Check { condition } => visit(*condition),
            Self::Call { arguments, .. } => arguments.iter().copied().for_each(visit),
        }
    }
}

/// Required state of an object-transfer destination before the effect.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirObjectDestinationMode {
    Initialize,
    Replace,
}

/// Effect of an object transfer on the source object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirObjectSourceMode {
    Copy,
    Move,
}

/// Canonical origin of an index upper bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirIndexBounds {
    Array { length: u64 },
    Slice { length: VirValueId },
}

/// One CFG successor and the values assigned to its block parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirBlockTarget {
    pub block: VirBlockId,
    pub arguments: Vec<VirValueId>,
}

/// A terminator is mandatory; VIR has no implicit fallthrough or return.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpannedVirTerminator {
    pub terminator: VirTerminator,
    pub source_span: ByteSpan,
}

/// Explicit runtime VIR control flow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirTerminator {
    Jump {
        target: VirBlockTarget,
    },
    Branch {
        /// The verifier derives positive/negative path facts on the two edges.
        condition: VirValueId,
        then_target: VirBlockTarget,
        else_target: VirBlockTarget,
    },
    Return {
        values: Vec<VirValueId>,
    },
}

impl VirTerminator {
    pub(crate) fn visit_operands(&self, mut visit: impl FnMut(VirValueId)) {
        match self {
            Self::Jump { target } => target.arguments.iter().copied().for_each(visit),
            Self::Branch {
                condition,
                then_target,
                else_target,
            } => {
                visit(*condition);
                then_target.arguments.iter().copied().for_each(&mut visit);
                else_target.arguments.iter().copied().for_each(visit);
            }
            Self::Return { values } => values.iter().copied().for_each(visit),
        }
    }
}
