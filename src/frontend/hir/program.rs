//! Table-organized HIR compilation unit and structural table validation.

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use super::body_validation::validate_body;
use super::ids::{
    HirContractId, HirFieldId, HirFunctionId, HirGenericParameterId, HirLayoutId, HirModuleId,
    HirPredicateId, HirRegionConstraintId, HirRegionId, HirSpecBinderId, HirSpecClauseId,
    HirTypeId, HirVariantId,
};
use super::regions::{HirRegion, HirRegionConstraint, HirRegionOrigin, HirRegionOwner};
use super::spec::HirSpecEnvironment;
use super::spec::{
    HirSpecBinderOwner, HirSpecClauseOwner, HirSpecContractPosition, HirSpecLocation,
    HirSpecSnapshot, HirSpecTermKind, HirTrustPolicyKind, HirTrustScope,
};
use super::types::{
    HirCallingConvention, HirFunctionType, HirIntegerType, HirLayout, HirMutability,
    HirTargetDataLayout, HirTypeDefinition, HirTypeKind,
};
use crate::{ByteSpan, DropCapability, SizeCapability, TypeCapabilities, ValueCapability};

/// Version of the in-memory HIR table schema.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirVersion {
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    V9,
    V10,
    /// Guarded alternatives for path-sensitive borrowed results.
    V11,
    /// Bounded fixed-field and slice borrow-result projections.
    V12,
}

impl HirVersion {
    /// Whether this HIR schema carries canonical borrow-region tables.
    #[must_use]
    pub const fn supports_borrow_regions(self) -> bool {
        matches!(
            self,
            Self::V4
                | Self::V5
                | Self::V6
                | Self::V7
                | Self::V8
                | Self::V9
                | Self::V10
                | Self::V11
                | Self::V12
        )
    }

    /// Whether this HIR schema separates storage declaration from values.
    #[must_use]
    pub const fn supports_deferred_locals(self) -> bool {
        matches!(
            self,
            Self::V6 | Self::V7 | Self::V8 | Self::V9 | Self::V10 | Self::V11 | Self::V12
        )
    }

    #[must_use]
    pub const fn supports_deferred_resources(self) -> bool {
        matches!(
            self,
            Self::V7 | Self::V8 | Self::V9 | Self::V10 | Self::V11 | Self::V12
        )
    }
}

/// Deterministic module path within one compilation unit.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HirModulePath {
    segments: Vec<String>,
}

impl HirModulePath {
    #[must_use]
    pub fn root() -> Self {
        Self {
            segments: vec!["crate".to_owned()],
        }
    }

    /// Builds a nonempty path whose segments are all nonempty.
    #[must_use]
    pub fn from_segments(segments: Vec<String>) -> Option<Self> {
        (!segments.is_empty() && segments.iter().all(|segment| !segment.is_empty()))
            .then_some(Self { segments })
    }

    #[must_use]
    pub fn segments(&self) -> &[String] {
        &self.segments
    }
}

/// One declaration referenced by a module without erasing entity kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirDeclaration {
    Function(HirFunctionId),
    Type(HirTypeId),
    Contract(HirContractId),
    Predicate(HirPredicateId),
}

/// Module table entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirModule {
    pub id: HirModuleId,
    pub path: HirModulePath,
    pub declarations: Vec<HirDeclaration>,
    pub span: ByteSpan,
}

/// Source visibility retained before symbol/export lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirVisibility {
    Private,
    Public,
}

/// Function signature using source-type identities rather than copied enums.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirFunctionSignature {
    pub ty: HirTypeId,
    pub parameters: Vec<HirTypeId>,
    pub return_type: HirTypeId,
    pub calling_convention: HirCallingConvention,
    /// Logical coordinates owned by this function; not a proved postcondition.
    pub borrow_result: Option<crate::BorrowResultRelation>,
    /// Guarded alternatives are used only when no unconditional relation
    /// exists. Guards refer to immutable entry parameter snapshots.
    pub borrow_result_alternatives: Vec<crate::BorrowResultAlternative>,
}

/// Structured function body with a single lexical root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirBody {
    /// Parameter locals in source-signature order.
    pub parameters: Vec<super::HirLocalId>,
    pub locals: Vec<super::HirLocal>,
    pub root: super::HirBlock,
}

/// Function table entry. `None` body represents an imported declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirFunction {
    pub id: HirFunctionId,
    pub module: HirModuleId,
    pub name: String,
    pub signature: HirFunctionSignature,
    pub generic_parameters: Vec<HirGenericParameterId>,
    pub body: Option<HirBody>,
    pub contract: HirContractId,
    pub visibility: HirVisibility,
    pub span: ByteSpan,
}

impl HirFunction {
    #[must_use]
    pub const fn body(&self) -> Option<&HirBody> {
        self.body.as_ref()
    }
}

/// Field table entry. The owner is the nominal struct/enum type definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirField {
    pub id: HirFieldId,
    pub owner: HirTypeId,
    pub name: String,
    pub ty: HirTypeId,
    pub span: ByteSpan,
}

/// Enum-variant table entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirVariant {
    pub id: HirVariantId,
    pub owner: HirTypeId,
    pub name: String,
    pub fields: Vec<HirFieldId>,
    pub discriminant: u64,
    pub span: ByteSpan,
}

/// Generic definition parameter retained until instance selection before VIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirGenericParameter {
    pub id: HirGenericParameterId,
    pub name: String,
    pub span: ByteSpan,
}

/// Contract identity attached to a function. Spec clauses arrive in stage 6.4;
/// an implicit empty entry keeps runtime functions and contracts separately ID'd.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirContract {
    pub id: HirContractId,
    pub function: HirFunctionId,
    pub is_implicit: bool,
    pub clauses: Vec<HirSpecClauseId>,
    pub span: ByteSpan,
}

/// Predicate declaration identity reserved for the Spec HIR table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirPredicate {
    pub id: HirPredicateId,
    pub module: HirModuleId,
    pub name: String,
    pub binders: Vec<HirSpecBinderId>,
    /// Predicate bodies remain gated; a present body is rejected in 6.4.5.
    pub body: Option<HirSpecClauseId>,
    pub span: ByteSpan,
}

/// One validated compilation unit organized as deterministic entity tables.
///
/// Construction data must pass [`HirProgram::from_tables`]; the validated
/// tables are not publicly mutable afterwards.
///
/// ```compile_fail
/// fn mutate_validated_hir(program: &mut nera::HirProgram) {
///     program.functions.clear();
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirProgram {
    version: HirVersion,
    data_layout: HirTargetDataLayout,
    entry_module: HirModuleId,
    entry_function: HirFunctionId,
    modules: Vec<HirModule>,
    types: Vec<HirTypeDefinition>,
    type_capabilities: Vec<TypeCapabilities>,
    layouts: Vec<HirLayout>,
    fields: Vec<HirField>,
    variants: Vec<HirVariant>,
    generic_parameters: Vec<HirGenericParameter>,
    regions: Vec<HirRegion>,
    region_constraints: Vec<HirRegionConstraint>,
    functions: Vec<HirFunction>,
    contracts: Vec<HirContract>,
    predicates: Vec<HirPredicate>,
    specs: HirSpecEnvironment,
}

/// Unvalidated deterministic tables consumed atomically by [`HirProgram`].
///
/// Keeping construction data separate from the immutable program prevents a
/// long positional constructor and makes every entity table explicit at API
/// call sites. Stage 6.6 can wrap this same boundary in raw/validated types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirProgramTables {
    pub data_layout: HirTargetDataLayout,
    pub entry_module: HirModuleId,
    pub entry_function: HirFunctionId,
    pub modules: Vec<HirModule>,
    pub types: Vec<HirTypeDefinition>,
    /// Producer-computed canonical capability for each dense type-table slot.
    pub type_capabilities: Vec<TypeCapabilities>,
    pub layouts: Vec<HirLayout>,
    pub fields: Vec<HirField>,
    pub variants: Vec<HirVariant>,
    pub generic_parameters: Vec<HirGenericParameter>,
    /// Canonical program-wide borrow-region table.
    pub regions: Vec<HirRegion>,
    /// Canonical program-wide `subregion <= superregion` constraints.
    pub region_constraints: Vec<HirRegionConstraint>,
    pub functions: Vec<HirFunction>,
    pub contracts: Vec<HirContract>,
    pub predicates: Vec<HirPredicate>,
    pub specs: HirSpecEnvironment,
}

impl HirProgramTables {
    /// Derives the canonical capability table from the complete type graph.
    /// Validation recomputes it and rejects later mutation.
    pub fn assign_canonical_type_capabilities(&mut self) -> Result<(), HirProgramValidationError> {
        self.type_capabilities = (0..self.types.len())
            .map(|index| {
                let raw = u32::try_from(index).map_err(|_| {
                    validation_error("type capability", index, "too many HIR types")
                })?;
                derive_type_capabilities(
                    &self.types,
                    &self.fields,
                    &self.variants,
                    HirTypeId::new(raw),
                )
                .ok_or_else(|| {
                    validation_error(
                        "type capability",
                        index,
                        "capability cannot be derived from the type graph",
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(())
    }

    /// Assigns the one canonical program-wide preorder identity to every HIR
    /// statement, expression, place, and pattern in these unvalidated tables.
    ///
    /// Table producers may use this once after constructing the complete body
    /// forest. [`HirProgram::from_tables`] still validates the result and never
    /// repairs malformed identities implicitly.
    pub fn assign_canonical_node_ids(&mut self) -> Result<(), HirProgramValidationError> {
        let mut next = 0;
        for function in &mut self.functions {
            if let Some(body) = &mut function.body {
                super::node_identity::assign_body_node_ids(body, &mut next, function.span)
                    .map_err(|_| validation_error("node", next as usize, "too many HIR nodes"))?;
            }
        }
        Ok(())
    }
}

impl HirProgram {
    /// Instantiates a signature reference with the caller's region, while
    /// preserving the exact pointee and access kind.
    pub(crate) fn reference_compatible(&self, actual: HirTypeId, expected: HirTypeId) -> bool {
        actual == expected
            || matches!((self.type_kind(actual), self.type_kind(expected)),
            (Some(HirTypeKind::Reference { pointee: a, mutability: am, .. }), Some(HirTypeKind::Reference { pointee: b, mutability: bm, .. })) if a == b && am == bm)
    }

    pub(crate) fn call_result_type(&self, call: &super::HirCall) -> Option<HirTypeId> {
        let signature = &self.function_by_id(call.callee)?.signature;
        if !matches!(
            self.type_kind(signature.return_type),
            Some(HirTypeKind::Reference { .. })
        ) {
            return Some(signature.return_type);
        }
        let Some(relation) = signature.borrow_result else {
            return (!signature.borrow_result_alternatives.is_empty())
                .then_some(call.instantiated_signature.return_type);
        };
        if relation.projection != crate::BorrowProjection::Whole {
            return Some(call.instantiated_signature.return_type);
        }
        let index = relation.parameter as usize;
        let ty = signature.parameters.get(index)?;
        let argument = call.arguments.get(index)?;
        self.reference_compatible(argument.ty, *ty)
            .then_some(argument.ty)
    }

    pub(crate) fn call_result_type_compatible(
        &self,
        call: &super::HirCall,
        actual: HirTypeId,
    ) -> bool {
        if self.call_result_type(call) == Some(actual) {
            return true;
        }
        let signature = &call.instantiated_signature;
        if let Some(relation) = signature.borrow_result
            && relation.projection != crate::BorrowProjection::Whole
            && self.reference_compatible(actual, signature.return_type)
        {
            let (Some(HirTypeKind::Reference { region: result, .. }), Some(source)) = (
                self.type_kind(actual),
                call.arguments
                    .get(relation.parameter as usize)
                    .and_then(|argument| match self.type_kind(argument.ty) {
                        Some(HirTypeKind::Reference { region, .. }) => Some(*region),
                        _ => None,
                    }),
            ) else {
                return false;
            };
            return self
                .region(*result)
                .is_some_and(|region| match region.owner {
                    HirRegionOwner::Function(owner) => {
                        self.region_is_subregion(owner, *result, source)
                    }
                    HirRegionOwner::Type(_) => false,
                });
        }
        if signature.borrow_result_alternatives.is_empty()
            || !self.reference_compatible(actual, signature.return_type)
        {
            return false;
        }
        let Some(HirTypeKind::Reference { region: result, .. }) = self.type_kind(actual) else {
            return false;
        };
        signature
            .borrow_result_alternatives
            .iter()
            .all(|alternative| {
                call.arguments
                    .get(alternative.relation.parameter as usize)
                    .and_then(|argument| match self.type_kind(argument.ty) {
                        Some(HirTypeKind::Reference { region, .. }) => Some(*region),
                        _ => None,
                    })
                    .is_some_and(|source| {
                        self.region(*result)
                            .is_some_and(|region| match region.owner {
                                HirRegionOwner::Function(owner) => {
                                    self.region_is_subregion(owner, *result, source)
                                }
                                HirRegionOwner::Type(_) => false,
                            })
                    })
            })
    }
    /// Constructs a program from deterministic tables and rejects every
    /// structurally inconsistent reference before returning it.
    pub fn from_tables(tables: HirProgramTables) -> Result<Self, HirProgramValidationError> {
        let program = Self {
            version: HirVersion::V12,
            data_layout: tables.data_layout,
            entry_module: tables.entry_module,
            entry_function: tables.entry_function,
            modules: tables.modules,
            types: tables.types,
            type_capabilities: tables.type_capabilities,
            layouts: tables.layouts,
            fields: tables.fields,
            variants: tables.variants,
            generic_parameters: tables.generic_parameters,
            regions: tables.regions,
            region_constraints: tables.region_constraints,
            functions: tables.functions,
            contracts: tables.contracts,
            predicates: tables.predicates,
            specs: tables.specs,
        };
        program.validate_tables()?;
        Ok(program)
    }

    #[must_use]
    pub const fn version(&self) -> HirVersion {
        self.version
    }

    #[must_use]
    pub const fn data_layout(&self) -> HirTargetDataLayout {
        self.data_layout
    }

    #[must_use]
    pub const fn entry_module_id(&self) -> HirModuleId {
        self.entry_module
    }

    #[must_use]
    pub const fn entry_function_id(&self) -> HirFunctionId {
        self.entry_function
    }

    /// Entry module selected by this compilation unit.
    #[must_use]
    pub fn entry_module(&self) -> &HirModule {
        self.module(self.entry_module)
            .expect("validated HIR entry module remains present")
    }

    /// Entry function selected by this compilation unit.
    #[must_use]
    pub fn entry_function(&self) -> &HirFunction {
        self.function_by_id(self.entry_function)
            .expect("validated HIR entry function remains present")
    }

    #[must_use]
    pub fn modules(&self) -> &[HirModule] {
        &self.modules
    }

    #[must_use]
    pub fn types(&self) -> &[HirTypeDefinition] {
        &self.types
    }

    /// Returns the validated canonical capability for one source type.
    #[must_use]
    pub fn type_capabilities(&self, id: HirTypeId) -> Option<TypeCapabilities> {
        self.type_definition(id)
            .and_then(|_| self.type_capabilities.get(id.index()).copied())
    }

    #[must_use]
    pub fn type_capability_table(&self) -> &[TypeCapabilities] {
        &self.type_capabilities
    }

    #[must_use]
    pub fn layouts(&self) -> &[HirLayout] {
        &self.layouts
    }

    #[must_use]
    pub fn fields(&self) -> &[HirField] {
        &self.fields
    }

    #[must_use]
    pub fn variants(&self) -> &[HirVariant] {
        &self.variants
    }

    #[must_use]
    pub fn generic_parameters(&self) -> &[HirGenericParameter] {
        &self.generic_parameters
    }

    #[must_use]
    pub fn regions(&self) -> &[HirRegion] {
        &self.regions
    }

    #[must_use]
    pub fn region_constraints(&self) -> &[HirRegionConstraint] {
        &self.region_constraints
    }

    #[must_use]
    pub fn functions(&self) -> &[HirFunction] {
        &self.functions
    }

    #[must_use]
    pub fn contracts(&self) -> &[HirContract] {
        &self.contracts
    }

    #[must_use]
    pub fn predicates(&self) -> &[HirPredicate] {
        &self.predicates
    }

    #[must_use]
    pub const fn specs(&self) -> &HirSpecEnvironment {
        &self.specs
    }

    #[must_use]
    pub fn module(&self, id: HirModuleId) -> Option<&HirModule> {
        self.modules.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn function_by_id(&self, id: HirFunctionId) -> Option<&HirFunction> {
        self.functions.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn type_definition(&self, id: HirTypeId) -> Option<&HirTypeDefinition> {
        self.types.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn type_kind(&self, id: HirTypeId) -> Option<&HirTypeKind> {
        self.type_definition(id).map(|definition| &definition.kind)
    }

    #[must_use]
    pub fn layout(&self, id: HirLayoutId) -> Option<&HirLayout> {
        self.layouts.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn field(&self, id: HirFieldId) -> Option<&HirField> {
        self.fields.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn variant(&self, id: HirVariantId) -> Option<&HirVariant> {
        self.variants.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn generic_parameter(&self, id: HirGenericParameterId) -> Option<&HirGenericParameter> {
        self.generic_parameters
            .get(id.index())
            .filter(|item| item.id == id)
    }

    #[must_use]
    pub fn region(&self, id: HirRegionId) -> Option<&HirRegion> {
        self.regions.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn region_constraint(&self, id: HirRegionConstraintId) -> Option<&HirRegionConstraint> {
        self.region_constraints
            .get(id.index())
            .filter(|item| item.id == id)
    }

    #[must_use]
    pub fn contract(&self, id: HirContractId) -> Option<&HirContract> {
        self.contracts.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn predicate(&self, id: HirPredicateId) -> Option<&HirPredicate> {
        self.predicates.get(id.index()).filter(|item| item.id == id)
    }

    #[must_use]
    pub fn layout_of(&self, ty: HirTypeId) -> Option<&HirLayout> {
        let layout = self.type_definition(ty)?.layout?;
        self.layout(layout)
    }

    pub fn validate_tables(&self) -> Result<(), HirProgramValidationError> {
        let mut next_node = 0;
        validate_dense("module", &self.modules, |item| item.id.get())?;
        validate_dense("type", &self.types, |item| item.id.get())?;
        validate_dense("layout", &self.layouts, |item| item.id.get())?;
        validate_dense("field", &self.fields, |item| item.id.get())?;
        validate_dense("variant", &self.variants, |item| item.id.get())?;
        validate_dense("generic parameter", &self.generic_parameters, |item| {
            item.id.get()
        })?;
        validate_dense("region", &self.regions, |item| item.id.get())?;
        validate_dense("region constraint", &self.region_constraints, |item| {
            item.id.get()
        })?;
        validate_dense("function", &self.functions, |item| item.id.get())?;
        validate_dense("contract", &self.contracts, |item| item.id.get())?;
        validate_dense("predicate", &self.predicates, |item| item.id.get())?;

        require(
            self.module(self.entry_module).is_some(),
            "program",
            0,
            "missing entry module",
        )?;
        require(
            self.function_by_id(self.entry_function).is_some(),
            "program",
            0,
            "missing entry function",
        )?;
        require(
            self.data_layout.pointer_size_bytes > 0
                && self.data_layout.pointer_alignment.is_power_of_two()
                && self
                    .data_layout
                    .pointer_size_bytes
                    .is_multiple_of(self.data_layout.pointer_alignment)
                && self.data_layout.usize_size_bytes > 0
                && self.data_layout.usize_alignment.is_power_of_two()
                && self
                    .data_layout
                    .usize_size_bytes
                    .is_multiple_of(self.data_layout.usize_alignment),
            "data layout",
            0,
            "invalid pointer or usize size/alignment",
        )?;
        require(
            self.entry_function().module == self.entry_module,
            "program",
            0,
            "entry function is outside the entry module",
        )?;

        let mut module_paths = BTreeSet::new();
        for module in &self.modules {
            require(
                !module.path.segments().is_empty()
                    && module
                        .path
                        .segments()
                        .iter()
                        .all(|segment| !segment.is_empty()),
                "module",
                module.id.index(),
                "empty module path",
            )?;
            require(
                module_paths.insert(&module.path),
                "module",
                module.id.index(),
                "duplicate module path",
            )?;
            let mut declarations = BTreeSet::new();
            for declaration in &module.declarations {
                require(
                    declarations.insert(*declaration),
                    "module",
                    module.id.index(),
                    "duplicate declaration",
                )?;
                let present_and_owned = match declaration {
                    HirDeclaration::Function(id) => self
                        .function_by_id(*id)
                        .is_some_and(|function| function.module == module.id),
                    HirDeclaration::Type(id) => self.type_definition(*id).is_some(),
                    HirDeclaration::Contract(id) => self.contract(*id).is_some_and(|contract| {
                        self.function_by_id(contract.function)
                            .is_some_and(|function| function.module == module.id)
                    }),
                    HirDeclaration::Predicate(id) => self
                        .predicate(*id)
                        .is_some_and(|predicate| predicate.module == module.id),
                };
                require(
                    present_and_owned,
                    "module",
                    module.id.index(),
                    "dangling or foreign declaration",
                )?;
            }
        }

        for definition in &self.types {
            require(
                definition.name.as_ref().is_none_or(|name| !name.is_empty()),
                "type",
                definition.id.index(),
                "empty type name",
            )?;
            if let Some(layout) = definition.layout {
                require(
                    self.layout(layout)
                        .is_some_and(|layout| layout.ty == definition.id),
                    "type",
                    definition.id.index(),
                    "layout does not describe this type",
                )?;
            }
            require(
                all_unique(definition.generic_parameters.iter().copied()),
                "type",
                definition.id.index(),
                "duplicate generic parameter",
            )?;
            for parameter in &definition.generic_parameters {
                require(
                    self.generic_parameter(*parameter).is_some(),
                    "type",
                    definition.id.index(),
                    "missing generic parameter",
                )?;
            }
            self.validate_type_kind(definition.id, &definition.kind)?;
        }

        for layout in &self.layouts {
            require(
                self.type_definition(layout.ty)
                    .is_some_and(|ty| ty.layout == Some(layout.id)),
                "layout",
                layout.id.index(),
                "source type does not select this layout",
            )?;
            require(
                layout.alignment.is_power_of_two(),
                "layout",
                layout.id.index(),
                "alignment is not a nonzero power of two",
            )?;
            require(
                layout.size_bytes % layout.alignment == 0,
                "layout",
                layout.id.index(),
                "size is not a multiple of alignment",
            )?;
            require(
                all_unique(layout.fields.iter().map(|field| field.field)),
                "layout",
                layout.id.index(),
                "duplicate field layout",
            )?;
            let aggregate_shape_matches = match self.type_kind(layout.ty) {
                Some(HirTypeKind::Struct { fields }) => {
                    layout.fields.len() == fields.len()
                        && fields
                            .iter()
                            .all(|field| layout.fields.iter().any(|layout| layout.field == *field))
                }
                Some(HirTypeKind::Enum { .. }) => layout.fields.is_empty(),
                _ => layout.fields.is_empty(),
            };
            require(
                aggregate_shape_matches,
                "layout",
                layout.id.index(),
                "field layouts do not match the source type",
            )?;
            let mut field_ranges = Vec::with_capacity(layout.fields.len());
            for field in &layout.fields {
                let field_definition = self.field(field.field);
                require(
                    field_definition.is_some_and(|field| field.owner == layout.ty),
                    "layout",
                    layout.id.index(),
                    "missing or foreign field layout target",
                )?;
                let field_range = field_definition
                    .and_then(|field| self.layout_of(field.ty))
                    .and_then(|field_layout| {
                        if layout.alignment >= field_layout.alignment
                            && field.offset_bytes % field_layout.alignment == 0
                        {
                            field
                                .offset_bytes
                                .checked_add(field_layout.size_bytes)
                                .map(|end| (field.offset_bytes, end))
                        } else {
                            None
                        }
                    });
                require(
                    field_range.is_some_and(|(_, end)| end <= layout.size_bytes),
                    "layout",
                    layout.id.index(),
                    "field layout exceeds aggregate size or is unresolved",
                )?;
                if let Some(range @ (start, end)) = field_range
                    && start < end
                {
                    field_ranges.push(range);
                }
            }
            require(
                ranges_are_disjoint(&mut field_ranges),
                "layout",
                layout.id.index(),
                "aggregate field layouts overlap",
            )?;
            self.validate_variant_layout(layout)?;
        }

        for field in &self.fields {
            let owner_contains_field = match self.type_kind(field.owner) {
                Some(HirTypeKind::Struct { fields }) => {
                    fields
                        .iter()
                        .filter(|candidate| **candidate == field.id)
                        .count()
                        == 1
                }
                Some(HirTypeKind::Enum { variants }) => {
                    variants
                        .iter()
                        .filter_map(|variant| self.variant(*variant))
                        .flat_map(|variant| &variant.fields)
                        .filter(|candidate| **candidate == field.id)
                        .count()
                        == 1
                }
                _ => false,
            };
            require(
                !field.name.is_empty()
                    && self.type_definition(field.owner).is_some()
                    && self.type_definition(field.ty).is_some()
                    && owner_contains_field,
                "field",
                field.id.index(),
                "empty name, missing type, or field is not owned exactly once",
            )?;
        }
        for variant in &self.variants {
            let owner_contains_variant = matches!(
                self.type_kind(variant.owner),
                Some(HirTypeKind::Enum { variants }) if variants.contains(&variant.id)
            );
            require(
                !variant.name.is_empty()
                    && owner_contains_variant
                    && all_unique(variant.fields.iter().copied())
                    && variant.fields.iter().all(|field| {
                        self.field(*field)
                            .is_some_and(|field| field.owner == variant.owner)
                    }),
                "variant",
                variant.id.index(),
                "empty name, missing owner, duplicate field, or foreign variant field",
            )?;
        }

        require(
            self.type_capabilities.len() == self.types.len(),
            "type capability",
            self.type_capabilities.len(),
            "capability table length does not match the type table",
        )?;
        for definition in &self.types {
            let expected =
                derive_type_capabilities(&self.types, &self.fields, &self.variants, definition.id);
            require(
                expected == self.type_capabilities.get(definition.id.index()).copied(),
                "type capability",
                definition.id.index(),
                "stored capability does not match the canonical type graph",
            )?;
        }

        for parameter in &self.generic_parameters {
            require(
                !parameter.name.is_empty(),
                "generic parameter",
                parameter.id.index(),
                "empty generic parameter name",
            )?;
        }

        self.validate_region_declarations()?;
        self.validate_region_constraints()?;

        let mut function_names = BTreeSet::new();
        for function in &self.functions {
            require(
                !function.name.is_empty()
                    && function_names.insert((function.module, function.name.as_str()))
                    && self.module(function.module).is_some_and(|module| {
                        module
                            .declarations
                            .contains(&HirDeclaration::Function(function.id))
                            && module
                                .declarations
                                .contains(&HirDeclaration::Contract(function.contract))
                    }),
                "function",
                function.id.index(),
                "empty/duplicate name, or function/contract is not declared by its module",
            )?;
            require(
                self.contracts.get(function.contract.index()).is_some(),
                "function",
                function.id.index(),
                "missing contract",
            )?;
            require(
                all_unique(function.generic_parameters.iter().copied())
                    && function
                        .generic_parameters
                        .iter()
                        .all(|parameter| self.generic_parameter(*parameter).is_some()),
                "function",
                function.id.index(),
                "missing or duplicate generic parameter",
            )?;
            let expected = HirTypeKind::Function(HirFunctionType {
                parameters: function.signature.parameters.clone(),
                return_type: function.signature.return_type,
                calling_convention: function.signature.calling_convention,
            });
            require(
                self.type_kind(function.signature.ty) == Some(&expected),
                "function",
                function.id.index(),
                "signature type does not match signature slots",
            )?;
            require(
                function
                    .signature
                    .parameters
                    .iter()
                    .chain([&function.signature.return_type])
                    .all(|ty| self.type_definition(*ty).is_some()),
                "function",
                function.id.index(),
                "missing signature type",
            )?;
            self.validate_function_regions(function)?;
            self.validate_borrow_result(function)?;
            if let Some(body) = &function.body {
                if let Err((_expected, found)) =
                    super::node_identity::validate_body_node_ids(body, &mut next_node)
                {
                    return Err(validation_error(
                        "node",
                        found.index(),
                        "HIR node ID is not the canonical program-wide preorder index",
                    ));
                }
                validate_dense("local", &body.locals, |local| local.id.get())?;
                for local in &body.locals {
                    require(
                        !local.name.is_empty()
                            && self.type_definition(local.ty).is_some()
                            && self.layout(local.layout).is_some_and(|layout| {
                                layout.ty == local.ty
                                    && self.type_definition(local.ty).and_then(|ty| ty.layout)
                                        == Some(local.layout)
                            }),
                        "local",
                        local.id.index(),
                        "empty local name or local type/layout mismatch",
                    )?;
                }
                validate_body(self, function, body)?;
            }
        }

        for contract in &self.contracts {
            require(
                self.function_by_id(contract.function)
                    .is_some_and(|function| function.contract == contract.id),
                "contract",
                contract.id.index(),
                "contract/function mismatch",
            )?;
            require(
                all_unique(contract.clauses.iter().copied())
                    && contract.clauses.windows(2).all(|pair| pair[0] < pair[1])
                    && contract.clauses.iter().all(|clause| {
                        self.specs
                            .clauses
                            .get(clause.index())
                            .is_some_and(|clause| {
                                matches!(
                                    clause.owner,
                                    HirSpecClauseOwner::Contract { contract: owner, .. }
                                        if owner == contract.id
                                )
                            })
                    }),
                "contract",
                contract.id.index(),
                "contract clauses are duplicate, unordered, missing, or foreign",
            )?;
        }
        for predicate in &self.predicates {
            require(
                !predicate.name.is_empty()
                    && self.module(predicate.module).is_some_and(|module| {
                        module
                            .declarations
                            .contains(&HirDeclaration::Predicate(predicate.id))
                    })
                    && predicate.body.is_none()
                    && all_unique(predicate.binders.iter().copied())
                    && predicate.binders.iter().all(|binder| {
                        self.specs
                            .binders
                            .get(binder.index())
                            .is_some_and(|binder| {
                                binder.owner == HirSpecBinderOwner::Predicate(predicate.id)
                            })
                    }),
                "predicate",
                predicate.id.index(),
                "invalid declaration, binder ownership, or gated predicate body",
            )?;
        }
        self.validate_specs()?;
        Ok(())
    }

    fn validate_region_declarations(&self) -> Result<(), HirProgramValidationError> {
        for region in &self.regions {
            let valid = match region.owner {
                HirRegionOwner::Function(owner) => {
                    self.function_by_id(owner).is_some_and(|function| {
                        span_contains(function.span, region.span)
                            && match region.origin {
                                HirRegionOrigin::Parameter { index } => usize::try_from(index)
                                    .ok()
                                    .and_then(|index| function.signature.parameters.get(index))
                                    .and_then(|ty| self.type_borrow_regions(*ty))
                                    .is_some_and(|regions| regions.contains(&region.id)),
                                HirRegionOrigin::Result => self
                                    .type_borrow_regions(function.signature.return_type)
                                    .is_some_and(|regions| regions.contains(&region.id)),
                                HirRegionOrigin::LexicalScope { .. }
                                | HirRegionOrigin::Inferred { .. } => function.body.is_some(),
                                HirRegionOrigin::AggregateErased => false,
                            }
                    })
                }
                HirRegionOwner::Type(owner) => {
                    matches!(region.origin, HirRegionOrigin::AggregateErased)
                        && self
                            .type_borrow_regions(owner)
                            .is_some_and(|regions| regions.contains(&region.id))
                        && self.fields.iter().any(|field| {
                            field.owner == owner
                                && span_contains(field.span, region.span)
                                && self
                                    .type_borrow_regions(field.ty)
                                    .is_some_and(|regions| regions.contains(&region.id))
                        })
                }
            };
            require(
                valid,
                "region",
                region.id.index(),
                "missing owner, foreign span, or origin is not anchored by its owner",
            )?;
        }
        Ok(())
    }

    fn validate_function_regions(
        &self,
        function: &HirFunction,
    ) -> Result<(), HirProgramValidationError> {
        for parameter in &function.signature.parameters {
            let regions = self.type_borrow_regions(*parameter).ok_or_else(|| {
                validation_error(
                    "function",
                    function.id.index(),
                    "parameter borrow regions cannot be resolved",
                )
            })?;
            require(
                regions.iter().all(|region| {
                    self.region(*region).is_some_and(|region| {
                        region.owner == HirRegionOwner::Function(function.id)
                            && matches!(region.origin, HirRegionOrigin::Parameter { .. })
                    })
                }),
                "function",
                function.id.index(),
                "parameter type contains a non-parameter or foreign borrow region",
            )?;
        }

        let result_regions = self
            .type_borrow_regions(function.signature.return_type)
            .ok_or_else(|| {
                validation_error(
                    "function",
                    function.id.index(),
                    "result borrow regions cannot be resolved",
                )
            })?;
        require(
            result_regions.iter().all(|region| {
                self.region(*region).is_some_and(|region| {
                    region.owner == HirRegionOwner::Function(function.id)
                        && matches!(
                            region.origin,
                            HirRegionOrigin::Parameter { .. } | HirRegionOrigin::Result
                        )
                })
            }),
            "function",
            function.id.index(),
            "result type contains a lexical or foreign borrow region",
        )
    }

    fn validate_borrow_result(
        &self,
        function: &HirFunction,
    ) -> Result<(), HirProgramValidationError> {
        let signature = &function.signature;
        let valid = match (
            self.type_kind(signature.return_type),
            signature.borrow_result,
        ) {
            (Some(HirTypeKind::Reference { mutability, .. }), Some(relation)) => {
                let access = if *mutability == HirMutability::Mutable {
                    crate::BorrowAccess::Mutable
                } else {
                    crate::BorrowAccess::Shared
                };
                let source_matches = signature
                    .parameters
                    .get(relation.parameter as usize)
                    .is_some_and(|parameter| {
                        let (
                            Some(HirTypeKind::Reference {
                                pointee: input,
                                mutability: input_mutability,
                                region: input_region,
                            }),
                            Some(HirTypeKind::Reference {
                                pointee: result,
                                mutability: result_mutability,
                                region: result_region,
                            }),
                        ) = (self.type_kind(*parameter), self.type_kind(signature.return_type))
                        else {
                            return false;
                        };
                        if input_mutability != result_mutability
                            || !self.region_is_subregion(
                                function.id,
                                *result_region,
                                *input_region,
                            )
                        {
                            return false;
                        }
                        match relation.projection {
                            crate::BorrowProjection::Whole => {
                                input == result
                                    && (*parameter == signature.return_type
                                        || function.body.is_none())
                            }
                            crate::BorrowProjection::Fixed {
                                offset_bytes,
                                size_bytes,
                                alignment,
                            } => {
                                let Some(input_layout) = self.layout_of(*input) else {
                                    return false;
                                };
                                let Some(result_layout) = self.layout_of(*result) else {
                                    return false;
                                };
                                self.type_capabilities(*result)
                                    .is_some_and(crate::TypeCapabilities::pointer_free_trivial)
                                    && size_bytes == result_layout.size_bytes
                                    && alignment == result_layout.alignment
                                    && offset_bytes
                                        .checked_add(size_bytes)
                                        .is_some_and(|end| end <= input_layout.size_bytes)
                                    && offset_bytes % alignment == 0
                            }
                            crate::BorrowProjection::Slice {
                                start,
                                end,
                                stride_bytes,
                                alignment,
                            } => {
                                let (
                                    Some(HirTypeKind::Slice { element: a, .. }),
                                    Some(HirTypeKind::Slice { element: b, .. }),
                                ) = (self.type_kind(*input), self.type_kind(*result))
                                else {
                                    return false;
                                };
                                let Some(layout) = self.layout_of(*a) else {
                                    return false;
                                };
                                a == b
                                    && self.type_capabilities(*a).is_some_and(
                                        crate::TypeCapabilities::pointer_free_trivial,
                                    )
                                    && stride_bytes == layout.size_bytes
                                    && alignment == layout.alignment
                                    && self.borrow_slice_bound_valid(signature, relation.parameter, start)
                                    && self.borrow_slice_bound_valid(signature, relation.parameter, end)
                                    && !matches!((start, end), (crate::BorrowSliceBound::Constant(a), crate::BorrowSliceBound::Constant(b)) if a > b)
                            }
                        }
                    });
                relation.result == 0
                    && relation.access == access
                    && source_matches
                    && signature.borrow_result_alternatives.is_empty()
            }
            (
                Some(HirTypeKind::Reference {
                    mutability, region, ..
                }),
                None,
            ) => {
                let access = if *mutability == HirMutability::Mutable {
                    crate::BorrowAccess::Mutable
                } else {
                    crate::BorrowAccess::Shared
                };
                let alternatives = &signature.borrow_result_alternatives;
                !alternatives.is_empty()
                    && self.region(*region).is_some_and(|region| {
                        region.owner == HirRegionOwner::Function(function.id)
                            && region.origin == HirRegionOrigin::Result
                    })
                    && alternatives.iter().all(|alternative| {
                        let relation = alternative.relation;
                        !alternative.guard.is_empty()
                            && relation.result == 0
                            && relation.projection == crate::BorrowProjection::Whole
                            && relation.access == access
                            && signature.parameters.get(relation.parameter as usize).is_some_and(
                                |parameter| {
                                    self.reference_compatible(*parameter, signature.return_type)
                                        && self.type_kind(*parameter).is_some_and(|kind| {
                                            matches!(kind, HirTypeKind::Reference { region: source, .. }
                                                if self.region_is_subregion(function.id, *region, *source))
                                        })
                                },
                            )
                            && alternative.guard.iter().all(|atom| match atom {
                                crate::BorrowGuardAtom::Boolean { parameter, .. } => signature
                                    .parameters
                                    .get(*parameter as usize)
                                    .is_some_and(|ty| {
                                        self.type_kind(*ty) == Some(&HirTypeKind::Bool)
                                    }),
                            })
                    })
            }
            (_, relation) => relation.is_none() && signature.borrow_result_alternatives.is_empty(),
        };
        require(
            valid,
            "function",
            function.id.index(),
            "invalid logical borrow result relation",
        )
    }

    fn borrow_slice_bound_valid(
        &self,
        signature: &HirFunctionSignature,
        source: u32,
        bound: crate::BorrowSliceBound,
    ) -> bool {
        match bound {
            crate::BorrowSliceBound::Constant(_) => true,
            crate::BorrowSliceBound::Parameter(parameter) => signature
                .parameters
                .get(parameter as usize)
                .is_some_and(|ty| {
                    self.type_kind(*ty)
                        == Some(&HirTypeKind::Integer(HirIntegerType::Usize))
                }),
            crate::BorrowSliceBound::SourceLength => signature
                .parameters
                .get(source as usize)
                .is_some_and(|ty| {
                    matches!(self.type_kind(*ty), Some(HirTypeKind::Reference { pointee, .. }) if matches!(self.type_kind(*pointee), Some(HirTypeKind::Slice { .. })))
                }),
        }
    }

    pub(super) fn region_is_subregion(
        &self,
        owner: HirFunctionId,
        subregion: HirRegionId,
        superregion: HirRegionId,
    ) -> bool {
        let mut pending = vec![subregion];
        let mut visited = BTreeSet::new();
        while let Some(region) = pending.pop() {
            if region == superregion {
                return true;
            }
            if visited.insert(region) {
                pending.extend(
                    self.region_constraints
                        .iter()
                        .filter(|c| c.owner == owner && c.subregion == region)
                        .map(|c| c.superregion),
                );
            }
        }
        false
    }

    fn validate_region_constraints(&self) -> Result<(), HirProgramValidationError> {
        let mut relations = BTreeSet::new();
        for constraint in &self.region_constraints {
            let function = self.function_by_id(constraint.owner);
            let subregion = self.region(constraint.subregion);
            let superregion = self.region(constraint.superregion);
            require(
                constraint.subregion != constraint.superregion
                    && function
                        .is_some_and(|function| span_contains(function.span, constraint.span))
                    && subregion.is_some_and(|region| {
                        region.owner == HirRegionOwner::Function(constraint.owner)
                    })
                    && superregion.is_some_and(|region| {
                        region.owner == HirRegionOwner::Function(constraint.owner)
                    })
                    && relations.insert((
                        constraint.owner,
                        constraint.subregion,
                        constraint.superregion,
                    )),
                "region constraint",
                constraint.id.index(),
                "constraint is reflexive, duplicate, dangling, foreign, or outside its function",
            )?;
        }
        Ok(())
    }

    pub(super) fn type_borrow_regions(&self, root: HirTypeId) -> Option<BTreeSet<HirRegionId>> {
        fn visit(
            program: &HirProgram,
            ty: HirTypeId,
            regions: &mut BTreeSet<HirRegionId>,
            visiting: &mut BTreeSet<HirTypeId>,
            depth: usize,
        ) -> Option<()> {
            if depth >= crate::TYPE_CAPABILITY_MAX_DEPTH || !visiting.insert(ty) {
                return None;
            }
            match program.type_kind(ty)? {
                HirTypeKind::Reference { region, .. } => {
                    program.region(*region)?;
                    regions.insert(*region);
                }
                HirTypeKind::Array { element, .. } => {
                    visit(program, *element, regions, visiting, depth + 1)?;
                }
                HirTypeKind::Tuple(elements) => {
                    for element in elements {
                        visit(program, *element, regions, visiting, depth + 1)?;
                    }
                }
                HirTypeKind::Struct { fields } => {
                    for field in fields {
                        let field = program.field(*field)?;
                        visit(program, field.ty, regions, visiting, depth + 1)?;
                    }
                }
                HirTypeKind::Enum { variants } => {
                    for variant in variants {
                        for field in &program.variant(*variant)?.fields {
                            let field = program.field(*field)?;
                            visit(program, field.ty, regions, visiting, depth + 1)?;
                        }
                    }
                }
                HirTypeKind::Function(function) => {
                    for parameter in &function.parameters {
                        visit(program, *parameter, regions, visiting, depth + 1)?;
                    }
                    visit(program, function.return_type, regions, visiting, depth + 1)?;
                }
                HirTypeKind::Unit
                | HirTypeKind::Bool
                | HirTypeKind::Integer(_)
                | HirTypeKind::Own { .. }
                | HirTypeKind::RawPointer { .. }
                | HirTypeKind::Slice { .. }
                | HirTypeKind::GenericParameter(_)
                | HirTypeKind::Never => {}
            }
            visiting.remove(&ty);
            Some(())
        }

        let mut regions = BTreeSet::new();
        visit(self, root, &mut regions, &mut BTreeSet::new(), 0)?;
        Some(regions)
    }

    /// Compares runtime value types while treating aggregate-declaration
    /// reference regions as binders rather than concrete loan identities.
    pub(crate) fn types_compatible(&self, actual: HirTypeId, expected: HirTypeId) -> bool {
        fn visit(
            program: &HirProgram,
            actual: HirTypeId,
            expected: HirTypeId,
            visiting: &mut BTreeSet<(HirTypeId, HirTypeId)>,
            depth: usize,
        ) -> bool {
            if actual == expected {
                return true;
            }
            if depth >= crate::TYPE_CAPABILITY_MAX_DEPTH || !visiting.insert((actual, expected)) {
                return false;
            }
            let compatible = match (program.type_kind(actual), program.type_kind(expected)) {
                (
                    Some(HirTypeKind::Reference {
                        pointee: left,
                        mutability: left_mutability,
                        ..
                    }),
                    Some(HirTypeKind::Reference {
                        pointee: right,
                        mutability: right_mutability,
                        ..
                    }),
                ) => {
                    left_mutability == right_mutability
                        && visit(program, *left, *right, visiting, depth + 1)
                }
                (
                    Some(HirTypeKind::Array {
                        element: left,
                        length: left_length,
                    }),
                    Some(HirTypeKind::Array {
                        element: right,
                        length: right_length,
                    }),
                ) => {
                    left_length == right_length
                        && visit(program, *left, *right, visiting, depth + 1)
                }
                (Some(HirTypeKind::Tuple(left)), Some(HirTypeKind::Tuple(right))) => {
                    left.len() == right.len()
                        && left
                            .iter()
                            .zip(right)
                            .all(|(left, right)| visit(program, *left, *right, visiting, depth + 1))
                }
                _ => false,
            };
            visiting.remove(&(actual, expected));
            compatible
        }

        visit(self, actual, expected, &mut BTreeSet::new(), 0)
    }

    fn validate_specs(&self) -> Result<(), HirProgramValidationError> {
        const MAX_SPEC_TERM_DEPTH: usize = 256;

        validate_dense("spec binder", &self.specs.binders, |item| item.id.get())?;
        validate_dense("spec term", &self.specs.terms, |item| item.id.get())?;
        validate_dense("spec clause", &self.specs.clauses, |item| item.id.get())?;
        validate_dense("spec prove", &self.specs.proves, |item| item.id.get())?;
        validate_dense("trust entry", &self.specs.trust_entries, |item| {
            item.id.get()
        })?;
        validate_dense("spec loop invariant", &self.specs.loop_invariants, |item| {
            item.id.get()
        })?;

        let mut binder_names = BTreeSet::new();
        for binder in &self.specs.binders {
            let owner_span = match binder.owner {
                HirSpecBinderOwner::Clause(clause_id) => self
                    .specs
                    .clauses
                    .get(clause_id.index())
                    .filter(|clause| clause.id == clause_id)
                    .map(|clause| clause.span),
                HirSpecBinderOwner::Predicate(predicate) => self
                    .predicate(predicate)
                    .filter(|predicate| predicate.binders.contains(&binder.id))
                    .map(|predicate| predicate.span),
            };
            require(
                !binder.name.is_empty()
                    && binder_names.insert((binder.owner, binder.name.as_str()))
                    && self.is_spec_scalar_type(binder.ty)
                    && owner_span.is_some_and(|span| span_contains(span, binder.span)),
                "spec binder",
                binder.id.index(),
                "empty name, invalid type, foreign owner, or span outside owner",
            )?;
        }

        let mut depths = Vec::with_capacity(self.specs.terms.len());
        for term in &self.specs.terms {
            let clause = self
                .specs
                .clauses
                .get(term.clause.index())
                .filter(|clause| clause.id == term.clause);
            require(
                clause.is_some_and(|clause| span_contains(clause.span, term.span))
                    && self.is_spec_scalar_type(term.ty),
                "spec term",
                term.id.index(),
                "missing clause, invalid type, or span outside clause",
            )?;

            let child = |id: super::HirSpecTermId| {
                self.specs
                    .terms
                    .get(id.index())
                    .filter(|child| child.id == id && id.index() < term.id.index())
                    .filter(|child| child.clause == term.clause)
            };
            let bool_type = |ty| matches!(self.type_kind(ty), Some(HirTypeKind::Bool));
            let u64_type = |ty| {
                matches!(
                    self.type_kind(ty),
                    Some(HirTypeKind::Integer(super::HirIntegerType::U64))
                )
            };
            let (valid, depth) = match &term.kind {
                HirSpecTermKind::Bool(_) => (bool_type(term.ty), 1),
                HirSpecTermKind::U64(_) => (u64_type(term.ty), 1),
                HirSpecTermKind::Binder(id) => {
                    let binder = self
                        .specs
                        .binders
                        .get(id.index())
                        .filter(|binder| binder.id == *id);
                    (
                        binder.is_some_and(|binder| {
                            binder.ty == term.ty
                                && binder.owner == HirSpecBinderOwner::Clause(term.clause)
                        }),
                        1,
                    )
                }
                HirSpecTermKind::Snapshot(snapshot) => {
                    (self.validate_spec_snapshot(term, *snapshot), 1)
                }
                HirSpecTermKind::Equal { left, right } => {
                    let left_id = *left;
                    let right_id = *right;
                    let left = child(left_id);
                    let right = child(right_id);
                    let valid = bool_type(term.ty)
                        && left.zip(right).is_some_and(|(left, right)| {
                            left.ty == right.ty && self.is_spec_scalar_type(left.ty)
                        });
                    (valid, child_depth(&depths, left_id, right_id))
                }
                HirSpecTermKind::LessThan { left, right }
                | HirSpecTermKind::LessOrEqual { left, right } => {
                    let valid = bool_type(term.ty)
                        && child(*left).is_some_and(|left| u64_type(left.ty))
                        && child(*right).is_some_and(|right| u64_type(right.ty));
                    (valid, child_depth(&depths, *left, *right))
                }
                HirSpecTermKind::Not(operand) => {
                    let valid = bool_type(term.ty)
                        && child(*operand).is_some_and(|operand| bool_type(operand.ty));
                    (valid, unary_depth(&depths, *operand))
                }
                HirSpecTermKind::And(operands) | HirSpecTermKind::Or(operands) => {
                    let valid = bool_type(term.ty)
                        && operands.len() >= 2
                        && operands.iter().all(|operand| {
                            child(*operand).is_some_and(|operand| bool_type(operand.ty))
                        });
                    (valid, nary_depth(&depths, operands))
                }
            };
            require(
                valid && depth <= MAX_SPEC_TERM_DEPTH,
                "spec term",
                term.id.index(),
                "ill-typed, cyclic/foreign, or exceeds the recursion-depth budget",
            )?;
            depths.push(depth);
        }

        for clause in &self.specs.clauses {
            let root = self
                .specs
                .terms
                .get(clause.root.index())
                .filter(|term| term.id == clause.root && term.clause == clause.id);
            let owner_valid = match clause.owner {
                HirSpecClauseOwner::Contract { contract, position } => self
                    .contract(contract)
                    .filter(|contract| contract.clauses.contains(&clause.id))
                    .is_some_and(|contract| {
                        clause.location
                            == match position {
                                HirSpecContractPosition::Requires => {
                                    HirSpecLocation::FunctionEntry {
                                        function: contract.function,
                                    }
                                }
                                HirSpecContractPosition::Ensures => {
                                    HirSpecLocation::FunctionResult {
                                        function: contract.function,
                                    }
                                }
                            }
                    }),
                HirSpecClauseOwner::Prove(prove_id) => self
                    .specs
                    .proves
                    .get(prove_id.index())
                    .is_some_and(|prove| {
                        prove.id == prove_id
                            && prove.clause == clause.id
                            && prove.location == clause.location
                    }),
                HirSpecClauseOwner::TrustEntry(entry_id) => self
                    .specs
                    .trust_entries
                    .get(entry_id.index())
                    .is_some_and(|entry| {
                        entry.id == entry_id
                            && entry.clause == clause.id
                            && entry.scope.location() == clause.location
                    }),
                HirSpecClauseOwner::LoopInvariant(invariant_id) => self
                    .specs
                    .loop_invariants
                    .get(invariant_id.index())
                    .is_some_and(|invariant| {
                        invariant.id == invariant_id
                            && invariant.clause == clause.id
                            && invariant.location == clause.location
                    }),
            };
            require(
                owner_valid
                    && root.is_some_and(|root| {
                        matches!(self.type_kind(root.ty), Some(HirTypeKind::Bool))
                    })
                    && self
                        .function_by_id(clause.location.function())
                        .is_some_and(|function| span_contains(function.span, clause.span)),
                "spec clause",
                clause.id.index(),
                "invalid owner/location, non-boolean root, or foreign span",
            )?;
        }

        for prove in &self.specs.proves {
            require(
                self.function_by_id(prove.function).is_some_and(|function| {
                    matches!(
                        prove.location,
                        HirSpecLocation::FunctionEntry { function: owner }
                            | HirSpecLocation::FunctionResult { function: owner }
                            if owner == function.id
                    ) && span_contains(function.span, prove.span)
                }) && self
                    .specs
                    .clauses
                    .get(prove.clause.index())
                    .is_some_and(|clause| {
                        clause.owner == HirSpecClauseOwner::Prove(prove.id)
                            && clause.location == prove.location
                    }),
                "spec prove",
                prove.id.index(),
                "prove must own a boolean clause at its function entry or result",
            )?;
        }

        for entry in &self.specs.trust_entries {
            let valid_policy = entry.policy == HirTrustPolicyKind::EntryPointAssumption
                && entry.scope
                    == (HirTrustScope::FunctionEntry {
                        function: self.entry_function,
                    });
            require(
                valid_policy
                    && self
                        .function_by_id(entry.scope.function())
                        .is_some_and(|function| span_contains(function.span, entry.span))
                    && self
                        .specs
                        .clauses
                        .get(entry.clause.index())
                        .is_some_and(|clause| {
                            clause.owner == HirSpecClauseOwner::TrustEntry(entry.id)
                                && clause.location == entry.scope.location()
                                && clause.span == entry.span
                        }),
                "trust entry",
                entry.id.index(),
                "policy denied, scope is not the program entry, or clause/origin mismatched",
            )?;
        }

        require(
            self.specs.loop_invariants.is_empty(),
            "spec loop invariant",
            0,
            "non-trivial loop invariants remain feature gated",
        )
    }

    fn is_spec_scalar_type(&self, ty: HirTypeId) -> bool {
        matches!(
            self.type_kind(ty),
            Some(HirTypeKind::Bool) | Some(HirTypeKind::Integer(super::HirIntegerType::U64))
        )
    }

    fn validate_spec_snapshot(&self, term: &super::HirSpecTerm, snapshot: HirSpecSnapshot) -> bool {
        let Some(clause) = self.specs.clauses.get(term.clause.index()) else {
            return false;
        };
        match snapshot {
            HirSpecSnapshot::Local { function, local } => self
                .function_by_id(function)
                .and_then(|function| function.body.as_ref().map(|body| (function, body)))
                .is_some_and(|(function, body)| {
                    clause.location
                        == HirSpecLocation::FunctionEntry {
                            function: function.id,
                        }
                        && body.parameters.contains(&local)
                        && body.locals.get(local.index()).is_some_and(|candidate| {
                            candidate.id == local && candidate.ty == term.ty
                        })
                }),
            HirSpecSnapshot::Result { function } => {
                self.function_by_id(function).is_some_and(|function| {
                    clause.location
                        == HirSpecLocation::FunctionResult {
                            function: function.id,
                        }
                        && function.signature.return_type == term.ty
                })
            }
        }
    }

    fn validate_type_kind(
        &self,
        id: HirTypeId,
        kind: &HirTypeKind,
    ) -> Result<(), HirProgramValidationError> {
        let type_exists = |ty| self.type_definition(ty).is_some();
        let valid = match kind {
            HirTypeKind::Unit
            | HirTypeKind::Bool
            | HirTypeKind::Integer(_)
            | HirTypeKind::Never => true,
            HirTypeKind::Own { pointee } | HirTypeKind::RawPointer { pointee, .. } => {
                type_exists(*pointee)
            }
            HirTypeKind::Reference {
                pointee, region, ..
            } => type_exists(*pointee) && self.region(*region).is_some(),
            HirTypeKind::Array { element, .. } | HirTypeKind::Slice { element, .. } => {
                type_exists(*element)
            }
            HirTypeKind::Tuple(elements) => elements.iter().all(|ty| type_exists(*ty)),
            HirTypeKind::Struct { fields } => {
                all_unique(fields.iter().copied())
                    && fields
                        .iter()
                        .all(|field| self.field(*field).is_some_and(|field| field.owner == id))
            }
            HirTypeKind::Enum { variants } => {
                all_unique(variants.iter().copied())
                    && variants.iter().all(|variant| {
                        self.variant(*variant)
                            .is_some_and(|variant| variant.owner == id)
                    })
            }
            HirTypeKind::Function(function) => function
                .parameters
                .iter()
                .chain([&function.return_type])
                .all(|ty| type_exists(*ty)),
            HirTypeKind::GenericParameter(parameter) => {
                self.generic_parameter(*parameter).is_some()
            }
        };
        require(valid, "type", id.index(), "dangling type-kind reference")
    }

    fn validate_variant_layout(&self, layout: &HirLayout) -> Result<(), HirProgramValidationError> {
        let Some(variant_layout) = &layout.variants else {
            return require(
                !matches!(self.type_kind(layout.ty), Some(HirTypeKind::Enum { .. })),
                "layout",
                layout.id.index(),
                "concrete enum layout is missing variant representation",
            );
        };
        let Some(HirTypeKind::Enum { variants }) = self.type_kind(layout.ty) else {
            return require(
                false,
                "layout",
                layout.id.index(),
                "non-enum layout has variant representation",
            );
        };
        require(
            variant_layout.tag_size_bytes > 0
                && variant_layout.tag_alignment.is_power_of_two()
                && variant_layout.tag_size_bytes % variant_layout.tag_alignment == 0
                && variant_layout.tag_alignment <= layout.alignment
                && variant_layout.tag_size_bytes <= layout.size_bytes,
            "layout",
            layout.id.index(),
            "invalid enum tag layout",
        )?;
        require(
            variant_layout.cases.len() == variants.len()
                && all_unique(variant_layout.cases.iter().map(|case| case.variant))
                && variants.iter().all(|variant| {
                    variant_layout
                        .cases
                        .iter()
                        .any(|case| case.variant == *variant)
                }),
            "layout",
            layout.id.index(),
            "enum layout cases do not match enum variants",
        )?;
        for case in &variant_layout.cases {
            let variant = self.variant(case.variant);
            require(
                variant.is_some_and(|variant| variant.owner == layout.ty)
                    && case.payload_offset_bytes >= variant_layout.tag_size_bytes
                    && case.payload_offset_bytes <= layout.size_bytes
                    && all_unique(case.fields.iter().map(|field| field.field)),
                "layout",
                layout.id.index(),
                "invalid enum variant case",
            )?;
            let Some(variant) = variant else {
                return require(false, "layout", layout.id.index(), "missing enum variant");
            };
            require(
                case.fields.len() == variant.fields.len()
                    && variant
                        .fields
                        .iter()
                        .all(|field| case.fields.iter().any(|layout| layout.field == *field)),
                "layout",
                layout.id.index(),
                "enum case fields do not match variant fields",
            )?;
            let mut field_ranges = Vec::with_capacity(case.fields.len());
            for field in &case.fields {
                let field_range = self
                    .field(field.field)
                    .filter(|field| field.owner == layout.ty)
                    .and_then(|field| self.layout_of(field.ty))
                    .and_then(|field_layout| {
                        let offset = case.payload_offset_bytes.checked_add(field.offset_bytes)?;
                        if layout.alignment >= field_layout.alignment
                            && offset % field_layout.alignment == 0
                        {
                            offset
                                .checked_add(field_layout.size_bytes)
                                .map(|end| (offset, end))
                        } else {
                            None
                        }
                    });
                require(
                    field_range.is_some_and(|(_, end)| end <= layout.size_bytes),
                    "layout",
                    layout.id.index(),
                    "enum field layout exceeds aggregate size or is unresolved",
                )?;
                if let Some(range @ (start, end)) = field_range
                    && start < end
                {
                    field_ranges.push(range);
                }
            }
            require(
                ranges_are_disjoint(&mut field_ranges),
                "layout",
                layout.id.index(),
                "enum field layouts overlap",
            )?;
        }
        Ok(())
    }
}

pub(super) fn derive_type_capabilities(
    types: &[HirTypeDefinition],
    fields: &[HirField],
    variants: &[HirVariant],
    root: HirTypeId,
) -> Option<TypeCapabilities> {
    fn lookup_type(types: &[HirTypeDefinition], id: HirTypeId) -> Option<&HirTypeDefinition> {
        types
            .get(id.index())
            .filter(|definition| definition.id == id)
    }

    fn visit(
        types: &[HirTypeDefinition],
        fields: &[HirField],
        variants: &[HirVariant],
        ty: HirTypeId,
        stack: &mut BTreeSet<HirTypeId>,
        depth: usize,
    ) -> Option<TypeCapabilities> {
        if depth >= crate::TYPE_CAPABILITY_MAX_DEPTH {
            return None;
        }
        if !stack.insert(ty) {
            return None;
        }
        let definition = lookup_type(types, ty)?;
        let sized = || {
            if definition.layout.is_some() {
                SizeCapability::Sized
            } else {
                SizeCapability::Unsized
            }
        };
        let fixed = |value, drop, contains_resource| TypeCapabilities {
            value,
            drop,
            contains_resource,
            size: sized(),
        };
        let child_types = match &definition.kind {
            HirTypeKind::Array { element, .. } => Some(vec![*element]),
            HirTypeKind::Tuple(elements) => Some(elements.clone()),
            HirTypeKind::Struct { fields: ids } => Some(
                ids.iter()
                    .map(|id| {
                        fields
                            .get(id.index())
                            .filter(|field| field.id == *id)
                            .map(|field| field.ty)
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            HirTypeKind::Enum { variants: ids } => Some(
                ids.iter()
                    .map(|id| variants.get(id.index()).filter(|variant| variant.id == *id))
                    .collect::<Option<Vec<_>>>()?
                    .into_iter()
                    .flat_map(|variant| variant.fields.iter())
                    .map(|id| {
                        fields
                            .get(id.index())
                            .filter(|field| field.id == *id)
                            .map(|field| field.ty)
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            _ => None,
        };
        let result = if let Some(children) = child_types {
            let children = children
                .into_iter()
                .map(|child| visit(types, fields, variants, child, stack, depth + 1))
                .collect::<Option<Vec<_>>>()?;
            TypeCapabilities {
                value: if children
                    .iter()
                    .all(|capability| capability.value == ValueCapability::Copy)
                {
                    ValueCapability::Copy
                } else {
                    ValueCapability::MoveOnly
                },
                drop: children
                    .iter()
                    .map(|capability| capability.drop)
                    .max()
                    .unwrap_or(DropCapability::TrivialDrop),
                contains_resource: children
                    .iter()
                    .any(|capability| capability.contains_resource),
                size: if definition.layout.is_some()
                    && children
                        .iter()
                        .all(|capability| capability.size == SizeCapability::Sized)
                {
                    SizeCapability::Sized
                } else {
                    SizeCapability::Unsized
                },
            }
        } else {
            match &definition.kind {
                HirTypeKind::Unit | HirTypeKind::Bool | HirTypeKind::Integer(_) => {
                    fixed(ValueCapability::Copy, DropCapability::TrivialDrop, false)
                }
                HirTypeKind::Own { pointee } => {
                    lookup_type(types, *pointee)?;
                    fixed(ValueCapability::MoveOnly, DropCapability::BuiltinDrop, true)
                }
                HirTypeKind::RawPointer { pointee, .. } => {
                    lookup_type(types, *pointee)?;
                    fixed(ValueCapability::Copy, DropCapability::TrivialDrop, true)
                }
                HirTypeKind::Reference {
                    pointee,
                    mutability,
                    ..
                } => {
                    lookup_type(types, *pointee)?;
                    fixed(
                        if *mutability == HirMutability::Const {
                            ValueCapability::Copy
                        } else {
                            ValueCapability::MoveOnly
                        },
                        DropCapability::TrivialDrop,
                        true,
                    )
                }
                HirTypeKind::Slice {
                    element,
                    mutability,
                } => {
                    lookup_type(types, *element)?;
                    fixed(
                        if *mutability == HirMutability::Const {
                            ValueCapability::Copy
                        } else {
                            ValueCapability::MoveOnly
                        },
                        DropCapability::TrivialDrop,
                        true,
                    )
                }
                HirTypeKind::Function(_) => TypeCapabilities {
                    value: ValueCapability::Copy,
                    drop: DropCapability::TrivialDrop,
                    contains_resource: false,
                    size: SizeCapability::Unsized,
                },
                HirTypeKind::GenericParameter(_) => TypeCapabilities {
                    value: ValueCapability::MoveOnly,
                    drop: DropCapability::UserDropGated,
                    contains_resource: true,
                    size: SizeCapability::Unsized,
                },
                HirTypeKind::Never => {
                    fixed(ValueCapability::Copy, DropCapability::TrivialDrop, false)
                }
                HirTypeKind::Array { .. }
                | HirTypeKind::Tuple(_)
                | HirTypeKind::Struct { .. }
                | HirTypeKind::Enum { .. } => unreachable!("aggregate handled above"),
            }
        };
        stack.remove(&ty);
        Some(result)
    }

    visit(types, fields, variants, root, &mut BTreeSet::new(), 0)
}

fn unary_depth(depths: &[usize], operand: super::HirSpecTermId) -> usize {
    depths
        .get(operand.index())
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}

fn child_depth(depths: &[usize], left: super::HirSpecTermId, right: super::HirSpecTermId) -> usize {
    depths
        .get(left.index())
        .zip(depths.get(right.index()))
        .and_then(|(left, right)| left.max(right).checked_add(1))
        .unwrap_or(usize::MAX)
}

fn nary_depth(depths: &[usize], operands: &[super::HirSpecTermId]) -> usize {
    operands
        .iter()
        .map(|operand| depths.get(operand.index()).copied())
        .collect::<Option<Vec<_>>>()
        .and_then(|depths| depths.into_iter().max())
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}

pub(super) const fn span_contains(parent: ByteSpan, child: ByteSpan) -> bool {
    parent.start() <= child.start() && child.end() <= parent.end()
}

fn all_unique<T: Ord>(items: impl IntoIterator<Item = T>) -> bool {
    let mut seen = BTreeSet::new();
    items.into_iter().all(|item| seen.insert(item))
}

fn ranges_are_disjoint(ranges: &mut [(u64, u64)]) -> bool {
    ranges.sort_unstable();
    ranges.windows(2).all(|pair| pair[0].1 <= pair[1].0)
}

fn validate_dense<T>(
    table: &'static str,
    items: &[T],
    raw_id: impl Fn(&T) -> u32,
) -> Result<(), HirProgramValidationError> {
    for (index, item) in items.iter().enumerate() {
        if usize::try_from(raw_id(item)).ok() != Some(index) {
            return Err(HirProgramValidationError {
                table,
                index,
                problem: "table ID does not equal its deterministic index",
            });
        }
    }
    Ok(())
}

pub(super) fn require(
    condition: bool,
    table: &'static str,
    index: usize,
    problem: &'static str,
) -> Result<(), HirProgramValidationError> {
    if condition {
        Ok(())
    } else {
        Err(validation_error(table, index, problem))
    }
}

pub(super) const fn validation_error(
    table: &'static str,
    index: usize,
    problem: &'static str,
) -> HirProgramValidationError {
    HirProgramValidationError {
        table,
        index,
        problem,
    }
}

/// Structural inconsistency in the HIR entity/type/layout tables.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HirProgramValidationError {
    table: &'static str,
    index: usize,
    problem: &'static str,
}

impl HirProgramValidationError {
    #[must_use]
    pub const fn table(self) -> &'static str {
        self.table
    }

    #[must_use]
    pub const fn index(self) -> usize {
        self.index
    }

    #[must_use]
    pub const fn problem(self) -> &'static str {
        self.problem
    }
}

impl fmt::Display for HirProgramValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "invalid HIR {} table entry {}: {}",
            self.table, self.index, self.problem
        )
    }
}

impl Error for HirProgramValidationError {}
