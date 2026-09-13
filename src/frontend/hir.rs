//! Table-organized typed HIR and all-or-nothing AST elaboration.

mod body_validation;
mod borrow_inference;
mod ids;
mod lifetimes;
mod local_spec;
mod node_identity;
mod place;
mod program;
mod regions;
mod resolve;
mod spec;
mod types;
mod validation;
pub(crate) mod visit;

pub(crate) use types::supports_builtin_allocation;

use std::collections::{BTreeMap, BTreeSet};

use super::{
    AstBlock, AstEnum, AstEnumVariantPayload, AstExpression, AstExpressionKind, AstFile,
    AstIntegerPredicate, AstPattern, AstPatternKind, AstPlace, AstPlaceProjection, AstStatement,
    AstStatementKind, AstStruct, AstType, AstVariantInitializer, AstVariantPatternPayload,
    FrontendFailure, span,
};
use crate::ByteSpan;

pub use ids::HirSpecAssertionId;
pub use ids::{
    HirContractId, HirFieldId, HirFunctionId, HirGenericParameterId, HirLayoutId, HirLocalId,
    HirLoopId, HirModuleId, HirNodeId, HirPredicateId, HirRegionConstraintId, HirRegionId,
    HirScopeId, HirSpecBinderId, HirSpecClauseId, HirSpecLoopInvariantId, HirSpecProveId,
    HirSpecTermId, HirTrustEntryId, HirTypeId, HirVariantId,
};
pub use place::{HirPlace, HirPlaceBase, HirProjection, HirProjectionKind};
pub use program::{
    HirBody, HirContract, HirDeclaration, HirField, HirFunction, HirFunctionSignature,
    HirGenericParameter, HirModule, HirModulePath, HirPredicate, HirProgram, HirProgramTables,
    HirProgramValidationError, HirVariant, HirVersion, HirVisibility,
};
pub use regions::{HirRegion, HirRegionConstraint, HirRegionOrigin, HirRegionOwner};
pub use resolve::{
    HirBoundsSource, HirPlaceAccess, HirPlaceResolutionError, HirPlaceResolutionErrorKind,
    ResolvedHirPlace, ResolvedHirProjection, ResolvedHirProjectionKind,
};
pub use spec::{HirSpecAssertion, HirSpecAssertionKind, HirSpecRoot};
pub use spec::{
    HirSpecBinder, HirSpecBinderOwner, HirSpecClause, HirSpecClauseOwner, HirSpecContractPosition,
    HirSpecEnvironment, HirSpecLocation, HirSpecLoopInvariant, HirSpecProve, HirSpecSnapshot,
    HirSpecTerm, HirSpecTermKind, HirTrustEntry, HirTrustPolicyKind, HirTrustScope,
};
pub use types::{
    HirAbiClass, HirCallingConvention, HirEndianness, HirFieldLayout, HirFunctionType,
    HirIntegerType, HirLayout, HirMutability, HirTargetDataLayout, HirTypeDefinition, HirTypeKind,
    HirVariantCaseLayout, HirVariantLayout,
};

/// One named local with references into the canonical type and layout tables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirLocal {
    pub id: HirLocalId,
    pub name: String,
    pub ty: HirTypeId,
    pub layout: HirLayoutId,
    /// The lexical block that owns this local.
    pub scope: HirScopeId,
    /// Whether the binding itself may be assigned through a local-rooted place.
    pub mutable: bool,
    pub declaration_span: ByteSpan,
}

/// Typed HIR statement and its exact source range.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirStatement {
    pub id: HirNodeId,
    pub kind: HirStatementKind,
    pub span: ByteSpan,
}

/// Statement operands use `HirLocalId`; lowering never resolves source names again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirStatementKind {
    /// Erased static obligation; its operands live only in the Spec arena.
    Prove {
        prove: HirSpecProveId,
    },
    /// Declares storage without producing a readable value. All reads remain
    /// subject to independent VIR initialization/validity obligations.
    Declare {
        local: HirLocalId,
    },
    Let {
        local: HirLocalId,
        value: HirExpression,
    },
    /// Typed place assignment.
    Assign {
        destination: HirPlace,
        value: HirExpression,
    },
    Free {
        pointer: HirLocalId,
    },
    Return {
        value: Option<HirExpression>,
    },
    /// Evaluates an expression only for its effects.
    Evaluate {
        expression: HirExpression,
    },
    Block {
        block: HirBlock,
    },
    If {
        condition: HirExpression,
        then_block: HirBlock,
        else_block: Option<HirBlock>,
    },
    While {
        loop_id: HirLoopId,
        condition: HirExpression,
        body: HirBlock,
    },
    For {
        loop_id: HirLoopId,
        pattern: HirPattern,
        source: HirForSource,
        body: HirBlock,
    },
    Match {
        scrutinee: HirExpression,
        arms: Vec<HirMatchArm>,
    },
    Break {
        target: HirLoopId,
    },
    Continue {
        target: HirLoopId,
    },
}

/// One lexical block. `locals` records declaration order independently from
/// executable initialization statements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirBlock {
    pub scope: HirScopeId,
    pub locals: Vec<HirLocalId>,
    pub statements: Vec<HirStatement>,
    pub span: ByteSpan,
}

/// A typed pattern and its source range.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirPattern {
    pub id: HirNodeId,
    pub kind: HirPatternKind,
    pub ty: HirTypeId,
    pub span: ByteSpan,
}

/// Canonical semantics of one by-value place use.
///
/// Elaboration selects this once from the concrete type capability and the
/// source use position. Lowering and every VIR consumer must preserve the
/// choice instead of reclassifying the type independently.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirUseMode {
    Copy,
    Move,
}

/// Pattern forms retained until CFG construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirPatternKind {
    Wildcard,
    Binding {
        local: HirLocalId,
        mode: HirUseMode,
    },
    Integer(u64),
    Bool(bool),
    Tuple(Vec<HirPattern>),
    Variant {
        variant: HirVariantId,
        fields: Vec<HirPattern>,
    },
}

/// Structured source of a `for` loop. More iterator forms can be added
/// without encoding them as calls in the control-flow tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirForSource {
    IntegerRange {
        start: HirExpression,
        end: HirExpression,
        inclusive: bool,
        item_type: HirTypeId,
    },
}

/// One match arm with an optional typed guard.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirMatchArm {
    pub pattern: HirPattern,
    pub guard: Option<HirExpression>,
    pub body: HirBlock,
    pub span: ByteSpan,
}

/// One pointer-offset operation in a flat chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HirPointerOffset {
    pub delta_bytes: u64,
    pub span: ByteSpan,
}

/// Typed expression; `ty` is produced once by HIR elaboration and consumed downstream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirExpression {
    pub id: HirNodeId,
    pub kind: HirExpressionKind,
    pub ty: HirTypeId,
    pub span: ByteSpan,
}

/// One source-ordered field operand in a struct or enum constructor.
///
/// The field has already been resolved to its canonical table identity.  The
/// vector order is the source evaluation order; consumers must not sort it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirFieldInitializer {
    pub field: HirFieldId,
    pub value: HirExpression,
}

/// Runtime expression forms after name and operator resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirExpressionKind {
    PointerDistance {
        begin: Box<HirExpression>,
        end: Box<HirExpression>,
    },
    /// The unique value of the zero-sized unit type. Surface construction is
    /// still gated, but typed aggregate fixtures need an explicit operand.
    Unit,
    Integer(u64),
    Bool(bool),
    /// Read array/slice metadata without copying or moving the referent.
    Length {
        place: Box<HirPlace>,
    },
    /// Positional tuple construction. Elements retain left-to-right source
    /// evaluation order and are matched to the canonical tuple element list.
    TupleConstructor {
        elements: Vec<HirExpression>,
    },
    /// Fixed-array construction in element-index order.
    ArrayConstructor {
        elements: Vec<HirExpression>,
    },
    /// Fixed-array repetition. The operand is evaluated exactly once and its
    /// trivial value is copied into each element in ascending index order.
    ArrayRepeatConstructor {
        value: Box<HirExpression>,
        length: u64,
    },
    /// Nominal struct construction. Field IDs are canonical while vector order
    /// remains the source evaluation order.
    StructConstructor {
        fields: Vec<HirFieldInitializer>,
    },
    /// Nominal enum construction for one canonical variant.
    EnumConstructor {
        variant: HirVariantId,
        fields: Vec<HirFieldInitializer>,
    },
    Compare {
        predicate: HirIntegerPredicate,
        left: Box<HirExpression>,
        right: Box<HirExpression>,
        operation_span: ByteSpan,
    },
    WordAdd {
        operands: Vec<HirExpression>,
        operation_spans: Vec<ByteSpan>,
    },
    PointerOffset {
        base: Box<HirExpression>,
        offsets: Vec<HirPointerOffset>,
    },
    Allocate {
        element_type: HirTypeId,
        element_count: u64,
        size_bytes: u64,
        alignment: u64,
    },
    /// Exposes the non-owning pointee address of an `Own<T>` place for raw
    /// pointer arithmetic without turning that address observation into a
    /// by-value move of the owner.
    OwnerAddress {
        place: Box<HirPlace>,
    },
    /// Reads the value currently stored at a place.
    Read {
        place: Box<HirPlace>,
        mode: HirUseMode,
    },
    /// Creates a reference without disguising the operation as a read.
    Borrow {
        place: Box<HirPlace>,
        mutability: HirMutability,
        region: HirRegionId,
    },
    /// Creates a raw address without implicitly reading the place.
    RawAddress {
        place: Box<HirPlace>,
        mutability: HirMutability,
    },
    /// A statically resolved direct call. No source name lookup remains below HIR.
    Call(HirCall),
}

/// Fully resolved direct-call site and the exact instantiated interface it uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirCall {
    pub callee: HirFunctionId,
    pub instantiated_signature: HirFunctionSignature,
    pub arguments: Vec<HirExpression>,
    pub contract: HirContractId,
    pub calling_convention: HirCallingConvention,
}

/// Unsigned integer comparison retained independently from VIR encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirIntegerPredicate {
    Equal,
    NotEqual,
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual,
}

const ROOT_SCOPE: HirScopeId = HirScopeId::new(0);

#[derive(Clone, Copy, Debug)]
struct CoreTypeIds {
    unit: HirTypeId,
    bool_: HirTypeId,
    u64_: HirTypeId,
    own_u64: HirTypeId,
    raw_mut_u64: HirTypeId,
    usize_: HirTypeId,
}

#[derive(Clone, Copy, Debug)]
struct CoreLayoutIds {
    unit: HirLayoutId,
    bool_: HirLayoutId,
    u64_: HirLayoutId,
    own_u64: HirLayoutId,
    raw_mut_u64: HirLayoutId,
    usize_: HirLayoutId,
}

impl CoreTypeIds {
    const fn new() -> Self {
        Self {
            unit: HirTypeId::new(0),
            bool_: HirTypeId::new(1),
            u64_: HirTypeId::new(2),
            own_u64: HirTypeId::new(3),
            raw_mut_u64: HirTypeId::new(4),
            usize_: HirTypeId::new(5),
        }
    }
}

impl CoreLayoutIds {
    const fn new() -> Self {
        Self {
            unit: HirLayoutId::new(0),
            bool_: HirLayoutId::new(1),
            u64_: HirLayoutId::new(2),
            own_u64: HirLayoutId::new(3),
            raw_mut_u64: HirLayoutId::new(4),
            usize_: HirLayoutId::new(5),
        }
    }
}

pub(super) fn elaborate_modules(
    files: &[&AstFile],
    graph: super::modules::ModuleGraph,
) -> Result<HirProgram, FrontendFailure> {
    let mut elaborator = Elaborator::new(graph);
    elaborator.elaborate(files).map_err(|mut failure| {
        if failure.source.is_none() {
            failure.source = Some(crate::VirSourceId::new(elaborator.current_module as u32));
        }
        failure
    })
}

#[derive(Clone, Copy, Debug)]
struct SemanticValue {
    ty: HirTypeId,
    allocation: Option<u32>,
}

#[derive(Clone, Copy, Debug)]
struct Binding {
    local: HirLocalId,
    value: SemanticValue,
}

struct ScopeFrame {
    id: HirScopeId,
    bindings: BTreeMap<String, Binding>,
    locals: Vec<HirLocalId>,
}

#[derive(Clone, Debug)]
struct FunctionDeclaration {
    id: HirFunctionId,
    contract: HirContractId,
    signature: HirFunctionSignature,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SurfaceVariantStyle {
    Unit,
    Tuple,
    Named,
}

struct Elaborator {
    specs: HirSpecEnvironment,
    graph: super::modules::ModuleGraph,
    current_module: usize,
    type_sources: BTreeMap<HirTypeId, crate::VirSourceSpan>,
    data_layout: HirTargetDataLayout,
    core_types: CoreTypeIds,
    types: Vec<HirTypeDefinition>,
    layouts: Vec<HirLayout>,
    fields: Vec<HirField>,
    variants: Vec<HirVariant>,
    regions: Vec<HirRegion>,
    region_constraints: Vec<HirRegionConstraint>,
    type_names: BTreeMap<String, HirTypeId>,
    variant_names: BTreeMap<(HirTypeId, String), HirVariantId>,
    variant_styles: BTreeMap<HirVariantId, SurfaceVariantStyle>,
    scopes: Vec<ScopeFrame>,
    locals: Vec<HirLocal>,
    next_allocation: u32,
    next_scope: u32,
    next_loop: u32,
    next_node: u32,
    active_loops: Vec<HirLoopId>,
    current_function: Option<HirFunctionId>,
    return_type: HirTypeId,
    function_names: BTreeMap<String, HirFunctionId>,
    function_declarations: Vec<FunctionDeclaration>,
}

impl Elaborator {
    fn new(graph: super::modules::ModuleGraph) -> Self {
        let data_layout = HirTargetDataLayout::x86_64();
        let core_types = CoreTypeIds::new();
        let core_layouts = CoreLayoutIds::new();
        let types = vec![
            type_definition(
                core_types.unit,
                "unit",
                HirTypeKind::Unit,
                Some(core_layouts.unit),
            ),
            type_definition(
                core_types.bool_,
                "bool",
                HirTypeKind::Bool,
                Some(core_layouts.bool_),
            ),
            type_definition(
                core_types.u64_,
                "u64",
                HirTypeKind::Integer(HirIntegerType::U64),
                Some(core_layouts.u64_),
            ),
            type_definition(
                core_types.own_u64,
                "own<u64>",
                HirTypeKind::Own {
                    pointee: core_types.u64_,
                },
                Some(core_layouts.own_u64),
            ),
            type_definition(
                core_types.raw_mut_u64,
                "*mut u64",
                HirTypeKind::RawPointer {
                    pointee: core_types.u64_,
                    mutability: HirMutability::Mutable,
                },
                Some(core_layouts.raw_mut_u64),
            ),
            type_definition(
                core_types.usize_,
                "usize",
                HirTypeKind::Integer(HirIntegerType::Usize),
                Some(core_layouts.usize_),
            ),
        ];
        let layouts = vec![
            layout(
                core_layouts.unit,
                core_types.unit,
                0,
                1,
                HirAbiClass::Ignore,
            ),
            layout(
                core_layouts.bool_,
                core_types.bool_,
                1,
                1,
                HirAbiClass::Scalar,
            ),
            layout(
                core_layouts.u64_,
                core_types.u64_,
                8,
                8,
                HirAbiClass::Scalar,
            ),
            layout(
                core_layouts.own_u64,
                core_types.own_u64,
                data_layout.pointer_size_bytes,
                data_layout.pointer_alignment,
                HirAbiClass::Scalar,
            ),
            layout(
                core_layouts.raw_mut_u64,
                core_types.raw_mut_u64,
                data_layout.pointer_size_bytes,
                data_layout.pointer_alignment,
                HirAbiClass::Scalar,
            ),
            layout(
                core_layouts.usize_,
                core_types.usize_,
                data_layout.usize_size_bytes,
                data_layout.usize_alignment,
                HirAbiClass::Scalar,
            ),
        ];
        let type_names = BTreeMap::from([
            ("unit".to_owned(), core_types.unit),
            ("bool".to_owned(), core_types.bool_),
            ("u64".to_owned(), core_types.u64_),
            ("Own<u64>".to_owned(), core_types.own_u64),
            ("ptr<u64>".to_owned(), core_types.raw_mut_u64),
            ("usize".to_owned(), core_types.usize_),
        ]);
        Self {
            graph,
            type_sources: BTreeMap::new(),
            current_module: 0,
            data_layout,
            core_types,
            types,
            layouts,
            fields: Vec::new(),
            variants: Vec::new(),
            regions: Vec::new(),
            region_constraints: Vec::new(),
            type_names,
            variant_names: BTreeMap::new(),
            variant_styles: BTreeMap::new(),
            scopes: Vec::new(),
            locals: Vec::new(),
            next_allocation: 0,
            next_scope: 1,
            next_loop: 0,
            next_node: 0,
            specs: HirSpecEnvironment::empty(),
            active_loops: Vec::new(),
            current_function: None,
            return_type: core_types.unit,
            function_names: BTreeMap::new(),
            function_declarations: Vec::new(),
        }
    }

    fn key(&self, name: &str) -> String {
        self.graph.key(self.current_module, name)
    }
    fn declaration_key(&self, name: &str) -> String {
        self.graph.declared_key(self.current_module, name)
    }
    fn elaborate(&mut self, files: &[&AstFile]) -> Result<HirProgram, FrontendFailure> {
        let mut declared = Vec::new();
        for (module, ast) in files.iter().enumerate() {
            self.current_module = module;
            let structs = self.declare_structs(ast.structs())?;
            let enums = self.declare_enums(ast.enums())?;
            declared.push((structs, enums));
        }
        for (module, ast) in files.iter().enumerate() {
            self.current_module = module;
            self.define_struct_fields(ast.structs(), &declared[module].0)?;
            self.define_enum_variants(ast.enums(), &declared[module].1)?;
        }
        for (module, ast) in files.iter().enumerate() {
            self.current_module = module;
            for (item, ty) in ast.structs().iter().zip(&declared[module].0) {
                self.ensure_layout(*ty, &mut Vec::new(), item.span)?;
            }
            for (item, ty) in ast.enums().iter().zip(&declared[module].1) {
                self.ensure_layout(*ty, &mut Vec::new(), item.span)?;
            }
        }
        self.validate_supported_fields()?;
        let ast_functions: Vec<_> = files
            .iter()
            .enumerate()
            .flat_map(|(module, ast)| ast.functions().iter().map(move |f| (module, f)))
            .collect();

        for (index, (module, function)) in ast_functions.iter().enumerate() {
            self.current_module = *module;
            let raw_id = u32::try_from(index).map_err(|_| {
                FrontendFailure::elaboration(function.span, "too many source functions")
            })?;
            let id = HirFunctionId::new(raw_id);
            if self
                .function_names
                .insert(self.declaration_key(&function.name), id)
                .is_some()
            {
                return Err(FrontendFailure::elaboration(
                    function.span,
                    "a function name must be unique within the source module",
                ));
            }
        }
        // All owners/names exist before building private signature drafts.
        // No public HIR or body can observe an unresolved return region.
        let mut drafts = Vec::with_capacity(ast_functions.len());
        for (index, (module, function)) in ast_functions.iter().enumerate() {
            self.current_module = *module;
            drafts.push(self.draft_borrow_signature(function, HirFunctionId::new(index as u32))?);
        }
        let inferred_borrow_sources = self.infer_borrow_sources(&ast_functions, &drafts)?;
        for (((module, function), draft), inferred_source) in ast_functions
            .iter()
            .zip(drafts)
            .zip(inferred_borrow_sources)
        {
            self.current_module = *module;
            let id = draft.owner;
            let raw_id = id.get();
            let (parameter_types, return_type, borrow_result, borrow_result_alternatives) =
                self.close_borrow_signature(function, draft, inferred_source)?;
            let signature_type = HirTypeId::new(u32::try_from(self.types.len()).map_err(|_| {
                FrontendFailure::elaboration(function.span, "too many HIR type definitions")
            })?);
            let signature = HirFunctionSignature {
                ty: signature_type,
                parameters: parameter_types,
                return_type,
                calling_convention: HirCallingConvention::Nera,
                borrow_result,
                borrow_result_alternatives,
            };
            self.types.push(HirTypeDefinition {
                id: signature_type,
                name: None,
                kind: HirTypeKind::Function(HirFunctionType {
                    parameters: signature.parameters.clone(),
                    return_type,
                    calling_convention: signature.calling_convention,
                }),
                generic_parameters: Vec::new(),
                layout: None,
            });
            self.function_declarations.push(FunctionDeclaration {
                id,
                contract: HirContractId::new(raw_id),
                signature,
            });
        }

        let mut functions = Vec::with_capacity(ast_functions.len());
        let mut contracts = Vec::with_capacity(ast_functions.len());
        let mut modules: Vec<_> = files
            .iter()
            .enumerate()
            .map(|(module, ast)| HirModule {
                id: HirModuleId::new(module as u32),
                path: HirModulePath::from_segments(
                    self.graph.scopes[module]
                        .path
                        .split("::")
                        .map(str::to_owned)
                        .collect(),
                )
                .unwrap(),
                declarations: declared[module]
                    .0
                    .iter()
                    .chain(&declared[module].1)
                    .copied()
                    .map(HirDeclaration::Type)
                    .collect(),
                span: ast.span(),
            })
            .collect();
        for (index, (module, function)) in ast_functions.iter().enumerate() {
            self.current_module = *module;
            let declaration = self
                .function_declarations
                .get(index)
                .cloned()
                .ok_or_else(|| {
                    FrontendFailure::elaboration(function.span, "missing function declaration")
                })?;
            self.scopes.clear();
            self.locals.clear();
            self.next_allocation = 0;
            self.next_scope = 1;
            self.next_loop = 0;
            self.active_loops.clear();
            self.current_function = Some(declaration.id);
            self.return_type = declaration.signature.return_type;
            let (root, parameters) =
                self.elaborate_root_block(&function.body, &function.parameters)?;
            self.current_function = None;
            let locals = std::mem::take(&mut self.locals);
            let mut body = HirBody {
                parameters,
                root,
                locals,
            };
            node_identity::assign_body_node_ids(&mut body, &mut self.next_node, function.span)?;
            functions.push(HirFunction {
                id: declaration.id,
                module: HirModuleId::new(*module as u32),
                name: function.name.clone(),
                signature: declaration.signature,
                generic_parameters: Vec::new(),
                body: Some(body),
                contract: declaration.contract,
                visibility: if files[*module].public.contains(&function.name) {
                    HirVisibility::Public
                } else {
                    HirVisibility::Private
                },
                span: function.span,
            });
            contracts.push(HirContract {
                id: declaration.contract,
                function: declaration.id,
                is_implicit: true,
                clauses: Vec::new(),
                span: function.span,
            });
            modules[*module]
                .declarations
                .push(HirDeclaration::Function(declaration.id));
            modules[*module]
                .declarations
                .push(HirDeclaration::Contract(declaration.contract));
        }
        let graph = &self.graph;
        let entry_module = HirModuleId::new(graph.entry_module as u32);
        let entry_function =
            self.function_names[&graph.declared_key(graph.entry_module, &graph.entry_name)];
        let ast = files[graph.entry_module];
        let mut tables = HirProgramTables {
            data_layout: self.data_layout,
            entry_module,
            entry_function,
            modules,
            types: std::mem::take(&mut self.types),
            type_capabilities: Vec::new(),
            layouts: std::mem::take(&mut self.layouts),
            fields: std::mem::take(&mut self.fields),
            variants: std::mem::take(&mut self.variants),
            generic_parameters: Vec::new(),
            regions: std::mem::take(&mut self.regions),
            region_constraints: std::mem::take(&mut self.region_constraints),
            functions,
            contracts,
            predicates: Vec::new(),
            specs: std::mem::replace(&mut self.specs, HirSpecEnvironment::empty()),
        };
        tables.assign_canonical_type_capabilities().map_err(|_| {
            FrontendFailure::elaboration(ast.span(), "typed HIR type capabilities are inconsistent")
        })?;
        HirProgram::from_tables(tables).map_err(|_| {
            FrontendFailure::elaboration(ast.span(), "typed HIR program tables are inconsistent")
        })
    }

    fn declare_structs(
        &mut self,
        structs: &[AstStruct],
    ) -> Result<Vec<HirTypeId>, FrontendFailure> {
        let mut ids = Vec::with_capacity(structs.len());
        for item in structs {
            let id = HirTypeId::new(u32::try_from(self.types.len()).map_err(|_| {
                FrontendFailure::elaboration(item.span, "too many HIR type definitions")
            })?);
            if self.type_names.contains_key(&item.name)
                || self
                    .type_names
                    .insert(self.declaration_key(&item.name), id)
                    .is_some()
            {
                return Err(FrontendFailure::elaboration(
                    item.span,
                    "a type name must be unique within the source module",
                ));
            }
            self.type_sources.insert(
                id,
                crate::VirSourceSpan {
                    source: crate::VirSourceId::new(self.current_module as u32),
                    span: item.span,
                },
            );
            self.types.push(HirTypeDefinition {
                id,
                name: Some(item.name.clone()),
                kind: HirTypeKind::Struct { fields: Vec::new() },
                generic_parameters: Vec::new(),
                layout: None,
            });
            ids.push(id);
        }
        Ok(ids)
    }

    fn define_struct_fields(
        &mut self,
        structs: &[AstStruct],
        ids: &[HirTypeId],
    ) -> Result<(), FrontendFailure> {
        for (item, owner) in structs.iter().zip(ids) {
            let mut names = BTreeSet::new();
            let mut field_ids = Vec::with_capacity(item.fields.len());
            for field in &item.fields {
                if !names.insert(field.name.as_str()) {
                    return Err(FrontendFailure::elaboration(
                        field.span,
                        "a struct field name must be unique",
                    ));
                }
                let ty = self.resolve_aggregate_field_type(&field.ty, *owner, field.span)?;
                let id = HirFieldId::new(u32::try_from(self.fields.len()).map_err(|_| {
                    FrontendFailure::elaboration(field.span, "too many HIR fields")
                })?);
                self.fields.push(HirField {
                    id,
                    owner: *owner,
                    name: field.name.clone(),
                    ty,
                    span: field.span,
                });
                field_ids.push(id);
            }
            let definition = self
                .types
                .get_mut(owner.index())
                .filter(|definition| definition.id == *owner)
                .ok_or_else(|| {
                    FrontendFailure::elaboration(item.span, "struct type declaration is missing")
                })?;
            definition.kind = HirTypeKind::Struct { fields: field_ids };
        }
        Ok(())
    }

    fn declare_enums(&mut self, enums: &[AstEnum]) -> Result<Vec<HirTypeId>, FrontendFailure> {
        let mut ids = Vec::with_capacity(enums.len());
        for item in enums {
            let id = HirTypeId::new(u32::try_from(self.types.len()).map_err(|_| {
                FrontendFailure::elaboration(item.span, "too many HIR type definitions")
            })?);
            if self.type_names.contains_key(&item.name)
                || self
                    .type_names
                    .insert(self.declaration_key(&item.name), id)
                    .is_some()
            {
                return Err(FrontendFailure::elaboration(
                    item.span,
                    "a type name must be unique within the source module",
                ));
            }
            self.type_sources.insert(
                id,
                crate::VirSourceSpan {
                    source: crate::VirSourceId::new(self.current_module as u32),
                    span: item.span,
                },
            );
            self.types.push(HirTypeDefinition {
                id,
                name: Some(item.name.clone()),
                kind: HirTypeKind::Enum {
                    variants: Vec::new(),
                },
                generic_parameters: Vec::new(),
                layout: None,
            });
            ids.push(id);
        }
        Ok(ids)
    }

    fn define_enum_variants(
        &mut self,
        enums: &[AstEnum],
        ids: &[HirTypeId],
    ) -> Result<(), FrontendFailure> {
        for (item, owner) in enums.iter().zip(ids) {
            if item.variants.len() > 256 {
                return Err(FrontendFailure::unsupported(
                    item.span,
                    "stage 6.5.9 enums may contain at most 256 variants",
                ));
            }
            let mut names = BTreeSet::new();
            let mut variant_ids = Vec::with_capacity(item.variants.len());
            for (discriminant, variant) in item.variants.iter().enumerate() {
                if !names.insert(variant.name.as_str()) {
                    return Err(FrontendFailure::elaboration(
                        variant.span,
                        "an enum variant name must be unique",
                    ));
                }
                let id = HirVariantId::new(u32::try_from(self.variants.len()).map_err(|_| {
                    FrontendFailure::elaboration(variant.span, "too many HIR enum variants")
                })?);
                let (style, field_types) = match &variant.payload {
                    AstEnumVariantPayload::Unit => (SurfaceVariantStyle::Unit, Vec::new()),
                    AstEnumVariantPayload::Tuple(fields) => (
                        SurfaceVariantStyle::Tuple,
                        fields
                            .iter()
                            .enumerate()
                            .map(|(index, field)| {
                                self.resolve_aggregate_field_type(&field.ty, *owner, field.span)
                                    .map(|ty| (index.to_string(), ty, field.span))
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    ),
                    AstEnumVariantPayload::Named(fields) => {
                        let mut field_names = BTreeSet::new();
                        let fields = fields
                            .iter()
                            .map(|field| {
                                if !field_names.insert(field.name.as_str()) {
                                    return Err(FrontendFailure::elaboration(
                                        field.span,
                                        "an enum variant field name must be unique",
                                    ));
                                }
                                Ok((
                                    field.name.clone(),
                                    self.resolve_aggregate_field_type(
                                        &field.ty, *owner, field.span,
                                    )?,
                                    field.span,
                                ))
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        (SurfaceVariantStyle::Named, fields)
                    }
                };
                let mut fields = Vec::with_capacity(field_types.len());
                for (name, ty, field_span) in field_types {
                    let field =
                        HirFieldId::new(u32::try_from(self.fields.len()).map_err(|_| {
                            FrontendFailure::elaboration(field_span, "too many HIR fields")
                        })?);
                    self.fields.push(HirField {
                        id: field,
                        owner: *owner,
                        name,
                        ty,
                        span: field_span,
                    });
                    fields.push(field);
                }
                let discriminant = u64::try_from(discriminant).map_err(|_| {
                    FrontendFailure::elaboration(variant.span, "enum discriminant is too large")
                })?;
                self.variants.push(HirVariant {
                    id,
                    owner: *owner,
                    name: variant.name.clone(),
                    fields,
                    discriminant,
                    span: variant.span,
                });
                self.variant_names
                    .insert((*owner, variant.name.clone()), id);
                self.variant_styles.insert(id, style);
                variant_ids.push(id);
            }
            let definition = self
                .types
                .get_mut(owner.index())
                .filter(|definition| definition.id == *owner)
                .ok_or_else(|| {
                    FrontendFailure::elaboration(item.span, "enum type declaration is missing")
                })?;
            definition.kind = HirTypeKind::Enum {
                variants: variant_ids,
            };
        }
        Ok(())
    }

    fn validate_supported_fields(&self) -> Result<(), FrontendFailure> {
        for field in &self.fields {
            if !self.is_surface_value_type(field.ty) {
                let mut failure = FrontendFailure::unsupported(
                    field.span,
                    "aggregate fields must be fixed-size values with supported ownership payload",
                );
                failure.source = self
                    .type_sources
                    .get(&field.owner)
                    .map(|origin| origin.source);
                return Err(failure);
            }
        }
        Ok(())
    }

    fn signature_type(
        &mut self,
        ty: &AstType,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        let resolved = self.resolve_ast_type(ty, source_span)?;
        if self.is_aggregate(resolved) {
            self.require_surface_aggregate(resolved, source_span)?;
            if !self.is_surface_copy_type(resolved)
                && !self.is_variant_free_owning_aggregate(resolved)
            {
                return Err(FrontendFailure::unsupported(
                    source_span,
                    "variant-dependent ownership-bearing aggregate ABI requires a conditional interface summary",
                ));
            }
        }
        Ok(resolved)
    }

    fn reference_pointee(
        &mut self,
        ty: &AstType,
        mutable: bool,
        span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        if let AstType::Slice { element } = ty {
            let element = self.resolve_ast_type(element, span)?;
            self.intern_slice_type(
                element,
                if mutable {
                    HirMutability::Mutable
                } else {
                    HirMutability::Const
                },
                span,
            )
        } else {
            self.resolve_ast_type(ty, span)
        }
    }

    fn parameter_type(
        &mut self,
        ty: &AstType,
        owner: HirFunctionId,
        index: usize,
        span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        let AstType::Reference { pointee, mutable } = ty else {
            return self.signature_type(ty, span);
        };
        let pointee = self.reference_pointee(pointee, *mutable, span)?;
        let region = HirRegionId::new(
            u32::try_from(self.regions.len())
                .map_err(|_| FrontendFailure::elaboration(span, "too many regions"))?,
        );
        self.regions.push(HirRegion {
            id: region,
            owner: HirRegionOwner::Function(owner),
            origin: HirRegionOrigin::Parameter {
                index: index as u32,
            },
            span,
        });
        self.intern_reference_type(
            pointee,
            if *mutable {
                HirMutability::Mutable
            } else {
                HirMutability::Const
            },
            region,
            span,
        )
    }

    fn reference_compatible(&self, actual: HirTypeId, expected: HirTypeId) -> bool {
        actual == expected
            || matches!((&self.types[actual.index()].kind, &self.types[expected.index()].kind),
            (HirTypeKind::Reference { pointee: a, mutability: am, .. }, HirTypeKind::Reference { pointee: b, mutability: bm, .. }) if a == b && am == bm)
    }

    fn resolve_ast_type(
        &mut self,
        ty: &AstType,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        match ty {
            AstType::Unit => Ok(self.core_types.unit),
            AstType::Bool => Ok(self.core_types.bool_),
            AstType::U64 => Ok(self.core_types.u64_),
            AstType::Usize => Ok(self.core_types.usize_),
            AstType::OwnU64 => Ok(self.core_types.own_u64),
            AstType::RawU64 => Ok(self.core_types.raw_mut_u64),
            AstType::Applied { .. } | AstType::ConstArray { .. } | AstType::Reference { .. } => {
                Err(FrontendFailure::unsupported(
                    source_span,
                    "reference types are currently restricted to local borrow bindings",
                ))
            }
            AstType::Slice { .. } => Err(FrontendFailure::unsupported(
                source_span,
                "a slice is unsized and may currently appear only behind `&` or `&mut`",
            )),
            AstType::Named(name) => {
                self.type_names
                    .get(&self.key(name))
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(source_span, "named type is not defined")
                    })
            }
            AstType::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|element| self.resolve_ast_type(element, source_span))
                    .collect::<Result<Vec<_>, _>>()?;
                self.intern_aggregate_type(HirTypeKind::Tuple(elements), source_span)
            }
            AstType::Array { element, length } => {
                let element = self.resolve_ast_type(element, source_span)?;
                self.intern_aggregate_type(
                    HirTypeKind::Array {
                        element,
                        length: *length,
                    },
                    source_span,
                )
            }
        }
    }

    fn resolve_aggregate_field_type(
        &mut self,
        ty: &AstType,
        owner: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        match ty {
            AstType::Reference { pointee, mutable } => {
                if matches!(pointee.as_ref(), AstType::Slice { .. }) {
                    return Err(FrontendFailure::unsupported(
                        source_span,
                        "slice views in aggregate storage require stored view metadata support",
                    ));
                }
                let mutability = if *mutable {
                    HirMutability::Mutable
                } else {
                    HirMutability::Const
                };
                let pointee = self.resolve_aggregate_field_type(pointee, owner, source_span)?;
                let region = HirRegionId::new(u32::try_from(self.regions.len()).map_err(|_| {
                    FrontendFailure::elaboration(source_span, "too many aggregate borrow regions")
                })?);
                self.regions.push(HirRegion {
                    id: region,
                    owner: HirRegionOwner::Type(owner),
                    origin: HirRegionOrigin::AggregateErased,
                    span: source_span,
                });
                self.intern_reference_type(pointee, mutability, region, source_span)
            }
            AstType::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|element| self.resolve_aggregate_field_type(element, owner, source_span))
                    .collect::<Result<Vec<_>, _>>()?;
                self.intern_aggregate_type(HirTypeKind::Tuple(elements), source_span)
            }
            AstType::Array { element, length } => {
                let element = self.resolve_aggregate_field_type(element, owner, source_span)?;
                self.intern_aggregate_type(
                    HirTypeKind::Array {
                        element,
                        length: *length,
                    },
                    source_span,
                )
            }
            AstType::Slice { .. } => Err(FrontendFailure::unsupported(
                source_span,
                "a slice is unsized and cannot be stored directly in an aggregate",
            )),
            _ => self.resolve_ast_type(ty, source_span),
        }
    }

    fn intern_slice_type(
        &mut self,
        element: HirTypeId,
        mutability: HirMutability,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        let kind = HirTypeKind::Slice {
            element,
            mutability,
        };
        if let Some(existing) = self
            .types
            .iter()
            .find(|definition| definition.kind == kind)
            .map(|definition| definition.id)
        {
            return Ok(existing);
        }
        if self.type_definition(element).is_none() {
            return Err(FrontendFailure::elaboration(
                source_span,
                "slice element type is missing",
            ));
        }
        let id = HirTypeId::new(u32::try_from(self.types.len()).map_err(|_| {
            FrontendFailure::elaboration(source_span, "too many HIR type definitions")
        })?);
        let layout = HirLayoutId::new(
            u32::try_from(self.layouts.len())
                .map_err(|_| FrontendFailure::elaboration(source_span, "too many HIR layouts"))?,
        );
        let size_bytes = self
            .data_layout
            .pointer_size_bytes
            .checked_add(self.data_layout.usize_size_bytes)
            .ok_or_else(|| FrontendFailure::elaboration(source_span, "slice layout overflows"))?;
        self.types.push(HirTypeDefinition {
            id,
            name: None,
            kind,
            generic_parameters: Vec::new(),
            layout: Some(layout),
        });
        self.layouts.push(HirLayout {
            id: layout,
            ty: id,
            size_bytes,
            alignment: self
                .data_layout
                .pointer_alignment
                .max(self.data_layout.usize_alignment),
            abi: HirAbiClass::ScalarPair,
            fields: Vec::new(),
            variants: None,
        });
        Ok(id)
    }

    fn intern_aggregate_type(
        &mut self,
        kind: HirTypeKind,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        if let Some(existing) = self
            .types
            .iter()
            .find(|definition| definition.kind == kind)
            .map(|definition| definition.id)
        {
            return Ok(existing);
        }
        let id = HirTypeId::new(u32::try_from(self.types.len()).map_err(|_| {
            FrontendFailure::elaboration(source_span, "too many HIR type definitions")
        })?);
        self.types.push(HirTypeDefinition {
            id,
            name: None,
            kind,
            generic_parameters: Vec::new(),
            layout: None,
        });
        Ok(id)
    }

    fn intern_reference_type(
        &mut self,
        pointee: HirTypeId,
        mutability: HirMutability,
        region: HirRegionId,
        source_span: ByteSpan,
    ) -> Result<HirTypeId, FrontendFailure> {
        if self.type_definition(pointee).is_none() {
            return Err(FrontendFailure::elaboration(
                source_span,
                "borrow pointee type is missing",
            ));
        }
        let id = HirTypeId::new(u32::try_from(self.types.len()).map_err(|_| {
            FrontendFailure::elaboration(source_span, "too many HIR type definitions")
        })?);
        let layout = HirLayoutId::new(
            u32::try_from(self.layouts.len())
                .map_err(|_| FrontendFailure::elaboration(source_span, "too many HIR layouts"))?,
        );
        self.types.push(HirTypeDefinition {
            id,
            name: None,
            kind: HirTypeKind::Reference {
                pointee,
                mutability,
                region,
            },
            generic_parameters: Vec::new(),
            layout: Some(layout),
        });
        let (size_bytes, alignment, abi) = if matches!(
            self.type_definition(pointee)
                .map(|definition| &definition.kind),
            Some(HirTypeKind::Slice { .. })
        ) {
            (
                self.data_layout
                    .pointer_size_bytes
                    .checked_add(self.data_layout.usize_size_bytes)
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            source_span,
                            "slice reference layout overflows",
                        )
                    })?,
                self.data_layout
                    .pointer_alignment
                    .max(self.data_layout.usize_alignment),
                HirAbiClass::ScalarPair,
            )
        } else {
            (
                self.data_layout.pointer_size_bytes,
                self.data_layout.pointer_alignment,
                HirAbiClass::Scalar,
            )
        };
        self.layouts.push(HirLayout {
            id: layout,
            ty: id,
            size_bytes,
            alignment,
            abi,
            fields: Vec::new(),
            variants: None,
        });
        Ok(id)
    }

    fn ensure_layout(
        &mut self,
        ty: HirTypeId,
        stack: &mut Vec<HirTypeId>,
        source_span: ByteSpan,
    ) -> Result<HirLayoutId, FrontendFailure> {
        let origin = self.type_sources.get(&ty).copied();
        self.ensure_layout_inner(ty, stack, origin.map_or(source_span, |source| source.span))
            .map_err(|mut failure| {
                if failure.source.is_none() {
                    failure.source = origin.map(|source| source.source);
                }
                failure
            })
    }

    fn ensure_layout_inner(
        &mut self,
        ty: HirTypeId,
        stack: &mut Vec<HirTypeId>,
        source_span: ByteSpan,
    ) -> Result<HirLayoutId, FrontendFailure> {
        if let Some(layout) = self
            .type_definition(ty)
            .and_then(|definition| definition.layout)
        {
            return Ok(layout);
        }
        if stack.contains(&ty) {
            return Err(FrontendFailure::elaboration(
                source_span,
                "recursive by-value aggregate has no finite layout",
            ));
        }
        stack.push(ty);
        let kind = self
            .type_definition(ty)
            .map(|definition| definition.kind.clone())
            .ok_or_else(|| FrontendFailure::elaboration(source_span, "type is missing"))?;
        let (size_bytes, alignment, fields, variants) = match kind {
            HirTypeKind::Array { element, length } => {
                let element_layout = self.ensure_layout(element, stack, source_span)?;
                let element_layout = self.layouts[element_layout.index()].clone();
                let size = element_layout
                    .size_bytes
                    .checked_mul(length)
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            source_span,
                            "array layout size overflows `u64`",
                        )
                    })?;
                (size, element_layout.alignment, Vec::new(), None)
            }
            HirTypeKind::Tuple(elements) => {
                let mut offset = 0u64;
                let mut alignment = 1u64;
                for element in elements {
                    let layout = self.ensure_layout(element, stack, source_span)?;
                    let layout = &self.layouts[layout.index()];
                    alignment = alignment.max(layout.alignment);
                    offset = align_up(offset, layout.alignment, source_span)?;
                    offset = offset.checked_add(layout.size_bytes).ok_or_else(|| {
                        FrontendFailure::elaboration(
                            source_span,
                            "tuple layout size overflows `u64`",
                        )
                    })?;
                }
                (
                    align_up(offset, alignment, source_span)?,
                    alignment,
                    Vec::new(),
                    None,
                )
            }
            HirTypeKind::Struct { fields: field_ids } => {
                let mut offset = 0u64;
                let mut alignment = 1u64;
                let mut layouts = Vec::with_capacity(field_ids.len());
                for field_id in field_ids {
                    let field = self.fields.get(field_id.index()).cloned().ok_or_else(|| {
                        FrontendFailure::elaboration(source_span, "struct field is missing")
                    })?;
                    let field_layout = self.ensure_layout(field.ty, stack, field.span)?;
                    let field_layout = &self.layouts[field_layout.index()];
                    alignment = alignment.max(field_layout.alignment);
                    offset = align_up(offset, field_layout.alignment, field.span)?;
                    layouts.push(HirFieldLayout {
                        field: field.id,
                        offset_bytes: offset,
                    });
                    offset = offset.checked_add(field_layout.size_bytes).ok_or_else(|| {
                        FrontendFailure::elaboration(
                            field.span,
                            "struct layout size overflows `u64`",
                        )
                    })?;
                }
                (
                    align_up(offset, alignment, source_span)?,
                    alignment,
                    layouts,
                    None,
                )
            }
            HirTypeKind::Enum {
                variants: variant_ids,
            } => {
                let mut payload_alignment = 1u64;
                let mut payload_size = 0u64;
                let mut cases = Vec::with_capacity(variant_ids.len());
                for variant_id in variant_ids {
                    let variant = self
                        .variants
                        .get(variant_id.index())
                        .filter(|variant| variant.id == variant_id)
                        .cloned()
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(source_span, "enum variant is missing")
                        })?;
                    let mut offset = 0u64;
                    let mut case_alignment = 1u64;
                    let mut field_layouts = Vec::with_capacity(variant.fields.len());
                    for field_id in variant.fields {
                        let field =
                            self.fields.get(field_id.index()).cloned().ok_or_else(|| {
                                FrontendFailure::elaboration(
                                    source_span,
                                    "enum variant field is missing",
                                )
                            })?;
                        let field_layout = self.ensure_layout(field.ty, stack, field.span)?;
                        let field_layout = &self.layouts[field_layout.index()];
                        case_alignment = case_alignment.max(field_layout.alignment);
                        offset = align_up(offset, field_layout.alignment, field.span)?;
                        field_layouts.push(HirFieldLayout {
                            field: field.id,
                            offset_bytes: offset,
                        });
                        offset = offset.checked_add(field_layout.size_bytes).ok_or_else(|| {
                            FrontendFailure::elaboration(
                                field.span,
                                "enum payload layout size overflows `u64`",
                            )
                        })?;
                    }
                    payload_alignment = payload_alignment.max(case_alignment);
                    payload_size =
                        payload_size.max(align_up(offset, case_alignment, variant.span)?);
                    cases.push((variant.id, field_layouts));
                }
                let tag_size_bytes = 1u64;
                let tag_alignment = 1u64;
                let payload_offset_bytes =
                    align_up(tag_size_bytes, payload_alignment, source_span)?;
                let alignment = tag_alignment.max(payload_alignment);
                let size_bytes = align_up(
                    payload_offset_bytes
                        .checked_add(payload_size)
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(
                                source_span,
                                "enum layout size overflows `u64`",
                            )
                        })?,
                    alignment,
                    source_span,
                )?;
                (
                    size_bytes,
                    alignment,
                    Vec::new(),
                    Some(HirVariantLayout {
                        tag_size_bytes,
                        tag_alignment,
                        cases: cases
                            .into_iter()
                            .map(|(variant, fields)| HirVariantCaseLayout {
                                variant,
                                payload_offset_bytes,
                                fields,
                            })
                            .collect(),
                    }),
                )
            }
            HirTypeKind::Own { .. } => (
                self.data_layout.pointer_size_bytes,
                self.data_layout.pointer_alignment,
                Vec::new(),
                None,
            ),
            _ => {
                return Err(FrontendFailure::elaboration(
                    source_span,
                    "surface aggregate element has no concrete supported layout",
                ));
            }
        };
        stack.pop();
        let id = HirLayoutId::new(
            u32::try_from(self.layouts.len())
                .map_err(|_| FrontendFailure::elaboration(source_span, "too many HIR layouts"))?,
        );
        self.layouts.push(HirLayout {
            id,
            ty,
            size_bytes,
            alignment,
            abi: if matches!(
                self.type_definition(ty).map(|definition| &definition.kind),
                Some(HirTypeKind::Own { .. })
            ) {
                HirAbiClass::Scalar
            } else if size_bytes == 0 {
                HirAbiClass::Ignore
            } else {
                HirAbiClass::Aggregate
            },
            fields,
            variants,
        });
        let definition = self
            .types
            .get_mut(ty.index())
            .ok_or_else(|| FrontendFailure::elaboration(source_span, "type is missing"))?;
        definition.layout = Some(id);
        Ok(id)
    }

    fn is_aggregate(&self, ty: HirTypeId) -> bool {
        matches!(
            self.type_definition(ty).map(|definition| &definition.kind),
            Some(
                HirTypeKind::Array { .. }
                    | HirTypeKind::Tuple(_)
                    | HirTypeKind::Struct { .. }
                    | HirTypeKind::Enum { .. }
            )
        )
    }

    fn elaborate_root_block(
        &mut self,
        block: &AstBlock,
        parameters: &[super::AstParameter],
    ) -> Result<(HirBlock, Vec<HirLocalId>), FrontendFailure> {
        self.scopes.push(ScopeFrame {
            id: ROOT_SCOPE,
            bindings: BTreeMap::new(),
            locals: Vec::new(),
        });
        let mut parameter_ids = Vec::with_capacity(parameters.len());
        for (index, parameter) in parameters.iter().enumerate() {
            if self
                .scopes
                .last()
                .is_some_and(|scope| scope.bindings.contains_key(&parameter.name))
            {
                return Err(FrontendFailure::elaboration(
                    parameter.span,
                    "a parameter name must be unique within its function",
                ));
            }
            let ty = self.function_declarations
                [self.current_function.expect("function body").index()]
            .signature
            .parameters[index];
            let allocation = if self.is_pointer(ty) {
                let identity = self.next_allocation;
                self.next_allocation = self.next_allocation.checked_add(1).ok_or_else(|| {
                    FrontendFailure::elaboration(parameter.span, "too many pointer parameters")
                })?;
                Some(identity)
            } else {
                None
            };
            parameter_ids.push(self.declare_local(
                &parameter.name,
                false,
                SemanticValue { ty, allocation },
                parameter.span,
            )?);
        }
        let result = self.elaborate_statements(&block.statements);
        let frame = self.scopes.pop().expect("root scope was pushed");
        let statements = result?;
        Ok((
            HirBlock {
                scope: ROOT_SCOPE,
                locals: frame.locals,
                statements,
                span: block.span,
            },
            parameter_ids,
        ))
    }

    fn elaborate_block(
        &mut self,
        block: &AstBlock,
        fixed_scope: Option<HirScopeId>,
    ) -> Result<HirBlock, FrontendFailure> {
        let scope = match fixed_scope {
            Some(scope) => scope,
            None => {
                let scope = HirScopeId::new(self.next_scope);
                self.next_scope = self.next_scope.checked_add(1).ok_or_else(|| {
                    FrontendFailure::elaboration(block.span, "too many lexical scopes")
                })?;
                scope
            }
        };
        self.scopes.push(ScopeFrame {
            id: scope,
            bindings: BTreeMap::new(),
            locals: Vec::new(),
        });

        let result = self.elaborate_statements(&block.statements);
        let frame = self.scopes.pop().expect("block scope was pushed");
        let statements = result?;
        if frame.id != scope {
            return Err(FrontendFailure::elaboration(
                block.span,
                "lexical scope stack is inconsistent",
            ));
        }
        Ok(HirBlock {
            scope,
            locals: frame.locals,
            statements,
            span: block.span,
        })
    }

    /// Keep recursive block traversal out of iterator adapter/Result collection
    /// frames, which accumulate on the host stack in debug builds.
    fn elaborate_statements(
        &mut self,
        statements: &[AstStatement],
    ) -> Result<Vec<HirStatement>, FrontendFailure> {
        let mut elaborated = Vec::with_capacity(statements.len());
        for statement in statements {
            elaborated.push(self.elaborate_statement(statement)?);
        }
        Ok(elaborated)
    }

    fn elaborate_statement(
        &mut self,
        statement: &AstStatement,
    ) -> Result<HirStatement, FrontendFailure> {
        let kind = match &statement.kind {
            AstStatementKind::Assert { expression } => {
                self.elaborate_assert(expression, statement.span)?
            }
            AstStatementKind::Declare { name, annotation } => {
                if self
                    .scopes
                    .last()
                    .is_some_and(|scope| scope.bindings.contains_key(name))
                {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "a binding cannot be defined twice in the same lexical scope",
                    ));
                }
                let ty = self.resolve_ast_type(annotation, statement.span)?;
                self.ensure_layout(ty, &mut Vec::new(), statement.span)?;
                if !types::supports_deferred_local_shape(&self.types, &self.fields, ty) {
                    return Err(FrontendFailure::unsupported(
                        statement.span,
                        "deferred locals require a scalar or fixed variant-free aggregate with trivial, Own or Reference leaves",
                    ));
                }
                if self
                    .resolved_layout(ty)
                    .is_none_or(|layout| layout.size_bytes == 0 || layout.size_bytes > 4096)
                {
                    return Err(FrontendFailure::unsupported(
                        statement.span,
                        "deferred local storage must have a nonzero size within the 4096 byte runtime profile",
                    ));
                }
                let local = self.declare_local(
                    name,
                    true,
                    SemanticValue {
                        ty,
                        allocation: None,
                    },
                    statement.span,
                )?;
                HirStatementKind::Declare { local }
            }
            AstStatementKind::Let {
                name,
                mutable,
                annotation,
                value,
            } => {
                if self
                    .scopes
                    .last()
                    .is_some_and(|scope| scope.bindings.contains_key(name))
                {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "a binding cannot be defined twice in the same lexical scope",
                    ));
                }
                let (value, semantic_value) = self.elaborate_expression(value)?;
                if let Some(annotation) = annotation {
                    let annotation_matches = match annotation {
                        AstType::RawU64 => {
                            matches!(self.type_definition(semantic_value.ty).map(|ty| &ty.kind),
                            Some(HirTypeKind::RawPointer { pointee, .. }) if *pointee == self.core_types.u64_)
                        }
                        AstType::Reference { pointee, mutable } => {
                            let mutability = if *mutable {
                                HirMutability::Mutable
                            } else {
                                HirMutability::Const
                            };
                            let pointee = match pointee.as_ref() {
                                AstType::Slice { element } => {
                                    let element = self.resolve_ast_type(element, statement.span)?;
                                    self.intern_slice_type(element, mutability, statement.span)?
                                }
                                _ => self.resolve_ast_type(pointee, statement.span)?,
                            };
                            matches!(
                                self.type_definition(semantic_value.ty)
                                    .map(|definition| &definition.kind),
                                Some(HirTypeKind::Reference {
                                    pointee: actual,
                                    mutability: actual_mutability,
                                    ..
                                }) if *actual == pointee && *actual_mutability == mutability
                            )
                        }
                        _ => {
                            self.resolve_ast_type(annotation, statement.span)? == semantic_value.ty
                        }
                    };
                    if !annotation_matches {
                        return Err(FrontendFailure::elaboration(
                            statement.span,
                            "local type annotation does not match its initializer",
                        ));
                    }
                }
                if semantic_value.ty == self.core_types.unit {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "unit call results cannot be bound to a local",
                    ));
                }
                if *mutable
                    && semantic_value.allocation.is_some()
                    && matches!(
                        self.type_definition(semantic_value.ty).map(|ty| &ty.kind),
                        Some(HirTypeKind::RawPointer { .. })
                    )
                {
                    return Err(FrontendFailure::unsupported(
                        statement.span,
                        "mutable raw bindings require authority-free addresses",
                    ));
                }
                if *mutable && !self.is_surface_assignable(semantic_value.ty) {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "mutable surface bindings require a trivial assignable value",
                    ));
                }
                let local = self.declare_local(name, *mutable, semantic_value, statement.span)?;
                HirStatementKind::Let { local, value }
            }
            AstStatementKind::Assign { destination, value } => {
                let (destination, destination_value) =
                    self.elaborate_place(destination, true, false)?;
                let (value, semantic) = self.elaborate_expression(value)?;
                // Owning SSA bindings remain immutable. Only addressed
                // resource leaves participate in refill/replacement; the
                // canonical resource effects independently consume authority.
                let owning_leaf = !destination.projections.is_empty()
                    && matches!(
                        self.type_definition(destination_value.ty)
                            .map(|ty| &ty.kind),
                        Some(HirTypeKind::Own { .. })
                    );
                if !self.types_compatible(semantic.ty, destination_value.ty)
                    || (!owning_leaf
                        && (semantic.allocation.is_some()
                            || !self.is_surface_assignable(semantic.ty)))
                {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "assignment value does not match the mutable destination",
                    ));
                }
                HirStatementKind::Assign { destination, value }
            }
            AstStatementKind::Store { pointer, value } => {
                let pointer_binding = self.lookup(pointer, statement.span)?;
                if !matches!(
                    self.type_definition(pointer_binding.value.ty)
                        .map(|definition| &definition.kind),
                    Some(
                        HirTypeKind::Own { .. }
                            | HirTypeKind::RawPointer {
                                mutability: HirMutability::Mutable,
                                ..
                            }
                            | HirTypeKind::Reference {
                                mutability: HirMutability::Mutable,
                                ..
                            }
                    )
                ) {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "store destination must be a writable pointer",
                    ));
                }
                let Some(pointee) = self.pointee_type(pointer_binding.value.ty) else {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "store destination must be a pointer",
                    ));
                };
                let (value, semantic_value) = self.elaborate_expression(value)?;
                if semantic_value.ty != pointee
                    || semantic_value.allocation.is_some()
                    || !self.is_surface_assignable(semantic_value.ty)
                {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "store value does not match the writable pointer destination",
                    ));
                }
                HirStatementKind::Assign {
                    destination: dereferenced_local_place(
                        pointer_binding.local,
                        pointee,
                        statement.span,
                    ),
                    value,
                }
            }
            AstStatementKind::Free { pointer } => {
                let pointer_binding = self.lookup(pointer, statement.span)?;
                if !matches!(
                    self.type_definition(pointer_binding.value.ty)
                        .map(|definition| &definition.kind),
                    Some(HirTypeKind::Own { .. })
                ) {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "`free` requires an owner pointer at allocation base",
                    ));
                }
                HirStatementKind::Free {
                    pointer: pointer_binding.local,
                }
            }
            AstStatementKind::Return { value } => {
                let value = match value {
                    Some(expression) => {
                        let (expression, semantic_value) = self.elaborate_expression(expression)?;
                        let compatible_borrow = self
                            .reference_compatible(semantic_value.ty, self.return_type)
                            && match (
                                self.reference_region(self.return_type),
                                self.reference_region(semantic_value.ty),
                                self.current_function,
                            ) {
                                (Some(result), Some(source), Some(owner)) => {
                                    self.region_contains(owner, result, source)
                                }
                                _ => false,
                            };
                        let compatible_inferred_source =
                            self.current_function.is_some_and(|owner| {
                                let signature =
                                    &self.function_declarations[owner.index()].signature;
                                let Some(relation) = signature.borrow_result else {
                                    return false;
                                };
                                if !self.reference_compatible(semantic_value.ty, self.return_type) {
                                    return false;
                                }
                                let (Some(actual), Some(source)) = (
                                    self.reference_region(semantic_value.ty),
                                    signature
                                        .parameters
                                        .get(relation.parameter as usize)
                                        .and_then(|ty| self.reference_region(*ty)),
                                ) else {
                                    return false;
                                };
                                self.region_contains(owner, actual, source)
                            });
                        if semantic_value.ty != self.return_type
                            && !compatible_borrow
                            && !compatible_inferred_source
                        {
                            return Err(FrontendFailure::elaboration(
                                statement.span,
                                "return value does not match the function return type",
                            ));
                        }
                        Some(expression)
                    }
                    None if self.return_type == self.core_types.unit => None,
                    None => {
                        return Err(FrontendFailure::elaboration(
                            statement.span,
                            "return value does not match the function return type",
                        ));
                    }
                };
                HirStatementKind::Return { value }
            }
            AstStatementKind::Block { block } => HirStatementKind::Block {
                block: self.elaborate_block(block, None)?,
            },
            AstStatementKind::If {
                condition,
                then_block,
                else_block,
            } => {
                let (condition, semantic) = self.elaborate_expression(condition)?;
                if semantic.ty != self.core_types.bool_ || semantic.allocation.is_some() {
                    return Err(FrontendFailure::elaboration(
                        condition.span,
                        "`if` condition must have type `bool`",
                    ));
                }
                HirStatementKind::If {
                    condition,
                    then_block: self.elaborate_block(then_block, None)?,
                    else_block: else_block
                        .as_ref()
                        .map(|block| self.elaborate_block(block, None))
                        .transpose()?,
                }
            }
            AstStatementKind::While { condition, body } => {
                let loop_id = HirLoopId::new(self.next_loop);
                self.next_loop = self.next_loop.checked_add(1).ok_or_else(|| {
                    FrontendFailure::elaboration(statement.span, "too many structured loops")
                })?;
                let (condition, semantic) = self.elaborate_expression(condition)?;
                if semantic.ty != self.core_types.bool_ || semantic.allocation.is_some() {
                    return Err(FrontendFailure::elaboration(
                        condition.span,
                        "`while` condition must have type `bool`",
                    ));
                }
                self.active_loops.push(loop_id);
                let body = self.elaborate_block(body, None);
                if self.active_loops.pop() != Some(loop_id) {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "loop target stack is inconsistent",
                    ));
                }
                HirStatementKind::While {
                    loop_id,
                    condition,
                    body: body?,
                }
            }
            AstStatementKind::For {
                binding,
                binding_span,
                start,
                end,
                body,
            } => {
                let loop_id = self.fresh_loop_id(statement.span)?;
                let (start, start_semantic) = self.elaborate_expression(start)?;
                let (end, end_semantic) = self.elaborate_expression(end)?;
                if !matches!(
                    self.type_definition(start_semantic.ty).map(|ty| &ty.kind),
                    Some(HirTypeKind::Integer(
                        HirIntegerType::U64 | HirIntegerType::Usize
                    ))
                ) || end_semantic.ty != start_semantic.ty
                    || start_semantic.allocation.is_some()
                    || end_semantic.allocation.is_some()
                {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "for-loop range bounds must have the same u64 or usize type",
                    ));
                }
                self.active_loops.push(loop_id);
                let body_and_pattern =
                    self.elaborate_for_body(body, binding, *binding_span, start_semantic.ty);
                if self.active_loops.pop() != Some(loop_id) {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "loop target stack is inconsistent",
                    ));
                }
                let (body, pattern) = body_and_pattern?;
                HirStatementKind::For {
                    loop_id,
                    pattern,
                    source: HirForSource::IntegerRange {
                        start,
                        end,
                        inclusive: false,
                        item_type: start_semantic.ty,
                    },
                    body,
                }
            }
            AstStatementKind::Match { scrutinee, arms } => {
                let (scrutinee, semantic) = self.elaborate_expression(scrutinee)?;
                let enum_variants = match self
                    .type_definition(semantic.ty)
                    .map(|definition| &definition.kind)
                {
                    Some(HirTypeKind::Enum { variants }) => Some(variants.clone()),
                    _ => None,
                };
                if enum_variants.is_some()
                    && !matches!(
                        &scrutinee.kind,
                        HirExpressionKind::Read { place, .. } if place.projections.is_empty()
                    )
                {
                    return Err(FrontendFailure::unsupported(
                        scrutinee.span,
                        "stage 6.5.9 enum match scrutinees must be local values",
                    ));
                }
                if semantic.ty != self.core_types.bool_
                    && semantic.ty != self.core_types.u64_
                    && enum_variants.is_none()
                {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "match values must have scalar or enum type",
                    ));
                }
                let mut hir_arms = Vec::with_capacity(arms.len());
                let mut covered_false = false;
                let mut covered_true = false;
                let mut covered_variants = BTreeSet::new();
                let mut exhaustive = false;
                for arm in arms {
                    if exhaustive {
                        return Err(FrontendFailure::elaboration(
                            arm.span,
                            "match arm is unreachable after exhaustive unguarded patterns",
                        ));
                    }
                    if enum_variants.is_some() && arm.guard.is_some() {
                        return Err(FrontendFailure::unsupported(
                            arm.span,
                            "stage 6.5.9 enum match guards remain gated",
                        ));
                    }
                    let scope = HirScopeId::new(self.next_scope);
                    self.next_scope = self.next_scope.checked_add(1).ok_or_else(|| {
                        FrontendFailure::elaboration(arm.span, "too many lexical scopes")
                    })?;
                    self.scopes.push(ScopeFrame {
                        id: scope,
                        bindings: BTreeMap::new(),
                        locals: Vec::new(),
                    });
                    let result = (|| {
                        let pattern =
                            self.elaborate_match_pattern(&arm.pattern, semantic.ty, false)?;
                        let guard = arm
                            .guard
                            .as_ref()
                            .map(|guard| {
                                let (guard, value) = self.elaborate_expression(guard)?;
                                if value.ty != self.core_types.bool_ || value.allocation.is_some() {
                                    return Err(FrontendFailure::elaboration(
                                        guard.span,
                                        "match guard must have type `bool`",
                                    ));
                                }
                                Ok(guard)
                            })
                            .transpose()?;
                        let statements = self.elaborate_statements(&arm.body.statements)?;
                        Ok((pattern, guard, statements))
                    })();
                    let frame = self.scopes.pop().expect("match-arm scope was pushed");
                    let (pattern, guard, statements) = result?;
                    let body = HirBlock {
                        scope,
                        locals: frame.locals,
                        statements,
                        span: arm.body.span,
                    };
                    if guard.is_none() {
                        match &pattern.kind {
                            HirPatternKind::Wildcard => exhaustive = true,
                            HirPatternKind::Bool(false) => covered_false = true,
                            HirPatternKind::Bool(true) => covered_true = true,
                            HirPatternKind::Variant { variant, .. } => {
                                covered_variants.insert(*variant);
                            }
                            HirPatternKind::Integer(_)
                            | HirPatternKind::Binding { .. }
                            | HirPatternKind::Tuple(_) => {}
                        }
                        exhaustive |=
                            semantic.ty == self.core_types.bool_ && covered_false && covered_true;
                        exhaustive |= enum_variants.as_ref().is_some_and(|variants| {
                            variants
                                .iter()
                                .all(|variant| covered_variants.contains(variant))
                        });
                    }
                    hir_arms.push(HirMatchArm {
                        pattern,
                        guard,
                        body,
                        span: arm.span,
                    });
                }
                if !exhaustive {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "match patterns are not exhaustively covered",
                    ));
                }
                HirStatementKind::Match {
                    scrutinee,
                    arms: hir_arms,
                }
            }
            AstStatementKind::Break | AstStatementKind::Continue => {
                let target = self.active_loops.last().copied().ok_or_else(|| {
                    FrontendFailure::elaboration(statement.span, "loop exit has no enclosing loop")
                })?;
                if matches!(&statement.kind, AstStatementKind::Break) {
                    HirStatementKind::Break { target }
                } else {
                    HirStatementKind::Continue { target }
                }
            }
            AstStatementKind::Evaluate { expression } => {
                let (expression, semantic) = self.elaborate_expression(expression)?;
                if semantic.ty != self.core_types.unit {
                    return Err(FrontendFailure::elaboration(
                        statement.span,
                        "discarded direct calls must currently return unit",
                    ));
                }
                HirStatementKind::Evaluate { expression }
            }
        };
        Ok(HirStatement {
            id: node_identity::UNASSIGNED_NODE_ID,
            kind,
            span: statement.span,
        })
    }

    fn fresh_loop_id(&mut self, source_span: ByteSpan) -> Result<HirLoopId, FrontendFailure> {
        let loop_id = HirLoopId::new(self.next_loop);
        self.next_loop = self.next_loop.checked_add(1).ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "too many structured loops")
        })?;
        Ok(loop_id)
    }

    fn elaborate_for_body(
        &mut self,
        block: &AstBlock,
        binding: &str,
        binding_span: ByteSpan,
        item_type: HirTypeId,
    ) -> Result<(HirBlock, HirPattern), FrontendFailure> {
        let scope = HirScopeId::new(self.next_scope);
        self.next_scope = self
            .next_scope
            .checked_add(1)
            .ok_or_else(|| FrontendFailure::elaboration(block.span, "too many lexical scopes"))?;
        self.scopes.push(ScopeFrame {
            id: scope,
            bindings: BTreeMap::new(),
            locals: Vec::new(),
        });
        let local = self.declare_local(
            binding,
            false,
            SemanticValue {
                ty: item_type,
                allocation: None,
            },
            binding_span,
        )?;
        let result = self.elaborate_statements(&block.statements);
        let frame = self.scopes.pop().expect("for-loop scope was pushed");
        let statements = result?;
        if frame.id != scope || frame.locals.first().copied() != Some(local) {
            return Err(FrontendFailure::elaboration(
                block.span,
                "for-loop lexical scope is inconsistent",
            ));
        }
        Ok((
            HirBlock {
                scope,
                locals: frame.locals,
                statements,
                span: block.span,
            },
            HirPattern {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirPatternKind::Binding {
                    local,
                    mode: HirUseMode::Copy,
                },
                ty: item_type,
                span: binding_span,
            },
        ))
    }

    fn elaborate_match_pattern(
        &mut self,
        pattern: &AstPattern,
        scrutinee_type: HirTypeId,
        payload_position: bool,
    ) -> Result<HirPattern, FrontendFailure> {
        let kind = match &pattern.kind {
            AstPatternKind::Wildcard => HirPatternKind::Wildcard,
            AstPatternKind::Binding(name) if payload_position => {
                if matches!(
                    self.type_definition(scrutinee_type).map(|ty| &ty.kind),
                    Some(HirTypeKind::Unit)
                ) {
                    return Err(FrontendFailure::unsupported(
                        pattern.span,
                        "unit payload bindings remain gated; use `_`",
                    ));
                }
                let local = self.declare_local(
                    name,
                    false,
                    SemanticValue {
                        ty: scrutinee_type,
                        allocation: None,
                    },
                    pattern.span,
                )?;
                HirPatternKind::Binding {
                    local,
                    mode: self.use_mode(scrutinee_type, pattern.span)?,
                }
            }
            AstPatternKind::Binding(_) => {
                return Err(FrontendFailure::unsupported(
                    pattern.span,
                    "top-level match bindings remain gated",
                ));
            }
            AstPatternKind::Integer(value) if scrutinee_type == self.core_types.u64_ => {
                if payload_position {
                    return Err(FrontendFailure::unsupported(
                        pattern.span,
                        "stage 6.5.9 payload patterns may only bind or ignore fields",
                    ));
                }
                HirPatternKind::Integer(*value)
            }
            AstPatternKind::Bool(value) if scrutinee_type == self.core_types.bool_ => {
                if payload_position {
                    return Err(FrontendFailure::unsupported(
                        pattern.span,
                        "stage 6.5.9 payload patterns may only bind or ignore fields",
                    ));
                }
                HirPatternKind::Bool(*value)
            }
            AstPatternKind::Integer(_) => {
                return Err(FrontendFailure::elaboration(
                    pattern.span,
                    "integer pattern requires a `u64` match value",
                ));
            }
            AstPatternKind::Bool(_) => {
                return Err(FrontendFailure::elaboration(
                    pattern.span,
                    "boolean pattern requires a `bool` match value",
                ));
            }
            AstPatternKind::Variant {
                enum_name,
                variant_name,
                payload,
            } => {
                if payload_position {
                    return Err(FrontendFailure::unsupported(
                        pattern.span,
                        "nested enum payload patterns remain gated",
                    ));
                }
                let owner = self
                    .type_names
                    .get(&self.key(enum_name))
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(pattern.span, "pattern enum is not defined")
                    })?;
                if owner != scrutinee_type {
                    return Err(FrontendFailure::elaboration(
                        pattern.span,
                        "variant pattern owner does not match the scrutinee type",
                    ));
                }
                let variant_id = self
                    .variant_names
                    .get(&(owner, variant_name.clone()))
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            pattern.span,
                            "variant pattern does not belong to its enum",
                        )
                    })?;
                let variant = self
                    .variants
                    .get(variant_id.index())
                    .filter(|variant| variant.id == variant_id)
                    .cloned()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(pattern.span, "enum variant is missing")
                    })?;
                let style = self
                    .variant_styles
                    .get(&variant_id)
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            pattern.span,
                            "enum variant surface shape is missing",
                        )
                    })?;
                let fields = match (style, payload) {
                    (SurfaceVariantStyle::Unit, AstVariantPatternPayload::Unit) => Vec::new(),
                    (SurfaceVariantStyle::Tuple, AstVariantPatternPayload::Tuple(patterns)) => {
                        if patterns.len() != variant.fields.len() {
                            return Err(FrontendFailure::elaboration(
                                pattern.span,
                                "tuple variant pattern has the wrong arity",
                            ));
                        }
                        let mut fields = Vec::with_capacity(patterns.len());
                        for (field_id, field_pattern) in variant.fields.iter().zip(patterns) {
                            let field =
                                self.fields.get(field_id.index()).cloned().ok_or_else(|| {
                                    FrontendFailure::elaboration(
                                        field_pattern.span,
                                        "enum field is missing",
                                    )
                                })?;
                            fields.push(self.elaborate_match_pattern(
                                field_pattern,
                                field.ty,
                                true,
                            )?);
                        }
                        fields
                    }
                    (SurfaceVariantStyle::Named, AstVariantPatternPayload::Named(patterns)) => {
                        let mut by_field = BTreeMap::new();
                        for field_pattern in patterns {
                            let field = variant
                                .fields
                                .iter()
                                .filter_map(|id| self.fields.get(id.index()))
                                .find(|field| field.name == field_pattern.name)
                                .cloned()
                                .ok_or_else(|| {
                                    FrontendFailure::elaboration(
                                        field_pattern.span,
                                        "named pattern field does not belong to its variant",
                                    )
                                })?;
                            if by_field.contains_key(&field.id) {
                                return Err(FrontendFailure::elaboration(
                                    field_pattern.span,
                                    "named pattern field appears more than once",
                                ));
                            }
                            let child = self.elaborate_match_pattern(
                                &field_pattern.pattern,
                                field.ty,
                                true,
                            )?;
                            by_field.insert(field.id, child);
                        }
                        if by_field.len() != variant.fields.len() {
                            return Err(FrontendFailure::elaboration(
                                pattern.span,
                                "named variant pattern must mention every field exactly once",
                            ));
                        }
                        variant
                            .fields
                            .iter()
                            .map(|field| {
                                by_field.remove(field).ok_or_else(|| {
                                    FrontendFailure::elaboration(
                                        pattern.span,
                                        "named variant pattern field is missing",
                                    )
                                })
                            })
                            .collect::<Result<Vec<_>, _>>()?
                    }
                    _ => {
                        return Err(FrontendFailure::elaboration(
                            pattern.span,
                            "variant pattern payload shape does not match its declaration",
                        ));
                    }
                };
                HirPatternKind::Variant {
                    variant: variant_id,
                    fields,
                }
            }
        };
        Ok(HirPattern {
            id: node_identity::UNASSIGNED_NODE_ID,
            kind,
            ty: scrutinee_type,
            span: pattern.span,
        })
    }

    fn elaborate_expression(
        &mut self,
        expression: &AstExpression,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        match &expression.kind {
            AstExpressionKind::GenericCall { .. }
            | AstExpressionKind::GenericStruct { .. }
            | AstExpressionKind::ConstRepeat { .. } => Err(FrontendFailure::elaboration(
                expression.span,
                "unresolved generic expression reached typed HIR",
            )),
            AstExpressionKind::Integer {
                value,
                explicit_usize,
                ..
            } => {
                let semantic = SemanticValue {
                    ty: if *explicit_usize {
                        self.core_types.usize_
                    } else {
                        self.core_types.u64_
                    },
                    allocation: None,
                };
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::Integer(*value),
                        ty: semantic.ty,
                        span: expression.span,
                    },
                    semantic,
                ))
            }
            AstExpressionKind::Bool(value) => {
                let semantic = SemanticValue {
                    ty: self.core_types.bool_,
                    allocation: None,
                };
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::Bool(*value),
                        ty: semantic.ty,
                        span: expression.span,
                    },
                    semantic,
                ))
            }
            AstExpressionKind::Unit => {
                let semantic = SemanticValue {
                    ty: self.core_types.unit,
                    allocation: None,
                };
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::Unit,
                        ty: semantic.ty,
                        span: expression.span,
                    },
                    semantic,
                ))
            }
            AstExpressionKind::Name(name) => {
                let binding = self.lookup(name, expression.span)?;
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::Read {
                            place: Box::new(local_place(
                                binding.local,
                                binding.value.ty,
                                expression.span,
                            )),
                            mode: self.use_mode(binding.value.ty, expression.span)?,
                        },
                        ty: binding.value.ty,
                        span: expression.span,
                    },
                    binding.value,
                ))
            }
            AstExpressionKind::Place(place) => {
                let (place, semantic) = self.elaborate_place(place, false, false)?;
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::Read {
                            place: Box::new(place),
                            mode: self.use_mode(semantic.ty, expression.span)?,
                        },
                        ty: semantic.ty,
                        span: expression.span,
                    },
                    semantic,
                ))
            }
            AstExpressionKind::Tuple(elements) => {
                let mut hir_elements = Vec::with_capacity(elements.len());
                let mut types = Vec::with_capacity(elements.len());
                for element in elements {
                    let (element, semantic) = self.elaborate_expression(element)?;
                    if !self.is_surface_value_type(semantic.ty) {
                        return Err(FrontendFailure::unsupported(
                            element.span,
                            "tuple element type is not supported by surface ownership lowering",
                        ));
                    }
                    types.push(semantic.ty);
                    hir_elements.push(element);
                }
                let ty = self.intern_aggregate_type(HirTypeKind::Tuple(types), expression.span)?;
                self.require_surface_aggregate(ty, expression.span)?;
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::TupleConstructor {
                            elements: hir_elements,
                        },
                        ty,
                        span: expression.span,
                    },
                    SemanticValue {
                        ty,
                        allocation: None,
                    },
                ))
            }
            AstExpressionKind::Array(elements) => {
                let Some(first) = elements.first() else {
                    return Err(FrontendFailure::elaboration(
                        expression.span,
                        "an empty array literal has no inferred element type",
                    ));
                };
                let (first, first_semantic) = self.elaborate_expression(first)?;
                if !self.is_surface_value_type(first_semantic.ty) {
                    return Err(FrontendFailure::unsupported(
                        first.span,
                        "array element type is not supported by surface ownership lowering",
                    ));
                }
                let mut hir_elements = Vec::with_capacity(elements.len());
                hir_elements.push(first);
                for element in &elements[1..] {
                    let (element, semantic) = self.elaborate_expression(element)?;
                    if !self.types_compatible(semantic.ty, first_semantic.ty) {
                        return Err(FrontendFailure::elaboration(
                            element.span,
                            "array literal elements must have one exact type",
                        ));
                    }
                    hir_elements.push(element);
                }
                let length = u64::try_from(hir_elements.len()).map_err(|_| {
                    FrontendFailure::elaboration(expression.span, "array literal is too large")
                })?;
                let ty = self.intern_aggregate_type(
                    HirTypeKind::Array {
                        element: first_semantic.ty,
                        length,
                    },
                    expression.span,
                )?;
                self.require_surface_aggregate(ty, expression.span)?;
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::ArrayConstructor {
                            elements: hir_elements,
                        },
                        ty,
                        span: expression.span,
                    },
                    SemanticValue {
                        ty,
                        allocation: None,
                    },
                ))
            }
            AstExpressionKind::ArrayRepeat { value, length } => {
                let (value, semantic) = self.elaborate_expression(value)?;
                if !self.is_surface_copy_type(semantic.ty) {
                    return Err(FrontendFailure::unsupported(
                        value.span,
                        "array repetition requires a proven trivial copy element",
                    ));
                }
                let ty = self.intern_aggregate_type(
                    HirTypeKind::Array {
                        element: semantic.ty,
                        length: *length,
                    },
                    expression.span,
                )?;
                self.require_surface_aggregate(ty, expression.span)?;
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::ArrayRepeatConstructor {
                            value: Box::new(value),
                            length: *length,
                        },
                        ty,
                        span: expression.span,
                    },
                    SemanticValue {
                        ty,
                        allocation: None,
                    },
                ))
            }
            AstExpressionKind::Struct { name, fields } => {
                let ty = self
                    .type_names
                    .get(&self.key(name))
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(expression.span, "struct type is not defined")
                    })?;
                let HirTypeKind::Struct {
                    fields: expected_fields,
                } = self
                    .type_definition(ty)
                    .map(|definition| definition.kind.clone())
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(expression.span, "struct type is missing")
                    })?
                else {
                    return Err(FrontendFailure::elaboration(
                        expression.span,
                        "literal owner is not a struct type",
                    ));
                };
                let mut seen = BTreeSet::new();
                let mut initializers = Vec::with_capacity(fields.len());
                for initializer in fields {
                    let field = expected_fields
                        .iter()
                        .filter_map(|id| self.fields.get(id.index()))
                        .find(|field| field.name == initializer.name)
                        .cloned()
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(
                                initializer.span,
                                "struct literal field does not belong to its owner",
                            )
                        })?;
                    if !seen.insert(field.id) {
                        return Err(FrontendFailure::elaboration(
                            initializer.span,
                            "struct literal field is initialized more than once",
                        ));
                    }
                    let (value, semantic) = self.elaborate_expression(&initializer.value)?;
                    if !self.types_compatible(semantic.ty, field.ty) {
                        return Err(FrontendFailure::elaboration(
                            initializer.value.span,
                            "struct literal field value has the wrong type",
                        ));
                    }
                    initializers.push(HirFieldInitializer {
                        field: field.id,
                        value,
                    });
                }
                if seen.len() != expected_fields.len() {
                    return Err(FrontendFailure::elaboration(
                        expression.span,
                        "struct literal must initialize every field exactly once",
                    ));
                }
                self.require_surface_aggregate(ty, expression.span)?;
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::StructConstructor {
                            fields: initializers,
                        },
                        ty,
                        span: expression.span,
                    },
                    SemanticValue {
                        ty,
                        allocation: None,
                    },
                ))
            }
            AstExpressionKind::EnumVariant {
                enum_name,
                variant_name,
                payload,
            } => {
                let ty = self
                    .type_names
                    .get(&self.key(enum_name))
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(expression.span, "enum type is not defined")
                    })?;
                if !matches!(
                    self.type_definition(ty).map(|definition| &definition.kind),
                    Some(HirTypeKind::Enum { .. })
                ) {
                    return Err(FrontendFailure::elaboration(
                        expression.span,
                        "variant constructor owner is not an enum type",
                    ));
                }
                let variant_id = self
                    .variant_names
                    .get(&(ty, variant_name.clone()))
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            expression.span,
                            "enum variant does not belong to its owner",
                        )
                    })?;
                let variant = self
                    .variants
                    .get(variant_id.index())
                    .filter(|variant| variant.id == variant_id)
                    .cloned()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(expression.span, "enum variant is missing")
                    })?;
                let style = self
                    .variant_styles
                    .get(&variant_id)
                    .copied()
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            expression.span,
                            "enum variant surface shape is missing",
                        )
                    })?;
                let initializers = match (style, payload) {
                    (SurfaceVariantStyle::Unit, AstVariantInitializer::Unit) => Vec::new(),
                    (SurfaceVariantStyle::Tuple, AstVariantInitializer::Tuple(values)) => {
                        if values.len() != variant.fields.len() {
                            return Err(FrontendFailure::elaboration(
                                expression.span,
                                "tuple variant constructor has the wrong arity",
                            ));
                        }
                        let mut initializers = Vec::with_capacity(values.len());
                        for (field_id, value) in variant.fields.iter().zip(values) {
                            let field =
                                self.fields.get(field_id.index()).cloned().ok_or_else(|| {
                                    FrontendFailure::elaboration(
                                        value.span,
                                        "enum field is missing",
                                    )
                                })?;
                            let (value, semantic) = self.elaborate_expression(value)?;
                            if !self.types_compatible(semantic.ty, field.ty) {
                                return Err(FrontendFailure::elaboration(
                                    value.span,
                                    "tuple variant field value has the wrong type",
                                ));
                            }
                            initializers.push(HirFieldInitializer {
                                field: field.id,
                                value,
                            });
                        }
                        initializers
                    }
                    (SurfaceVariantStyle::Named, AstVariantInitializer::Named(values)) => {
                        let mut seen = BTreeSet::new();
                        let mut initializers = Vec::with_capacity(values.len());
                        for initializer in values {
                            let field = variant
                                .fields
                                .iter()
                                .filter_map(|id| self.fields.get(id.index()))
                                .find(|field| field.name == initializer.name)
                                .cloned()
                                .ok_or_else(|| {
                                    FrontendFailure::elaboration(
                                        initializer.span,
                                        "named variant field does not belong to its variant",
                                    )
                                })?;
                            if !seen.insert(field.id) {
                                return Err(FrontendFailure::elaboration(
                                    initializer.span,
                                    "named variant field is initialized more than once",
                                ));
                            }
                            let (value, semantic) =
                                self.elaborate_expression(&initializer.value)?;
                            if !self.types_compatible(semantic.ty, field.ty) {
                                return Err(FrontendFailure::elaboration(
                                    value.span,
                                    "named variant field value has the wrong type",
                                ));
                            }
                            initializers.push(HirFieldInitializer {
                                field: field.id,
                                value,
                            });
                        }
                        if seen.len() != variant.fields.len() {
                            return Err(FrontendFailure::elaboration(
                                expression.span,
                                "named variant constructor must initialize every field exactly once",
                            ));
                        }
                        initializers
                    }
                    _ => {
                        return Err(FrontendFailure::elaboration(
                            expression.span,
                            "enum constructor payload shape does not match its variant",
                        ));
                    }
                };
                self.require_surface_aggregate(ty, expression.span)?;
                Ok((
                    HirExpression {
                        id: node_identity::UNASSIGNED_NODE_ID,
                        kind: HirExpressionKind::EnumConstructor {
                            variant: variant_id,
                            fields: initializers,
                        },
                        ty,
                        span: expression.span,
                    },
                    SemanticValue {
                        ty,
                        allocation: None,
                    },
                ))
            }
            AstExpressionKind::Allocate {
                element_type,
                count,
            } => self.elaborate_allocate(element_type, *count, expression.span),
            AstExpressionKind::Load { pointer } => self.elaborate_load(pointer, expression.span),
            AstExpressionKind::Borrow { place, mutable } => {
                self.elaborate_borrow(place, *mutable, expression.span)
            }
            AstExpressionKind::RawAddress { place, mutable } => {
                self.elaborate_raw_address(place, *mutable, expression.span)
            }
            AstExpressionKind::Add(operands) => self.elaborate_add(operands, expression.span),
            AstExpressionKind::Compare {
                predicate,
                left,
                right,
                operation_span,
            } => self.elaborate_compare(*predicate, left, right, *operation_span, expression.span),
            AstExpressionKind::Call { callee, arguments } => {
                self.elaborate_call(callee, arguments, expression.span)
            }
        }
    }

    fn elaborate_call(
        &mut self,
        callee: &str,
        arguments: &[AstExpression],
        source_span: ByteSpan,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        if callee == "ptr_byte_distance" && !self.function_names.contains_key(&self.key(callee)) {
            if self
                .scopes
                .iter()
                .any(|scope| scope.bindings.contains_key(callee))
            {
                return Err(FrontendFailure::elaboration(
                    source_span,
                    "local ptr_byte_distance is not callable",
                ));
            }
            let [begin, end] = arguments else {
                return Err(FrontendFailure::elaboration(
                    source_span,
                    "ptr_byte_distance expects two raw pointers",
                ));
            };
            let (begin, begin_value) = self.elaborate_expression(begin)?;
            let (end, end_value) = self.elaborate_expression(end)?;
            if !self.matching_raw_pointers(begin_value.ty, end_value.ty) {
                return Err(FrontendFailure::elaboration(
                    source_span,
                    "ptr_byte_distance requires raw pointers with the same pointee type",
                ));
            }
            let ty = self.core_types.usize_;
            return Ok((
                HirExpression {
                    id: node_identity::UNASSIGNED_NODE_ID,
                    kind: HirExpressionKind::PointerDistance {
                        begin: Box::new(begin),
                        end: Box::new(end),
                    },
                    ty,
                    span: source_span,
                },
                SemanticValue {
                    ty,
                    allocation: None,
                },
            ));
        }
        if callee == "len" && !self.function_names.contains_key(&self.key(callee)) {
            if self
                .scopes
                .iter()
                .any(|scope| scope.bindings.contains_key(callee))
            {
                return Err(FrontendFailure::elaboration(
                    source_span,
                    "local len is not callable",
                ));
            }
            let [argument] = arguments else {
                return Err(FrontendFailure::elaboration(
                    source_span,
                    "len expects one array or slice place",
                ));
            };
            let place = match &argument.kind {
                AstExpressionKind::Name(name) => {
                    let binding = self.lookup(name, argument.span)?;
                    local_place(binding.local, binding.value.ty, argument.span)
                }
                AstExpressionKind::Place(place) => self.elaborate_place(place, false, false)?.0,
                _ => {
                    return Err(FrontendFailure::unsupported(
                        argument.span,
                        "len expects an array or slice place",
                    ));
                }
            };
            let kind = self.type_definition(place.ty).map(|ty| &ty.kind);
            let valid = matches!(
                kind,
                Some(HirTypeKind::Array { .. } | HirTypeKind::Slice { .. })
            ) || matches!(kind, Some(HirTypeKind::Reference { pointee, .. }) if matches!(self.type_definition(*pointee).map(|ty| &ty.kind), Some(HirTypeKind::Array { .. } | HirTypeKind::Slice { .. })));
            if !valid {
                return Err(FrontendFailure::elaboration(
                    argument.span,
                    "len requires an array or slice, without implicit raw/Own dereference",
                ));
            }
            let ty = self.core_types.usize_;
            return Ok((
                HirExpression {
                    id: node_identity::UNASSIGNED_NODE_ID,
                    kind: HirExpressionKind::Length {
                        place: Box::new(place),
                    },
                    ty,
                    span: source_span,
                },
                SemanticValue {
                    ty,
                    allocation: None,
                },
            ));
        }
        let callee_id = self
            .function_names
            .get(&self.key(callee))
            .copied()
            .ok_or_else(|| {
                FrontendFailure::elaboration(source_span, "direct call target is not defined")
            })?;
        let declaration = self
            .function_declarations
            .get(callee_id.index())
            .filter(|declaration| declaration.id == callee_id)
            .cloned()
            .ok_or_else(|| {
                FrontendFailure::elaboration(source_span, "direct call target is missing")
            })?;
        if arguments.len() != declaration.signature.parameters.len() {
            return Err(FrontendFailure::elaboration(
                source_span,
                "direct call argument count does not match the callee signature",
            ));
        }
        let mut hir_arguments = Vec::with_capacity(arguments.len());
        for (argument, expected) in arguments.iter().zip(&declaration.signature.parameters) {
            let (argument, semantic) = self.elaborate_expression(argument)?;
            if !self.reference_compatible(semantic.ty, *expected) {
                return Err(FrontendFailure::elaboration(
                    argument.span,
                    "direct call argument type does not match the callee signature",
                ));
            }
            hir_arguments.push(argument);
        }
        self.check_call_region_constraints(&declaration, &hir_arguments, source_span)?;
        let ty = if let Some(relation) = declaration.signature.borrow_result {
            if relation.projection == crate::BorrowProjection::Whole {
                hir_arguments[relation.parameter as usize].ty
            } else {
                let HirTypeKind::Reference {
                    pointee,
                    mutability,
                    ..
                } = self.types[declaration.signature.return_type.index()].kind
                else {
                    return Err(FrontendFailure::elaboration(
                        source_span,
                        "projected borrow result is not a reference",
                    ));
                };
                let source_region = self
                    .reference_region(hir_arguments[relation.parameter as usize].ty)
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            source_span,
                            "projected borrow argument has no region",
                        )
                    })?;
                self.intern_reference_type(pointee, mutability, source_region, source_span)?
            }
        } else if !declaration.signature.borrow_result_alternatives.is_empty() {
            let owner = self.current_function.expect("call inside a function");
            let scope = self.scopes.last().map(|scope| scope.id).ok_or_else(|| {
                FrontendFailure::elaboration(source_span, "call has no active scope")
            })?;
            let HirTypeKind::Reference {
                pointee,
                mutability,
                ..
            } = &self.types[declaration.signature.return_type.index()].kind
            else {
                return Err(FrontendFailure::elaboration(
                    source_span,
                    "conditional borrow result is not a reference",
                ));
            };
            let region = HirRegionId::new(
                u32::try_from(self.regions.len())
                    .map_err(|_| FrontendFailure::elaboration(source_span, "too many regions"))?,
            );
            self.regions.push(HirRegion {
                id: region,
                owner: HirRegionOwner::Function(owner),
                // The call result is an interface-derived region bounded by
                // every possible source, not a lexical loan creation site.
                origin: HirRegionOrigin::Inferred { scope },
                span: source_span,
            });
            for source in declaration
                .signature
                .borrow_result_alternatives
                .iter()
                .map(|alternative| alternative.relation.parameter)
                .collect::<BTreeSet<_>>()
            {
                let source_region = self
                    .reference_region(hir_arguments[source as usize].ty)
                    .ok_or_else(|| {
                        FrontendFailure::elaboration(
                            source_span,
                            "conditional borrow argument has no region",
                        )
                    })?;
                self.region_constraints.push(HirRegionConstraint {
                    id: HirRegionConstraintId::new(self.region_constraints.len() as u32),
                    owner,
                    subregion: region,
                    superregion: source_region,
                    span: source_span,
                });
            }
            self.intern_reference_type(*pointee, *mutability, region, source_span)?
        } else {
            declaration.signature.return_type
        };
        let allocation = if self.is_pointer(ty) {
            let identity = self.next_allocation;
            self.next_allocation = self.next_allocation.checked_add(1).ok_or_else(|| {
                FrontendFailure::elaboration(source_span, "too many pointer-producing expressions")
            })?;
            Some(identity)
        } else {
            None
        };
        Ok((
            HirExpression {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirExpressionKind::Call(HirCall {
                    callee: declaration.id,
                    instantiated_signature: declaration.signature.clone(),
                    arguments: hir_arguments,
                    contract: declaration.contract,
                    calling_convention: declaration.signature.calling_convention,
                }),
                ty,
                span: source_span,
            },
            SemanticValue { ty, allocation },
        ))
    }

    fn matching_raw_pointers(&self, left: HirTypeId, right: HirTypeId) -> bool {
        matches!((self.type_definition(left).map(|t| &t.kind), self.type_definition(right).map(|t| &t.kind)),
            (Some(HirTypeKind::RawPointer { pointee: a, .. }), Some(HirTypeKind::RawPointer { pointee: b, .. })) if a == b)
    }

    fn elaborate_compare(
        &mut self,
        predicate: AstIntegerPredicate,
        left: &AstExpression,
        right: &AstExpression,
        operation_span: ByteSpan,
        source_span: ByteSpan,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        let (left, left_value) = self.elaborate_expression(left)?;
        let (right, right_value) = self.elaborate_expression(right)?;
        if !self.matching_raw_pointers(left_value.ty, right_value.ty)
            && (left_value.ty != right_value.ty
                || (left_value.ty != self.core_types.u64_
                    && left_value.ty != self.core_types.usize_)
                || left_value.allocation.is_some()
                || right_value.allocation.is_some())
        {
            return Err(FrontendFailure::elaboration(
                operation_span,
                "comparison requires matching integers or raw pointers with the same pointee type",
            ));
        }
        let semantic = SemanticValue {
            ty: self.core_types.bool_,
            allocation: None,
        };
        Ok((
            HirExpression {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirExpressionKind::Compare {
                    predicate: match predicate {
                        AstIntegerPredicate::Equal => HirIntegerPredicate::Equal,
                        AstIntegerPredicate::NotEqual => HirIntegerPredicate::NotEqual,
                        AstIntegerPredicate::LessThan => HirIntegerPredicate::LessThan,
                        AstIntegerPredicate::LessOrEqual => HirIntegerPredicate::LessOrEqual,
                        AstIntegerPredicate::GreaterThan => HirIntegerPredicate::GreaterThan,
                        AstIntegerPredicate::GreaterOrEqual => HirIntegerPredicate::GreaterOrEqual,
                    },
                    left: Box::new(left),
                    right: Box::new(right),
                    operation_span,
                },
                ty: semantic.ty,
                span: source_span,
            },
            semantic,
        ))
    }

    fn elaborate_allocate(
        &mut self,
        element: &AstType,
        count: u64,
        source_span: ByteSpan,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        let element_type = self.resolve_ast_type(element, source_span)?;
        if !types::supports_builtin_allocation(
            &self.types,
            &self.fields,
            &self.variants,
            element_type,
            count,
        ) {
            return Err(FrontendFailure::unsupported(
                source_span,
                "alloc requires u64 storage or one fixed aggregate with supported resource leaves; repeated aggregates and nested tagged payloads are not supported",
            ));
        }
        self.ensure_layout(element_type, &mut Vec::new(), source_span)?;
        let element_layout = self.resolved_layout(element_type).ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "missing allocation element layout")
        })?;
        let element_size = element_layout.size_bytes;
        let alignment = element_layout.alignment;
        if element_type != self.core_types.u64_ && (element_size == 0 || element_size > 4096) {
            return Err(FrontendFailure::unsupported(
                source_span,
                "heap aggregate storage must have a nonzero size within the 4096 byte runtime profile",
            ));
        }
        let size_bytes = count.checked_mul(element_size).ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "allocation byte size overflows `u64`")
        })?;
        let allocation = self.next_allocation;
        self.next_allocation = self.next_allocation.checked_add(1).ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "too many Core0 allocations")
        })?;
        let ty = self.intern_aggregate_type(
            HirTypeKind::Own {
                pointee: element_type,
            },
            source_span,
        )?;
        self.ensure_layout(ty, &mut Vec::new(), source_span)?;
        let semantic = SemanticValue {
            ty,
            allocation: Some(allocation),
        };
        Ok((
            HirExpression {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirExpressionKind::Allocate {
                    element_type,
                    element_count: count,
                    size_bytes,
                    alignment,
                },
                ty,
                span: source_span,
            },
            semantic,
        ))
    }

    fn elaborate_load(
        &self,
        pointer: &str,
        source_span: ByteSpan,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        let pointer = self.lookup(pointer, source_span)?;
        let Some(pointee) = self.pointee_type(pointer.value.ty) else {
            return Err(FrontendFailure::elaboration(
                source_span,
                "load source must be a pointer",
            ));
        };
        let semantic = SemanticValue {
            ty: pointee,
            allocation: None,
        };
        Ok((
            HirExpression {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirExpressionKind::Read {
                    place: Box::new(dereferenced_local_place(
                        pointer.local,
                        pointee,
                        source_span,
                    )),
                    mode: self.use_mode(pointee, source_span)?,
                },
                ty: semantic.ty,
                span: source_span,
            },
            semantic,
        ))
    }

    fn elaborate_raw_address(
        &mut self,
        place: &AstPlace,
        mutable: bool,
        source_span: ByteSpan,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        let base = self.lookup(&place.base, place.span)?;
        let kind = self.type_definition(base.value.ty).map(|ty| &ty.kind);
        if matches!(kind, Some(HirTypeKind::RawPointer { .. }))
            || (place.projections.is_empty()
                && matches!(
                    kind,
                    Some(HirTypeKind::Own { .. } | HirTypeKind::Reference { .. })
                ))
        {
            return Err(FrontendFailure::unsupported(
                source_span,
                "raw address requires sized local storage or an Own/reference pointee; raw-pointer recovery and pointer-binding storage remain gated",
            ));
        }
        let (place, semantic) = self.elaborate_place(place, mutable, false)?;
        if matches!(
            self.type_definition(semantic.ty).map(|ty| &ty.kind),
            Some(HirTypeKind::Slice { .. })
        ) {
            return Err(FrontendFailure::unsupported(
                source_span,
                "unsized raw slice addresses remain gated; address a sized element instead",
            ));
        }
        let mutability = if mutable {
            HirMutability::Mutable
        } else {
            HirMutability::Const
        };
        let ty = self.intern_aggregate_type(
            HirTypeKind::RawPointer {
                pointee: semantic.ty,
                mutability,
            },
            source_span,
        )?;
        if self.types[ty.index()].layout.is_none() {
            let layout =
                HirLayoutId::new(u32::try_from(self.layouts.len()).map_err(|_| {
                    FrontendFailure::elaboration(source_span, "too many HIR layouts")
                })?);
            self.types[ty.index()].layout = Some(layout);
            self.layouts.push(HirLayout {
                id: layout,
                ty,
                size_bytes: self.data_layout.pointer_size_bytes,
                alignment: self.data_layout.pointer_alignment,
                abi: HirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            });
        }
        Ok((
            HirExpression {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirExpressionKind::RawAddress {
                    place: Box::new(place),
                    mutability,
                },
                ty,
                span: source_span,
            },
            SemanticValue {
                ty,
                allocation: None,
            },
        ))
    }

    fn elaborate_borrow(
        &mut self,
        place: &AstPlace,
        mutable: bool,
        source_span: ByteSpan,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        let base = self.lookup(&place.base, place.span)?;
        let reborrow_parent_region = match self
            .type_definition(base.value.ty)
            .map(|definition| &definition.kind)
        {
            Some(HirTypeKind::Reference { region, .. })
                if matches!(
                    place.projections.first(),
                    Some(
                        AstPlaceProjection::Dereference { .. }
                            | AstPlaceProjection::Field { .. }
                            | AstPlaceProjection::TupleElement { .. }
                            | AstPlaceProjection::Index { .. }
                            | AstPlaceProjection::Slice { .. }
                    )
                ) =>
            {
                Some(*region)
            }
            Some(HirTypeKind::Reference { .. }) => {
                return Err(FrontendFailure::unsupported(
                    source_span,
                    "borrowing a reference binding itself is distinct from reborrowing its dereference and remains unsupported",
                ));
            }
            Some(HirTypeKind::RawPointer { .. }) => {
                return Err(FrontendFailure::unsupported(
                    source_span,
                    "recovering a safe reference from a raw pointer remains gated to the explicit system/trusted boundary in stages 10.1/10.3",
                ));
            }
            _ => None,
        };
        if place.projections.is_empty()
            && matches!(
                self.type_definition(base.value.ty)
                    .map(|definition| &definition.kind),
                Some(HirTypeKind::Own { .. } | HirTypeKind::RawPointer { .. })
            )
        {
            return Err(FrontendFailure::unsupported(
                source_span,
                "borrowing a pointer binding itself is not in the local borrow slice; borrow its dereference instead",
            ));
        }

        let mutability = if mutable {
            HirMutability::Mutable
        } else {
            HirMutability::Const
        };
        let (place, semantic) = self.elaborate_place(place, mutable, true)?;
        let owner = self.current_function.ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "borrow expression has no owning function")
        })?;
        let scope = self.scopes.last().map(|scope| scope.id).ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "borrow expression has no lexical scope")
        })?;
        let region = HirRegionId::new(u32::try_from(self.regions.len()).map_err(|_| {
            FrontendFailure::elaboration(source_span, "too many inferred borrow regions")
        })?);
        self.regions.push(HirRegion {
            id: region,
            owner: HirRegionOwner::Function(owner),
            origin: HirRegionOrigin::Inferred { scope },
            span: source_span,
        });
        if let Some(superregion) = reborrow_parent_region {
            let id = HirRegionConstraintId::new(
                u32::try_from(self.region_constraints.len()).map_err(|_| {
                    FrontendFailure::elaboration(
                        source_span,
                        "too many inferred borrow-region constraints",
                    )
                })?,
            );
            self.region_constraints.push(HirRegionConstraint {
                id,
                owner,
                subregion: region,
                superregion,
                span: source_span,
            });
        }
        let reference = self.intern_reference_type(semantic.ty, mutability, region, source_span)?;
        let semantic = SemanticValue {
            ty: reference,
            allocation: None,
        };
        Ok((
            HirExpression {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirExpressionKind::Borrow {
                    place: Box::new(place),
                    mutability,
                    region,
                },
                ty: reference,
                span: source_span,
            },
            semantic,
        ))
    }

    fn elaborate_add(
        &mut self,
        operands: &[AstExpression],
        source_span: ByteSpan,
    ) -> Result<(HirExpression, SemanticValue), FrontendFailure> {
        if operands.len() < 2 {
            return Err(FrontendFailure::elaboration(
                source_span,
                "addition requires at least two operands",
            ));
        }
        let first = operands.first().ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "addition requires at least two operands")
        })?;
        let (mut first_hir, first_value) = self.elaborate_expression(first)?;

        if self.is_pointer(first_value.ty) {
            if matches!(
                self.type_definition(first_value.ty).map(|ty| &ty.kind),
                Some(HirTypeKind::Reference { .. })
            ) {
                return Err(FrontendFailure::unsupported(
                    source_span,
                    "byte offset requires a raw pointer; form an address with `&raw *reference` first",
                ));
            }
            if matches!(
                self.type_definition(first_value.ty).map(|ty| &ty.kind),
                Some(HirTypeKind::Own { .. })
            ) {
                let HirExpressionKind::Read {
                    place,
                    mode: HirUseMode::Move,
                } = first_hir.kind
                else {
                    return Err(FrontendFailure::unsupported(
                        first.span,
                        "raw address calculation from an owner currently requires a place",
                    ));
                };
                if !place.projections.is_empty() {
                    return Err(FrontendFailure::unsupported(
                        first.span,
                        "raw address calculation from a stored owner remains gated",
                    ));
                }
                first_hir.kind = HirExpressionKind::OwnerAddress { place };
                first_hir.ty = self.core_types.raw_mut_u64;
            }
            let mut offsets = Vec::with_capacity(operands.len() - 1);
            for (index, right) in operands[1..].iter().enumerate() {
                let AstExpressionKind::Integer {
                    value: delta_bytes,
                    explicit_u64: false,
                    explicit_usize: false,
                } = right.kind
                else {
                    return Err(FrontendFailure::elaboration(
                        right.span,
                        "pointer offset must be an unsuffixed integer literal",
                    ));
                };
                offsets.push(HirPointerOffset {
                    delta_bytes,
                    span: operation_span(
                        first.span,
                        right.span,
                        source_span,
                        index,
                        operands.len(),
                    ),
                });
            }
            let semantic = SemanticValue {
                ty: first_hir.ty,
                allocation: first_value.allocation,
            };
            return Ok((
                HirExpression {
                    id: node_identity::UNASSIGNED_NODE_ID,
                    kind: HirExpressionKind::PointerOffset {
                        base: Box::new(first_hir),
                        offsets,
                    },
                    ty: semantic.ty,
                    span: source_span,
                },
                semantic,
            ));
        }

        let mut hir_operands = Vec::with_capacity(operands.len());
        hir_operands.push(first_hir);
        let mut operation_spans = Vec::with_capacity(operands.len() - 1);
        for (index, right) in operands[1..].iter().enumerate() {
            let (right_hir, right_value) = self.elaborate_expression(right)?;
            let operation_span =
                operation_span(first.span, right.span, source_span, index, operands.len());
            if ![self.core_types.u64_, self.core_types.usize_].contains(&first_value.ty)
                || right_value.ty != first_value.ty
            {
                return Err(FrontendFailure::elaboration(
                    operation_span,
                    "addition requires matching u64 or usize operands, or a pointer and byte offset",
                ));
            }
            hir_operands.push(right_hir);
            operation_spans.push(operation_span);
        }
        let semantic = SemanticValue {
            ty: first_value.ty,
            allocation: None,
        };
        Ok((
            HirExpression {
                id: node_identity::UNASSIGNED_NODE_ID,
                kind: HirExpressionKind::WordAdd {
                    operands: hir_operands,
                    operation_spans,
                },
                ty: semantic.ty,
                span: source_span,
            },
            semantic,
        ))
    }

    fn elaborate_place(
        &mut self,
        place: &AstPlace,
        write: bool,
        allow_slice: bool,
    ) -> Result<(HirPlace, SemanticValue), FrontendFailure> {
        let binding = self.lookup(&place.base, place.span)?;
        let local = self
            .locals
            .get(binding.local.index())
            .filter(|local| local.id == binding.local)
            .ok_or_else(|| {
                FrontendFailure::elaboration(place.span, "place base local is missing")
            })?;
        let mut current = binding.value.ty;
        let auto_dereference = matches!(
            self.type_definition(current)
                .map(|definition| &definition.kind),
            Some(HirTypeKind::Reference { .. } | HirTypeKind::Own { .. })
        ) && matches!(
            place.projections.first(),
            Some(AstPlaceProjection::Field { .. } | AstPlaceProjection::TupleElement { .. })
        ) || (matches!(
            place.projections.first(),
            Some(AstPlaceProjection::Index { .. })
        ) && self.pointee_type(current).is_some_and(|pointee| {
            matches!(
                self.type_definition(pointee).map(|ty| &ty.kind),
                Some(HirTypeKind::Array { .. })
            )
        }));
        let explicit_dereference = matches!(
            place.projections.first(),
            Some(AstPlaceProjection::Dereference { .. })
        );
        let through_slice_reference = matches!(
            place.projections.first(),
            Some(AstPlaceProjection::Index { .. } | AstPlaceProjection::Slice { .. })
        ) && matches!(
            self.type_definition(current).map(|definition| &definition.kind),
            Some(HirTypeKind::Reference { pointee, .. })
                if matches!(
                    self.type_definition(*pointee).map(|definition| &definition.kind),
                    Some(HirTypeKind::Slice { .. })
                )
        );
        if write {
            if explicit_dereference || auto_dereference || through_slice_reference {
                let writable = match self
                    .type_definition(current)
                    .map(|definition| &definition.kind)
                {
                    Some(HirTypeKind::Own { .. }) => true,
                    Some(
                        HirTypeKind::RawPointer { mutability, .. }
                        | HirTypeKind::Reference { mutability, .. },
                    ) => *mutability == HirMutability::Mutable,
                    _ => false,
                };
                if !writable {
                    return Err(FrontendFailure::elaboration(
                        place.span,
                        "assignment destination is not writable through this pointer",
                    ));
                }
            } else if !local.mutable {
                return Err(FrontendFailure::elaboration(
                    place.span,
                    "assignment destination is not mutable",
                ));
            }
        }
        let mut projections =
            Vec::with_capacity(place.projections.len() + usize::from(auto_dereference));
        if auto_dereference {
            let pointee = self.pointee_type(current).ok_or_else(|| {
                FrontendFailure::elaboration(place.span, "reference pointee type is missing")
            })?;
            projections.push(HirProjection {
                kind: HirProjectionKind::Dereference,
                result_type: pointee,
                span: place.span,
            });
            current = pointee;
        }
        for projection in &place.projections {
            let (kind, result_type, projection_span) = match projection {
                AstPlaceProjection::Dereference { span } => {
                    if !projections.is_empty() {
                        return Err(FrontendFailure::unsupported(
                            *span,
                            "only a leading named-pointer dereference is supported in a place",
                        ));
                    }
                    let pointee = self.pointee_type(current).ok_or_else(|| {
                        FrontendFailure::elaboration(*span, "dereference requires a pointer")
                    })?;
                    (HirProjectionKind::Dereference, pointee, *span)
                }
                AstPlaceProjection::Field { name, span } => {
                    let HirTypeKind::Struct { fields } = self
                        .type_definition(current)
                        .map(|definition| definition.kind.clone())
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(*span, "place field owner is missing")
                        })?
                    else {
                        return Err(FrontendFailure::elaboration(
                            *span,
                            "named field projection requires a struct",
                        ));
                    };
                    let field = fields
                        .iter()
                        .filter_map(|field| self.fields.get(field.index()))
                        .find(|field| field.name == *name)
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(
                                *span,
                                "struct field does not exist on this owner",
                            )
                        })?;
                    (
                        HirProjectionKind::Field { field: field.id },
                        field.ty,
                        *span,
                    )
                }
                AstPlaceProjection::TupleElement { index, span } => {
                    let HirTypeKind::Tuple(elements) = self
                        .type_definition(current)
                        .map(|definition| definition.kind.clone())
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(*span, "tuple place owner is missing")
                        })?
                    else {
                        return Err(FrontendFailure::elaboration(
                            *span,
                            "numeric field projection requires a tuple",
                        ));
                    };
                    let result = usize::try_from(*index)
                        .ok()
                        .and_then(|index| elements.get(index))
                        .copied()
                        .ok_or_else(|| {
                            FrontendFailure::elaboration(
                                *span,
                                "tuple element index is out of bounds",
                            )
                        })?;
                    (
                        HirProjectionKind::TupleElement { index: *index },
                        result,
                        *span,
                    )
                }
                AstPlaceProjection::Index { index, span } => {
                    let (element, length) = match self
                        .type_definition(current)
                        .map(|definition| definition.kind.clone())
                    {
                        Some(HirTypeKind::Array { element, length }) => (element, Some(length)),
                        Some(HirTypeKind::Slice { element, .. }) => (element, None),
                        Some(HirTypeKind::Reference { pointee, .. }) => {
                            match self
                                .type_definition(pointee)
                                .map(|definition| &definition.kind)
                            {
                                Some(HirTypeKind::Slice { element, .. }) => (*element, None),
                                _ => {
                                    return Err(FrontendFailure::elaboration(
                                        *span,
                                        "index projection requires an array or slice view",
                                    ));
                                }
                            }
                        }
                        _ => {
                            return Err(FrontendFailure::elaboration(
                                *span,
                                "index projection requires an array or slice view",
                            ));
                        }
                    };
                    let kind = if let AstExpressionKind::Integer { value, .. } = index.kind {
                        if length.is_some_and(|length| value >= length) {
                            return Err(FrontendFailure::elaboration(
                                index.span,
                                "constant array index is out of bounds",
                            ));
                        }
                        HirProjectionKind::ConstantIndex { index: value }
                    } else {
                        let (index, semantic) = self.elaborate_expression(index)?;
                        if semantic.ty != self.core_types.usize_ || semantic.allocation.is_some() {
                            return Err(FrontendFailure::elaboration(
                                index.span,
                                "dynamic array index must have type `usize`",
                            ));
                        }
                        HirProjectionKind::DynamicIndex {
                            index: Box::new(index),
                        }
                    };
                    (kind, element, *span)
                }
                AstPlaceProjection::Slice { start, end, span } => {
                    if !allow_slice {
                        return Err(FrontendFailure::unsupported(
                            *span,
                            "a slice range must be created by `&place[start..end]` or `&mut place[start..end]`",
                        ));
                    }
                    let (element, writable) = match self
                        .type_definition(current)
                        .map(|definition| definition.kind.clone())
                    {
                        Some(HirTypeKind::Array { element, .. }) => (element, true),
                        Some(HirTypeKind::Slice {
                            element,
                            mutability,
                        }) => (element, mutability == HirMutability::Mutable),
                        Some(HirTypeKind::Reference {
                            pointee,
                            mutability,
                            ..
                        }) => match self
                            .type_definition(pointee)
                            .map(|definition| &definition.kind)
                        {
                            Some(HirTypeKind::Slice { element, .. }) => {
                                (*element, mutability == HirMutability::Mutable)
                            }
                            _ => {
                                return Err(FrontendFailure::elaboration(
                                    *span,
                                    "slice projection requires an array or slice view",
                                ));
                            }
                        },
                        _ => {
                            return Err(FrontendFailure::elaboration(
                                *span,
                                "slice projection requires an array or slice view",
                            ));
                        }
                    };
                    if write && !writable {
                        return Err(FrontendFailure::elaboration(
                            *span,
                            "mutable subslice requires a mutable source view",
                        ));
                    }
                    let lower_bound =
                        |this: &mut Self,
                         bound: &AstExpression|
                         -> Result<HirExpression, FrontendFailure> {
                            let (mut expression, semantic) = this.elaborate_expression(bound)?;
                            if semantic.allocation.is_some() {
                                return Err(FrontendFailure::elaboration(
                                    bound.span,
                                    "slice bounds must have type `usize`",
                                ));
                            }
                            if semantic.ty == this.core_types.u64_
                                && matches!(
                                    bound.kind,
                                    AstExpressionKind::Integer {
                                        explicit_u64: false,
                                        ..
                                    }
                                )
                            {
                                expression.ty = this.core_types.usize_;
                            } else if semantic.ty != this.core_types.usize_ {
                                return Err(FrontendFailure::elaboration(
                                    bound.span,
                                    "slice bounds must have type `usize`",
                                ));
                            }
                            Ok(expression)
                        };
                    let start = start
                        .as_deref()
                        .map(|bound| lower_bound(self, bound).map(Box::new))
                        .transpose()?;
                    let end = end
                        .as_deref()
                        .map(|bound| lower_bound(self, bound).map(Box::new))
                        .transpose()?;
                    let mutability = if write {
                        HirMutability::Mutable
                    } else {
                        HirMutability::Const
                    };
                    let result = self.intern_slice_type(element, mutability, *span)?;
                    (HirProjectionKind::Slice { start, end }, result, *span)
                }
            };
            projections.push(HirProjection {
                kind,
                result_type,
                span: projection_span,
            });
            current = result_type;
        }
        Ok((
            HirPlace {
                id: node_identity::UNASSIGNED_NODE_ID,
                base: HirPlaceBase::Local(binding.local),
                projections,
                ty: current,
                span: place.span,
            },
            SemanticValue {
                ty: current,
                allocation: None,
            },
        ))
    }

    fn require_surface_aggregate(
        &mut self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let layout = self.ensure_layout(ty, &mut Vec::new(), source_span)?;
        let layout = &self.layouts[layout.index()];
        if layout.size_bytes == 0 || layout.size_bytes > 4096 {
            return Err(FrontendFailure::unsupported(
                source_span,
                "surface aggregate size is outside the 1..=4096 byte budget",
            ));
        }
        if !self.is_surface_value_type(ty) {
            return Err(FrontendFailure::unsupported(
                source_span,
                "surface aggregate contains an unsupported ownership payload",
            ));
        }
        Ok(())
    }

    fn is_surface_assignable(&self, ty: HirTypeId) -> bool {
        ty != self.core_types.unit
            && (self.is_surface_copy_type(ty)
                || matches!(
                    self.type_definition(ty).map(|definition| &definition.kind),
                    Some(HirTypeKind::Reference { .. } | HirTypeKind::RawPointer { .. })
                )
                || (self.is_aggregate(ty) && self.is_surface_value_type(ty)))
    }

    fn is_surface_copy_type(&self, ty: HirTypeId) -> bool {
        self.current_type_capabilities(ty)
            .is_some_and(crate::TypeCapabilities::pointer_free_trivial)
            && !matches!(
                self.type_definition(ty).map(|definition| &definition.kind),
                Some(HirTypeKind::Function(_) | HirTypeKind::Never)
            )
    }

    fn is_variant_free_owning_aggregate(&self, ty: HirTypeId) -> bool {
        let capabilities = self.current_type_capabilities(ty);
        if !capabilities.is_some_and(|capabilities| {
            capabilities.value == crate::ValueCapability::MoveOnly
                && capabilities.drop == crate::DropCapability::BuiltinDrop
                && capabilities.contains_resource
                && capabilities.size == crate::SizeCapability::Sized
        }) {
            return false;
        }
        self.is_variant_free_abi_type(ty)
    }

    fn is_variant_free_abi_type(&self, ty: HirTypeId) -> bool {
        match self.type_definition(ty).map(|definition| &definition.kind) {
            Some(
                HirTypeKind::Unit
                | HirTypeKind::Bool
                | HirTypeKind::Integer(_)
                | HirTypeKind::Own { .. },
            ) => true,
            Some(HirTypeKind::Array { element, .. }) => self.is_variant_free_abi_type(*element),
            Some(HirTypeKind::Tuple(elements)) => elements
                .iter()
                .all(|element| self.is_variant_free_abi_type(*element)),
            Some(HirTypeKind::Struct { fields }) => fields.iter().all(|field| {
                self.fields
                    .get(field.index())
                    .is_some_and(|field| self.is_variant_free_abi_type(field.ty))
            }),
            Some(
                HirTypeKind::Enum { .. }
                | HirTypeKind::RawPointer { .. }
                | HirTypeKind::Reference { .. }
                | HirTypeKind::Slice { .. }
                | HirTypeKind::Function(_)
                | HirTypeKind::GenericParameter(_)
                | HirTypeKind::Never,
            )
            | None => false,
        }
    }

    fn is_surface_value_type(&self, ty: HirTypeId) -> bool {
        self.current_type_capabilities(ty)
            .is_some_and(|capabilities| {
                capabilities.size == crate::SizeCapability::Sized
                    && capabilities.drop != crate::DropCapability::UserDropGated
            })
            && match self.type_definition(ty).map(|definition| &definition.kind) {
                Some(
                    HirTypeKind::Unit
                    | HirTypeKind::Bool
                    | HirTypeKind::Integer(_)
                    | HirTypeKind::Own { .. }
                    | HirTypeKind::Reference { .. }
                    | HirTypeKind::Array { .. }
                    | HirTypeKind::Tuple(_)
                    | HirTypeKind::Struct { .. }
                    | HirTypeKind::Enum { .. },
                ) => true,
                Some(
                    HirTypeKind::RawPointer { .. }
                    | HirTypeKind::Slice { .. }
                    | HirTypeKind::Function(_)
                    | HirTypeKind::GenericParameter(_)
                    | HirTypeKind::Never,
                )
                | None => false,
            }
    }

    fn use_mode(
        &self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<HirUseMode, FrontendFailure> {
        match self
            .current_type_capabilities(ty)
            .map(|capabilities| capabilities.value)
        {
            Some(crate::ValueCapability::Copy) => Ok(HirUseMode::Copy),
            Some(crate::ValueCapability::MoveOnly) => Ok(HirUseMode::Move),
            None => Err(FrontendFailure::elaboration(
                source_span,
                "value capability cannot be derived for by-value use",
            )),
        }
    }

    fn current_type_capabilities(&self, ty: HirTypeId) -> Option<crate::TypeCapabilities> {
        program::derive_type_capabilities(&self.types, &self.fields, &self.variants, ty)
    }

    fn types_compatible(&self, actual: HirTypeId, expected: HirTypeId) -> bool {
        fn compatible(
            elaborator: &Elaborator,
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
            let result = match (
                elaborator
                    .type_definition(actual)
                    .map(|definition| &definition.kind),
                elaborator
                    .type_definition(expected)
                    .map(|definition| &definition.kind),
            ) {
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
                        && compatible(elaborator, *left, *right, visiting, depth + 1)
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
                        && compatible(elaborator, *left, *right, visiting, depth + 1)
                }
                (Some(HirTypeKind::Tuple(left)), Some(HirTypeKind::Tuple(right))) => {
                    left.len() == right.len()
                        && left.iter().zip(right).all(|(left, right)| {
                            compatible(elaborator, *left, *right, visiting, depth + 1)
                        })
                }
                _ => false,
            };
            visiting.remove(&(actual, expected));
            result
        }

        compatible(self, actual, expected, &mut BTreeSet::new(), 0)
    }

    fn declare_local(
        &mut self,
        name: &str,
        mutable: bool,
        value: SemanticValue,
        declaration_span: ByteSpan,
    ) -> Result<HirLocalId, FrontendFailure> {
        let scope = self.scopes.last().map(|scope| scope.id).ok_or_else(|| {
            FrontendFailure::elaboration(declaration_span, "local has no lexical scope")
        })?;
        let raw_id = u32::try_from(self.locals.len()).map_err(|_| {
            FrontendFailure::elaboration(declaration_span, "too many local bindings")
        })?;
        let id = HirLocalId::new(raw_id);
        let layout = self
            .type_definition(value.ty)
            .and_then(|definition| definition.layout)
            .ok_or_else(|| {
                FrontendFailure::elaboration(declaration_span, "local type has no resolved layout")
            })?;
        self.locals.push(HirLocal {
            id,
            name: name.to_owned(),
            ty: value.ty,
            layout,
            scope,
            mutable,
            declaration_span,
        });
        let frame = self.scopes.last_mut().ok_or_else(|| {
            FrontendFailure::elaboration(declaration_span, "local has no lexical scope")
        })?;
        frame.locals.push(id);
        frame
            .bindings
            .insert(name.to_owned(), Binding { local: id, value });
        Ok(id)
    }

    fn type_definition(&self, id: HirTypeId) -> Option<&HirTypeDefinition> {
        self.types.get(id.index()).filter(|item| item.id == id)
    }

    fn resolved_layout(&self, ty: HirTypeId) -> Option<&HirLayout> {
        let id = self.type_definition(ty)?.layout?;
        self.layouts
            .get(id.index())
            .filter(|layout| layout.id == id)
    }

    fn is_pointer(&self, ty: HirTypeId) -> bool {
        self.pointee_type(ty).is_some()
    }

    fn pointee_type(&self, ty: HirTypeId) -> Option<HirTypeId> {
        match &self.type_definition(ty)?.kind {
            HirTypeKind::Own { pointee }
            | HirTypeKind::RawPointer { pointee, .. }
            | HirTypeKind::Reference { pointee, .. } => Some(*pointee),
            _ => None,
        }
    }

    fn lookup(&self, name: &str, source_span: ByteSpan) -> Result<Binding, FrontendFailure> {
        let Some(binding) = self
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.bindings.get(name).copied())
        else {
            return Err(FrontendFailure::elaboration(
                source_span,
                "name must be defined before it is used",
            ));
        };
        Ok(binding)
    }
}

fn local_place(local: HirLocalId, ty: HirTypeId, source_span: ByteSpan) -> HirPlace {
    HirPlace {
        id: node_identity::UNASSIGNED_NODE_ID,
        base: HirPlaceBase::Local(local),
        projections: Vec::new(),
        ty,
        span: source_span,
    }
}

fn dereferenced_local_place(
    local: HirLocalId,
    pointee: HirTypeId,
    source_span: ByteSpan,
) -> HirPlace {
    HirPlace {
        id: node_identity::UNASSIGNED_NODE_ID,
        base: HirPlaceBase::Local(local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::Dereference,
            result_type: pointee,
            span: source_span,
        }],
        ty: pointee,
        span: source_span,
    }
}

fn type_definition(
    id: HirTypeId,
    name: &str,
    kind: HirTypeKind,
    layout: Option<HirLayoutId>,
) -> HirTypeDefinition {
    HirTypeDefinition {
        id,
        name: Some(name.to_owned()),
        kind,
        generic_parameters: Vec::new(),
        layout,
    }
}

fn layout(
    id: HirLayoutId,
    ty: HirTypeId,
    size_bytes: u64,
    alignment: u64,
    abi: HirAbiClass,
) -> HirLayout {
    HirLayout {
        id,
        ty,
        size_bytes,
        alignment,
        abi,
        fields: Vec::new(),
        variants: None,
    }
}

fn align_up(value: u64, alignment: u64, source_span: ByteSpan) -> Result<u64, FrontendFailure> {
    if !alignment.is_power_of_two() {
        return Err(FrontendFailure::elaboration(
            source_span,
            "aggregate field alignment is invalid",
        ));
    }
    value
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
        .ok_or_else(|| {
            FrontendFailure::elaboration(source_span, "aggregate layout alignment overflows `u64`")
        })
}

fn operation_span(
    first: ByteSpan,
    right: ByteSpan,
    expression: ByteSpan,
    index: usize,
    operand_count: usize,
) -> ByteSpan {
    if index + 2 == operand_count {
        expression
    } else {
        span(first.start(), right.end())
    }
}
