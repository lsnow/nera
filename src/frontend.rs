//! Source frontend producing CST, AST, typed HIR and validated VIR.
//!
//! Intermediate Draft VIR is intentionally not part of the public facade:
//!
//! ```compile_fail
//! fn cannot_observe_draft(_: nera::DraftVirUnit) {}
//! ```

mod core_projection;
pub mod hir;
mod instantiate;
mod lower;
mod modules;
pub use instantiate::{InstanceInfo, InstanceKey, InstantiationReport, TemplateInfo};
mod parser;

use std::error::Error;
use std::fmt;
use std::ops::Range;

use crate::lexer::{Lexed, Token, TokenKind, lex};
use crate::{ByteSpan, Diagnostic, SourceFile, ValidatedVirUnit};

pub use hir::{
    HirAbiClass, HirBlock, HirBody, HirBoundsSource, HirCall, HirCallingConvention, HirContract,
    HirContractId, HirDeclaration, HirEndianness, HirExpression, HirExpressionKind, HirField,
    HirFieldId, HirFieldInitializer, HirFieldLayout, HirForSource, HirFunction, HirFunctionId,
    HirFunctionSignature, HirFunctionType, HirGenericParameter, HirGenericParameterId,
    HirIntegerPredicate, HirIntegerType, HirLayout, HirLayoutId, HirLocal, HirLocalId, HirLoopId,
    HirMatchArm, HirModule, HirModuleId, HirModulePath, HirMutability, HirNodeId, HirPattern,
    HirPatternKind, HirPlace, HirPlaceAccess, HirPlaceBase, HirPlaceResolutionError,
    HirPlaceResolutionErrorKind, HirPointerOffset, HirPredicate, HirPredicateId, HirProgram,
    HirProgramTables, HirProgramValidationError, HirProjection, HirProjectionKind, HirRegion,
    HirRegionConstraint, HirRegionConstraintId, HirRegionId, HirRegionOrigin, HirRegionOwner,
    HirScopeId, HirSpecBinder, HirSpecBinderId, HirSpecBinderOwner, HirSpecClause, HirSpecClauseId,
    HirSpecClauseOwner, HirSpecContractPosition, HirSpecEnvironment, HirSpecLocation,
    HirSpecLoopInvariant, HirSpecLoopInvariantId, HirSpecProve, HirSpecProveId, HirSpecSnapshot,
    HirSpecTerm, HirSpecTermId, HirSpecTermKind, HirStatement, HirStatementKind,
    HirTargetDataLayout, HirTrustEntry, HirTrustEntryId, HirTrustPolicyKind, HirTrustScope,
    HirTypeDefinition, HirTypeId, HirTypeKind, HirUseMode, HirVariant, HirVariantCaseLayout,
    HirVariantId, HirVariantLayout, HirVersion, HirVisibility, ResolvedHirPlace,
    ResolvedHirProjection, ResolvedHirProjectionKind,
};

/// User-visible class of a frontend issue.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FrontendIssueKind {
    Lexical,
    Syntax,
    Unsupported,
    Elaboration,
}

/// A classified frontend diagnostic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontendIssue {
    kind: FrontendIssueKind,
    diagnostic: Diagnostic,
    source: Option<crate::VirSourceId>,
}

impl FrontendIssue {
    pub fn source_id(&self) -> Option<crate::VirSourceId> {
        self.source
    }
    #[must_use]
    pub const fn kind(&self) -> FrontendIssueKind {
        self.kind
    }

    #[must_use]
    pub const fn diagnostic(&self) -> &Diagnostic {
        &self.diagnostic
    }

    /// Classifies implementation support separately from language errors.
    #[must_use]
    pub const fn capability_failure_kind(&self) -> Option<crate::CapabilityFailureKind> {
        match self.kind {
            FrontendIssueKind::Unsupported => {
                Some(crate::CapabilityFailureKind::RuntimeSemanticsUnsupported)
            }
            FrontendIssueKind::Lexical
            | FrontendIssueKind::Syntax
            | FrontendIssueKind::Elaboration => None,
        }
    }
}

/// The overall result of the Core0 frontend pipeline.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FrontendStatus {
    AcceptedProposal,
    Invalid,
    Unsupported,
}

/// Lossless CST for the accepted source compilation unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CstFile {
    tokens: Vec<Token>,
    functions: Vec<CstFunction>,
}

impl CstFile {
    #[must_use]
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    #[must_use]
    pub fn function(&self) -> &CstFunction {
        self.functions
            .first()
            .expect("accepted CST contains an entry function")
    }

    #[must_use]
    pub fn functions(&self) -> &[CstFunction] {
        &self.functions
    }
}

/// CST ranges for the accepted function. Token indices refer to `CstFile::tokens`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CstFunction {
    span: ByteSpan,
    name_span: ByteSpan,
    body_span: ByteSpan,
    token_range: Range<usize>,
}

impl CstFunction {
    #[must_use]
    pub const fn span(&self) -> ByteSpan {
        self.span
    }

    #[must_use]
    pub const fn name_span(&self) -> ByteSpan {
        self.name_span
    }

    #[must_use]
    pub const fn body_span(&self) -> ByteSpan {
        self.body_span
    }

    #[must_use]
    pub fn token_range(&self) -> Range<usize> {
        self.token_range.clone()
    }
}

/// Normalized AST for the currently admitted surface subset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstFile {
    module: Option<String>,
    imports: Vec<(String, ByteSpan)>,
    public: std::collections::BTreeSet<String>,
    structs: Vec<AstStruct>,
    enums: Vec<AstEnum>,
    functions: Vec<AstFunction>,
    span: ByteSpan,
}

impl AstFile {
    #[must_use]
    pub fn module_name(&self) -> Option<&str> {
        self.module.as_deref()
    }

    #[must_use]
    pub fn is_public(&self, name: &str) -> bool {
        self.public.contains(name)
    }

    #[must_use]
    pub fn function(&self) -> &AstFunction {
        self.functions
            .first()
            .expect("accepted AST contains an entry function")
    }

    #[must_use]
    pub fn functions(&self) -> &[AstFunction] {
        &self.functions
    }

    #[must_use]
    pub fn structs(&self) -> &[AstStruct] {
        &self.structs
    }

    #[must_use]
    pub fn enums(&self) -> &[AstEnum] {
        &self.enums
    }

    #[must_use]
    pub const fn span(&self) -> ByteSpan {
        self.span
    }
}

/// A non-generic nominal struct admitted by the stage 6.5.8 surface slice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstStruct {
    pub name: String,
    pub generics: Vec<AstGenericParameter>,
    pub fields: Vec<AstStructField>,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstStructField {
    pub name: String,
    pub ty: AstType,
    pub span: ByteSpan,
}

/// A non-generic nominal enum admitted by the stage 6.5.9 surface slice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstEnum {
    pub name: String,
    pub generics: Vec<AstGenericParameter>,
    pub variants: Vec<AstEnumVariant>,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstEnumVariant {
    pub name: String,
    pub payload: AstEnumVariantPayload,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstEnumVariantPayload {
    Unit,
    Tuple(Vec<AstEnumTupleField>),
    Named(Vec<AstStructField>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstEnumTupleField {
    pub ty: AstType,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstFunction {
    pub name: String,
    pub generics: Vec<AstGenericParameter>,
    pub parameters: Vec<AstParameter>,
    pub return_type: AstType,
    pub body: AstBlock,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstParameter {
    pub name: String,
    pub ty: AstType,
    pub span: ByteSpan,
}

/// Concrete source types retained by the incremental surface AST.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AstType {
    Unit,
    Bool,
    U64,
    Usize,
    OwnU64,
    RawU64,
    /// A reference with an elided, use-site inferred lifetime.
    Reference {
        pointee: Box<AstType>,
        mutable: bool,
    },
    Tuple(Vec<AstType>),
    Array {
        element: Box<AstType>,
        length: u64,
    },
    /// An unsized slice pointee. Surface values use it behind `&`/`&mut`.
    Slice {
        element: Box<AstType>,
    },
    Named(String),
    Applied {
        name: String,
        arguments: Vec<AstGenericArgument>,
    },
    ConstArray {
        element: Box<AstType>,
        length: AstConstExpression,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstGenericParameter {
    Type(String),
    Const(String),
}
impl AstGenericParameter {
    pub fn name(&self) -> &str {
        match self {
            Self::Type(n) | Self::Const(n) => n,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AstGenericArgument {
    Type(AstType),
    Const(AstConstExpression),
}

/// Checked, non-wrapping u64 literal/binder sums; not runtime integer arithmetic.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AstConstExpression {
    Literal(u64),
    Name(String),
    Add(Vec<AstConstExpression>),
}

/// One lexical surface block, including its braces when they are explicit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstBlock {
    pub statements: Vec<AstStatement>,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstStatement {
    pub kind: AstStatementKind,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstStatementKind {
    /// Mutable, explicitly typed storage declaration without a value.
    Declare {
        name: String,
        annotation: AstType,
    },
    Let {
        name: String,
        mutable: bool,
        annotation: Option<AstType>,
        value: AstExpression,
    },
    Assign {
        destination: AstPlace,
        value: AstExpression,
    },
    Store {
        pointer: String,
        value: AstExpression,
    },
    Free {
        pointer: String,
    },
    Return {
        value: Option<AstExpression>,
    },
    Block {
        block: AstBlock,
    },
    If {
        condition: AstExpression,
        then_block: AstBlock,
        else_block: Option<AstBlock>,
    },
    While {
        condition: AstExpression,
        body: AstBlock,
    },
    /// A half-open integer range loop, `for name in start..end`.
    For {
        binding: String,
        binding_span: ByteSpan,
        start: AstExpression,
        end: AstExpression,
        body: AstBlock,
    },
    Match {
        scrutinee: AstExpression,
        arms: Vec<AstMatchArm>,
    },
    Break,
    Continue,
    Evaluate {
        expression: AstExpression,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstMatchArm {
    pub pattern: AstPattern,
    pub guard: Option<AstExpression>,
    pub body: AstBlock,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstPattern {
    pub kind: AstPatternKind,
    pub span: ByteSpan,
}

/// Scalar and enum pattern forms admitted through stage 6.5.9.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstPatternKind {
    Wildcard,
    Binding(String),
    Integer(u64),
    Bool(bool),
    Variant {
        enum_name: String,
        variant_name: String,
        payload: AstVariantPatternPayload,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstVariantPatternPayload {
    Unit,
    Tuple(Vec<AstPattern>),
    Named(Vec<AstNamedPattern>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstNamedPattern {
    pub name: String,
    pub pattern: AstPattern,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstExpression {
    pub kind: AstExpressionKind,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstExpressionKind {
    GenericCall {
        callee: String,
        types: Vec<AstGenericArgument>,
        arguments: Vec<AstExpression>,
    },
    GenericStruct {
        name: String,
        types: Vec<AstGenericArgument>,
        fields: Vec<AstFieldInitializer>,
    },
    ConstRepeat {
        value: Box<AstExpression>,
        length: AstConstExpression,
    },
    Integer {
        value: u64,
        explicit_u64: bool,
        explicit_usize: bool,
    },
    Bool(bool),
    Name(String),
    Place(AstPlace),
    Unit,
    Tuple(Vec<AstExpression>),
    Array(Vec<AstExpression>),
    ArrayRepeat {
        value: Box<AstExpression>,
        length: u64,
    },
    Struct {
        name: String,
        fields: Vec<AstFieldInitializer>,
    },
    EnumVariant {
        enum_name: String,
        variant_name: String,
        payload: AstVariantInitializer,
    },
    /// A left-associated chain stored flat to avoid recursion proportional to source length.
    Add(Vec<AstExpression>),
    Allocate {
        element_type: AstType,
        count: u64,
    },
    Load {
        pointer: String,
    },
    /// Creates a shared or mutable reference to one source place.
    Borrow {
        place: AstPlace,
        mutable: bool,
    },
    /// Address formation without creating a reference or permission.
    RawAddress {
        place: AstPlace,
        mutable: bool,
    },
    Compare {
        predicate: AstIntegerPredicate,
        left: Box<AstExpression>,
        right: Box<AstExpression>,
        operation_span: ByteSpan,
    },
    Call {
        callee: String,
        arguments: Vec<AstExpression>,
    },
}

/// A source-ordered struct-literal field initializer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstFieldInitializer {
    pub name: String,
    pub value: AstExpression,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstVariantInitializer {
    Unit,
    Tuple(Vec<AstExpression>),
    Named(Vec<AstFieldInitializer>),
}

/// A local-rooted surface place. Projection operands remain expressions so
/// elaboration can preserve their single-evaluation order in typed HIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstPlace {
    pub base: String,
    pub projections: Vec<AstPlaceProjection>,
    pub span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AstPlaceProjection {
    /// An explicit leading dereference, as in `&*owner`.
    Dereference {
        span: ByteSpan,
    },
    Field {
        name: String,
        span: ByteSpan,
    },
    TupleElement {
        index: u64,
        span: ByteSpan,
    },
    Index {
        index: Box<AstExpression>,
        span: ByteSpan,
    },
    Slice {
        start: Option<Box<AstExpression>>,
        end: Option<Box<AstExpression>>,
        span: ByteSpan,
    },
}

/// Unsigned integer comparison selected by the surface operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AstIntegerPredicate {
    Equal,
    NotEqual,
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual,
}

/// A Core0 register number. Registers are assigned canonically from zero.
pub type Register = u32;

/// A frozen compatibility proposal corresponding to `Nera.Core.Instruction`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreInstruction {
    Set {
        destination: Register,
        word: u64,
    },
    Add {
        destination: Register,
        left: Register,
        right: Register,
    },
    Allocate {
        destination: Register,
        size_bytes: u64,
        alignment: u64,
        region: u64,
    },
    Offset {
        destination: Register,
        base: Register,
        delta_bytes: u64,
    },
    Store {
        pointer: Register,
        source: Register,
    },
    Load {
        destination: Register,
        pointer: Register,
    },
    Free {
        pointer: Register,
    },
    Return {
        source: Register,
    },
}

/// A proposed instruction and the source construct that produced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpannedCoreInstruction {
    pub instruction: CoreInstruction,
    pub source_span: ByteSpan,
}

/// VIR-derived Core0 output retained for the frozen stage 3 certification prototype.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreProgramProposal {
    pub function_name: String,
    pub instructions: Vec<SpannedCoreInstruction>,
    pub register_count: Register,
    pub source_span: ByteSpan,
}

/// A structurally valid VIR program is outside the frozen stage 3 Core0 subset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Core0CompatibilityError {
    source_span: ByteSpan,
}

impl Core0CompatibilityError {
    pub(super) const fn new(source_span: ByteSpan) -> Self {
        Self { source_span }
    }

    #[must_use]
    pub const fn source_span(&self) -> ByteSpan {
        self.source_span
    }
}

impl fmt::Display for Core0CompatibilityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("validated VIR is outside the frozen Core0 compatibility subset")
    }
}

impl Error for Core0CompatibilityError {}

/// Production frontend artifacts through the validated VIR boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontendOutput {
    instantiations: InstantiationReport,
    files: Vec<FrontendFile>,
    lexed: Lexed,
    cst: Option<CstFile>,
    ast: Option<AstFile>,
    hir: Option<HirProgram>,
    vir: Option<ValidatedVirUnit>,
    issues: Vec<FrontendIssue>,
    status: FrontendStatus,
}

impl FrontendOutput {
    pub fn instantiations(&self) -> &InstantiationReport {
        &self.instantiations
    }
    /// Per-file artifacts; local spans inherit the frontend-file source ID.
    /// A session resolves it with `SourceAnalysis::locate_file_span`.
    pub fn files(&self) -> &[FrontendFile] {
        &self.files
    }
    /// Move the validated input into the verification facade without retaining
    /// or cloning the intermediate CST/AST/HIR graphs.
    pub(crate) fn into_verification_parts(
        self,
    ) -> (
        FrontendStatus,
        Vec<FrontendIssue>,
        Option<ValidatedVirUnit>,
        InstantiationReport,
    ) {
        (self.status, self.issues, self.vir, self.instantiations)
    }
    #[must_use]
    pub const fn lexed(&self) -> &Lexed {
        &self.lexed
    }

    #[must_use]
    pub const fn cst(&self) -> Option<&CstFile> {
        self.cst.as_ref()
    }

    #[must_use]
    pub const fn ast(&self) -> Option<&AstFile> {
        self.ast.as_ref()
    }

    /// Table-organized typed compilation unit produced by elaboration.
    #[must_use]
    pub const fn hir(&self) -> Option<&HirProgram> {
        self.hir.as_ref()
    }

    #[must_use]
    pub const fn vir(&self) -> Option<&ValidatedVirUnit> {
        self.vir.as_ref()
    }

    #[must_use]
    pub fn issues(&self) -> &[FrontendIssue] {
        &self.issues
    }

    #[must_use]
    pub const fn status(&self) -> FrontendStatus {
        self.status
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontendFile {
    /// Local to the frontend file table, not a persistent source identity.
    pub source: crate::VirSourceId,
    pub lexed: Lexed,
    pub cst: CstFile,
    pub ast: AstFile,
}

/// Runs the production source-to-validated-VIR pipeline.
#[must_use]
pub fn analyze(source: &SourceFile) -> FrontendOutput {
    crate::session::CompilerSession::single(source.clone(), Default::default())
        .analyze("input.nera")
        .expect("single-source production configuration")
        .into_frontend()
}

/// The only production frontend implementation. Session owns input/configuration.
pub(crate) fn analyze_single_source(source: &SourceFile) -> FrontendOutput {
    analyze_sources(&[source], &["crate".to_owned()], 0, None)
}

/// Parse independently, collect the closed graph, then elaborate and lower ONCE.
pub(crate) fn analyze_sources(
    sources: &[&SourceFile],
    paths: &[String],
    root: usize,
    entry: Option<&str>,
) -> FrontendOutput {
    let mut files = Vec::new();
    for (index, source) in sources.iter().enumerate() {
        let lexed = lex(source);
        let parse = || -> Result<ParsedFile, FrontendFailure> {
            if let Some(issue) = lexed.issues().first() {
                return Err(FrontendFailure {
                    kind: FrontendIssueKind::Lexical,
                    span: issue.diagnostic().primary_span().unwrap_or(span(0, 0)),
                    message: "invalid source bytes or token",
                    source: None,
                });
            }
            if let Some(span) = lexed.tokens().iter().find_map(|token| {
                (token.kind() == TokenKind::Identifier && !token.raw(source).is_ascii())
                    .then_some(token.span())
            }) {
                return Err(FrontendFailure::unsupported(
                    span,
                    "Unicode identifiers are not supported by the Core0 verified profile",
                ));
            }
            parser::parse(source, lexed.tokens(), entry.is_some())
        };
        let parsed = match parse() {
            Ok(parsed) => parsed,
            Err(mut failure) => {
                failure.source = entry.map(|_| crate::VirSourceId::new(index as u32));
                let mut output = failed_output(lexed, failure);
                // Preserve the scanner's precise diagnostics and all lexical issues.
                if !output.lexed.issues().is_empty() {
                    output.issues = output
                        .lexed
                        .issues()
                        .iter()
                        .map(|issue| FrontendIssue {
                            kind: FrontendIssueKind::Lexical,
                            diagnostic: issue.diagnostic().clone(),
                            source: entry.map(|_| crate::VirSourceId::new(index as u32)),
                        })
                        .collect();
                }
                return output;
            }
        };
        files.push(FrontendFile {
            source: crate::VirSourceId::new(index as u32),
            cst: CstFile {
                tokens: lexed.tokens().to_vec(),
                functions: parsed.cst,
            },
            ast: parsed.ast,
            lexed,
        });
    }
    let asts: Vec<_> = files.iter().map(|file| &file.ast).collect();
    let result = (|| {
        let graph = if let Some(entry) = entry {
            let mapped: Vec<_> = paths.iter().cloned().zip(asts.iter().copied()).collect();
            modules::ModuleGraph::build(&mapped, entry)?
        } else {
            modules::ModuleGraph::single(asts[0])?
        };
        let (concrete, instances) = instantiate::run(&asts, &graph)?;
        let concrete: Vec<_> = concrete.iter().collect();
        let hir = hir::elaborate_modules(&concrete, graph)?;
        let vir = if entry.is_some() {
            lower::lower_modules(&hir, sources)?
        } else {
            lower::lower(&hir, sources[0])?
        };
        Ok::<_, FrontendFailure>((hir, vir, instances))
    })();
    match result {
        Ok((hir, vir, instantiations)) => FrontendOutput {
            instantiations,
            lexed: files[root].lexed.clone(),
            cst: Some(files[root].cst.clone()),
            ast: Some(files[root].ast.clone()),
            files,
            hir: Some(hir),
            vir: Some(vir),
            issues: Vec::new(),
            status: FrontendStatus::AcceptedProposal,
        },
        Err(mut failure) => {
            if entry.is_none() {
                failure.source = None;
            }
            failed_output(files[root].lexed.clone(), failure)
        }
    }
}

fn failed_output(lexed: Lexed, failure: FrontendFailure) -> FrontendOutput {
    let status = if failure.kind == FrontendIssueKind::Unsupported {
        FrontendStatus::Unsupported
    } else {
        FrontendStatus::Invalid
    };
    FrontendOutput {
        instantiations: InstantiationReport::default(),
        files: Vec::new(),
        lexed,
        cst: None,
        ast: None,
        hir: None,
        vir: None,
        issues: vec![FrontendIssue {
            kind: failure.kind,
            diagnostic: Diagnostic::error(failure.message).with_primary_span(failure.span),
            source: failure.source,
        }],
        status,
    }
}

/// Explicitly projects resolved runtime VIR into the frozen stage 3 Core0
/// proposal. The projection cannot observe specification tables.
///
/// This compatibility operation is not part of production frontend acceptance
/// or execution. Failure means that valid VIR is outside the historical Core0
/// subset; it does not make the source program invalid.
pub fn project_core0_compat(
    vir: &crate::ResolvedRuntimeVirView<'_>,
) -> Result<CoreProgramProposal, Core0CompatibilityError> {
    core_projection::project(vir)
}

pub(super) struct ParsedFile {
    cst: Vec<CstFunction>,
    ast: AstFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FrontendFailure {
    kind: FrontendIssueKind,
    span: ByteSpan,
    message: &'static str,
    source: Option<crate::VirSourceId>,
}

impl FrontendFailure {
    pub(super) const fn syntax(span: ByteSpan, message: &'static str) -> Self {
        Self {
            kind: FrontendIssueKind::Syntax,
            source: None,
            span,
            message,
        }
    }

    pub(super) const fn unsupported(span: ByteSpan, message: &'static str) -> Self {
        Self {
            kind: FrontendIssueKind::Unsupported,
            source: None,
            span,
            message,
        }
    }

    pub(super) const fn elaboration(span: ByteSpan, message: &'static str) -> Self {
        Self {
            kind: FrontendIssueKind::Elaboration,
            source: None,
            span,
            message,
        }
    }
}

pub(super) fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(start, end).expect("frontend constructs ordered spans")
}

#[cfg(test)]
mod tests {
    use super::{
        CoreInstruction, FrontendIssueKind, FrontendStatus, HirCallingConvention, HirIntegerType,
        HirTypeKind, analyze as analyze_source, project_core0_compat,
    };
    use crate::{SourceFile, VirInstruction, VirTerminator};

    fn analyze(text: &str) -> super::FrontendOutput {
        analyze_source(&SourceFile::from_text("test.nera", text))
    }

    fn project_core(output: &super::FrontendOutput) -> super::CoreProgramProposal {
        let resolved = output
            .vir()
            .expect("accepted output has validated VIR")
            .resolve()
            .expect("test VIR resolves");
        project_core0_compat(resolved.runtime())
            .expect("test program is inside the frozen Core0 compatibility subset")
    }

    #[test]
    fn lowers_a_complete_core0_function() {
        let output = analyze(
            "fn example() -> u64 {\n\
                 let left = 20;\n\
                 let right = 22;\n\
                 let value = left + right;\n\
                 let memory = alloc<u64>(1);\n\
                 *memory = value;\n\
                 let loaded = *memory;\n\
                 free(memory);\n\
                 return loaded;\n\
             }",
        );
        assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
        assert!(output.cst().is_some());
        assert!(output.ast().is_some());
        let hir = output.hir().expect("accepted output has typed HIR");
        let function = hir.entry_function();
        let body = function.body().expect("Core0 function has a body");
        assert_eq!(hir.entry_function().signature.parameters, []);
        assert_eq!(
            hir.type_kind(function.signature.return_type),
            Some(&HirTypeKind::Integer(HirIntegerType::U64))
        );
        assert_eq!(
            hir.entry_function().signature.calling_convention,
            HirCallingConvention::Nera
        );
        assert_eq!(
            body.locals
                .iter()
                .map(|local| local.name.as_str())
                .collect::<Vec<_>>(),
            ["left", "right", "value", "memory", "loaded"]
        );
        assert_eq!(
            hir.type_kind(body.locals[0].ty),
            Some(&HirTypeKind::Integer(HirIntegerType::U64))
        );
        let word_layout = hir.layout(body.locals[0].layout).expect("u64 layout");
        assert_eq!((word_layout.size_bytes, word_layout.alignment), (8, 8));
        assert!(matches!(
            hir.type_kind(body.locals[3].ty),
            Some(HirTypeKind::Own { pointee })
                if hir.type_kind(*pointee)
                    == Some(&HirTypeKind::Integer(HirIntegerType::U64))
        ));
        assert!(
            body.locals
                .iter()
                .enumerate()
                .all(|(index, local)| local.id.index() == index)
        );
        let vir = output.vir().expect("accepted output has validated VIR");
        assert_eq!(vir.runtime().functions.len(), 1);
        let block = &vir.runtime().functions[0].blocks[0];
        assert!(
            block
                .instructions
                .iter()
                .any(|spanned| matches!(spanned.instruction, VirInstruction::Allocate { .. }))
        );
        assert!(
            block
                .instructions
                .iter()
                .any(|spanned| matches!(spanned.instruction, VirInstruction::Initialize { .. }))
        );
        assert!(matches!(
            block.terminator.terminator,
            VirTerminator::Return { .. }
        ));
        let core = project_core(&output);
        assert_eq!(core.register_count, 5);
        assert!(matches!(
            core.instructions.last().map(|item| &item.instruction),
            Some(CoreInstruction::Return { .. })
        ));
    }

    #[test]
    fn elaboration_builds_deterministic_hir_program_tables() {
        let source = "fn tabled() -> u64 { let memory = alloc<u64>(1); let value = *memory; free(memory); return value; }";
        let first = analyze(source);
        let second = analyze(source);
        let hir = first.hir().expect("accepted output has HIR tables");

        assert_eq!(
            hir,
            second.hir().expect("second elaboration has HIR tables")
        );
        assert!(hir.validate_tables().is_ok());
        assert_eq!(hir.version(), super::HirVersion::V12);
        assert_eq!(hir.modules().len(), 1);
        assert_eq!(hir.functions().len(), 1);
        assert_eq!(hir.contracts().len(), 1);
        assert_eq!(hir.types().len(), 7);
        assert_eq!(hir.layouts().len(), 6);
        assert!(hir.fields().is_empty());
        assert!(hir.variants().is_empty());
        assert!(hir.generic_parameters().is_empty());
        assert!(hir.predicates().is_empty());
        assert!(
            hir.types()
                .iter()
                .enumerate()
                .all(|(index, ty)| ty.id.index() == index)
        );
        assert!(
            hir.layouts()
                .iter()
                .enumerate()
                .all(|(index, layout)| layout.id.index() == index)
        );

        let function = hir.entry_function();
        assert!(matches!(
            hir.type_kind(function.signature.ty),
            Some(HirTypeKind::Function(signature))
                if signature.parameters == function.signature.parameters
                    && signature.return_type == function.signature.return_type
                    && signature.calling_convention == function.signature.calling_convention
        ));
        let body = function.body().expect("Core0 function has a body");
        assert!(body.locals.iter().all(|local| {
            hir.layout(local.layout).is_some_and(|layout| {
                layout.ty == local.ty
                    && hir.type_definition(local.ty).and_then(|ty| ty.layout) == Some(local.layout)
            })
        }));
    }

    #[test]
    fn unit_function_gets_canonical_zero_return() {
        let output = analyze("fn empty() { return; }");
        let function = &output.vir().expect("accepted").runtime().functions[0];
        assert!(function.signature.results.is_empty());
        assert!(matches!(
            function.blocks[0].terminator.terminator,
            VirTerminator::Return { ref values } if values.is_empty()
        ));
        let core = project_core(&output);
        let instructions = &core.instructions;
        assert!(matches!(
            instructions.as_slice(),
            [
                super::SpannedCoreInstruction {
                    instruction: CoreInstruction::Set { word: 0, .. },
                    ..
                },
                super::SpannedCoreInstruction {
                    instruction: CoreInstruction::Return { .. },
                    ..
                }
            ]
        ));
    }

    #[test]
    fn valid_deferred_features_are_unsupported() {
        for text in [
            "fn 名字() { return; }",
            "fn f<'a, 'b>() { return; }",
            "fn f() -> u64 { return 1.0; }",
            "fn f() { \"text\"; return; }",
        ] {
            let output = analyze(text);
            assert_eq!(output.status(), FrontendStatus::Unsupported, "{text}");
            assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Unsupported);
        }

        let unknown_callee = analyze("fn f() -> u64 { return missing(); }");
        assert_eq!(unknown_callee.status(), FrontendStatus::Invalid);
        assert_eq!(
            unknown_callee.issues()[0].kind(),
            FrontendIssueKind::Elaboration
        );
    }

    #[test]
    fn specification_contract_and_trust_surface_remains_deferred() {
        for text in [
            "fn f() requires forall index in 0..1: true; { return; }",
            "fn f() ensures old(0) == 0; { return; }",
            "fn f() reads memory[0..1]; { return; }",
            "fn f() writes memory[0..1]; { return; }",
            "fn f() decreases 1; { return; }",
            "fn f() where T: Copy { return; }",
            "struct Item { value: u64, invariant true; } fn f() { return; }",
            "fn f() { invariant true; return; }",
            "fn f() { proof { } return; }",
            "fn f() { ghost let value = 1; return; }",
            "trusted extern fn platform(); fn f() { return; }",
            "theorem identity() { } fn f() { return; }",
        ] {
            let output = analyze(text);
            assert!(output.lexed().issues().is_empty(), "{text}");
            assert_eq!(output.status(), FrontendStatus::Unsupported, "{text}");
            assert_eq!(
                output.issues()[0].kind(),
                FrontendIssueKind::Unsupported,
                "{text}"
            );
            assert!(output.ast().is_none(), "{text}");
            assert!(output.hir().is_none(), "{text}");
            assert!(output.vir().is_none(), "{text}");
        }
    }

    #[test]
    fn malformed_number_is_lexical() {
        let output = analyze("fn f() -> u64 { return 0b102; }");
        assert_eq!(output.status(), FrontendStatus::Invalid);
        assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Lexical);
    }

    #[test]
    fn use_after_free_is_preserved_for_vir_resource_analysis() {
        let output = analyze(
            "fn bad() -> u64 {\n\
                 let memory = alloc<u64>(1);\n\
                 free(memory);\n\
                 return *memory;\n\
             }",
        );
        assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
        let instructions =
            &output.vir().expect("accepted").runtime().functions[0].blocks[0].instructions;
        let free = instructions
            .iter()
            .position(|item| matches!(item.instruction, VirInstruction::Free { .. }))
            .expect("free reaches VIR");
        let load = instructions
            .iter()
            .position(|item| matches!(item.instruction, VirInstruction::Load { .. }))
            .expect("load reaches VIR");
        assert!(free < load);
    }

    #[test]
    fn memory_leak_remains_a_valid_vir_program() {
        let output = analyze("fn leak() { let memory = alloc<u64>(1); return; }");
        assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
    }

    #[test]
    fn pointer_offset_lowers_to_immediate_byte_delta() {
        let output = analyze(
            "fn offset() {\n\
                 let memory = alloc<u64>(2);\n\
                 let next = memory + 8;\n\
                 free(memory);\n\
                 return;\n\
             }",
        );
        assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
        let next = output
            .hir()
            .expect("accepted")
            .entry_function()
            .body()
            .expect("Core0 function body")
            .locals
            .iter()
            .find(|local| local.name == "next")
            .expect("next local");
        let hir = output.hir().expect("accepted");
        assert!(matches!(
            hir.type_kind(next.ty),
            Some(HirTypeKind::RawPointer { pointee, .. })
                if hir.type_kind(*pointee)
                    == Some(&HirTypeKind::Integer(HirIntegerType::U64))
        ));
        assert!(
            output.vir().expect("accepted").runtime().functions[0].blocks[0]
                .instructions
                .iter()
                .any(|item| matches!(item.instruction, VirInstruction::PointerOffset { .. }))
        );
        assert!(
            project_core(&output)
                .instructions
                .iter()
                .any(|item| matches!(
                    item.instruction,
                    CoreInstruction::Offset { delta_bytes: 8, .. }
                ))
        );
    }

    #[test]
    fn numeric_boundary_and_contextual_intrinsic_names_are_accepted() {
        for text in [
            "fn f() -> u64 { return 0xbe + 1; }",
            "fn f() -> u64 { let alloc = 1; return alloc; }",
            "fn f() -> u64 { let free = 1; return free; }",
        ] {
            assert_eq!(analyze(text).status(), FrontendStatus::AcceptedProposal);
        }
    }

    #[test]
    fn deferred_types_patterns_and_intrinsic_arguments_are_unsupported() {
        for text in [
            "fn f() -> ptr<bool> { return; }",
            "fn f() { let (left, right) = pair; return; }",
            "fn f() { let Some(value) = option; return; }",
            "fn f() { free(memory + 8); return; }",
            "fn f() { let n = 1; let memory = alloc<u64>(n); return; }",
        ] {
            let output = analyze(text);
            assert_eq!(output.status(), FrontendStatus::Unsupported, "{text}");
            assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Unsupported);
        }
    }

    #[test]
    fn return_shape_must_match_the_declared_surface_type() {
        for text in ["fn bad() -> u64 { return; }", "fn bad() { return 1; }"] {
            let output = analyze(text);
            assert_eq!(output.status(), FrontendStatus::Invalid);
            assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Elaboration);
            assert!(output.hir().is_none());
            assert!(output.vir().is_none());
        }
    }

    #[test]
    fn ordinary_pointer_assignments_refine_after_the_complete_cfg() {
        let output = analyze(
            "fn update_memory() -> u64 {
                 let memory = alloc<u64>(1);
                 let alias = memory + 0;
                 *alias = 1;
                 *memory = 2;
                 let value = *memory;
                 free(memory);
                 return value;
             }",
        );
        assert_eq!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{:?}",
            output.issues()
        );
        let instructions =
            &output.vir().expect("accepted").runtime().functions[0].blocks[0].instructions;
        assert_eq!(
            instructions
                .iter()
                .filter(|item| matches!(item.instruction, VirInstruction::Write { .. }))
                .count(),
            0
        );
        assert_eq!(
            instructions
                .iter()
                .filter(|item| matches!(item.instruction, VirInstruction::Initialize { .. }))
                .count(),
            1
        );
        assert_eq!(
            instructions
                .iter()
                .filter(|item| matches!(item.instruction, VirInstruction::Store { .. }))
                .count(),
            1
        );
        assert_eq!(
            project_core(&output)
                .instructions
                .iter()
                .filter(|item| matches!(item.instruction, CoreInstruction::Store { .. }))
                .count(),
            2
        );
    }

    #[test]
    fn derived_pointer_cannot_be_freed_as_an_owner() {
        let output = analyze(
            "fn bad() {\n\
                 let memory = alloc<u64>(2);\n\
                 let next = memory + 8;\n\
                 free(next);\n\
                 return;\n\
             }",
        );
        assert_eq!(output.status(), FrontendStatus::Invalid);
        assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Elaboration);
    }

    #[test]
    fn excessive_parenthesis_nesting_is_diagnosed_without_recursing_unboundedly() {
        let depth = 20_000;
        let source = format!(
            "fn deep() -> u64 {{ return {}0{}; }}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let output = analyze(&source);
        assert_eq!(output.status(), FrontendStatus::Unsupported);
        assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Unsupported);
    }

    #[test]
    fn long_flat_addition_does_not_create_a_recursive_ast_chain() {
        let terms = 20_000;
        let expression = vec!["1"; terms].join("+");
        let output = analyze(&format!("fn flat() -> u64 {{ return {expression}; }}"));
        assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
        assert_eq!(project_core(&output).register_count, 39_999);
    }
}
