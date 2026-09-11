//! Source-bound public module interface projection.
//!
//! The artifact is descriptive only: no verifier verdict, summary permission,
//! cache authorization, proof seal, or native-link authorization can be stored in it.

use crate::frontend::{AstGenericArgument, InstanceInfo};
use crate::session::{CompilationInput, SourceAnalysis};
use crate::{
    BorrowResultAlternative, BorrowResultRelation, CfgAnalysisConfig, DropCapability, HirAbiClass,
    HirCallingConvention, HirFunction, HirIntegerType, HirLayout, HirModule, HirModuleId,
    HirMutability, HirProgram, HirTypeDefinition, HirTypeId, HirTypeKind, HirVisibility,
    TypeCapabilities, ValueCapability,
};
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterfaceArtifactVersion {
    V1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceSourceIdentity {
    pub logical_name: String,
    pub display_path: PathBuf,
    pub bytes: Vec<u8>,
}

/// Exact first-version analysis identity. The complete closed source set is
/// also the dependency closure; this is deliberately not a content hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceInputIdentity {
    pub sources: Vec<InterfaceSourceIdentity>,
    pub selected_source: String,
    pub entry: Option<String>,
    pub capability_profile: String,
    pub language: String,
    pub target: String,
    pub runtime: String,
    pub verifier: String,
    pub interpreter: String,
    pub backend: String,
    pub formal_checker: String,
    pub hir_schema: u32,
    pub vir_schema: u32,
    pub analysis: CfgAnalysisConfig,
}

impl InterfaceInputIdentity {
    fn from_input(input: &CompilationInput) -> Self {
        let profile = input.effective().profile();
        Self {
            sources: input
                .sources()
                .entries()
                .iter()
                .map(|entry| InterfaceSourceIdentity {
                    logical_name: entry.logical_name().to_owned(),
                    display_path: entry.file().path().to_owned(),
                    bytes: entry.file().bytes().to_vec(),
                })
                .collect(),
            selected_source: input.logical_name().to_owned(),
            entry: input.entry().map(str::to_owned),
            capability_profile: profile.profile().to_owned(),
            language: profile.language().to_owned(),
            target: profile.target().to_owned(),
            runtime: profile.runtime().to_owned(),
            verifier: profile.verifier().to_owned(),
            interpreter: profile.interpreter().to_owned(),
            backend: profile.backend().to_owned(),
            formal_checker: profile.formal_checker().to_owned(),
            hir_schema: profile.hir_schema(),
            vir_schema: profile.vir_schema(),
            analysis: input.effective().analysis(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceModuleIdentity {
    pub path: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceInstanceIdentity {
    pub definition: String,
    pub arguments: Vec<AstGenericArgument>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum InterfaceDeclarationIdentity {
    Named {
        module: InterfaceModuleIdentity,
        name: String,
    },
    ConcreteInstance(InterfaceInstanceIdentity),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceType {
    Unit,
    Bool,
    Integer(HirIntegerType),
    Own(Box<Self>),
    RawPointer {
        pointee: Box<Self>,
        mutability: HirMutability,
    },
    /// Region names/table IDs are intentionally absent. Borrow dependencies
    /// are published by the containing function's normalized result relation.
    Reference {
        pointee: Box<Self>,
        mutability: HirMutability,
    },
    Array {
        element: Box<Self>,
        length: u64,
    },
    Slice {
        element: Box<Self>,
        mutability: HirMutability,
    },
    Tuple(Vec<Self>),
    Nominal(InterfaceDeclarationIdentity),
    Function {
        parameters: Vec<Self>,
        result: Box<Self>,
        calling_convention: HirCallingConvention,
    },
    Never,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InterfaceLayout {
    pub size_bytes: u64,
    pub alignment: u64,
    pub abi: HirAbiClass,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceField {
    pub name: String,
    pub ty: InterfaceType,
    pub offset_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceVariant {
    pub name: String,
    pub discriminant: u64,
    pub payload_offset_bytes: u64,
    pub fields: Vec<InterfaceField>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceNominalKind {
    Struct { fields: Vec<InterfaceField> },
    Enum { variants: Vec<InterfaceVariant> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceTypeDeclaration {
    pub identity: InterfaceDeclarationIdentity,
    pub layout: InterfaceLayout,
    pub capabilities: TypeCapabilities,
    pub kind: InterfaceNominalKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterfaceMemoryRole {
    PlainValue,
    Owner,
    RawPointer,
    SharedBorrow,
    MutableBorrow,
    AggregateResource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterfaceTransferMode {
    Copy,
    Move,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceParameterEffect {
    pub parameter: u32,
    pub transfer: InterfaceTransferMode,
    pub memory: InterfaceMemoryRole,
    pub drop: DropCapability,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfacePrecondition {
    InitializedValue {
        parameter: u32,
    },
    LiveOwner {
        parameter: u32,
    },
    LiveBorrow {
        parameter: u32,
        mutability: HirMutability,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceEffectSkeleton {
    pub parameters: Vec<InterfaceParameterEffect>,
    pub preconditions: Vec<InterfacePrecondition>,
    pub result_capabilities: TypeCapabilities,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceFunction {
    pub identity: InterfaceDeclarationIdentity,
    pub parameters: Vec<InterfaceType>,
    pub result: InterfaceType,
    pub calling_convention: HirCallingConvention,
    pub borrow_result: Option<BorrowResultRelation>,
    pub borrow_result_alternatives: Vec<BorrowResultAlternative>,
    /// Type-derived shape only, not a checked callee summary.
    pub effects: InterfaceEffectSkeleton,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceModule {
    pub identity: InterfaceModuleIdentity,
    pub types: Vec<InterfaceTypeDeclaration>,
    pub functions: Vec<InterfaceFunction>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceArtifactError {
    FrontendNotAccepted,
    MissingTypedHir,
    MissingValidatedVir,
    Inconsistent(&'static str),
    UnsupportedType,
}

impl fmt::Display for InterfaceArtifactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "module interface projection: {self:?}")
    }
}

impl Error for InterfaceArtifactError {}

/// An immutable projection. Private outer fields prevent callers from
/// manufacturing an artifact; `matches_analysis` always recomputes it anyway.
///
/// ```compile_fail
/// let artifact = nera::InterfaceArtifact { /* private identity fields */ };
/// ```
///
/// ```compile_fail
/// # fn inspect(artifact: &nera::InterfaceArtifact) {
/// let checked = artifact.is_checked();
/// # }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceArtifact {
    version: InterfaceArtifactVersion,
    input: InterfaceInputIdentity,
    instances: Vec<InterfaceInstanceIdentity>,
    modules: Vec<InterfaceModule>,
}

impl InterfaceArtifact {
    pub const fn version(&self) -> InterfaceArtifactVersion {
        self.version
    }

    pub const fn input(&self) -> &InterfaceInputIdentity {
        &self.input
    }

    pub fn instances(&self) -> &[InterfaceInstanceIdentity] {
        &self.instances
    }

    pub fn modules(&self) -> &[InterfaceModule] {
        &self.modules
    }

    pub fn matches_input(&self, input: &CompilationInput) -> bool {
        self.input == InterfaceInputIdentity::from_input(input)
    }

    /// Reprojects the complete interface; matching input bytes alone cannot
    /// excuse a producer bug or a mutated interface payload.
    pub fn matches_analysis(&self, analysis: &SourceAnalysis) -> bool {
        Self::project(analysis).is_ok_and(|candidate| candidate == *self)
    }

    fn project(analysis: &SourceAnalysis) -> Result<Self, InterfaceArtifactError> {
        let frontend = analysis.frontend();
        if frontend.status() != crate::FrontendStatus::AcceptedProposal {
            return Err(InterfaceArtifactError::FrontendNotAccepted);
        }
        let hir = frontend
            .hir()
            .ok_or(InterfaceArtifactError::MissingTypedHir)?;
        frontend
            .vir()
            .ok_or(InterfaceArtifactError::MissingValidatedVir)?;
        let mut projector = Projector::new(hir, analysis)?;
        let modules = projector.modules()?;
        Ok(Self {
            version: InterfaceArtifactVersion::V1,
            input: InterfaceInputIdentity::from_input(analysis.input()),
            instances: projector.instances.into_iter().collect(),
            modules,
        })
    }
}

impl SourceAnalysis {
    /// Project public, source-bound interface data without running or importing
    /// a verifier result.
    pub fn interface_artifact(&self) -> Result<InterfaceArtifact, InterfaceArtifactError> {
        InterfaceArtifact::project(self)
    }
}

struct Projector<'a> {
    hir: &'a HirProgram,
    analysis: &'a SourceAnalysis,
    type_owners: BTreeMap<HirTypeId, HirModuleId>,
    instances: BTreeSet<InterfaceInstanceIdentity>,
}

impl<'a> Projector<'a> {
    fn new(
        hir: &'a HirProgram,
        analysis: &'a SourceAnalysis,
    ) -> Result<Self, InterfaceArtifactError> {
        let mut type_owners = BTreeMap::new();
        for module in hir.modules() {
            for declaration in &module.declarations {
                if let crate::HirDeclaration::Type(ty) = declaration {
                    if type_owners.insert(*ty, module.id).is_some() {
                        return Err(InterfaceArtifactError::Inconsistent(
                            "type declared by multiple modules",
                        ));
                    }
                }
            }
        }
        Ok(Self {
            hir,
            analysis,
            type_owners,
            instances: BTreeSet::new(),
        })
    }

    fn modules(&mut self) -> Result<Vec<InterfaceModule>, InterfaceArtifactError> {
        let mut modules = Vec::new();
        for module in self.hir.modules() {
            let mut types = Vec::new();
            let mut functions = Vec::new();
            for declaration in &module.declarations {
                match declaration {
                    crate::HirDeclaration::Type(id) => {
                        let definition = self
                            .hir
                            .type_definition(*id)
                            .ok_or(InterfaceArtifactError::Inconsistent("missing public type"))?;
                        if self.is_public_type(module, definition)? {
                            types.push(self.type_declaration(module, definition)?);
                        }
                    }
                    crate::HirDeclaration::Function(id) => {
                        let function = self.hir.function_by_id(*id).ok_or(
                            InterfaceArtifactError::Inconsistent("missing public function"),
                        )?;
                        if self.is_public_function(module, function)? {
                            functions.push(self.function(module, function)?);
                        }
                    }
                    crate::HirDeclaration::Contract(_) | crate::HirDeclaration::Predicate(_) => {}
                }
            }
            types.sort_by(|a, b| a.identity.cmp(&b.identity));
            functions.sort_by(|a, b| a.identity.cmp(&b.identity));
            modules.push(InterfaceModule {
                identity: module_identity(module),
                types,
                functions,
            });
        }
        modules.sort_by(|a, b| a.identity.cmp(&b.identity));
        Ok(modules)
    }

    fn is_public_type(
        &self,
        module: &HirModule,
        definition: &HirTypeDefinition,
    ) -> Result<bool, InterfaceArtifactError> {
        let Some(name) = definition.name.as_deref() else {
            return Ok(false);
        };
        self.is_public_name(module, name)
    }

    fn is_public_function(
        &self,
        module: &HirModule,
        function: &HirFunction,
    ) -> Result<bool, InterfaceArtifactError> {
        if function.visibility == HirVisibility::Public {
            return Ok(true);
        }
        match self.instance(module.id, &function.name) {
            Some(instance) => self.original_is_public(instance),
            None => Ok(false),
        }
    }

    fn is_public_name(
        &self,
        module: &HirModule,
        name: &str,
    ) -> Result<bool, InterfaceArtifactError> {
        if let Some(instance) = self.instance(module.id, name) {
            return self.original_is_public(instance);
        }
        let file = self
            .analysis
            .frontend()
            .files()
            .get(module.id.index())
            .ok_or(InterfaceArtifactError::Inconsistent("missing module AST"))?;
        Ok(file.ast.is_public(name))
    }

    fn original_is_public(&self, instance: &InstanceInfo) -> Result<bool, InterfaceArtifactError> {
        let name = instance.key.definition.rsplit("::").next().ok_or(
            InterfaceArtifactError::Inconsistent("invalid instance definition"),
        )?;
        let definition_module = instance
            .key
            .definition
            .rsplit_once("::")
            .map(|(module, _)| module)
            .ok_or(InterfaceArtifactError::Inconsistent(
                "invalid instance definition",
            ))?;
        let file = self
            .analysis
            .frontend()
            .files()
            .get(instance.source.get() as usize)
            .ok_or(InterfaceArtifactError::Inconsistent("missing instance AST"))?;
        if file.ast.module_name().unwrap_or("crate") != definition_module {
            return Err(InterfaceArtifactError::Inconsistent(
                "instance definition module mismatch",
            ));
        }
        Ok(file.ast.is_public(name))
    }

    fn instance(&self, module: HirModuleId, generated_name: &str) -> Option<&InstanceInfo> {
        self.analysis
            .frontend()
            .instantiations()
            .instances
            .iter()
            .find(|instance| {
                instance.source.get() == module.get() && instance.generated_name == generated_name
            })
    }

    fn identity(&mut self, module: &HirModule, name: &str) -> InterfaceDeclarationIdentity {
        if let Some(instance) = self.instance(module.id, name) {
            let identity = InterfaceInstanceIdentity {
                definition: instance.key.definition.clone(),
                arguments: instance.key.arguments.clone(),
            };
            self.instances.insert(identity.clone());
            InterfaceDeclarationIdentity::ConcreteInstance(identity)
        } else {
            InterfaceDeclarationIdentity::Named {
                module: module_identity(module),
                name: name.to_owned(),
            }
        }
    }

    fn type_declaration(
        &mut self,
        module: &HirModule,
        definition: &HirTypeDefinition,
    ) -> Result<InterfaceTypeDeclaration, InterfaceArtifactError> {
        let name = definition
            .name
            .as_deref()
            .ok_or(InterfaceArtifactError::Inconsistent("unnamed nominal type"))?;
        let layout =
            self.hir
                .layout_of(definition.id)
                .ok_or(InterfaceArtifactError::Inconsistent(
                    "public type has no layout",
                ))?;
        let identity = self.identity(module, name);
        let kind = match &definition.kind {
            HirTypeKind::Struct { fields } => InterfaceNominalKind::Struct {
                fields: fields
                    .iter()
                    .map(|id| {
                        let field = self
                            .hir
                            .field(*id)
                            .ok_or(InterfaceArtifactError::Inconsistent("missing struct field"))?;
                        let offset = layout
                            .fields
                            .iter()
                            .find(|candidate| candidate.field == *id)
                            .ok_or(InterfaceArtifactError::Inconsistent(
                                "missing struct field layout",
                            ))?
                            .offset_bytes;
                        Ok(InterfaceField {
                            name: field.name.clone(),
                            ty: self.ty(field.ty)?,
                            offset_bytes: offset,
                        })
                    })
                    .collect::<Result<_, InterfaceArtifactError>>()?,
            },
            HirTypeKind::Enum { variants } => {
                let variant_layout =
                    layout
                        .variants
                        .as_ref()
                        .ok_or(InterfaceArtifactError::Inconsistent(
                            "missing enum variant layout",
                        ))?;
                InterfaceNominalKind::Enum {
                    variants: variants
                        .iter()
                        .map(|id| {
                            let variant = self.hir.variant(*id).ok_or(
                                InterfaceArtifactError::Inconsistent("missing enum variant"),
                            )?;
                            let case = variant_layout
                                .cases
                                .iter()
                                .find(|candidate| candidate.variant == *id)
                                .ok_or(InterfaceArtifactError::Inconsistent(
                                    "missing enum case layout",
                                ))?;
                            let fields = variant
                                .fields
                                .iter()
                                .map(|field_id| {
                                    let field = self.hir.field(*field_id).ok_or(
                                        InterfaceArtifactError::Inconsistent("missing enum field"),
                                    )?;
                                    let offset = case
                                        .fields
                                        .iter()
                                        .find(|candidate| candidate.field == *field_id)
                                        .ok_or(InterfaceArtifactError::Inconsistent(
                                            "missing enum field layout",
                                        ))?
                                        .offset_bytes;
                                    Ok(InterfaceField {
                                        name: field.name.clone(),
                                        ty: self.ty(field.ty)?,
                                        offset_bytes: offset,
                                    })
                                })
                                .collect::<Result<_, InterfaceArtifactError>>()?;
                            Ok(InterfaceVariant {
                                name: variant.name.clone(),
                                discriminant: variant.discriminant,
                                payload_offset_bytes: case.payload_offset_bytes,
                                fields,
                            })
                        })
                        .collect::<Result<_, InterfaceArtifactError>>()?,
                }
            }
            _ => {
                return Err(InterfaceArtifactError::Inconsistent(
                    "named non-nominal type",
                ));
            }
        };
        Ok(InterfaceTypeDeclaration {
            identity,
            layout: interface_layout(layout),
            capabilities: self.hir.type_capabilities(definition.id).ok_or(
                InterfaceArtifactError::Inconsistent("missing type capability"),
            )?,
            kind,
        })
    }

    fn function(
        &mut self,
        module: &HirModule,
        function: &HirFunction,
    ) -> Result<InterfaceFunction, InterfaceArtifactError> {
        let contract =
            self.hir
                .contract(function.contract)
                .ok_or(InterfaceArtifactError::Inconsistent(
                    "missing function contract",
                ))?;
        if !contract.is_implicit || !contract.clauses.is_empty() {
            return Err(InterfaceArtifactError::Inconsistent(
                "explicit interface contracts are not part of artifact v1",
            ));
        }
        let parameters = function
            .signature
            .parameters
            .iter()
            .map(|ty| self.ty(*ty))
            .collect::<Result<Vec<_>, _>>()?;
        let result = self.ty(function.signature.return_type)?;
        let mut parameter_effects = Vec::new();
        let mut preconditions = Vec::new();
        for (index, ty) in function.signature.parameters.iter().copied().enumerate() {
            let parameter = u32::try_from(index)
                .map_err(|_| InterfaceArtifactError::Inconsistent("too many parameters"))?;
            let capabilities =
                self.hir
                    .type_capabilities(ty)
                    .ok_or(InterfaceArtifactError::Inconsistent(
                        "missing parameter capability",
                    ))?;
            let memory = memory_role(self.hir.type_kind(ty), capabilities)?;
            parameter_effects.push(InterfaceParameterEffect {
                parameter,
                transfer: match capabilities.value {
                    ValueCapability::Copy => InterfaceTransferMode::Copy,
                    ValueCapability::MoveOnly => InterfaceTransferMode::Move,
                },
                memory,
                drop: capabilities.drop,
            });
            preconditions.push(InterfacePrecondition::InitializedValue { parameter });
            match self.hir.type_kind(ty) {
                Some(HirTypeKind::Own { .. }) => {
                    preconditions.push(InterfacePrecondition::LiveOwner { parameter });
                }
                Some(HirTypeKind::Reference { mutability, .. }) => {
                    preconditions.push(InterfacePrecondition::LiveBorrow {
                        parameter,
                        mutability: *mutability,
                    });
                }
                _ => {}
            }
        }
        let result_capabilities = self
            .hir
            .type_capabilities(function.signature.return_type)
            .ok_or(InterfaceArtifactError::Inconsistent(
                "missing result capability",
            ))?;
        Ok(InterfaceFunction {
            identity: self.identity(module, &function.name),
            parameters,
            result,
            calling_convention: function.signature.calling_convention,
            borrow_result: function.signature.borrow_result,
            borrow_result_alternatives: function.signature.borrow_result_alternatives.clone(),
            effects: InterfaceEffectSkeleton {
                parameters: parameter_effects,
                preconditions,
                result_capabilities,
            },
        })
    }

    fn ty(&mut self, id: HirTypeId) -> Result<InterfaceType, InterfaceArtifactError> {
        let definition =
            self.hir
                .type_definition(id)
                .ok_or(InterfaceArtifactError::Inconsistent(
                    "missing interface type",
                ))?;
        if matches!(
            definition.kind,
            HirTypeKind::Struct { .. } | HirTypeKind::Enum { .. }
        ) {
            let name = definition
                .name
                .as_deref()
                .ok_or(InterfaceArtifactError::Inconsistent("unnamed nominal type"))?;
            let owner = *self
                .type_owners
                .get(&id)
                .ok_or(InterfaceArtifactError::Inconsistent(
                    "nominal type has no module",
                ))?;
            let module = self
                .hir
                .module(owner)
                .ok_or(InterfaceArtifactError::Inconsistent(
                    "missing nominal module",
                ))?;
            return Ok(InterfaceType::Nominal(self.identity(module, name)));
        }
        Ok(match &definition.kind {
            HirTypeKind::Unit => InterfaceType::Unit,
            HirTypeKind::Bool => InterfaceType::Bool,
            HirTypeKind::Integer(integer) => InterfaceType::Integer(*integer),
            HirTypeKind::Own { pointee } => InterfaceType::Own(Box::new(self.ty(*pointee)?)),
            HirTypeKind::RawPointer {
                pointee,
                mutability,
            } => InterfaceType::RawPointer {
                pointee: Box::new(self.ty(*pointee)?),
                mutability: *mutability,
            },
            HirTypeKind::Reference {
                pointee,
                mutability,
                ..
            } => InterfaceType::Reference {
                pointee: Box::new(self.ty(*pointee)?),
                mutability: *mutability,
            },
            HirTypeKind::Array { element, length } => InterfaceType::Array {
                element: Box::new(self.ty(*element)?),
                length: *length,
            },
            HirTypeKind::Slice {
                element,
                mutability,
            } => InterfaceType::Slice {
                element: Box::new(self.ty(*element)?),
                mutability: *mutability,
            },
            HirTypeKind::Tuple(elements) => InterfaceType::Tuple(
                elements
                    .iter()
                    .map(|element| self.ty(*element))
                    .collect::<Result<_, _>>()?,
            ),
            HirTypeKind::Function(function) => InterfaceType::Function {
                parameters: function
                    .parameters
                    .iter()
                    .map(|parameter| self.ty(*parameter))
                    .collect::<Result<_, _>>()?,
                result: Box::new(self.ty(function.return_type)?),
                calling_convention: function.calling_convention,
            },
            HirTypeKind::Never => InterfaceType::Never,
            HirTypeKind::Struct { .. } | HirTypeKind::Enum { .. } => {
                return Err(InterfaceArtifactError::Inconsistent(
                    "anonymous nominal interface type",
                ));
            }
            HirTypeKind::GenericParameter(_) => {
                return Err(InterfaceArtifactError::UnsupportedType);
            }
        })
    }
}

fn module_identity(module: &HirModule) -> InterfaceModuleIdentity {
    InterfaceModuleIdentity {
        path: module.path.segments().to_vec(),
    }
}

fn interface_layout(layout: &HirLayout) -> InterfaceLayout {
    InterfaceLayout {
        size_bytes: layout.size_bytes,
        alignment: layout.alignment,
        abi: layout.abi,
    }
}

fn memory_role(
    kind: Option<&HirTypeKind>,
    capabilities: TypeCapabilities,
) -> Result<InterfaceMemoryRole, InterfaceArtifactError> {
    Ok(
        match kind.ok_or(InterfaceArtifactError::Inconsistent(
            "missing parameter type",
        ))? {
            HirTypeKind::Own { .. } => InterfaceMemoryRole::Owner,
            HirTypeKind::RawPointer { .. } => InterfaceMemoryRole::RawPointer,
            HirTypeKind::Reference {
                mutability: HirMutability::Const,
                ..
            } => InterfaceMemoryRole::SharedBorrow,
            HirTypeKind::Reference {
                mutability: HirMutability::Mutable,
                ..
            } => InterfaceMemoryRole::MutableBorrow,
            _ if capabilities.contains_resource => InterfaceMemoryRole::AggregateResource,
            _ => InterfaceMemoryRole::PlainValue,
        },
    )
}
