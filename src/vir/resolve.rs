use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::ops::Deref;

use super::{
    RuntimeVirView, ValidatedVirUnit, VirBasicBlock, VirBlockId, VirCallTarget, VirFunction,
    VirFunctionId, VirInstruction, VirUnit,
};
use crate::ByteSpan;

/// Runtime-only resolved view consumed by execution and code generation.
///
/// It owns only the local-call index and borrows only the canonical memory and
/// runtime tables. There is no path from this type to specification tables.
///
/// ```compile_fail
/// fn observe_spec(view: &nera::ResolvedRuntimeVirView<'_>) {
///     let _ = view.specs;
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedRuntimeVirView<'unit> {
    runtime: RuntimeVirView<'unit>,
    functions_by_symbol: BTreeMap<String, VirFunctionId>,
}

impl<'unit> ResolvedRuntimeVirView<'unit> {
    #[must_use]
    pub const fn as_runtime(&self) -> RuntimeVirView<'unit> {
        self.runtime
    }

    /// Returns the uniquely bound function ID for a call target whose runtime
    /// signature and contract handle match the resolved unit.
    #[must_use]
    pub fn call_target_id(&self, target: &VirCallTarget) -> Option<VirFunctionId> {
        let id = *self.functions_by_symbol.get(&target.symbol)?;
        let function = self.function(id)?;
        (function.signature == target.signature && function.contract == target.contract)
            .then_some(id)
    }

    pub(super) fn function(&self, id: VirFunctionId) -> Option<&'unit VirFunction> {
        self.runtime
            .functions
            .iter()
            .find(|function| function.id == id)
    }

    pub(super) fn block(
        &self,
        function: VirFunctionId,
        block: VirBlockId,
    ) -> Option<&'unit VirBasicBlock> {
        self.function(function)?
            .blocks
            .iter()
            .find(|candidate| candidate.id == block)
    }

    pub(super) fn call_function(&self, target: &VirCallTarget) -> Option<&'unit VirFunction> {
        self.call_target_id(target).and_then(|id| self.function(id))
    }
}

impl<'unit> Deref for ResolvedRuntimeVirView<'unit> {
    type Target = RuntimeVirView<'unit>;

    fn deref(&self) -> &Self::Target {
        &self.runtime
    }
}

/// A validated VIR unit whose runtime calls and specification references have
/// crossed the single resolution boundary.
///
/// Runtime consumers require an explicit [`ResolvedVirUnit::runtime`] downgrade;
/// the full unit does not implicitly dereference to its runtime-only view.
///
/// ```compile_fail
/// fn execute_full(unit: &nera::ResolvedVirUnit<'_>) {
///     let _ = nera::interpret(unit);
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedVirUnit<'unit> {
    validated: &'unit ValidatedVirUnit,
    runtime: ResolvedRuntimeVirView<'unit>,
}

impl<'unit> ResolvedVirUnit<'unit> {
    pub(crate) const fn as_unit(&self) -> &'unit VirUnit {
        self.validated.as_unit()
    }

    /// Returns the execution/code-generation view. The returned type cannot
    /// observe contracts, ghost terms, Prove obligations or trust entries.
    #[must_use]
    pub const fn runtime(&self) -> &ResolvedRuntimeVirView<'unit> {
        &self.runtime
    }
}

/// A deterministic failure while binding validated VIR calls.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirResolutionError {
    kind: VirResolutionErrorKind,
    function: VirFunctionId,
    block: Option<VirBlockId>,
    source_span: ByteSpan,
}

impl VirResolutionError {
    #[must_use]
    pub const fn kind(&self) -> &VirResolutionErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn function(&self) -> VirFunctionId {
        self.function
    }

    #[must_use]
    pub const fn block(&self) -> Option<VirBlockId> {
        self.block
    }

    #[must_use]
    pub const fn source_span(&self) -> ByteSpan {
        self.source_span
    }
}

/// Machine-readable call-resolution errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirResolutionErrorKind {
    DuplicateFunctionSymbol(String),
    UnsupportedExternalCall(String),
    CallSignatureMismatch(String),
    CallContractMismatch(String),
    CallAbiMismatch(String),
}

impl fmt::Display for VirResolutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            VirResolutionErrorKind::DuplicateFunctionSymbol(symbol) => {
                write!(formatter, "duplicate VIR function symbol `{symbol}`")
            }
            VirResolutionErrorKind::UnsupportedExternalCall(symbol) => {
                write!(
                    formatter,
                    "external VIR call `{symbol}` has no execution binding"
                )
            }
            VirResolutionErrorKind::CallSignatureMismatch(symbol) => {
                write!(
                    formatter,
                    "VIR call target `{symbol}` has a mismatched signature"
                )
            }
            VirResolutionErrorKind::CallContractMismatch(symbol) => {
                write!(
                    formatter,
                    "VIR call target `{symbol}` has a mismatched contract"
                )
            }
            VirResolutionErrorKind::CallAbiMismatch(symbol) => {
                write!(
                    formatter,
                    "VIR call target `{symbol}` has a mismatched aggregate ABI"
                )
            }
        }
    }
}

impl Error for VirResolutionError {}

pub(super) fn resolve(
    validated: &ValidatedVirUnit,
) -> Result<ResolvedVirUnit<'_>, VirResolutionError> {
    let mut functions_by_symbol = BTreeMap::new();
    for function in validated.runtime().functions {
        if functions_by_symbol
            .insert(function.name.clone(), function.id)
            .is_some()
        {
            return Err(function_error(
                function,
                VirResolutionErrorKind::DuplicateFunctionSymbol(function.name.clone()),
            ));
        }
    }

    for function in validated.runtime().functions {
        for block in &function.blocks {
            for spanned in &block.instructions {
                let VirInstruction::Call { target, .. } = &spanned.instruction else {
                    continue;
                };
                let Some(callee_id) = functions_by_symbol.get(&target.symbol) else {
                    return Err(call_error(
                        function,
                        block,
                        spanned.source_span,
                        VirResolutionErrorKind::UnsupportedExternalCall(target.symbol.clone()),
                    ));
                };
                let callee = validated
                    .runtime()
                    .functions
                    .iter()
                    .find(|candidate| candidate.id == *callee_id)
                    .expect("validated VIR contains every indexed function");
                if callee.signature != target.signature {
                    return Err(call_error(
                        function,
                        block,
                        spanned.source_span,
                        VirResolutionErrorKind::CallSignatureMismatch(target.symbol.clone()),
                    ));
                }
                if callee.contract != target.contract {
                    return Err(call_error(
                        function,
                        block,
                        spanned.source_span,
                        VirResolutionErrorKind::CallContractMismatch(target.symbol.clone()),
                    ));
                }
                let callee_abi = validated
                    .runtime()
                    .abis
                    .function(callee.id)
                    .expect("validated VIR contains every function ABI");
                let target_abi = target
                    .abi
                    .clone()
                    .unwrap_or_else(|| super::VirAbiSignature::identity(&target.signature));
                if target_abi != callee_abi.signature {
                    return Err(call_error(
                        function,
                        block,
                        spanned.source_span,
                        VirResolutionErrorKind::CallAbiMismatch(target.symbol.clone()),
                    ));
                }
            }
        }
    }

    Ok(ResolvedVirUnit {
        validated,
        runtime: ResolvedRuntimeVirView {
            runtime: validated.runtime(),
            functions_by_symbol,
        },
    })
}

fn function_error(function: &VirFunction, kind: VirResolutionErrorKind) -> VirResolutionError {
    VirResolutionError {
        kind,
        function: function.id,
        block: None,
        source_span: function.source_span,
    }
}

fn call_error(
    function: &VirFunction,
    block: &VirBasicBlock,
    source_span: ByteSpan,
    kind: VirResolutionErrorKind,
) -> VirResolutionError {
    VirResolutionError {
        kind,
        function: function.id,
        block: Some(block.id),
        source_span,
    }
}
