use std::error::Error;
use std::fmt;
use std::str::FromStr;

use crate::{VirFunctionId, VirSignature, VirType};

const TARGET_TRIPLE: &str = "x86_64-unknown-linux-gnu";
const WORD_BYTES: u64 = 8;
const INTEGER_ARGUMENT_REGISTERS: [X86_64IntegerRegister; 6] = [
    X86_64IntegerRegister::Rdi,
    X86_64IntegerRegister::Rsi,
    X86_64IntegerRegister::Rdx,
    X86_64IntegerRegister::Rcx,
    X86_64IntegerRegister::R8,
    X86_64IntegerRegister::R9,
];
const CALLER_SAVED_REGISTERS: [X86_64IntegerRegister; 9] = [
    X86_64IntegerRegister::Rax,
    X86_64IntegerRegister::Rcx,
    X86_64IntegerRegister::Rdx,
    X86_64IntegerRegister::Rsi,
    X86_64IntegerRegister::Rdi,
    X86_64IntegerRegister::R8,
    X86_64IntegerRegister::R9,
    X86_64IntegerRegister::R10,
    X86_64IntegerRegister::R11,
];
const CALLEE_PRESERVED_REGISTERS: [X86_64IntegerRegister; 7] = [
    X86_64IntegerRegister::Rbx,
    X86_64IntegerRegister::Rbp,
    X86_64IntegerRegister::Rsp,
    X86_64IntegerRegister::R12,
    X86_64IntegerRegister::R13,
    X86_64IntegerRegister::R14,
    X86_64IntegerRegister::R15,
];
const ALLOCATABLE_CALLEE_SAVED_REGISTERS: [X86_64IntegerRegister; 5] = [
    X86_64IntegerRegister::Rbx,
    X86_64IntegerRegister::R12,
    X86_64IntegerRegister::R13,
    X86_64IntegerRegister::R14,
    X86_64IntegerRegister::R15,
];

/// The frozen stage 4.6 native target.
pub const X86_64_UNKNOWN_LINUX_GNU: X86_64LinuxTarget = X86_64LinuxTarget(());

/// Frozen configuration for the x86_64 GNU/Linux userspace backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64LinuxTarget(());

impl X86_64LinuxTarget {
    #[must_use]
    pub const fn triple(self) -> &'static str {
        TARGET_TRIPLE
    }

    #[must_use]
    pub const fn endianness(self) -> NativeEndianness {
        NativeEndianness::Little
    }

    #[must_use]
    pub const fn object_format(self) -> NativeObjectFormat {
        NativeObjectFormat::Elf64
    }

    #[must_use]
    pub const fn assembly_syntax(self) -> GnuAssemblySyntax {
        GnuAssemblySyntax::IntelNoPrefix
    }

    #[must_use]
    pub const fn isa_baseline(self) -> X86_64IsaBaseline {
        X86_64IsaBaseline::V1
    }

    #[must_use]
    pub const fn pointer_size_bytes(self) -> u8 {
        8
    }

    #[must_use]
    pub const fn runtime_word_size_bytes(self) -> u8 {
        WORD_BYTES as u8
    }

    #[must_use]
    pub const fn call_stack_alignment_bytes(self) -> u8 {
        16
    }

    #[must_use]
    pub const fn uses_red_zone(self) -> bool {
        false
    }

    #[must_use]
    pub const fn emits_position_independent_executables(self) -> bool {
        true
    }

    #[must_use]
    pub const fn integer_argument_registers(self) -> &'static [X86_64IntegerRegister] {
        &INTEGER_ARGUMENT_REGISTERS
    }

    #[must_use]
    pub const fn caller_saved_registers(self) -> &'static [X86_64IntegerRegister] {
        &CALLER_SAVED_REGISTERS
    }

    #[must_use]
    pub const fn callee_preserved_registers(self) -> &'static [X86_64IntegerRegister] {
        &CALLEE_PRESERVED_REGISTERS
    }

    /// Callee-preserved registers available after reserving `%rbp` and `%rsp`.
    #[must_use]
    pub const fn allocatable_callee_saved_registers(self) -> &'static [X86_64IntegerRegister] {
        &ALLOCATABLE_CALLEE_SAVED_REGISTERS
    }

    #[must_use]
    pub const fn direct_result_register(self) -> X86_64IntegerRegister {
        X86_64IntegerRegister::Rax
    }

    #[must_use]
    pub const fn stack_pointer_register(self) -> X86_64IntegerRegister {
        X86_64IntegerRegister::Rsp
    }

    #[must_use]
    pub const fn frame_pointer_register(self) -> X86_64IntegerRegister {
        X86_64IntegerRegister::Rbp
    }

    /// Produces an assembler-local symbol without embedding a user name.
    #[must_use]
    pub fn internal_function_symbol(self, function: VirFunctionId) -> String {
        format!(".Lnera_v0_fn_{}", function.get())
    }

    /// The only process-visible entry symbol emitted by native v0.
    #[must_use]
    pub const fn executable_entry_symbol(self) -> &'static str {
        "main"
    }

    /// Erases verifier-only types and classifies one remaining runtime word.
    #[must_use]
    pub const fn classify_type(self, ty: VirType) -> Option<X86_64RuntimeType> {
        match ty {
            VirType::U64 => Some(X86_64RuntimeType::U64),
            VirType::Bool => Some(X86_64RuntimeType::Bool),
            VirType::Pointer { .. } => Some(X86_64RuntimeType::Pointer),
            VirType::Permission => None,
        }
    }

    /// Erases permissions and assigns the frozen Nera-internal runtime ABI.
    pub fn classify_signature(
        self,
        signature: &VirSignature,
    ) -> Result<X86_64RuntimeSignature, X86_64AbiError> {
        let parameter_types = runtime_values(self, &signature.parameters);
        let result_types = runtime_values(self, &signature.results);
        check_value_count(X86_64AbiComponent::Parameters, parameter_types.len())?;
        check_value_count(X86_64AbiComponent::Results, result_types.len())?;

        let result_buffer = (result_types.len() > 1).then(|| X86_64ResultBuffer {
            pointer_register: X86_64IntegerRegister::Rdi,
            size_bytes: u64::from(
                u32::try_from(result_types.len())
                    .expect("the runtime result count was checked above"),
            ) * WORD_BYTES,
            alignment_bytes: WORD_BYTES as u8,
        });

        let reserved_registers = usize::from(result_buffer.is_some());
        let mut stack_parameter_count = 0_u32;
        let parameters = parameter_types
            .into_iter()
            .enumerate()
            .map(|(runtime_index, (vir_index, ty))| {
                let register_index = runtime_index + reserved_registers;
                let location = if let Some(register) =
                    INTEGER_ARGUMENT_REGISTERS.get(register_index).copied()
                {
                    X86_64AbiParameterLocation::Register(register)
                } else {
                    let slot = stack_parameter_count;
                    stack_parameter_count = stack_parameter_count
                        .checked_add(1)
                        .expect("the runtime parameter count was checked above");
                    X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(
                        slot,
                    ))
                };
                X86_64AbiParameter {
                    vir_index,
                    ty,
                    location,
                }
            })
            .collect();

        let indirect_results = result_types.len() > 1;
        let results = result_types
            .into_iter()
            .enumerate()
            .map(|(runtime_index, (vir_index, ty))| {
                let location = if indirect_results {
                    X86_64AbiResultLocation::ResultBuffer {
                        offset_bytes: u64::try_from(runtime_index)
                            .expect("the runtime result count was checked above")
                            * WORD_BYTES,
                    }
                } else {
                    X86_64AbiResultLocation::Register(X86_64IntegerRegister::Rax)
                };
                X86_64AbiResult {
                    vir_index,
                    ty,
                    location,
                }
            })
            .collect();

        Ok(X86_64RuntimeSignature {
            parameters,
            results,
            result_buffer,
            stack_parameter_count,
        })
    }

    /// Classifies the stricter libc `main` wrapper boundary.
    pub fn classify_entry(
        self,
        signature: &VirSignature,
    ) -> Result<X86_64EntryAbi, X86_64AbiError> {
        let runtime_signature = self.classify_signature(signature)?;
        if !signature.parameters.is_empty() {
            return Err(abi_error(X86_64AbiErrorKind::EntryParametersUnsupported {
                vir_count: signature.parameters.len(),
                runtime_count: runtime_signature.parameters.len(),
            }));
        }

        let result = match runtime_signature.results.as_slice() {
            [] => X86_64EntryResult::Unit,
            [result] if result.ty == X86_64RuntimeType::Bool => X86_64EntryResult::BoolExitStatus,
            [result] if result.ty == X86_64RuntimeType::U64 => {
                X86_64EntryResult::U64Low32ExitStatus
            }
            results => {
                return Err(abi_error(X86_64AbiErrorKind::EntryResultsUnsupported {
                    runtime_types: results.iter().map(|result| result.ty).collect(),
                }));
            }
        };

        Ok(X86_64EntryAbi {
            runtime_signature,
            result,
        })
    }
}

impl Default for X86_64LinuxTarget {
    fn default() -> Self {
        X86_64_UNKNOWN_LINUX_GNU
    }
}

impl fmt::Display for X86_64LinuxTarget {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(TARGET_TRIPLE)
    }
}

impl FromStr for X86_64LinuxTarget {
    type Err = NativeTargetError;

    fn from_str(triple: &str) -> Result<Self, Self::Err> {
        if triple == TARGET_TRIPLE {
            Ok(X86_64_UNKNOWN_LINUX_GNU)
        } else {
            Err(NativeTargetError {
                triple: triple.to_owned(),
            })
        }
    }
}

/// Byte order selected by a native target profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NativeEndianness {
    Little,
}

/// Object container selected by a native target profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NativeObjectFormat {
    Elf64,
}

/// GNU assembler syntax selected before assembly emission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GnuAssemblySyntax {
    IntelNoPrefix,
}

/// Minimum x86_64 instruction-set contract; no optional extension is assumed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64IsaBaseline {
    V1,
}

/// Integer registers named by the frozen internal calling convention.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64IntegerRegister {
    Rax,
    Rbx,
    Rdi,
    Rsi,
    Rdx,
    Rcx,
    Rbp,
    Rsp,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

/// Runtime word classes retained after verifier-only erasure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64RuntimeType {
    U64,
    Bool,
    Pointer,
}

/// Location of one ordinary runtime parameter at a Nera call boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64AbiParameterLocation {
    Register(X86_64IntegerRegister),
    CallerStack(X86_64CallerStackLocation),
}

/// Physical location of one argument passed in the frozen caller stack area.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64CallerStackLocation {
    slot: u32,
}

impl X86_64CallerStackLocation {
    #[must_use]
    pub const fn from_slot(slot: u32) -> Self {
        Self { slot }
    }

    /// Zero-based order among stack arguments.
    #[must_use]
    pub const fn slot(self) -> u32 {
        self.slot
    }

    /// Address relative to `%rsp` immediately before `call` executes.
    #[must_use]
    pub const fn offset_from_call_site_rsp_bytes(self) -> u64 {
        self.slot as u64 * WORD_BYTES
    }

    /// Address relative to `%rsp` at callee entry, above the return address.
    #[must_use]
    pub const fn offset_from_callee_entry_rsp_bytes(self) -> u64 {
        WORD_BYTES + self.offset_from_call_site_rsp_bytes()
    }

    /// Address after the mandatory `push rbp; mov rbp, rsp` prologue.
    #[must_use]
    pub const fn offset_from_callee_frame_pointer_bytes(self) -> u64 {
        2 * WORD_BYTES + self.offset_from_call_site_rsp_bytes()
    }
}

/// One retained parameter and its original VIR signature position.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64AbiParameter {
    vir_index: usize,
    ty: X86_64RuntimeType,
    location: X86_64AbiParameterLocation,
}

impl X86_64AbiParameter {
    #[must_use]
    pub const fn vir_index(self) -> usize {
        self.vir_index
    }

    #[must_use]
    pub const fn ty(self) -> X86_64RuntimeType {
        self.ty
    }

    #[must_use]
    pub const fn location(self) -> X86_64AbiParameterLocation {
        self.location
    }
}

/// Location of one ordinary runtime result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64AbiResultLocation {
    Register(X86_64IntegerRegister),
    ResultBuffer { offset_bytes: u64 },
}

/// One retained result and its original VIR signature position.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64AbiResult {
    vir_index: usize,
    ty: X86_64RuntimeType,
    location: X86_64AbiResultLocation,
}

impl X86_64AbiResult {
    #[must_use]
    pub const fn vir_index(self) -> usize {
        self.vir_index
    }

    #[must_use]
    pub const fn ty(self) -> X86_64RuntimeType {
        self.ty
    }

    #[must_use]
    pub const fn location(self) -> X86_64AbiResultLocation {
        self.location
    }
}

/// Hidden result-buffer contract for functions with multiple runtime results.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64ResultBuffer {
    pointer_register: X86_64IntegerRegister,
    size_bytes: u64,
    alignment_bytes: u8,
}

impl X86_64ResultBuffer {
    #[must_use]
    pub const fn pointer_register(self) -> X86_64IntegerRegister {
        self.pointer_register
    }

    #[must_use]
    pub const fn size_bytes(self) -> u64 {
        self.size_bytes
    }

    #[must_use]
    pub const fn alignment_bytes(self) -> u8 {
        self.alignment_bytes
    }
}

/// A VIR signature after permission erasure and ABI location assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64RuntimeSignature {
    parameters: Vec<X86_64AbiParameter>,
    results: Vec<X86_64AbiResult>,
    result_buffer: Option<X86_64ResultBuffer>,
    stack_parameter_count: u32,
}

impl X86_64RuntimeSignature {
    #[must_use]
    pub fn parameters(&self) -> &[X86_64AbiParameter] {
        &self.parameters
    }

    #[must_use]
    pub fn results(&self) -> &[X86_64AbiResult] {
        &self.results
    }

    #[must_use]
    pub const fn result_buffer(&self) -> Option<X86_64ResultBuffer> {
        self.result_buffer
    }

    #[must_use]
    pub const fn stack_parameter_count(&self) -> u32 {
        self.stack_parameter_count
    }

    #[must_use]
    pub const fn stack_argument_size_bytes(&self) -> u64 {
        self.stack_parameter_count as u64 * WORD_BYTES
    }

    /// Total caller stack area, including trailing padding for call alignment.
    #[must_use]
    pub const fn outgoing_stack_size_bytes(&self) -> u64 {
        align_up(
            self.stack_argument_size_bytes(),
            X86_64_UNKNOWN_LINUX_GNU.call_stack_alignment_bytes() as u64,
        )
    }

    #[must_use]
    pub const fn outgoing_stack_padding_bytes(&self) -> u64 {
        self.outgoing_stack_size_bytes() - self.stack_argument_size_bytes()
    }

    /// Bytes restored by the caller after the call returns.
    #[must_use]
    pub const fn caller_stack_cleanup_bytes(&self) -> u64 {
        self.outgoing_stack_size_bytes()
    }
}

/// Process-facing result behavior of the generated libc `main` wrapper.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64EntryResult {
    Unit,
    BoolExitStatus,
    U64Low32ExitStatus,
}

/// A signature admitted at the native executable entry boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64EntryAbi {
    runtime_signature: X86_64RuntimeSignature,
    result: X86_64EntryResult,
}

impl X86_64EntryAbi {
    #[must_use]
    pub const fn runtime_signature(&self) -> &X86_64RuntimeSignature {
        &self.runtime_signature
    }

    #[must_use]
    pub const fn result(&self) -> X86_64EntryResult {
        self.result
    }
}

/// Signature side whose runtime cardinality exceeded the frozen representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64AbiComponent {
    Parameters,
    Results,
}

/// Machine-readable x86_64 ABI classification failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64AbiErrorKind {
    TooManyRuntimeValues {
        component: X86_64AbiComponent,
        count: usize,
    },
    EntryParametersUnsupported {
        vir_count: usize,
        runtime_count: usize,
    },
    EntryResultsUnsupported {
        runtime_types: Vec<X86_64RuntimeType>,
    },
}

/// A deterministic failure while applying the frozen native ABI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64AbiError {
    kind: X86_64AbiErrorKind,
}

impl X86_64AbiError {
    #[must_use]
    pub const fn kind(&self) -> &X86_64AbiErrorKind {
        &self.kind
    }
}

impl fmt::Display for X86_64AbiError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            X86_64AbiErrorKind::TooManyRuntimeValues { component, count } => {
                write!(
                    formatter,
                    "x86_64 ABI {component:?} contain {count} runtime values; at most {} are representable",
                    u32::MAX
                )
            }
            X86_64AbiErrorKind::EntryParametersUnsupported {
                vir_count,
                runtime_count,
            } => write!(
                formatter,
                "native entry has {vir_count} VIR parameters ({runtime_count} after erasure); entry parameters are unsupported"
            ),
            X86_64AbiErrorKind::EntryResultsUnsupported { runtime_types } => write!(
                formatter,
                "native entry runtime results {runtime_types:?} cannot be represented as a process status"
            ),
        }
    }
}

impl Error for X86_64AbiError {}

/// Unsupported native target requested by exact target triple.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeTargetError {
    triple: String,
}

impl NativeTargetError {
    #[must_use]
    pub fn triple(&self) -> &str {
        &self.triple
    }

    #[must_use]
    pub const fn capability_failure_kind(&self) -> crate::CapabilityFailureKind {
        crate::CapabilityFailureKind::TargetUnsupported
    }
}

impl fmt::Display for NativeTargetError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "native target `{}` is unsupported; expected `{TARGET_TRIPLE}`",
            self.triple
        )
    }
}

impl Error for NativeTargetError {}

fn runtime_values(target: X86_64LinuxTarget, types: &[VirType]) -> Vec<(usize, X86_64RuntimeType)> {
    types
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(index, ty)| target.classify_type(ty).map(|ty| (index, ty)))
        .collect()
}

fn check_value_count(component: X86_64AbiComponent, count: usize) -> Result<(), X86_64AbiError> {
    if u32::try_from(count).is_err() {
        return Err(abi_error(X86_64AbiErrorKind::TooManyRuntimeValues {
            component,
            count,
        }));
    }
    Ok(())
}

const fn abi_error(kind: X86_64AbiErrorKind) -> X86_64AbiError {
    X86_64AbiError { kind }
}

const fn align_up(value: u64, alignment: u64) -> u64 {
    let remainder = value % alignment;
    if remainder == 0 {
        value
    } else {
        value + (alignment - remainder)
    }
}
