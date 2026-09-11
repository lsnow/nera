//! Validated-IR/state inconsistencies, distinct from unresolved resource obligations.
use super::{
    AbstractAllocationError, ContractApplicationError, Error, ResourceStateDefinitionError,
    VirLoanId, VirMemoryAccess, VirType, VirValueId, VirVariantId, fmt,
};

/// Unsupported boundary or internal inconsistency while applying transfer to
/// structurally validated VIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransferError {
    MissingLoanTransferContext,
    InvalidValidatedLoan(VirLoanId),
    StateDefinition(ResourceStateDefinitionError),
    InvalidAllocation(AbstractAllocationError),
    AbstractValueTypeMismatch {
        value: VirValueId,
        expected: VirType,
        found: VirType,
    },
    ResultTypeMismatch {
        value: VirValueId,
        declared: VirType,
        abstract_type: VirType,
    },
    InvalidValidatedAlignment(u64),
    InvalidValidatedMemoryAccess(VirMemoryAccess),
    InvalidValidatedEnumVariant {
        access: VirMemoryAccess,
        variant: VirVariantId,
    },
    InvalidValidatedCallShape {
        arguments: usize,
        parameters: usize,
        results: usize,
        expected_results: usize,
    },
    InvalidValidatedCallResultType {
        value: VirValueId,
        declared: VirType,
        expected: VirType,
    },
    InvalidDerivedRange,
    ContractApplication(ContractApplicationError),
}

impl From<ResourceStateDefinitionError> for TransferError {
    fn from(error: ResourceStateDefinitionError) -> Self {
        Self::StateDefinition(error)
    }
}

impl From<AbstractAllocationError> for TransferError {
    fn from(error: AbstractAllocationError) -> Self {
        Self::InvalidAllocation(error)
    }
}

impl From<ContractApplicationError> for TransferError {
    fn from(error: ContractApplicationError) -> Self {
        Self::ContractApplication(error)
    }
}

impl fmt::Display for TransferError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingLoanTransferContext => {
                formatter.write_str("loan effect transfer requires a validated borrow environment")
            }
            Self::InvalidValidatedLoan(loan) => write!(
                formatter,
                "validated VIR contains invalid loan metadata for l{}",
                loan.get()
            ),
            Self::StateDefinition(error) => error.fmt(formatter),
            Self::InvalidAllocation(error) => error.fmt(formatter),
            Self::AbstractValueTypeMismatch {
                value,
                expected,
                found,
            } => write!(
                formatter,
                "abstract value %{} has type {found:?}; expected {expected:?}",
                value.get()
            ),
            Self::ResultTypeMismatch {
                value,
                declared,
                abstract_type,
            } => write!(
                formatter,
                "transfer result %{} is declared {declared:?} but produced {abstract_type:?}",
                value.get()
            ),
            Self::InvalidValidatedAlignment(alignment) => write!(
                formatter,
                "validated VIR contains invalid allocation alignment {alignment}"
            ),
            Self::InvalidValidatedMemoryAccess(access) => write!(
                formatter,
                "validated VIR contains unresolved memory access type{}/layout{}",
                access.ty.get(),
                access.layout.get()
            ),
            Self::InvalidValidatedEnumVariant { access, variant } => write!(
                formatter,
                "validated VIR enum type{}/layout{} has no variant{}",
                access.ty.get(),
                access.layout.get(),
                variant.get()
            ),
            Self::InvalidValidatedCallShape {
                arguments,
                parameters,
                results,
                expected_results,
            } => write!(
                formatter,
                "validated call has {arguments} arguments for {parameters} parameters and \
                 {results} results for {expected_results} expected results"
            ),
            Self::InvalidValidatedCallResultType {
                value,
                declared,
                expected,
            } => write!(
                formatter,
                "validated call result %{} is declared {declared:?}; expected {expected:?}",
                value.get()
            ),
            Self::InvalidDerivedRange => {
                formatter.write_str("transfer produced an invalid byte range")
            }
            Self::ContractApplication(error) => error.fmt(formatter),
        }
    }
}

impl Error for TransferError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::StateDefinition(error) => Some(error),
            Self::InvalidAllocation(error) => Some(error),
            Self::ContractApplication(error) => Some(error),
            _ => None,
        }
    }
}
