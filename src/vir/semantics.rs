//! Frozen runtime semantics shared by every VIR consumer.

use super::{VirIntegerPredicate, VirUnitVersion};

/// Stable identity of a runtime semantic profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirSemanticProfileId {
    SystemV1,
    SystemV2,
}

/// Arithmetic behavior for one unsigned word operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirArithmeticSemantics {
    Wrapping,
    RuntimeFault,
    Unsupported,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirComparisonSemantics {
    Unsigned,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirPointerOffsetSemantics {
    /// Unsigned byte addition must remain within the same live allocation;
    /// the one-past address is representable but cannot be dereferenced.
    CheckedLiveAllocation,
    /// Live allocation bounds AND the preserved arithmetic domain. Domain
    /// containment is checked separately from numeric addition by consumers.
    CheckedLiveDomain,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirFailureDisposition {
    Abort,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirDivergenceSemantics {
    NoResult,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirProveSemantics {
    GhostErasedAfterVerification,
}

/// Complete semantic identity carried by raw runtime VIR and rechecked by the
/// validator before any consumer can obtain a resolved view.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirRuntimeSemanticProfile {
    pub id: VirSemanticProfileId,
    pub word_bits: u16,
    pub addition: VirArithmeticSemantics,
    pub subtraction: VirArithmeticSemantics,
    pub multiplication: VirArithmeticSemantics,
    pub division: VirArithmeticSemantics,
    pub remainder: VirArithmeticSemantics,
    pub shift_left: VirArithmeticSemantics,
    pub shift_right: VirArithmeticSemantics,
    pub division_by_zero: VirFailureDisposition,
    pub comparison: VirComparisonSemantics,
    pub pointer_offset: VirPointerOffsetSemantics,
    pub allocation_failure: VirFailureDisposition,
    pub memory_fault: VirFailureDisposition,
    pub runtime_check_failure: VirFailureDisposition,
    pub abort: VirFailureDisposition,
    pub divergence: VirDivergenceSemantics,
    pub prove: VirProveSemantics,
}

/// The arithmetic/failure profile accepted by current VIR.
pub const VIR_SYSTEM_SEMANTICS_V1: VirRuntimeSemanticProfile = VirRuntimeSemanticProfile {
    id: VirSemanticProfileId::SystemV1,
    word_bits: 64,
    addition: VirArithmeticSemantics::Wrapping,
    subtraction: VirArithmeticSemantics::Unsupported,
    multiplication: VirArithmeticSemantics::Unsupported,
    division: VirArithmeticSemantics::Unsupported,
    remainder: VirArithmeticSemantics::Unsupported,
    shift_left: VirArithmeticSemantics::Unsupported,
    shift_right: VirArithmeticSemantics::Unsupported,
    division_by_zero: VirFailureDisposition::Abort,
    comparison: VirComparisonSemantics::Unsigned,
    pointer_offset: VirPointerOffsetSemantics::CheckedLiveAllocation,
    allocation_failure: VirFailureDisposition::Abort,
    memory_fault: VirFailureDisposition::Abort,
    runtime_check_failure: VirFailureDisposition::Abort,
    abort: VirFailureDisposition::Abort,
    divergence: VirDivergenceSemantics::NoResult,
    prove: VirProveSemantics::GhostErasedAfterVerification,
};

impl VirRuntimeSemanticProfile {
    #[must_use]
    pub const fn canonical_for(version: VirUnitVersion) -> Option<Self> {
        match version {
            VirUnitVersion::V14
            | VirUnitVersion::V15
            | VirUnitVersion::V16
            | VirUnitVersion::V17
            | VirUnitVersion::V18
            | VirUnitVersion::V19
            | VirUnitVersion::V20
            | VirUnitVersion::V21 => Some(VIR_SYSTEM_SEMANTICS_V2),
            VirUnitVersion::V6
            | VirUnitVersion::V7
            | VirUnitVersion::V8
            | VirUnitVersion::V9
            | VirUnitVersion::V10
            | VirUnitVersion::V11
            | VirUnitVersion::V12
            | VirUnitVersion::V13 => Some(VIR_SYSTEM_SEMANTICS_V1),
            VirUnitVersion::V1
            | VirUnitVersion::V2
            | VirUnitVersion::V3
            | VirUnitVersion::V4
            | VirUnitVersion::V5 => None,
        }
    }

    #[must_use]
    pub const fn word_add(self, left: u64, right: u64) -> u64 {
        match self.addition {
            VirArithmeticSemantics::Wrapping => left.wrapping_add(right),
            VirArithmeticSemantics::RuntimeFault | VirArithmeticSemantics::Unsupported => {
                // Validation admits no current profile with these alternatives.
                left.wrapping_add(right)
            }
        }
    }

    #[must_use]
    pub const fn compare(self, predicate: VirIntegerPredicate, left: u64, right: u64) -> bool {
        match self.comparison {
            VirComparisonSemantics::Unsigned => match predicate {
                VirIntegerPredicate::Equal => left == right,
                VirIntegerPredicate::NotEqual => left != right,
                VirIntegerPredicate::LessThan => left < right,
                VirIntegerPredicate::LessOrEqual => left <= right,
                VirIntegerPredicate::GreaterThan => left > right,
                VirIntegerPredicate::GreaterOrEqual => left >= right,
            },
        }
    }

    #[must_use]
    pub const fn checked_pointer_offset(
        self,
        base: u64,
        delta: u64,
        allocation_size: u64,
    ) -> Option<u64> {
        match self.pointer_offset {
            VirPointerOffsetSemantics::CheckedLiveAllocation
            | VirPointerOffsetSemantics::CheckedLiveDomain => match base.checked_add(delta) {
                Some(offset) if offset <= allocation_size => Some(offset),
                Some(_) | None => None,
            },
        }
    }
}

/// Current profile: word arithmetic is unchanged; addresses cannot escape
/// their canonical subobject/sequence extent merely by remaining in allocation.
pub const VIR_SYSTEM_SEMANTICS_V2: VirRuntimeSemanticProfile = VirRuntimeSemanticProfile {
    id: VirSemanticProfileId::SystemV2,
    pointer_offset: VirPointerOffsetSemantics::CheckedLiveDomain,
    ..VIR_SYSTEM_SEMANTICS_V1
};
