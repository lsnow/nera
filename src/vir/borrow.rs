//! Canonical borrow-region declarations and closed loan-effect metadata.

use super::{
    VirBlockId, VirBorrowRegionConstraintId, VirBorrowRegionId, VirFunctionId, VirLoanId,
    VirMemoryAccess, VirOriginId, VirValueId,
};

/// Frame-local names for interface loans; instruction-defined loans occupy
/// the lower half of the identifier space.
pub(crate) fn interface_loan_id(parameter: u32) -> VirLoanId {
    VirLoanId::new(u32::MAX - parameter)
}

/// Source/ABI role that introduced one VIR borrow region.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirBorrowRegionOrigin {
    Lexical,
    Parameter { index: u32 },
    Result { index: u32 },
    Inferred,
}

/// Program points at which a reference in one borrow region may be used.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirBorrowRegionScope {
    /// Signature-visible region spanning the complete function.
    Function,
    /// Canonical sorted set of CFG blocks retained after lexical lowering.
    Blocks(Vec<VirBlockId>),
}

/// One canonical borrow region owned by exactly one VIR function.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VirBorrowRegion {
    pub id: VirBorrowRegionId,
    pub owner: VirFunctionId,
    pub origin: VirBorrowRegionOrigin,
    pub scope: VirBorrowRegionScope,
    pub source_origin: VirOriginId,
}

/// Canonical `subregion <= superregion` inclusion constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirBorrowRegionConstraint {
    pub id: VirBorrowRegionConstraintId,
    pub owner: VirFunctionId,
    pub subregion: VirBorrowRegionId,
    pub superregion: VirBorrowRegionId,
    pub source_origin: VirOriginId,
}

/// Borrow-region universe shared by validation and verification.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VirBorrowEnvironment {
    regions: Vec<VirBorrowRegion>,
    constraints: Vec<VirBorrowRegionConstraint>,
}

impl VirBorrowEnvironment {
    /// Bounded reachability for an authority-selected parent's actual region.
    /// None means a missing region or exhausted edge-scan budget, never an
    /// implicit inclusion assumption. Edges in other functions are irrelevant.
    pub(crate) fn includes(
        &self,
        sub: VirBorrowRegionId,
        sup: VirBorrowRegionId,
        limit: usize,
    ) -> Option<bool> {
        let owner = self.region(sub)?.owner;
        if self.region(sup)?.owner != owner {
            return Some(false);
        }
        if sub == sup {
            return Some(true);
        }
        let mut seen = std::collections::BTreeSet::new();
        let mut pending = vec![sub];
        let mut visits = 0usize;
        while let Some(current) = pending.pop() {
            if !seen.insert(current) {
                continue;
            }
            for edge in self.constraints.iter().filter(|edge| edge.owner == owner) {
                visits = visits.checked_add(1)?;
                if visits > limit {
                    return None;
                }
                if edge.subregion == current {
                    if edge.superregion == sup {
                        return Some(true);
                    }
                    pending.push(edge.superregion);
                }
            }
        }
        Some(false)
    }
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            regions: Vec::new(),
            constraints: Vec::new(),
        }
    }

    /// Constructs raw tables. [`super::VirUnit::validate`] remains responsible
    /// for density, ownership, origin and scope invariants.
    #[must_use]
    pub const fn from_tables(
        regions: Vec<VirBorrowRegion>,
        constraints: Vec<VirBorrowRegionConstraint>,
    ) -> Self {
        Self {
            regions,
            constraints,
        }
    }

    #[must_use]
    pub fn regions(&self) -> &[VirBorrowRegion] {
        &self.regions
    }

    #[must_use]
    pub fn constraints(&self) -> &[VirBorrowRegionConstraint] {
        &self.constraints
    }

    #[must_use]
    pub fn region(&self, id: VirBorrowRegionId) -> Option<&VirBorrowRegion> {
        self.regions
            .get(id.get() as usize)
            .filter(|region| region.id == id)
    }

    #[must_use]
    pub fn constraint(
        &self,
        id: VirBorrowRegionConstraintId,
    ) -> Option<&VirBorrowRegionConstraint> {
        self.constraints
            .get(id.get() as usize)
            .filter(|constraint| constraint.id == id)
    }
}

/// Access kind granted by one canonical loan.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirLoanKind {
    Shared,
    Mutable,
}

/// Canonical allocation-relative half-open range protected by a loan.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirLoanRange {
    pub start_bytes: u64,
    pub end_bytes: u64,
}

impl VirLoanRange {
    #[must_use]
    pub const fn len_bytes(self) -> Option<u64> {
        self.end_bytes.checked_sub(self.start_bytes)
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.start_bytes <= other.start_bytes && other.end_bytes <= self.end_bytes
    }
}

/// Immutable metadata repeated by every effect for independent validation.
///
/// `reference` is the canonical logical `Reference<T>` memory access. The
/// source/result SSA slots are its physical pointer/permission pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirLoanEffect {
    pub loan: VirLoanId,
    pub kind: VirLoanKind,
    pub region: VirBorrowRegionId,
    pub parent: Option<VirLoanId>,
    pub source_pointer: VirValueId,
    pub source_permission: VirValueId,
    pub reference: VirMemoryAccess,
    pub range: VirLoanRange,
    pub origin: VirOriginId,
}

/// Authority-directed loan effect for interface references, dynamic children,
/// or references moved out of aggregate payloads (alias/end).
///
/// The permission carries the unforgeable loan identity.  Keeping the
/// nominal reference access here still lets the validator reject forged
/// pointer shapes without requiring lowering to predict which guarded loan
/// instance a field or parameter contains. Reborrow additionally declares its
/// fresh child identity and region on the instruction itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirLoanAuthorityEffect {
    pub source_pointer: VirValueId,
    pub source_permission: VirValueId,
    pub reference: VirMemoryAccess,
    pub origin: VirOriginId,
}
