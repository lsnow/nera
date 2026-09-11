//! Canonical borrow-region identities and inclusion constraints.

use super::{HirFunctionId, HirRegionConstraintId, HirRegionId, HirScopeId, HirTypeId};
use crate::ByteSpan;

/// Source/producer role that introduced one borrow region.
///
/// Parameter and result regions are signature-visible. Lexical and inferred
/// regions are visible only in their owning scope and descendants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirRegionOrigin {
    LexicalScope {
        scope: HirScopeId,
    },
    Parameter {
        index: u32,
    },
    Result,
    Inferred {
        scope: HirScopeId,
    },
    /// A region-erased slot in a nominal aggregate declaration.
    ///
    /// Values stored in this slot retain their concrete loan identity in VIR;
    /// this HIR region is only the type-level binder for `&T` field syntax.
    AggregateErased,
}

impl HirRegionOrigin {
    /// Returns the lexical scope that bounds this region, when it has one.
    #[must_use]
    pub const fn lexical_scope(self) -> Option<HirScopeId> {
        match self {
            Self::LexicalScope { scope } | Self::Inferred { scope } => Some(scope),
            Self::Parameter { .. } | Self::Result | Self::AggregateErased => None,
        }
    }
}

/// Entity that owns one canonical HIR borrow-region declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirRegionOwner {
    Function(HirFunctionId),
    Type(HirTypeId),
}

/// One canonical borrow region owned by a function or aggregate type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HirRegion {
    pub id: HirRegionId,
    pub owner: HirRegionOwner,
    pub origin: HirRegionOrigin,
    pub span: ByteSpan,
}

/// Canonical `subregion <= superregion` inclusion constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HirRegionConstraint {
    pub id: HirRegionConstraintId,
    pub owner: HirFunctionId,
    pub subregion: HirRegionId,
    pub superregion: HirRegionId,
    pub span: ByteSpan,
}
