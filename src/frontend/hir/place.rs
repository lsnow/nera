//! Typed HIR places and projections.

use super::{HirExpression, HirFieldId, HirLocalId, HirNodeId, HirTypeId, HirVariantId};
use crate::ByteSpan;

/// A storage location rooted at a local and refined by typed projections.
///
/// `ty` is the type after applying every projection. Validation recomputes it
/// from `base` and checks every intermediate [`HirProjection::result_type`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirPlace {
    pub id: HirNodeId,
    pub base: HirPlaceBase,
    pub projections: Vec<HirProjection>,
    pub ty: HirTypeId,
    pub span: ByteSpan,
}

/// The root of a place. Stage 6.2 initially admits only function locals.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirPlaceBase {
    Local(HirLocalId),
}

/// One typed step in a place projection chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirProjection {
    pub kind: HirProjectionKind,
    pub result_type: HirTypeId,
    pub span: ByteSpan,
}

/// Ways to refine a place without implicitly reading its value.
///
/// Runtime index and range expressions are boxed because expressions can in
/// turn contain places. This keeps the Rust representation finite and owned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirProjectionKind {
    Dereference,
    Field {
        field: HirFieldId,
    },
    TupleElement {
        index: u64,
    },
    ConstantIndex {
        index: u64,
    },
    DynamicIndex {
        index: Box<HirExpression>,
    },
    Slice {
        start: Option<Box<HirExpression>>,
        end: Option<Box<HirExpression>>,
    },
    Downcast {
        variant: HirVariantId,
    },
}
