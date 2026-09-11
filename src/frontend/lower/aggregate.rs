//! Aggregate-storage identities determined before CFG lowering.

use crate::ByteSpan;
use crate::frontend::hir::{HirLocalId, HirNodeId, HirTypeId};

/// Storage for an aggregate constructor or a resource-assignment RHS snapshot.
#[derive(Clone, Copy)]
pub(super) struct ObjectTemporaryStorage {
    pub(super) owner: HirNodeId,
    pub(super) ty: HirTypeId,
    pub(super) span: ByteSpan,
    pub(super) local: HirLocalId,
}
