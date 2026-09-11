//! Canonical place, address and object values shared by lowering operations.

use super::cfg::LoweredValue;
use crate::frontend::hir::{HirLocalId, HirTypeId};
use crate::vir::{VirMemoryAccess, VirValueId};

#[derive(Clone, Debug)]
pub(super) enum LoweredPlace {
    Local(HirLocalId),
    Address(LoweredAddress),
    Slice(Box<LoweredValue>),
}

#[derive(Clone, Copy, Debug)]
pub(super) struct LoweredAddress {
    pub(super) pointer: VirValueId,
    pub(super) permission: VirValueId,
    pub(super) metadata: Option<VirValueId>,
    pub(super) ty: HirTypeId,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct LoweredObject {
    pub(super) pointer: VirValueId,
    pub(super) permission: VirValueId,
    pub(super) access: VirMemoryAccess,
    pub(super) drop_flag: Option<VirValueId>,
}
