//! Typed identifiers for entities stored in one [`HirProgram`](super::HirProgram).

macro_rules! define_hir_id {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u32);

        impl $name {
            #[must_use]
            pub const fn new(raw: u32) -> Self {
                Self(raw)
            }

            #[must_use]
            pub const fn get(self) -> u32 {
                self.0
            }

            #[must_use]
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

define_hir_id!(/// Module table index.
    HirModuleId);
define_hir_id!(/// Function table index.
    HirFunctionId);
define_hir_id!(/// Source-type table index.
    HirTypeId);
define_hir_id!(/// Target-layout table index, deliberately distinct from [`HirTypeId`].
    HirLayoutId);
define_hir_id!(/// Field table index.
    HirFieldId);
define_hir_id!(/// Enum-variant table index.
    HirVariantId);
define_hir_id!(/// Function-contract table index.
    HirContractId);
define_hir_id!(/// Module-predicate table index.
    HirPredicateId);
define_hir_id!(/// Generic-parameter table index.
    HirGenericParameterId);
define_hir_id!(/// Reference-region identity.
    HirRegionId);
define_hir_id!(/// Borrow-region inclusion-constraint table index.
    HirRegionConstraintId);
define_hir_id!(/// Stable local index within one HIR function.
    HirLocalId);
define_hir_id!(/// Lexical-scope identity within one HIR function body.
    HirScopeId);
define_hir_id!(/// Structured loop identity within one HIR function body.
    HirLoopId);
define_hir_id!(/// Program-wide canonical preorder identity for a HIR node.
    HirNodeId);
define_hir_id!(/// Ghost/specification binder table index.
    HirSpecBinderId);
define_hir_id!(/// Pure specification term table index.
    HirSpecTermId);
define_hir_id!(/// Specification clause table index.
    HirSpecClauseId);
define_hir_id!(/// Proof-obligation table index.
    HirSpecProveId);
define_hir_id!(/// Audited trust-entry table index.
    HirTrustEntryId);
define_hir_id!(/// Loop-invariant table index.
    HirSpecLoopInvariantId);
