//! Logical borrow-return coordinates shared by HIR and VIR, not proof facts.
//! The containing function/signature owns these indices. Physical slots,
//! concrete regions and actual loan tokens are deliberately absent.

/// Publication budget for complete guarded borrow-result worlds.
pub const MAX_BORROW_RESULT_ALTERNATIVES: usize = 4;
/// Publication budget for conjunctive atoms selecting one borrow-result world.
pub const MAX_BORROW_RESULT_GUARD_ATOMS: usize = 4;
/// Maximum number of mutually recursive borrow-returning functions admitted by
/// the pre-HIR structural source solver.
pub const MAX_BORROW_SOURCE_SCC_FUNCTIONS: usize = 64;
/// Maximum number of simultaneous source-lattice updates for one SCC or loop.
pub const MAX_BORROW_SOURCE_FIXPOINT_ITERATIONS: usize = 64;
/// Maximum number of source relations provisionally retained by one SCC.
pub const MAX_BORROW_SOURCE_RELATIONS: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BorrowAccess {
    Shared,
    Mutable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BorrowSliceBound {
    Constant(u64),
    /// One logical `usize` parameter, evaluated at function entry.
    Parameter(u32),
    /// The length metadata of the source slice parameter.
    SourceLength,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BorrowProjection {
    /// Exact input view, including the length of a slice.
    Whole,
    /// One statically resolved, pointer-free subobject of the source referent.
    Fixed {
        offset_bytes: u64,
        size_bytes: u64,
        alignment: u64,
    },
    /// One contiguous slice subview. Bounds are element indices in the source
    /// slice, not byte addresses, and are interpreted from entry snapshots.
    Slice {
        start: BorrowSliceBound,
        end: BorrowSliceBound,
        stride_bytes: u64,
        alignment: u64,
    },
}

/// One entry-snapshot predicate selecting a borrow-result world.  Guards use
/// logical parameter coordinates, never body-local SSA identities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BorrowGuardAtom {
    Boolean { parameter: u32, expected: bool },
}

/// A structural interface claim. Its owner must validate indices and shape;
/// the SSA checker and resource verifier must independently check its body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BorrowResultRelation {
    pub parameter: u32,
    pub result: u32,
    pub projection: BorrowProjection,
    pub access: BorrowAccess,
}

impl BorrowResultRelation {
    #[must_use]
    pub const fn whole(parameter: u32, access: BorrowAccess) -> Self {
        Self {
            parameter,
            result: 0,
            projection: BorrowProjection::Whole,
            access,
        }
    }
}

/// One guarded source alternative.  All atoms are conjunctive; alternatives
/// are disjunctive and must cover every normal return of a checked body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BorrowResultAlternative {
    pub guard: Vec<BorrowGuardAtom>,
    pub relation: BorrowResultRelation,
}

impl BorrowResultAlternative {
    #[must_use]
    pub fn boolean(parameter: u32, expected: bool, relation: BorrowResultRelation) -> Self {
        Self {
            guard: vec![BorrowGuardAtom::Boolean {
                parameter,
                expected,
            }],
            relation,
        }
    }
}
