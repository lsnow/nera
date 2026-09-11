//! One source/mutation/consumer manifest. No verifier-derived expected answers.
// Library/CLI and native consumers deliberately read different observations.
#![allow(dead_code)]
use nera::ResourceObligationKind as K;

#[derive(Clone, Copy, Debug)]
pub enum Fault {
    Initialization,
    Move,
    Lifetime,
    Borrow,
    Bounds,
    DoubleFree,
}
impl Fault {
    pub fn matches_execution(self, kind: &nera::VirExecutionErrorKind) -> bool {
        use nera::VirExecutionErrorKind as E;
        match self {
            Self::Initialization | Self::Move => matches!(
                kind,
                E::UninitializedRead { .. } | E::UninitializedObjectLeaf { .. }
            ),
            Self::Lifetime => matches!(
                kind,
                E::PermissionAlreadyConsumed(_) | E::UseAfterFree { .. }
            ),
            Self::DoubleFree => matches!(kind, E::DoubleFree { .. }),
            Self::Borrow => matches!(kind, E::LoanAccessConflict { .. } | E::LoanConflict { .. }),
            Self::Bounds => matches!(kind, E::IndexOutOfBounds { .. }),
        }
    }
    pub fn matches(self, kind: K) -> bool {
        match self {
            Self::Initialization => matches!(
                kind,
                K::MemoryInitialized { .. } | K::ObjectValueBytesInitialized { .. }
            ),
            Self::Move => matches!(
                kind,
                K::ResourcePayloadAvailable { .. }
                    | K::ObjectValueBytesInitialized { .. }
                    | K::MemoryInitialized { .. }
            ),
            Self::Lifetime | Self::DoubleFree => matches!(
                kind,
                K::AllocationLive { .. }
                    | K::ObjectAllocationLive { .. }
                    | K::PermissionAvailable { .. }
                    | K::PermissionCanFree { .. }
                    | K::AllocationOwned { .. }
            ),
            Self::Borrow => matches!(
                kind,
                K::LoanCompatible { .. }
                    | K::LoanParentActive { .. }
                    | K::LoanRegionIncluded { .. }
            ),
            Self::Bounds => matches!(
                kind,
                K::IndexWithinBounds { .. } | K::SliceIndexWithinBounds { .. }
            ),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Mutation {
    pub name: &'static str,
    pub from: &'static str,
    pub to: &'static str,
    pub fault: Fault,
    /// Concrete execution on the two chosen guards; None means a runtime fault.
    pub execution: [Option<u64>; 2],
}

#[derive(Debug)]
pub struct Case {
    pub name: &'static str,
    pub path: &'static str,
    pub source: String,
    pub branch: usize,
    pub value: u64,
    pub allocations: usize,
    /// These call sites must actually apply a Closed summary, not just use a skeleton.
    pub applied: &'static [(&'static str, &'static str)],
    pub recursive: Option<&'static str>,
    /// Checked body, but this edge still uses the conservative call skeleton.
    pub skeleton: Option<(&'static str, &'static str)>,
    pub mutations: &'static [Mutation],
}

pub fn replace_once(source: &str, from: &str, to: &str) -> String {
    assert_eq!(source.matches(from).count(), 1, "mutation anchor: {from}");
    source.replacen(from, to, 1)
}

pub fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for branch in 0..2 {
        let flag = if branch == 0 { "true" } else { "false" };
        macro_rules! fixture {
            ($file:literal) => {
                (
                    concat!("spec/cases/verify/", $file, ".nera"),
                    include_str!(concat!("../../spec/cases/verify/", $file, ".nera")),
                )
            };
        }
        let (path, source) = fixture!("relation-composition");
        cases.push(Case {
            name: "range-init-recursive-slice",
            path,
            source: replace_once(
                source,
                "build(3usize, 1usize)",
                if branch == 0 {
                    "build(3usize, 1usize)"
                } else {
                    "build(3usize, 3usize)"
                },
            ),
            branch,
            value: if branch == 0 { 42 } else { 0 },
            allocations: 0,
            applied: &[],
            recursive: None,
            skeleton: Some(("build", "edit")),
            mutations: &[Mutation {
                name: "missing-prefix-initialization",
                from: "a[i] = 42;",
                to: "let skipped = 42;",
                fault: Fault::Initialization,
                execution: [None, Some(0)],
            }],
        });
        let (path, source) = fixture!("partial-refill");
        cases.push(Case {
            name: "nested-move-refill",
            path,
            source: replace_once(source, "return true;", &format!("return {flag};")),
            branch,
            value: 42,
            allocations: 3,
            applied: &[("main", "choose")],
            recursive: None,
            skeleton: None,
            mutations: &[Mutation {
                name: "missing-refill",
                from: "value.nested = moved;",
                to: "",
                fault: Fault::Move,
                execution: [None, None],
            }],
        });
        let (path, source) = fixture!("summary-conditional");
        cases.push(Case {
            name: "conditional-owner-provenance",
            path,
            source: replace_once(source, "run(true)", &format!("run({flag})")),
            branch,
            value: 42,
            allocations: branch + 1,
            applied: &[("run", "outer"), ("outer", "choose")],
            recursive: None,
            skeleton: None,
            mutations: &[Mutation {
                name: "freed-fresh-result",
                from: "*q = 42;",
                to: "free(q);",
                fault: Fault::Lifetime,
                execution: [Some(42), None],
            }],
        });
        let (path, source) = fixture!("summary-borrows");
        cases.push(Case {
            name: "borrowed-child-summary",
            path,
            source: replace_once(source, "run(true)", &format!("run({flag})")),
            branch,
            value: if branch == 0 { 42 } else { 21 },
            allocations: 0,
            applied: &[("run", "outer"), ("outer", "inner")],
            recursive: None,
            skeleton: None,
            mutations: &[Mutation {
                name: "parent-write-during-child-loan",
                from: "view[0] = view[0] + 1;",
                to: "parent[0] = 0; view[0] = view[0] + 1;",
                fault: Fault::Borrow,
                execution: [None, None],
            }],
        });
        let (path, source) = fixture!("sibling-slices");
        cases.push(Case {
            name: "disjoint-sibling-regions",
            path,
            source: replace_once(
                source,
                "split(2usize)",
                if branch == 0 {
                    "split(2usize)"
                } else {
                    "split(0usize)"
                },
            ),
            branch,
            value: if branch == 0 { 42 } else { 0 },
            allocations: 0,
            applied: &[("main", "split")],
            recursive: None,
            skeleton: None,
            mutations: &[Mutation {
                name: "overlapping-siblings",
                from: "&mut parent[mid..]",
                to: "&mut parent[..mid]",
                fault: Fault::Borrow,
                execution: [None, Some(0)],
            }],
        });
        let (path, source) = fixture!("auto-memory-composition");
        cases.push(Case {
            name: "packet-init-move-raw-recursive-index",
            path,
            source: replace_once(source, "run(true)", &format!("run({flag})")),
            branch,
            value: 42,
            allocations: 1,
            applied: &[("run", "index")],
            recursive: Some("index"),
            skeleton: None,
            mutations: &[
                Mutation {
                    name: "recursive-index-out-of-bounds",
                    from: "return 1usize;",
                    to: "return 2usize;",
                    fault: Fault::Bounds,
                    execution: [None, Some(42)],
                },
                Mutation {
                    name: "missing-else-initialization",
                    from: "packet.word = 2;",
                    to: "",
                    fault: Fault::Initialization,
                    execution: [Some(42), None],
                },
                Mutation {
                    name: "double-free",
                    from: "free(owner);",
                    to: "free(owner); free(owner);",
                    fault: Fault::DoubleFree,
                    execution: [None, None],
                },
            ],
        });
    }
    cases
}
