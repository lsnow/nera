//! Bounded relation CFG/loop/call families. Ordinals pin both verdicts;
//! entropy changes executed indices, bounds and excluded branches.
pub const FAMILY_COUNT: u64 = 12;
pub const POSITIVE_COUNT: u64 = 6;
pub const fn expected_checked(ordinal: u64) -> bool {
    ordinal % FAMILY_COUNT < POSITIVE_COUNT
}

pub fn source(ordinal: u64, entropy: u64) -> String {
    let family = ordinal % FAMILY_COUNT;
    let source = match family % POSITIVE_COUNT {
        0 => include_str!("../../../spec/cases/verify/disjoint-elements.nera"),
        1 => include_str!("../../../spec/cases/verify/sibling-slices.nera"),
        2 => include_str!("../../../spec/cases/verify/strided-chunks.nera"),
        3 => include_str!("../../../spec/cases/verify/strided-regions.nera"),
        4 => include_str!("../../../spec/cases/verify/relation-composition.nera"),
        _ => include_str!("../../../spec/cases/verify/relation-acceptance.nera"),
    };
    let mut source = source.to_owned();
    if family.is_multiple_of(POSITIVE_COUNT) && entropy & 1 != 0 {
        source = source.replace("update(0usize, 2usize)", "update(2usize, 0usize)");
    }
    if family % POSITIVE_COUNT == 1 {
        source = source.replace("split(2usize)", &format!("split({}usize)", entropy % 3 + 1));
    }
    if family % POSITIVE_COUNT == 4 {
        let n = entropy % 4 + 1;
        source = source.replace(
            "build(3usize, 1usize)",
            &format!("build({n}usize, {}usize)", n - 1),
        );
    }
    if family % POSITIVE_COUNT == 5 {
        let n = entropy % 4 + 5;
        source = source.replace(
            "build(6usize, 1usize, 4usize)",
            &format!("build({n}usize, 1usize, 4usize)"),
        );
    }
    if family % POSITIVE_COUNT == 2 && entropy & 1 != 0 {
        source = source.replace("edit(0usize, 2usize)", "edit(1usize, 3usize)");
    }
    if family % POSITIVE_COUNT == 3 && entropy & 1 != 0 {
        source = source.replace(
            "edit(0usize, 1usize, 1usize, 2usize)",
            "edit(1usize, 0usize, 2usize, 1usize)",
        );
    }
    if !expected_checked(family) {
        let (from, to) = match family % POSITIVE_COUNT {
            0 => ("if i != j", "if true"),
            1 => ("parent[mid..]", "parent[..mid]"),
            2 => ("i + 2usize <= j", "i < j"),
            3 => ("if col != next", "if true"),
            4 => ("a[i] = 42;", "if i != 0usize { a[i] = 42; }"),
            _ => ("if len(view) > 0usize", "if true"),
        };
        let mutated = source.replace(from, to);
        assert_ne!(
            source, mutated,
            "relation mutation must hit family {family}"
        );
        source = mutated;
    }
    source
}
