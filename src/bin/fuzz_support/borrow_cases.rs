//! Bounded, source-generated borrow CFG/loop/call cases. Family selection is
//! ordinal-based so a full cycle cannot silently lose its negative coverage;
//! entropy varies values, loop/recursion depths, and the executed branch.

pub const FAMILY_COUNT: u64 = 8;

pub const fn expected_checked(ordinal: u64) -> bool {
    ordinal % FAMILY_COUNT < 4
}

pub fn source(ordinal: u64, entropy: u64) -> String {
    let value = entropy % 32 + 1;
    let depth = (entropy >> 8) % 4 + 1;
    let flag = entropy & 1 == 0;
    match ordinal % FAMILY_COUNT {
        0 => format!(
            "fn main() -> u64 {{ let mut value = {value}; let parent = &mut value;
                for i in 0..{depth} {{ let child = &mut *parent; bump(child); *parent = *parent + 1; }}
                return *parent; }}
             fn bump(r: &mut u64) {{ *r = *r + 1; return; }}"
        ),
        1 => format!(
            "fn main() -> u64 {{ let value = {value}; let r = recurse(&value, 0); return *r; }}
             fn recurse(r: &u64, n: u64) -> &u64 {{ if n == {depth} {{ return r; }} return recurse(r, n + 1); }}"
        ),
        2 => format!(
            "fn main() -> u64 {{ let value = {value}; let r = &value; return select(r, r, {flag}); }}
             fn select(a: &u64, b: &u64, flag: bool) -> u64 {{ if flag {{ return *a; }} return *b; }}"
        ),
        3 => format!(
            "fn main() -> u64 {{ let values = [{value}, 2, 3]; let r = identity(&values[..]); return r[0]; }}
             fn identity(r: &[u64]) -> &[u64] {{ return r; }}"
        ),
        4 => format!(
            "fn main() -> u64 {{ let mut value = {value}; let r = identity(&value); value = 0; return *r; }}
             fn identity(r: &u64) -> &u64 {{ return r; }}"
        ),
        5 => format!(
            "fn main() -> u64 {{ let mut value = {value}; let parent = &mut value;
                for i in 0..{depth} {{ let child = &mut *parent; *parent = 0; bump(child); }}
                return *parent; }}
             fn bump(r: &mut u64) {{ *r = *r + 1; return; }}"
        ),
        6 => format!(
            "fn main() -> u64 {{ return branch(false); }}
             fn branch(flag: bool) -> u64 {{ let mut value = {value}; let r = identity(&value);
                if flag {{ value = 0; }} return *r; }}
             fn identity(r: &u64) -> &u64 {{ return r; }}"
        ),
        _ => format!(
            "fn main() -> u64 {{ let values = [{value}, 2, 3]; let r = identity(&values[1..]); return r[2]; }}
             fn identity(r: &[u64]) -> &[u64] {{ return r; }}"
        ),
    }
}
