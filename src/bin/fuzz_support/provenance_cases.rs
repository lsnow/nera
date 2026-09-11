//! Bounded provenance families. Selection pins verdicts; entropy varies the
//! concrete branch, repeated allocations, subview offset and recursion depth.
pub const FAMILY_COUNT: u64 = 12;
pub const POSITIVE_COUNT: u64 = 6;

pub const fn expected_checked(ordinal: u64) -> bool {
    ordinal % FAMILY_COUNT < POSITIVE_COUNT
}

pub fn source(ordinal: u64, entropy: u64) -> String {
    let negative = !expected_checked(ordinal);
    let flag = entropy & 1 == 0;
    let count = entropy % 4 + 1;
    match ordinal % POSITIVE_COUNT {
        0 => {
            let other = if negative { "&raw b[1]" } else { "&raw a[1]" };
            format!(
                "fn main() -> u64 {{ return check({flag}); }}
                fn check(flag: bool) -> u64 {{ let a=[20,22]; let b=[0,0]; let mut p=&raw a[0];
                if choose(flag) {{ p=p+8; }} else {{ p={other}; }}
                if p==&raw a[1] {{ return 42; }} return 0; }}
                fn choose(flag: bool) -> bool {{ if flag {{ return true; }} return false; }}"
            )
        }
        1 => {
            let offset = if negative { 24 } else { 16 };
            format!(
                "fn main() -> u64 {{ for i in 0usize..{count}usize {{
                let owner=alloc<u64>(2); let begin=&raw *owner; let mut cursor=begin;
                for j in 0usize..2usize {{ cursor=cursor+0; }}
                let end=cursor+{offset};
                if ptr_byte_distance(begin,end)!=16usize {{ return 0; }} free(owner);
                }} return 42; }}"
            )
        }
        2 => {
            let other = if negative {
                "&raw p.right[0]"
            } else {
                "(&raw p.left[1])+8"
            };
            format!(
                "struct Pair {{ left: [u64;2], right: [u64;2], }}
                fn main() -> u64 {{ let p=Pair {{ left:[20,22],right:[0,0] }};
                let begin=&raw p.left[0]; let end=begin+16; let other={other};
                if end==other {{ return 42; }} return 0; }}"
            )
        }
        3 => {
            let start = entropy % 3;
            let end = start + 1;
            let offset = if negative { 16 } else { 8 };
            format!(
                "fn main() -> u64 {{ let a=[1,2,3,4]; let empty=identity(&a[4..4]);
                if len(empty)!=0usize {{ return 0; }} let view=identity(&a[{start}..{end}]);
                let begin=&raw view[0]; let end=begin+{offset};
                if ptr_byte_distance(begin,end)==8usize {{ return 42; }} return 0; }}
                fn identity(a: &[u64]) -> &[u64] {{ return a; }}"
            )
        }
        4 => {
            let tail = if negative {
                "consume(b); if old==old { return 42; } return 0;"
            } else {
                "let moved=b.p; let same=old==&raw *moved; free(moved); if same { return 42; } return 0;"
            };
            format!(
                "struct Box {{ p: Own<u64>, }}
                fn main() -> u64 {{ let p=alloc<u64>(1); *p=42; let old=&raw *p;
                let b=Box {{ p:p }}; {tail} }}
                fn consume(b: Box) {{ return; }}"
            )
        }
        _ => {
            let other = if negative { "b" } else { "a" };
            format!(
                "fn main() -> u64 {{ let x=42; let r=identity(&x,0); return compare(r,r); }}
                fn identity(r: &u64, n: u64) -> &u64 {{
                    if n=={count} {{ return r; }} return identity(r,n+1); }}
                fn compare(a: &u64,b: &u64) -> u64 {{ let x=&raw *a; let y=&raw *{other};
                    if x==y {{ return 42; }} return 0; }}"
            )
        }
    }
}
