//! Bounded call-graph/conditional/SCC families with independent expected verdicts.
//! All generated executions terminate; recursion depth, declaration order, branch
//! choice and wrapper depth vary without changing the safe/unsafe partition.
pub const FAMILY_COUNT: u64 = 8;
pub const fn expected_checked(ordinal: u64) -> bool {
    ordinal % FAMILY_COUNT < 4
}
pub fn source(ordinal: u64, entropy: u64) -> String {
    let bad = !expected_checked(ordinal);
    let depth = entropy % 4 + 1;
    let flag = entropy & 1 == 0;
    match ordinal % 4 {
        0 => {
            let index = usize::from(bad);
            let mut text = "fn main()->u64 { let a=[42]; return a[w0(0)]; }".to_owned();
            for i in 0..depth {
                let next = if i + 1 == depth {
                    "index".to_owned()
                } else {
                    format!("w{}", i + 1)
                };
                text.push_str(&format!("fn w{i}(n:u64)->usize {{ return {next}(n); }}"));
            }
            text.push_str(&format!("fn index(n:u64)->usize {{ if n=={depth} {{ return {index}usize; }} return index(n+1); }}"));
            text
        }
        1 => {
            let value = if bad { 1 } else { 0 };
            let a = format!(
                "fn a(n:u64)->usize {{ if n=={depth} {{ return {value}usize; }} return b(n+1); }}"
            );
            let b = format!(
                "fn b(n:u64)->usize {{ if n=={depth} {{ return {value}usize; }} return a(n+1); }}"
            );
            format!(
                "fn main()->u64 {{ let v=[42]; return v[a(0)]; }}{}{}",
                if flag { &a } else { &b },
                if flag { &b } else { &a }
            )
        }
        2 => {
            let write = if bad { "" } else { "*q=42;" };
            format!("fn main()->u64 {{ let p=alloc<u64>(1); *p=42; let q=pick(p,{flag},0); return *q; }}
            fn pick(p:Own<u64>,flag:bool,n:u64)->Own<u64> {{ if n=={depth} {{ if flag {{ return p; }} free(p); let q=alloc<u64>(1); {write} return q; }} return pick(p,flag,n+1); }}")
        }
        _ => {
            let access = if bad {
                "let a=[42]; let i=1usize; *p=a[i];"
            } else {
                "*p=42;"
            };
            format!("fn main()->u64 {{ let mut x=0; fill(&mut x,0); let r=id(&x); return *r; }}
            fn fill(p:&mut u64,n:u64) {{ if n=={depth} {{ {access} return; }} fill(p,n+1); return; }}
            fn id(p:&u64)->&u64 {{ return p; }}")
        }
    }
}
