pub const INITIALIZE: &str = include_str!("../../spec/cases/verify/loop-arena-initialize.nera");
pub const ADJACENT_VIEWS: &str =
    "fn main()->u64 {let p=alloc<[u64;8]>(1); p[0]=7; p[7]=9; let mut total=0;
    {let left=&p[0]; let right=&p[7]; let mut i=1usize;
    while i<7usize {invariant 1usize<=i; invariant i<=7usize;
        p[i]=42; i=i+1usize;} total=*left+*right;} free(p); return total;}";

pub fn erase_invariants(source: &str) -> String {
    source
        .split_inclusive('\n')
        .map(|line| {
            if line.trim_start().starts_with("invariant ") {
                line.chars()
                    .map(|c| if c == '\n' { c } else { ' ' })
                    .collect()
            } else {
                line.to_owned()
            }
        })
        .collect()
}

pub fn initialized_update() -> String {
    INITIALIZE
        .replace(
            "let p = alloc<[u64; 8]>(1);",
            "let mut backing = [0,0,0,0,0,0,0,0]; let p = &mut backing;",
        )
        .replace("free(p);", "")
}

pub fn capacity_failure() -> String {
    INITIALIZE.replace("return initialize(6usize);", "return reserve(8usize);")
        + "\nfn reserve(end:usize)->u64 {if end<1usize {return 0;} if end>7usize {return 0;} return initialize(end);}\n"
}
