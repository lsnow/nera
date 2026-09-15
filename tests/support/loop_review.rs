pub const MIXED: &str = "fn main()->u64 {
    let mut i=0;
    while i<3 {
        invariant i<=3;
        i=i+1;
    }
    let mut j=0;
    while j<3 {j=j+1;}
    return i+j;
}";

pub const FOR_BOUND: &str = "fn main()->u64 {return count(3usize);}
fn count(n:usize)->u64 {
    let mut total=0;
    for i in 0usize..n {
        invariant i<=n;
        total=total+1;
    }
    return total;
}";

pub const READ_ONLY: &str = "fn main()->u64 {
    let p=alloc<u64>(1); *p=7; let mut i=0;
    while i<3 {
        invariant i<=3;
        let value=*p; assert value==7;
        observe(&*p); i=i+1;
    }
    free(p); return 42;
}
fn observe(p:&u64) reads (); writes (); {return;}";

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
