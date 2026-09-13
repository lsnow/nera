pub const SOURCE: &str = r#"
fn main() -> u64 {
    let mut x = 1;
    assert x == 1;
    x = 2;
    assert x == 2 && !(x == 3);
    let p = alloc<u64>(1);
    assert alive(p.region);
    *p = x;
    assert initialized(p, 0..1);
    let value = *p;
    free(p);
    return value;
}
"#;

pub fn erased() -> String {
    // Preserve all byte offsets, so source metadata cannot mask runtime changes.
    SOURCE
        .split('\n')
        .map(|line| {
            if line.trim_start().starts_with("assert ") {
                " ".repeat(line.len())
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}
