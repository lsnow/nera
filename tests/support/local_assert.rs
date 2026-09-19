pub const SOURCE: &str = r#"
fn main() -> u64 {
    let mut x = 1;
    assert x == 1;
    x = 2;
    assert x == 2;
    let p = alloc<u64>(1);
    *p = x;
    assert *p == 2;
    let value = *p;
    free(p);
    return value;
}
"#;
