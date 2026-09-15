pub const SCALAR: &str = include_str!("../../spec/cases/verify/loop-scalar-target.nera");
pub const UPDATE: &str = include_str!("../../spec/cases/verify/loop-update-target.nera");
pub const INITIALIZE: &str = include_str!("../../spec/cases/verify/loop-initialize-target.nera");

/// Erase only whole invariant lines, preserving all other text and byte spans.
pub fn erased(source: &str) -> String {
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

/// Local expansion keeps the same loop body but removes the contracted call
/// boundary. extent() supplies a runtime value with an exact inferred summary.
pub fn inline(source: &str, n: usize) -> String {
    let source = erased(source);
    let body = &source[source.find("    let ").unwrap()..];
    let body = body.replace("return i;", "if i == n { return 42; } return 99;");
    format!("fn main()->u64 {{ let n=extent();\n{body}\nfn extent()->usize {{return {n}usize;}}")
}
