pub const SOURCE: &str = include_str!("../../spec/cases/verify/spec-arena-local.nera");

pub fn erased() -> String {
    // Keep byte positions, so dump equality also checks runtime source mappings.
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
