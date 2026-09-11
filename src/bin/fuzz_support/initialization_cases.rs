//! Bounded initialization families shared by both fuzzers and acceptance tests.
//! Ordinal, not entropy, fixes coverage and the expected static verdict.

pub const FAMILY_COUNT: u64 = 8;

pub const fn expected_checked(ordinal: u64) -> bool {
    ordinal % FAMILY_COUNT < 4
}

pub fn source(ordinal: u64, entropy: u64) -> String {
    let value = entropy % 32 + 1;
    let length = (entropy >> 8) % 8 + 1;
    let flag = entropy & 1 == 0;
    match ordinal % FAMILY_COUNT {
        0 => format!(
            "struct Padded {{ flag: bool, words: [u64; {length}], }}
             fn main() -> u64 {{ let p = make({flag}); return read(&p); }}
             fn make(b: bool) -> Padded {{ let mut p: Padded;
               for i in 0usize..{length}usize {{ p.words[i] = {value}; }}
               if b {{ p.flag = true; return p; }} p.flag = false; return p; }}
             fn read(p: &Padded) -> u64 {{ return p.words[0]; }}"
        ),
        1 => format!(
            "struct Pair {{ owner: Own<u64>, word: u64, }}
             fn main() -> u64 {{ let a = alloc<u64>(1); *a = {value}; let mut p: Pair;
               p.owner = a; p.word = 1; let q = repair(p, {flag});
               let owner = q.owner; return *owner; }}
             fn repair(p: Pair, b: bool) -> Pair {{ let mut q = p; let moved = q.owner;
               if b {{ q.owner = moved; return q; }} q.owner = moved; return q; }}"
        ),
        2 => format!(
            "struct Pair {{ left: Own<u64>, right: Own<u64>, }}
             fn main() -> u64 {{ for i in 0..{length} {{ let mut p: Pair;
               let a = alloc<u64>(1); *a = {value}; p.left = a;
               if i == 0 {{ continue; }} if i == 2 {{ break; }} }} return {value}; }}"
        ),
        3 => format!(
            "enum Item {{ Empty, Full(Own<u64>), }}
             fn main() -> u64 {{ let p = alloc<Item>(1); let a = alloc<u64>(1); *a = {value};
               *p = Item::Full(a); if {flag} {{ *p = Item::Empty; }} free(p); return {value}; }}"
        ),
        4 => format!(
            "struct Pair {{ left: u64, right: u64, }}
             fn main() -> u64 {{ return branch(false); }}
             fn branch(b: bool) -> u64 {{ let mut p: Pair; p.left = {value};
               if b {{ return p.right; }} return p.left; }}"
        ),
        5 => format!(
            "fn main() -> u64 {{ let p = alloc<[u64; {length}]>(1);
               for i in 0usize..{length}usize {{ if i == 0usize {{ continue; }} p[i] = {value}; }}
               let answer = p[0]; free(p); return answer; }}"
        ),
        6 => format!(
            "struct Pair {{ left: u64, right: u64, }}
             fn main() -> u64 {{ let mut p: Pair; p.left = {value}; empty(&p); return {value}; }}
             fn empty(p: &Pair) {{ return; }}"
        ),
        _ => format!(
            "struct Pair {{ owner: Own<u64>, word: u64, }}
             fn main() -> u64 {{ let a = alloc<u64>(1); *a = {value}; let mut p: Pair;
               p.owner = a; p.word = 1; let owner = p.owner; let whole = p; return *owner; }}"
        ),
    }
}

/// Effect deletion is an untrusted proposal. Validation may reject it; otherwise
/// replay the verifier and execute only a fully checked result. A redundant
/// deleted write can be safe, so mutations do not have a blanket reject oracle.
pub fn check_effect_mutation(program: &nera::ValidatedVirUnit, ordinal: u64) {
    use nera::VirInstruction;
    let mut unit = program.as_unit().clone();
    let candidates = unit
        .runtime
        .functions
        .iter()
        .enumerate()
        .flat_map(|(f, body)| {
            body.blocks.iter().enumerate().flat_map(move |(b, block)| {
                block
                    .instructions
                    .iter()
                    .enumerate()
                    .filter_map(move |(i, item)| {
                        matches!(
                            item.instruction,
                            VirInstruction::Write { .. }
                                | VirInstruction::Initialize { .. }
                                | VirInstruction::Store { .. }
                                | VirInstruction::ObjectDrop { .. }
                                | VirInstruction::ResourceInitialize { .. }
                                | VirInstruction::EnumSetDiscriminant { .. }
                                | VirInstruction::ObjectTransfer { .. }
                        )
                        .then_some((f, b, i))
                    })
            })
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return;
    }
    let (f, b, i) = candidates[(ordinal % candidates.len() as u64) as usize];
    unit.runtime.functions[f].blocks[b].instructions.remove(i);
    unit.rebuild_source_map_from_runtime("initialization-effect-mutation.vir", 100_000);
    if let Ok(validated) = unit.into_validated() {
        let resolved = validated.resolve().expect("validated mutation resolves");
        let first = nera::verify_program(&resolved, nera::CfgAnalysisConfig::default());
        assert_eq!(
            first,
            nera::verify_program(&resolved, nera::CfgAnalysisConfig::default())
        );
        if first.is_ok_and(|result| result.is_memory_checked_core0()) {
            nera::interpret(resolved.runtime()).expect("checked effect mutation executes safely");
        }
    }
    let mut invalid_origin = program.as_unit().clone();
    let item = &mut invalid_origin.runtime.functions[f].blocks[b].instructions[i];
    item.source_span = nera::ByteSpan::new(usize::MAX - 1, usize::MAX).unwrap();
    assert!(
        invalid_origin.into_validated().is_err(),
        "out-of-source origin is not evidence"
    );
}
