use std::env;
use std::process::ExitCode;

use nera::{SourceFile, VirInterpreterConfig, analyze, interpret_with_config};

#[path = "fuzz_support/spec_mutation.rs"]
mod spec_mutation;

#[path = "fuzz_support/borrow_cases.rs"]
mod borrow_cases;

#[path = "fuzz_support/initialization_cases.rs"]
mod initialization_cases;
#[path = "fuzz_support/provenance_cases.rs"]
mod provenance_cases;
#[path = "fuzz_support/relation_cases.rs"]
mod relation_cases;

use spec_mutation::check_spec_mutation;

const DEFAULT_ITERATIONS: u64 = 100_000;
const DEFAULT_SEED: u64 = 0x4e45_5241_4655_5a5a;
const MAX_RANDOM_BYTES: usize = 2_048;
const MAX_STRUCTURED_SIZE: usize = 2_048;
// Mutated loops need not terminate. Replay their success OR budget fault;
// this is an unverified determinism oracle, never a static safety verdict.
const MAX_REPLAY_STEPS: u64 = 4_096;
const BORROW_CASE_INTERVAL: u64 = 32;
const BORROW_CASE_OFFSET: u64 = 8;
const INITIALIZATION_CASE_OFFSET: u64 = 24;
const RELATION_CASE_OFFSET: u64 = 4;
const PROVENANCE_CASE_OFFSET: u64 = 12;

const BOUNDARY_CASES: &[&[u8]] = &[
    b"fn f() -> u64 { return 0xbe+1; }",
    b"fn f() -> u64 { return 1usize+2; }",
    b"fn generic<'a, 'b>() { return; }",
    b"fn f() { \"deferred\"; return; }",
    b"fn f() -> u64 { return foo(); }",
    b"fn f() { let memory=alloc<u64>(1); return; }",
    b"fn f() -> u64 { let alloc=1; return alloc; }",
    b"fn f() -> u64 { return 0xff.0; }",
    b"fn f() -> u64 { return 1e2.3; }",
];

const STRUCTURED_CASES: &[&[u8]] = &[
    b"fn blocks() -> u64 { let mut value = 0; { if true { value = 1; } else { value = 2; } } return value; }",
    b"fn looped() -> u64 { let mut index = 0; while index < 4 { index = index + 1; if index == 2 { continue; } } return index; }",
    b"fn ranged() -> u64 { let mut sum = 0; for item in begin()..5 { if item == 3 { break; } sum = sum + item; } return sum; } fn begin() -> u64 { return 0; }",
    b"fn selected() -> u64 { match choose() { 0 => { return 10; }, 2 if allow(true) => { return 20; }, _ => { return 30; }, } } fn choose() -> u64 { return 2; } fn allow(value: bool) -> bool { return value; }",
    b"fn nested() -> u64 { let mut sum = 0; for outer in 0..3 { let mut inner = 0; while inner < 3 { inner = inner + 1; if inner == 2 { continue; } sum = sum + outer; } } match sum { 6 => { return sum; }, _ => { return 0; }, } }",
    b"fn entry() -> u64 { return recur(0); } fn recur(value: u64) -> u64 { if value < 3 { return recur(value + 1); } return value; }",
];

const AGGREGATE_CASES: &[&[u8]] = &[
    include_bytes!("../../spec/cases/verify/initialization-interfaces.nera"),
    include_bytes!("../../spec/cases/verify/initialization-interfaces-owning.nera"),
    include_bytes!("../../spec/cases/verify/initialization-interface-incomplete.nera"),
    include_bytes!("../../spec/cases/verify/loop-initialization.nera"),
    include_bytes!("../../spec/cases/verify/loop-initialization-skipped.nera"),
    include_bytes!("../../spec/cases/verify/heap-construction.nera"),
    include_bytes!("../../spec/cases/verify/heap-enum-construction.nera"),
    b"struct Pair { left: u64, right: u64, } fn main() -> u64 { let p = alloc<Pair>(1); p.left = 42; let r = &*p; return r.left; }",
    include_bytes!("../../spec/cases/verify/partial-construction.nera"),
    include_bytes!("../../spec/cases/verify/partial-construction-loop.nera"),
    include_bytes!("../../spec/cases/verify/partial-refill.nera"),
    b"struct S { owner: Own<u64>, } fn main() -> u64 { let a = alloc<u64>(1); *a = 42; let v = S { owner: a }; let moved = v.owner; let r = &v; return 0; }",
    b"fn main() -> u64 { let mut v: [u64; 2]; v[0] = 9; v = [40, 2]; return v[0] + v[1]; }",
    b"fn main() -> u64 { let mut v: [u64; 2]; v[0] = 42; let r = &v; return 0; }",
    b"fn main() -> u64 { let mut i = 0; while i < 2 { let mut v: u64; if i == 0 { v = 42; } let x = v; i = i + 1; } return i; }",
    include_bytes!("../../spec/cases/aggregate/surface.nera"),
    include_bytes!("../../spec/cases/aggregate/dynamic-object.nera"),
    include_bytes!("../../spec/cases/aggregate/enum-surface.nera"),
    include_bytes!("../../spec/cases/aggregate/enum-switch.nera"),
    include_bytes!("../../spec/cases/aggregate/abi-direct.nera"),
    include_bytes!("../../spec/cases/aggregate/abi-indirect.nera"),
    b"fn slice_surface_stays_gated() -> u64 { let values = [1, 2]; let view = values[0..2]; return view[0]; }",
];

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut iterations = DEFAULT_ITERATIONS;
    let mut seed = DEFAULT_SEED;
    let mut args = env::args().skip(1);
    while let Some(argument) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("missing value after `{argument}`"))?;
        match argument.as_str() {
            "--iterations" => {
                iterations = value
                    .parse()
                    .map_err(|_| format!("invalid iteration count `{value}`"))?;
            }
            "--seed" => {
                seed = value
                    .parse()
                    .map_err(|_| format!("invalid seed `{value}`"))?;
            }
            _ => return Err(format!("unknown option `{argument}`")),
        }
    }

    let mut generator = Generator::new(seed);
    for case in 0..iterations {
        let bytes = generate_case(&mut generator, case);
        let source = SourceFile::new(format!("fuzz-{case}.nera"), bytes);
        let first = analyze(&source);
        let second = analyze(&source);
        assert_eq!(
            first, second,
            "frontend must be deterministic for case {case}"
        );
        check_invariants(&source, &first);
        if case % BORROW_CASE_INTERVAL == PROVENANCE_CASE_OFFSET
            && case / BORROW_CASE_INTERVAL < provenance_cases::FAMILY_COUNT
        {
            let resolved = first
                .vir()
                .expect("provenance seed lowers")
                .resolve()
                .expect("provenance seed resolves");
            let checked = nera::verify_program(&resolved, nera::CfgAnalysisConfig::default())
                .expect("provenance analysis converges")
                .is_memory_checked_core0();
            assert_eq!(
                checked,
                provenance_cases::expected_checked(case / BORROW_CASE_INTERVAL)
            );
        }
        if case % BORROW_CASE_INTERVAL == RELATION_CASE_OFFSET
            && case / BORROW_CASE_INTERVAL < relation_cases::FAMILY_COUNT
        {
            let resolved = first
                .vir()
                .expect("relation seed lowers")
                .resolve()
                .expect("relation seed resolves");
            let checked = nera::verify_program(&resolved, nera::CfgAnalysisConfig::default())
                .expect("relation analysis converges")
                .is_memory_checked_core0();
            assert_eq!(
                checked,
                relation_cases::expected_checked(case / BORROW_CASE_INTERVAL)
            );
        }
        if case % BORROW_CASE_INTERVAL == INITIALIZATION_CASE_OFFSET
            && case / BORROW_CASE_INTERVAL < initialization_cases::FAMILY_COUNT
        {
            let program = first.vir().expect("initialization seed lowers");
            let resolved = program.resolve().expect("initialization seed resolves");
            let checked = nera::verify_program(&resolved, nera::CfgAnalysisConfig::default())
                .expect("initialization seed verifies")
                .is_memory_checked_core0();
            assert_eq!(
                checked,
                initialization_cases::expected_checked(case / BORROW_CASE_INTERVAL)
            );
            initialization_cases::check_effect_mutation(program, case / BORROW_CASE_INTERVAL);
        }
        if case % BORROW_CASE_INTERVAL == BORROW_CASE_OFFSET
            && case / BORROW_CASE_INTERVAL < borrow_cases::FAMILY_COUNT
        {
            let resolved = first
                .vir()
                .expect("borrow seed lowers")
                .resolve()
                .expect("borrow seed resolves");
            let checked = nera::verify_program(&resolved, nera::CfgAnalysisConfig::default())
                .expect("borrow seed verifies")
                .is_memory_checked_core0();
            assert_eq!(
                checked,
                borrow_cases::expected_checked(case / BORROW_CASE_INTERVAL)
            );
        }
        if let (Some(first_vir), Some(second_vir)) = (first.vir(), second.vir()) {
            let replay_config = VirInterpreterConfig {
                max_steps: MAX_REPLAY_STEPS,
                max_call_depth: 32,
                ..VirInterpreterConfig::default()
            };
            assert_eq!(
                first_vir.stable_dump(),
                second_vir.stable_dump(),
                "VIR dump must be deterministic for case {case}"
            );
            let first_execution = first_vir
                .resolve()
                .map(|resolved| interpret_with_config(resolved.runtime(), replay_config));
            let second_execution = second_vir
                .resolve()
                .map(|resolved| interpret_with_config(resolved.runtime(), replay_config));
            assert_eq!(
                first_execution, second_execution,
                "VIR execution and resolution must be deterministic for case {case}"
            );
            if case % 8 == 0 {
                check_spec_mutation(first_vir, case);
            }
        }
    }

    println!("frontend fuzz gate passed: iterations={iterations}, seed={seed}");
    Ok(())
}

fn generate_case(generator: &mut Generator, case: u64) -> Vec<u8> {
    if case % BORROW_CASE_INTERVAL == PROVENANCE_CASE_OFFSET {
        let ordinal = case / BORROW_CASE_INTERVAL;
        let mut bytes = provenance_cases::source(ordinal, generator.next_u64()).into_bytes();
        if ordinal >= provenance_cases::FAMILY_COUNT {
            mutate_structured_source(generator, &mut bytes);
        }
        return bytes;
    }
    if case % BORROW_CASE_INTERVAL == RELATION_CASE_OFFSET {
        let ordinal = case / BORROW_CASE_INTERVAL;
        let mut bytes = relation_cases::source(ordinal, generator.next_u64()).into_bytes();
        if ordinal >= relation_cases::FAMILY_COUNT {
            mutate_structured_source(generator, &mut bytes);
        }
        return bytes;
    }

    if case % BORROW_CASE_INTERVAL == INITIALIZATION_CASE_OFFSET {
        let ordinal = case / BORROW_CASE_INTERVAL;
        let mut bytes = initialization_cases::source(ordinal, generator.next_u64()).into_bytes();
        if ordinal >= initialization_cases::FAMILY_COUNT {
            mutate_structured_source(generator, &mut bytes);
        }
        return bytes;
    }
    if case % BORROW_CASE_INTERVAL == BORROW_CASE_OFFSET {
        let ordinal = case / BORROW_CASE_INTERVAL;
        let mut bytes = borrow_cases::source(ordinal, generator.next_u64()).into_bytes();
        // Keep the existing seven-family and spec-mutation schedules intact.
        // Insert a complete borrow cycle before mutating its source bytes.
        if ordinal >= borrow_cases::FAMILY_COUNT {
            mutate_structured_source(generator, &mut bytes);
        }
        return bytes;
    }
    let ordinal = case / 7;
    match case % 7 {
        0 => random_bytes(generator),
        1 => mutated_core0(generator),
        2 => nested_expression(generator, ordinal),
        3 => additive_expression(generator, ordinal),
        4 => boundary_case(generator, ordinal),
        5 => structured_control_flow(generator, ordinal),
        _ => aggregate_source(generator, ordinal),
    }
}

fn aggregate_source(generator: &mut Generator, ordinal: u64) -> Vec<u8> {
    let mut bytes = AGGREGATE_CASES[ordinal as usize % AGGREGATE_CASES.len()].to_vec();
    if ordinal as usize >= AGGREGATE_CASES.len() {
        mutate_structured_source(generator, &mut bytes);
    }
    bytes
}

fn structured_control_flow(generator: &mut Generator, ordinal: u64) -> Vec<u8> {
    let mut bytes = STRUCTURED_CASES[ordinal as usize % STRUCTURED_CASES.len()].to_vec();
    if ordinal as usize >= STRUCTURED_CASES.len() {
        mutate_structured_source(generator, &mut bytes);
    }
    bytes
}

fn mutate_structured_source(generator: &mut Generator, bytes: &mut Vec<u8>) {
    match generator.next_u64() % 4 {
        0 => {
            let index = generator.bounded(bytes.len() + 1);
            bytes.insert(index, b" \t\n"[generator.bounded(3)]);
        }
        1 if !bytes.is_empty() => {
            let replacements = b"{}[]();,=<>_+:";
            let index = generator.bounded(bytes.len());
            bytes[index] = replacements[generator.bounded(replacements.len())];
        }
        2 if bytes.len() < MAX_RANDOM_BYTES => {
            let insertions = b"{}[]();,:";
            let index = generator.bounded(bytes.len() + 1);
            bytes.insert(index, insertions[generator.bounded(insertions.len())]);
        }
        3 if !bytes.is_empty() => {
            let index = generator.bounded(bytes.len());
            bytes.remove(index);
        }
        _ => {}
    }
}

fn random_bytes(generator: &mut Generator) -> Vec<u8> {
    let length = generator.bounded(MAX_RANDOM_BYTES + 1);
    (0..length).map(|_| generator.next_u64() as u8).collect()
}

fn mutated_core0(generator: &mut Generator) -> Vec<u8> {
    let mut bytes = b"fn fuzz() -> u64 { let memory = alloc<u64>(2); *memory = 40 + 2; let value = *memory; free(memory); return value; }".to_vec();
    let mutations = 1 + generator.bounded(8);
    for _ in 0..mutations {
        match generator.next_u64() % 3 {
            0 if !bytes.is_empty() => {
                let index = generator.bounded(bytes.len());
                bytes[index] = generator.next_u64() as u8;
            }
            1 if bytes.len() < MAX_RANDOM_BYTES => {
                let index = generator.bounded(bytes.len() + 1);
                bytes.insert(index, generator.next_u64() as u8);
            }
            2 if !bytes.is_empty() => {
                let index = generator.bounded(bytes.len());
                bytes.remove(index);
            }
            _ => {}
        }
    }
    bytes
}

fn nested_expression(generator: &mut Generator, ordinal: u64) -> Vec<u8> {
    let depth = match ordinal {
        0 => 255,
        1 => 256,
        2 => 257,
        _ => generator.bounded(MAX_STRUCTURED_SIZE + 1),
    };
    let closing_depth = if generator.next_u64().is_multiple_of(4) {
        depth.saturating_sub(generator.bounded(depth.saturating_add(1)))
    } else {
        depth
    };
    format!(
        "fn nested() -> u64 {{ return {}0{}; }}",
        "(".repeat(depth),
        ")".repeat(closing_depth)
    )
    .into_bytes()
}

fn additive_expression(generator: &mut Generator, ordinal: u64) -> Vec<u8> {
    let terms = match ordinal {
        0 => 1,
        1 => 256,
        2 => MAX_STRUCTURED_SIZE,
        _ => 1 + generator.bounded(MAX_STRUCTURED_SIZE),
    };
    let expression = vec!["1"; terms].join("+");
    format!("fn additive() -> u64 {{ return {expression}; }}").into_bytes()
}

fn boundary_case(generator: &mut Generator, ordinal: u64) -> Vec<u8> {
    let mut bytes = BOUNDARY_CASES[ordinal as usize % BOUNDARY_CASES.len()].to_vec();
    if ordinal as usize >= BOUNDARY_CASES.len() && generator.next_u64().is_multiple_of(2) {
        let index = generator.bounded(bytes.len() + 1);
        bytes.insert(index, b" \t\n"[generator.bounded(3)]);
    }
    bytes
}

fn check_invariants(source: &SourceFile, output: &nera::FrontendOutput) {
    match output.status() {
        nera::FrontendStatus::AcceptedProposal => {
            assert!(output.hir().is_some());
            assert!(output.vir().is_some());
        }
        nera::FrontendStatus::Invalid | nera::FrontendStatus::Unsupported => {
            assert!(output.hir().is_none());
            assert!(output.vir().is_none());
        }
    }
    assert!(output.lexed().has_bounded_contiguous_spans(source.len()));
    assert!(
        output
            .lexed()
            .tokens()
            .iter()
            .all(|token| token.span().end() <= source.len())
    );
    assert!(output.issues().iter().all(|issue| {
        issue
            .diagnostic()
            .primary_span()
            .is_none_or(|span| span.end() <= source.len())
    }));
    if let Some(hir) = output.hir() {
        assert!(hir.entry_function().span.end() <= source.len());
        let body = hir
            .entry_function()
            .body()
            .expect("accepted Core0 function has a body");
        assert!(
            body.locals
                .iter()
                .enumerate()
                .all(|(index, local)| local.id.index() == index
                    && local.declaration_span.end() <= source.len())
        );
    }
    if let Some(vir) = output.vir() {
        assert!(vir.runtime().functions.iter().all(|function| {
            function.source_span.end() <= source.len()
                && function.blocks.iter().all(|block| {
                    block.source_span.end() <= source.len()
                        && block
                            .instructions
                            .iter()
                            .all(|instruction| instruction.source_span.end() <= source.len())
                        && block.terminator.source_span.end() <= source.len()
                })
        }));
    }
}

struct Generator(u64);

impl Generator {
    const fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(2_862_933_555_777_941_757)
            .wrapping_add(3_037_000_493);
        self.0 ^ self.0.rotate_left(17)
    }

    fn bounded(&mut self, upper_exclusive: usize) -> usize {
        debug_assert!(upper_exclusive > 0);
        (self.next_u64() % upper_exclusive as u64) as usize
    }
}
