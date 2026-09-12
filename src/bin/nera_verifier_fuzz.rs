use std::env;
use std::process::ExitCode;

use nera::{
    ByteSpan, CfgAnalysisConfig, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock,
    VirBlockId, VirConstant, VirContractId, VirFunction, VirFunctionId, VirInstruction,
    VirRegionId, VirSignature, VirTerminator, VirType, VirUnit, VirValue, VirValueId, analyze,
    interpret, verify_program,
};

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
#[path = "fuzz_support/summary_cases.rs"]
mod summary_cases;

use spec_mutation::check_spec_mutation;

const DEFAULT_ITERATIONS: u64 = 100_000;
const DEFAULT_SEED: u64 = 0x4e45_5241_5645_5249;
const AGGREGATE_CASE_INTERVAL: u64 = 32;
const RESOURCE_CFG_CASE_OFFSET: u64 = AGGREGATE_CASE_INTERVAL / 2;
const BORROW_CFG_CASE_OFFSET: u64 = 8;
const INITIALIZATION_CASE_OFFSET: u64 = 24;
const RELATION_CASE_OFFSET: u64 = 4;
const PROVENANCE_CASE_OFFSET: u64 = 12;
const SUMMARY_CASE_OFFSET: u64 = 20;

const AGGREGATE_VERIFIER_CASES: &[&[u8]] = &[
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
    b"fn aggregate_oob() -> u64 { let values = [1, 2]; let index = 3usize; return values[index]; }",
];

const RESOURCE_CFG_VERIFIER_CASES: &[&[u8]] = &[
    include_bytes!("../../spec/cases/verify/resource-acceptance.nera"),
    include_bytes!("../../spec/cases/verify/conditional-uaf.nera"),
    include_bytes!("../../spec/cases/verify/drop-scope.nera"),
    include_bytes!("../../spec/cases/control-flow/loop-resource-mismatch.nera"),
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
    let mut arguments = env::args().skip(1);
    while let Some(argument) = arguments.next() {
        let value = arguments
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
    let mut checked = 0_u64;
    let mut rejected = 0_u64;
    let mut aggregate_checked = 0_u64;
    let mut aggregate_rejected = 0_u64;
    let mut resource_cfg_checked = 0_u64;
    let mut resource_cfg_rejected = 0_u64;
    let mut borrow_cfg_checked = 0_u64;
    let mut borrow_cfg_rejected = 0_u64;
    let mut relation_checked = 0_u64;
    let mut relation_rejected = 0_u64;
    let mut provenance_checked = 0_u64;
    let mut provenance_rejected = 0_u64;
    let mut initialization_checked = 0_u64;
    let mut initialization_rejected = 0_u64;
    let mut summary_checked = 0_u64;
    let mut summary_rejected = 0_u64;
    for case in 0..iterations {
        let program = generate_case(&mut generator, case);
        let aggregate = case % AGGREGATE_CASE_INTERVAL == 0;
        let resource_cfg = case % AGGREGATE_CASE_INTERVAL == RESOURCE_CFG_CASE_OFFSET;
        let borrow_cfg = case % AGGREGATE_CASE_INTERVAL == BORROW_CFG_CASE_OFFSET;
        let initialization = case % AGGREGATE_CASE_INTERVAL == INITIALIZATION_CASE_OFFSET;
        let provenance = case % AGGREGATE_CASE_INTERVAL == PROVENANCE_CASE_OFFSET;
        let summary = case % AGGREGATE_CASE_INTERVAL == SUMMARY_CASE_OFFSET;
        if initialization {
            initialization_cases::check_effect_mutation(&program, case / AGGREGATE_CASE_INTERVAL);
        }
        if case % 8 == 0 {
            check_spec_mutation(&program, case);
        }
        let first = verify_program(
            &program.resolve().expect("verification input resolves"),
            CfgAnalysisConfig::default(),
        );
        let second = verify_program(
            &program.resolve().expect("verification input resolves"),
            CfgAnalysisConfig::default(),
        );
        assert_eq!(
            first, second,
            "verifier must be deterministic for case {case}"
        );
        if case % AGGREGATE_CASE_INTERVAL == RELATION_CASE_OFFSET {
            let checked = first
                .as_ref()
                .is_ok_and(nera::ProgramVerification::is_memory_checked_core0);
            assert_eq!(
                checked,
                relation_cases::expected_checked(case / AGGREGATE_CASE_INTERVAL),
                "relation family changed its verdict at case {case}"
            );
            relation_checked += u64::from(checked);
            relation_rejected += u64::from(!checked);
        }
        if borrow_cfg {
            assert_eq!(
                first
                    .as_ref()
                    .is_ok_and(nera::ProgramVerification::is_memory_checked_core0),
                borrow_cases::expected_checked(case / AGGREGATE_CASE_INTERVAL),
                "borrow CFG/loop/call family changed its expected result at case {case}: {first:#?}"
            );
        }

        if provenance {
            let checked = first
                .as_ref()
                .is_ok_and(nera::ProgramVerification::is_memory_checked_core0);
            assert_eq!(
                checked,
                provenance_cases::expected_checked(case / AGGREGATE_CASE_INTERVAL),
                "provenance CFG/loop/call family changed its verdict at case {case}: {first:#?}"
            );
            provenance_checked += u64::from(checked);
            provenance_rejected += u64::from(!checked);
        }

        if summary {
            let checked = first
                .as_ref()
                .is_ok_and(nera::ProgramVerification::is_memory_checked_core0);
            assert_eq!(
                checked,
                summary_cases::expected_checked(case / AGGREGATE_CASE_INTERVAL),
                "summary family case {case}: {first:#?}"
            );
            summary_checked += u64::from(checked);
            summary_rejected += u64::from(!checked);
        }

        if initialization {
            let checked = first
                .as_ref()
                .is_ok_and(nera::ProgramVerification::is_memory_checked_core0);
            assert_eq!(
                checked,
                initialization_cases::expected_checked(case / AGGREGATE_CASE_INTERVAL),
                "initialization family changed its verdict at case {case}: {first:#?}"
            );
            initialization_checked += u64::from(checked);
            initialization_rejected += u64::from(!checked);
        }

        match first {
            Ok(verification) if verification.is_memory_checked_core0() => {
                checked += 1;
                aggregate_checked += u64::from(aggregate);
                resource_cfg_checked += u64::from(resource_cfg);
                borrow_cfg_checked += u64::from(borrow_cfg);
                let resolved = program
                    .resolve()
                    .unwrap_or_else(|error| panic!("checked case {case} must resolve: {error}"));
                let execution = interpret(resolved.runtime()).unwrap_or_else(|error| {
                    panic!("checked case {case} faulted in the VIR interpreter: {error}")
                });
                if provenance || summary {
                    assert_eq!(
                        execution.values(),
                        [nera::VirRuntimeValue::U64(42)],
                        "provenance/summary case {case}"
                    );
                }
            }
            Ok(verification) => {
                rejected += 1;
                aggregate_rejected += u64::from(aggregate);
                resource_cfg_rejected += u64::from(resource_cfg);
                borrow_cfg_rejected += u64::from(borrow_cfg);
                assert!(
                    !verification.diagnostics().is_empty(),
                    "unchecked case {case} must retain a diagnostic"
                );
            }
            Err(_) => {
                rejected += 1;
                aggregate_rejected += u64::from(aggregate);
                resource_cfg_rejected += u64::from(resource_cfg);
                borrow_cfg_rejected += u64::from(borrow_cfg);
            }
        }
    }

    if iterations > 1 && (checked == 0 || rejected == 0) {
        return Err(format!(
            "fuzz corpus did not exercise both outcomes: checked={checked}, rejected={rejected}"
        ));
    }
    let aggregate_cycle = AGGREGATE_CASE_INTERVAL * AGGREGATE_VERIFIER_CASES.len() as u64;
    if iterations >= aggregate_cycle && (aggregate_checked == 0 || aggregate_rejected == 0) {
        return Err(format!(
            "aggregate fuzz corpus did not exercise both outcomes: checked={aggregate_checked}, rejected={aggregate_rejected}"
        ));
    }
    let resource_cfg_cycle = AGGREGATE_CASE_INTERVAL * RESOURCE_CFG_VERIFIER_CASES.len() as u64;
    if iterations >= resource_cfg_cycle && (resource_cfg_checked == 0 || resource_cfg_rejected == 0)
    {
        return Err(format!(
            "resource CFG fuzz corpus did not exercise both outcomes: checked={resource_cfg_checked}, rejected={resource_cfg_rejected}"
        ));
    }
    if iterations >= AGGREGATE_CASE_INTERVAL * borrow_cases::FAMILY_COUNT
        && (borrow_cfg_checked == 0 || borrow_cfg_rejected == 0)
    {
        return Err(format!(
            "borrow CFG corpus must exercise both outcomes: checked={borrow_cfg_checked}, rejected={borrow_cfg_rejected}"
        ));
    }
    if iterations >= AGGREGATE_CASE_INTERVAL * initialization_cases::FAMILY_COUNT
        && (initialization_checked == 0 || initialization_rejected == 0)
    {
        return Err("initialization corpus must exercise both outcomes".into());
    }
    if iterations >= AGGREGATE_CASE_INTERVAL * relation_cases::FAMILY_COUNT
        && (relation_checked == 0 || relation_rejected == 0)
    {
        return Err("relation corpus must exercise both outcomes".into());
    }
    if iterations >= AGGREGATE_CASE_INTERVAL * provenance_cases::FAMILY_COUNT
        && (provenance_checked == 0 || provenance_rejected == 0)
    {
        return Err("provenance corpus must exercise both outcomes".into());
    }
    if iterations >= AGGREGATE_CASE_INTERVAL * summary_cases::FAMILY_COUNT
        && (summary_checked == 0 || summary_rejected == 0)
    {
        return Err("summary corpus must exercise both outcomes".into());
    }
    println!("summary fuzz: checked={summary_checked}, rejected={summary_rejected}");
    println!(
        "verifier fuzz gate passed: iterations={iterations}, seed={seed}, checked={checked}, rejected={rejected}, aggregate_checked={aggregate_checked}, aggregate_rejected={aggregate_rejected}, resource_cfg_checked={resource_cfg_checked}, resource_cfg_rejected={resource_cfg_rejected}, borrow_cfg_checked={borrow_cfg_checked}, borrow_cfg_rejected={borrow_cfg_rejected}, initialization_checked={initialization_checked}, initialization_rejected={initialization_rejected}, relation_checked={relation_checked}, relation_rejected={relation_rejected}, provenance_checked={provenance_checked}, provenance_rejected={provenance_rejected}"
    );
    Ok(())
}

#[derive(Clone, Copy)]
enum MemoryAction {
    WriteLoad,
    InitializeLoad,
    LoadUninitialized,
    StoreUninitialized,
    FreeThenLoad,
}

struct FuzzCase {
    size: u64,
    offset: u64,
    split: Option<u64>,
    permission_choice: u64,
    rejoin: bool,
    action: MemoryAction,
    free_after: bool,
}

fn generate_case(generator: &mut Generator, ordinal: u64) -> nera::ValidatedVirUnit {
    if ordinal % AGGREGATE_CASE_INTERVAL == SUMMARY_CASE_OFFSET {
        let source = summary_cases::source(ordinal / AGGREGATE_CASE_INTERVAL, generator.next_u64());
        let output = analyze(&nera::SourceFile::from_text(
            format!("verifier-summary-fuzz-{ordinal}.nera"),
            &source,
        ));
        return output
            .vir()
            .unwrap_or_else(|| panic!("summary seed must lower: {source}\n{:?}", output.issues()))
            .clone();
    }
    if ordinal % AGGREGATE_CASE_INTERVAL == PROVENANCE_CASE_OFFSET {
        let source =
            provenance_cases::source(ordinal / AGGREGATE_CASE_INTERVAL, generator.next_u64());
        let output = analyze(&nera::SourceFile::from_text(
            format!("verifier-provenance-fuzz-{ordinal}.nera"),
            &source,
        ));
        return output
            .vir()
            .unwrap_or_else(|| {
                panic!(
                    "provenance seed must lower: {source}\n{:?}",
                    output.issues()
                )
            })
            .clone();
    }
    if ordinal % AGGREGATE_CASE_INTERVAL == RELATION_CASE_OFFSET {
        let source =
            relation_cases::source(ordinal / AGGREGATE_CASE_INTERVAL, generator.next_u64());
        let output = analyze(&nera::SourceFile::from_text(
            format!("verifier-relation-fuzz-{ordinal}.nera"),
            &source,
        ));
        return output
            .vir()
            .unwrap_or_else(|| panic!("relation seed must lower: {source}\n{:?}", output.issues()))
            .clone();
    }

    if ordinal % AGGREGATE_CASE_INTERVAL == INITIALIZATION_CASE_OFFSET {
        let source =
            initialization_cases::source(ordinal / AGGREGATE_CASE_INTERVAL, generator.next_u64());
        let output = analyze(&nera::SourceFile::from_text(
            format!("verifier-initialization-fuzz-{ordinal}.nera"),
            &source,
        ));
        return output
            .vir()
            .unwrap_or_else(|| {
                panic!(
                    "initialization seed must lower: {source}\n{:?}",
                    output.issues()
                )
            })
            .clone();
    }
    if ordinal.is_multiple_of(AGGREGATE_CASE_INTERVAL) {
        return aggregate_case(ordinal / AGGREGATE_CASE_INTERVAL);
    }
    if ordinal % AGGREGATE_CASE_INTERVAL == RESOURCE_CFG_CASE_OFFSET {
        return resource_cfg_case(ordinal / AGGREGATE_CASE_INTERVAL);
    }
    if ordinal % AGGREGATE_CASE_INTERVAL == BORROW_CFG_CASE_OFFSET {
        let source = borrow_cases::source(ordinal / AGGREGATE_CASE_INTERVAL, generator.next_u64());
        let output = analyze(&nera::SourceFile::from_text(
            format!("verifier-borrow-cfg-fuzz-{ordinal}.nera"),
            &source,
        ));
        return output
            .vir()
            .unwrap_or_else(|| panic!("borrow seed must lower: {source}\n{:?}", output.issues()))
            .clone();
    }
    let case = if ordinal.is_multiple_of(16) {
        let words = 1 + generator.bounded(8);
        let selected = generator.bounded(words);
        FuzzCase {
            size: words * 8,
            offset: selected * 8,
            split: None,
            permission_choice: 0,
            rejoin: false,
            action: MemoryAction::WriteLoad,
            free_after: true,
        }
    } else {
        let action = match generator.next_u64() % 5 {
            0 => MemoryAction::WriteLoad,
            1 => MemoryAction::InitializeLoad,
            2 => MemoryAction::LoadUninitialized,
            3 => MemoryAction::StoreUninitialized,
            _ => MemoryAction::FreeThenLoad,
        };
        let size = generator.bounded(129);
        FuzzCase {
            size,
            offset: generator.bounded(size.saturating_add(25)),
            split: (generator.next_u64() & 1 == 0)
                .then(|| generator.bounded(size.saturating_add(17))),
            permission_choice: generator.next_u64() % 3,
            rejoin: generator.next_u64() & 1 == 0,
            action,
            free_after: generator.next_u64() & 1 == 0,
        }
    };
    build_case(case)
}

fn resource_cfg_case(ordinal: u64) -> nera::ValidatedVirUnit {
    let source = RESOURCE_CFG_VERIFIER_CASES[ordinal as usize % RESOURCE_CFG_VERIFIER_CASES.len()];
    let source =
        nera::SourceFile::new(format!("verifier-resource-cfg-fuzz-{ordinal}.nera"), source);
    let output = analyze(&source);
    output
        .vir()
        .unwrap_or_else(|| {
            panic!(
                "resource CFG fuzz seed must lower to VIR: {:?}",
                output.issues()
            )
        })
        .clone()
}

fn aggregate_case(ordinal: u64) -> nera::ValidatedVirUnit {
    let source = AGGREGATE_VERIFIER_CASES[ordinal as usize % AGGREGATE_VERIFIER_CASES.len()];
    let source = nera::SourceFile::new(format!("verifier-aggregate-fuzz-{ordinal}.nera"), source);
    let output = analyze(&source);
    output
        .vir()
        .unwrap_or_else(|| {
            panic!(
                "aggregate fuzz seed must lower to VIR: {:?}",
                output.issues()
            )
        })
        .clone()
}

fn build_case(case: FuzzCase) -> nera::ValidatedVirUnit {
    let span = ByteSpan::new(0, 1).expect("valid fuzz span");
    let mut instructions = vec![
        spanned(
            span,
            VirInstruction::Constant {
                result: word(0),
                value: VirConstant::U64(case.size),
            },
        ),
        spanned(
            span,
            VirInstruction::Allocate {
                pointer_result: pointer(1),
                permission_result: permission(2),
                size_bytes: VirValueId::new(0),
                alignment: 8,
                region: VirRegionId::new(0),
                element: nera::VirMemoryAccess::core_u64(),
            },
        ),
        spanned(
            span,
            VirInstruction::Constant {
                result: word(3),
                value: VirConstant::U64(case.offset),
            },
        ),
        spanned(
            span,
            VirInstruction::PointerOffset {
                result: pointer(4),
                base: VirValueId::new(1),
                delta_bytes: VirValueId::new(3),
            },
        ),
        spanned(
            span,
            VirInstruction::Constant {
                result: word(5),
                value: VirConstant::U64(0xa5a5),
            },
        ),
    ];

    let access_permission = if let Some(split) = case.split {
        instructions.extend([
            spanned(
                span,
                VirInstruction::Constant {
                    result: word(6),
                    value: VirConstant::U64(split),
                },
            ),
            spanned(
                span,
                VirInstruction::PermissionSplit {
                    left_result: permission(7),
                    right_result: permission(8),
                    source: VirValueId::new(2),
                    split_at_bytes: VirValueId::new(6),
                },
            ),
        ]);
        match case.permission_choice {
            0 => VirValueId::new(2),
            1 => VirValueId::new(7),
            _ => VirValueId::new(8),
        }
    } else {
        VirValueId::new(2)
    };

    if matches!(case.action, MemoryAction::FreeThenLoad) {
        instructions.push(spanned(
            span,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: access_permission,
            },
        ));
    }
    match case.action {
        MemoryAction::WriteLoad => {
            instructions.push(spanned(
                span,
                VirInstruction::Write {
                    pointer: VirValueId::new(4),
                    value: VirValueId::new(5),
                    permission: access_permission,
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ));
            instructions.push(spanned(
                span,
                VirInstruction::Load {
                    result: word(9),
                    pointer: VirValueId::new(4),
                    permission: access_permission,
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ));
        }
        MemoryAction::InitializeLoad => {
            instructions.push(spanned(
                span,
                VirInstruction::Initialize {
                    pointer: VirValueId::new(4),
                    value: VirValueId::new(5),
                    permission: access_permission,
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ));
            instructions.push(spanned(
                span,
                VirInstruction::Load {
                    result: word(9),
                    pointer: VirValueId::new(4),
                    permission: access_permission,
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ));
        }
        MemoryAction::LoadUninitialized | MemoryAction::FreeThenLoad => {
            instructions.push(spanned(
                span,
                VirInstruction::Load {
                    result: word(9),
                    pointer: VirValueId::new(4),
                    permission: access_permission,
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ));
        }
        MemoryAction::StoreUninitialized => instructions.push(spanned(
            span,
            VirInstruction::Store {
                pointer: VirValueId::new(4),
                value: VirValueId::new(5),
                permission: access_permission,
                access: nera::VirMemoryAccess::core_u64(),
            },
        )),
    }

    let final_permission = if case.split.is_some() && case.rejoin {
        instructions.push(spanned(
            span,
            VirInstruction::PermissionJoin {
                result: permission(10),
                left: VirValueId::new(7),
                right: VirValueId::new(8),
            },
        ));
        VirValueId::new(10)
    } else {
        access_permission
    };
    if case.free_after && !matches!(case.action, MemoryAction::FreeThenLoad) {
        instructions.push(spanned(
            span,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: final_permission,
            },
        ));
    }

    let signature = VirSignature {
        parameters: Vec::new(),
        results: Vec::new(),
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "verifier_fuzz".to_owned(),
            signature: signature.clone(),
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions,
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return { values: Vec::new() },
                    source_span: span,
                },
                source_span: span,
            }],
            source_span: span,
        }],
    )
    .into_validated()
    .expect("fuzz generator must produce structurally valid VIR")
}

fn spanned(span: ByteSpan, instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span,
    }
}

fn word(id: u32) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty: VirType::U64,
    }
}

fn pointer(id: u32) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty: VirType::Pointer {
            access: nera::VirMemoryAccess::core_u64(),
        },
    }
}

fn permission(id: u32) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty: VirType::Permission,
    }
}

struct Generator {
    state: u64,
}

impl Generator {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        let mut value = self.state;
        value ^= value << 13;
        value ^= value >> 7;
        value ^= value << 17;
        self.state = value;
        value
    }

    fn bounded(&mut self, upper: u64) -> u64 {
        if upper == 0 {
            0
        } else {
            self.next_u64() % upper
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Generator, check_spec_mutation, generate_case};
    use nera::{CfgAnalysisConfig, interpret, verify_program};

    #[test]
    fn generated_verifier_cases_are_deterministic_and_checked_cases_execute() {
        let mut generator = Generator::new(0x5eed);
        let mut checked = 0;
        let mut rejected = 0;
        for ordinal in 0..2_000 {
            let program = generate_case(&mut generator, ordinal);
            if ordinal < 5 {
                check_spec_mutation(&program, ordinal);
            }
            let first = verify_program(
                &program.resolve().expect("verification input resolves"),
                CfgAnalysisConfig::default(),
            );
            let second = verify_program(
                &program.resolve().expect("verification input resolves"),
                CfgAnalysisConfig::default(),
            );
            assert_eq!(first, second);
            if first
                .as_ref()
                .is_ok_and(nera::ProgramVerification::is_memory_checked_core0)
            {
                checked += 1;
                interpret(
                    program
                        .resolve()
                        .expect("generated program resolves")
                        .runtime(),
                )
                .expect("checked generated program executes");
            } else {
                rejected += 1;
            }
        }
        assert!(checked > 0);
        assert!(rejected > 0);
    }
}
