use nera::{FrontendOutput, SourceFile, analyze};

#[test]
fn every_single_byte_and_byte_pair_is_bounded_and_deterministic() {
    for first in 0_u8..=u8::MAX {
        check_bytes(vec![first]);
        for second in 0_u8..=u8::MAX {
            let source = SourceFile::new("pair.nera", [first, second]);
            let output = analyze(&source);
            check_invariants(&source, &output);
        }
    }
}

#[test]
fn deterministic_generated_bytes_do_not_panic_or_escape_source_bounds() {
    let mut generator = Generator::new(0x4e45_5241_5354_4732);
    for case in 0..10_000 {
        let length = (generator.next_u64() % 513) as usize;
        let bytes: Vec<u8> = (0..length).map(|_| generator.next_u64() as u8).collect();
        let source = SourceFile::new(format!("generated-{case}.nera"), bytes);
        let first = analyze(&source);
        let second = analyze(&source);
        assert_eq!(
            first, second,
            "frontend must be deterministic for case {case}"
        );
        check_invariants(&source, &first);
    }
}

#[test]
fn structured_expression_boundaries_are_bounded_and_deterministic() {
    for depth in [0, 1, 255, 256, 257, 20_000] {
        let text = format!(
            "fn nested() -> u64 {{ return {}0{}; }}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        check_text_twice(&format!("nested-{depth}.nera"), text);
    }

    for terms in [1, 2, 256, 20_000] {
        let expression = vec!["1"; terms].join("+");
        check_text_twice(
            &format!("additive-{terms}.nera"),
            format!("fn additive() -> u64 {{ return {expression}; }}"),
        );
    }
}

#[test]
fn known_lexer_and_deferred_syntax_boundaries_are_deterministic() {
    for (case, text) in [
        "fn f() -> u64 { return 0xbe+1; }",
        "fn f() -> u64 { return 1usize+2; }",
        "fn generic<'a, 'b>() { return; }",
        "fn f() { \"deferred\"; return; }",
        "fn f() -> u64 { return foo(); }",
        "fn f() { let memory=alloc<u64>(1); return; }",
        "fn f() -> u64 { let alloc=1; return alloc; }",
    ]
    .into_iter()
    .enumerate()
    {
        check_text_twice(&format!("boundary-{case}.nera"), text.to_owned());
    }
}

fn check_text_twice(name: &str, text: String) {
    let source = SourceFile::new(name, text);
    let first = analyze(&source);
    let second = analyze(&source);
    assert_eq!(first, second, "frontend must be deterministic for {name}");
    check_invariants(&source, &first);
}

fn check_bytes(bytes: Vec<u8>) {
    let source = SourceFile::new("generated.nera", bytes);
    let output = analyze(&source);
    check_invariants(&source, &output);
}

fn check_invariants(source: &SourceFile, output: &FrontendOutput) {
    match output.status() {
        nera::FrontendStatus::AcceptedProposal => {
            assert!(output.cst().is_some());
            assert!(output.ast().is_some());
            assert!(output.hir().is_some());
            assert!(output.vir().is_some());
        }
        nera::FrontendStatus::Invalid | nera::FrontendStatus::Unsupported => {
            assert!(output.hir().is_none());
            assert!(output.vir().is_none());
        }
    }
    assert!(output.lexed().has_bounded_contiguous_spans(source.len()));
    for token in output.lexed().tokens() {
        assert!(token.span().start() <= token.span().end());
        assert!(token.span().end() <= source.len());
    }
    for issue in output.issues() {
        if let Some(span) = issue.diagnostic().primary_span() {
            assert!(span.start() <= span.end());
            assert!(span.end() <= source.len());
        }
    }
    if let Some(cst) = output.cst() {
        assert_eq!(cst.tokens(), output.lexed().tokens());
        assert!(cst.function().span().end() <= source.len());
    }
    if let Some(ast) = output.ast() {
        assert!(ast.function().span.end() <= source.len());
    }
    if let Some(hir) = output.hir() {
        assert!(hir.entry_function().span.end() <= source.len());
        let body = hir
            .entry_function()
            .body()
            .expect("accepted Core0 function has a body");
        assert!(
            body.locals
                .iter()
                .all(|local| local.declaration_span.end() <= source.len())
        );
    }
    if let Some(vir) = output.vir() {
        for function in vir.runtime().functions {
            assert!(function.source_span.end() <= source.len());
            for block in &function.blocks {
                assert!(block.source_span.end() <= source.len());
                assert!(
                    block
                        .instructions
                        .iter()
                        .all(|instruction| instruction.source_span.end() <= source.len())
                );
                assert!(block.terminator.source_span.end() <= source.len());
            }
        }
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
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 ^ self.0.rotate_right(29)
    }
}
