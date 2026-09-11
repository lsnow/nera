use nera::{FrontendIssueKind, FrontendStatus, SourceFile, TokenKind, analyze, lex};

#[test]
fn accepted_corpus_produces_every_frontend_artifact() {
    let source = SourceFile::new(
        "accepted-core0.nera",
        include_bytes!("../spec/cases/frontend/accepted-core0.nera"),
    );
    let output = analyze(&source);

    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "frontend issues: {:?}",
        output.issues()
    );
    assert!(output.issues().is_empty());
    assert!(output.cst().is_some());
    assert!(output.ast().is_some());
    assert!(output.hir().is_some());
    assert!(output.vir().is_some());
    assert!(output.lexed().has_bounded_contiguous_spans(source.len()));
}

#[test]
fn valid_but_deferred_features_are_unsupported() {
    for (path, bytes) in [
        (
            "unsupported-unicode.nera",
            include_bytes!("../spec/cases/frontend/unsupported-unicode.nera").as_slice(),
        ),
        (
            "unsupported-float.nera",
            include_bytes!("../spec/cases/frontend/unsupported-float.nera").as_slice(),
        ),
        (
            "unsupported-generics.nera",
            include_bytes!("../spec/cases/frontend/unsupported-generics.nera").as_slice(),
        ),
        (
            "unsupported-expression.nera",
            include_bytes!("../spec/cases/frontend/unsupported-expression.nera").as_slice(),
        ),
        (
            "unsupported-control-flow.nera",
            include_bytes!("../spec/cases/frontend/unsupported-control-flow.nera").as_slice(),
        ),
    ] {
        let output = analyze(&SourceFile::new(path, bytes));
        assert_eq!(output.status(), FrontendStatus::Unsupported, "{path}");
        assert_eq!(
            output.issues()[0].kind(),
            FrontendIssueKind::Unsupported,
            "{path}"
        );
        assert!(output.hir().is_none(), "{path}");
        assert!(output.vir().is_none(), "{path}");
    }
}

#[test]
fn concrete_multiple_functions_are_accepted() {
    let source = SourceFile::new(
        "direct-call.nera",
        include_bytes!("../spec/cases/control-flow/direct-call.nera"),
    );
    let output = analyze(&source);

    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "frontend issues: {:?}",
        output.issues()
    );
    assert_eq!(output.cst().expect("CST").functions().len(), 3);
    assert_eq!(output.ast().expect("AST").functions().len(), 3);
    assert_eq!(output.hir().expect("HIR").functions().len(), 3);
    assert_eq!(output.vir().expect("VIR").runtime().functions.len(), 3);
}

#[test]
fn malformed_number_is_invalid_not_unsupported() {
    let source = SourceFile::new(
        "invalid-number.nera",
        include_bytes!("../spec/cases/frontend/invalid-number.nera"),
    );
    let output = analyze(&source);

    assert_eq!(output.status(), FrontendStatus::Invalid);
    assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Lexical);
}

#[test]
fn lexer_surface_corpus_has_no_lexical_errors() {
    let source = SourceFile::new(
        "lexer-surface.nera",
        include_bytes!("../spec/cases/frontend/lexer-surface.nera"),
    );
    let lexed = lex(&source);

    assert!(lexed.issues().is_empty());
    assert!(lexed.has_bounded_contiguous_spans(source.len()));
    assert!(
        lexed
            .tokens()
            .iter()
            .any(|token| token.kind() == TokenKind::FloatLiteral)
    );
    assert!(
        lexed
            .tokens()
            .iter()
            .any(|token| token.kind() == TokenKind::ByteStringLiteral)
    );
}

#[test]
fn hex_encoded_arbitrary_byte_corpus_never_loses_input() {
    let corpus = include_str!("../spec/cases/frontend/arbitrary-bytes.hex");
    for (line_number, line) in corpus.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let bytes = decode_hex(line);
        let source = SourceFile::new(format!("arbitrary-{line_number}.nera"), bytes);
        let first = analyze(&source);
        let second = analyze(&source);
        assert_eq!(first, second, "corpus line {line_number}");
        assert!(
            first.lexed().has_bounded_contiguous_spans(source.len()),
            "corpus line {line_number}"
        );
    }
}

fn decode_hex(text: &str) -> Vec<u8> {
    assert_eq!(text.len() % 2, 0, "hex corpus rows have whole bytes");
    text.as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let digits = std::str::from_utf8(pair).expect("hex corpus is ASCII");
            u8::from_str_radix(digits, 16).expect("valid hex corpus")
        })
        .collect()
}
