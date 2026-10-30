//! Bounded logical precedence parsing, independent of runtime arithmetic.
use super::*;
use crate::frontend::{AstLogicalExpression as E, AstLogicalExpressionKind as K};

impl Parser<'_, '_> {
    pub(super) fn parse_logical_expression(&mut self) -> Result<E, FrontendFailure> {
        self.logical_expression_delimited(false)
    }

    fn logical_expression_delimited(&mut self, comma: bool) -> Result<E, FrontendFailure> {
        let (expression, _) = self.logical(0, 0)?;
        if is_deferred_expression_continuation(self.current().kind())
            && !(comma && self.at_punctuation(Punctuation::Comma))
        {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "logical expression feature is outside the supported theory",
            ));
        }
        Ok(expression)
    }

    fn logical_call(&mut self, nesting: usize) -> Result<(E, usize), FrontendFailure> {
        let token = self.bump();
        let callee = self.identifier_text(token);
        self.bump();
        let mut arguments = Vec::new();
        let mut height = 1;
        while !self.at_punctuation(Punctuation::RightParen) {
            if arguments.len() >= 32 {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "logical call argument budget exceeded",
                ));
            }
            let (argument, child_height) = self.logical(0, nesting + 1)?;
            height = height.max(child_height + 1);
            if nesting + height >= MAX_EXPRESSION_NESTING {
                return Err(FrontendFailure::unsupported(
                    argument.span,
                    "logical call nesting budget exceeded",
                ));
            }
            arguments.push(argument);
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
        }
        let end = self
            .expect_punctuation(Punctuation::RightParen, "expected `)` after logical call")?
            .span()
            .end();
        let location = span(token.span().start(), end);
        // Preserve the established representation of builtin/simple calls.
        // Rich logical operands stay in the specification AST throughout.
        let kind = match arguments
            .iter()
            .map(legacy_call_argument)
            .collect::<Option<Vec<_>>>()
        {
            Some(arguments) => K::Value(AstExpression {
                span: location,
                kind: AstExpressionKind::Call { callee, arguments },
            }),
            None => K::Call { callee, arguments },
        };
        Ok((
            E {
                span: location,
                kind,
            },
            height,
        ))
    }

    fn logical_range_call(&mut self, nesting: usize) -> Result<(E, usize), FrontendFailure> {
        Ok({
            let callee = self.identifier_text(self.current());
            let begin = self.bump().span().start();
            self.bump();
            let mut arguments = Vec::new();
            for index in 0..if callee == "len" { 1 } else { 2 } {
                if index != 0 {
                    self.expect_punctuation(Punctuation::Comma, "disjoint requires two ranges")?;
                }
                let value = if self.current().kind() == TokenKind::Keyword(Keyword::Result) {
                    self.parse_name_or_place(self.current(), nesting + 1, true)?
                } else {
                    self.parse_primary(nesting + 1, false)?
                };
                arguments.push(value);
            }
            let end = self
                .expect_punctuation(
                    Punctuation::RightParen,
                    "expected `)` after disjoint ranges",
                )?
                .span()
                .end();
            let span = span(begin, end);
            (
                E {
                    span,
                    kind: K::Value(AstExpression {
                        span,
                        kind: AstExpressionKind::Call { callee, arguments },
                    }),
                },
                1,
            )
        })
    }

    fn logical_alive_call(&mut self, _nesting: usize) -> Result<(E, usize), FrontendFailure> {
        Ok({
            let start = self.bump().span().start();
            self.bump();
            let name = self.current();
            if name.kind() != TokenKind::Identifier {
                return Err(FrontendFailure::unsupported(
                    name.span(),
                    "alive requires pointer.region",
                ));
            }
            self.bump();
            self.expect_punctuation(Punctuation::Dot, "expected `.region` in alive observation")?;
            let region = self.current();
            if region.kind() != TokenKind::Keyword(Keyword::Region) {
                return Err(FrontendFailure::unsupported(
                    region.span(),
                    "alive requires pointer.region",
                ));
            }
            self.bump();
            let end = self
                .expect_punctuation(
                    Punctuation::RightParen,
                    "expected `)` after alive observation",
                )?
                .span()
                .end();
            let argument_span = span(name.span().start(), region.span().end());
            let argument = AstExpression {
                span: argument_span,
                kind: AstExpressionKind::Place(AstPlace {
                    base: String::from_utf8_lossy(name.raw(self.source)).into_owned(),
                    projections: vec![AstPlaceProjection::Field {
                        name: "region".into(),
                        span: region.span(),
                    }],
                    span: argument_span,
                }),
            };
            let value = AstExpression {
                span: span(start, end),
                kind: AstExpressionKind::Call {
                    callee: "alive".into(),
                    arguments: vec![argument],
                },
            };
            (
                E {
                    span: value.span,
                    kind: K::Value(value),
                },
                1,
            )
        })
    }

    fn logical_memory_call(&mut self, nesting: usize) -> Result<(E, usize), FrontendFailure> {
        Ok({
            let builtin = self.current().raw(self.source).to_vec();
            let begin = self.bump().span().start();
            self.bump();
            let pointer = if self.current().kind() == TokenKind::Keyword(Keyword::Result) {
                self.parse_name_or_place(self.current(), nesting + 1, true)?
            } else {
                self.parse_primary(nesting + 1, false)?
            };
            if self.at_punctuation(Punctuation::Comma) {
                self.bump();
                let (start, a) = self.logical(0, nesting + 1)?;
                self.expect_punctuation(
                    Punctuation::Range,
                    "expected half-open element range in initialized",
                )?;
                let (end, b) = self.logical(0, nesting + 1)?;
                let finish = self
                    .expect_punctuation(
                        Punctuation::RightParen,
                        "expected `)` after initialized range",
                    )?
                    .span()
                    .end();
                (
                    E {
                        span: span(begin, finish),
                        kind: if builtin == b"initialized" {
                            K::InitializedRange {
                                pointer,
                                start: Box::new(start),
                                end: Box::new(end),
                            }
                        } else {
                            K::ResourceRange {
                                writable: builtin == b"writable",
                                pointer,
                                start: Box::new(start),
                                end: Box::new(end),
                            }
                        },
                    },
                    a.max(b) + 1,
                )
            } else {
                if builtin != b"initialized" {
                    return Err(FrontendFailure::unsupported(
                        span(begin, pointer.span.end()),
                        "readable/writable require an explicit half-open element range",
                    ));
                }
                let finish = self
                    .expect_punctuation(
                        Punctuation::RightParen,
                        "expected `)` after initialized pointer",
                    )?
                    .span()
                    .end();
                let value = AstExpression {
                    span: span(begin, finish),
                    kind: AstExpressionKind::Call {
                        callee: "initialized".into(),
                        arguments: vec![pointer],
                    },
                };
                (
                    E {
                        span: value.span,
                        kind: K::Value(value),
                    },
                    1,
                )
            }
        })
    }

    fn logical(&mut self, min: u8, nesting: usize) -> Result<(E, usize), FrontendFailure> {
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "logical expression nesting budget exceeded",
            ));
        }
        let mut grouped = self.at_punctuation(Punctuation::LeftParen);
        let (mut left, mut height) = if self.at_punctuation(Punctuation::Bang) {
            // Count a prefix run without consuming a parser stack frame per
            // token. Reject at the same nesting boundary before building AST.
            let mut starts = Vec::new();
            while self.at_punctuation(Punctuation::Bang) {
                starts.push(self.bump().span().start());
                if nesting + starts.len() >= MAX_EXPRESSION_NESTING {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "logical expression nesting budget exceeded",
                    ));
                }
            }
            let (mut operand, height) = self.logical(6, nesting + starts.len())?;
            let height = height + starts.len();
            for start in starts.into_iter().rev() {
                operand = E {
                    span: span(start, operand.span.end()),
                    kind: K::Not(Box::new(operand)),
                };
            }
            (operand, height)
        } else if self.at_punctuation(Punctuation::LeftParen) {
            let start = self.bump().span().start();
            let (mut expression, height) = self.logical(0, nesting + 1)?;
            let end = self
                .expect_punctuation(Punctuation::RightParen, "expected `)` in assertion")?
                .span()
                .end();
            expression.span = span(start, end);
            (expression, height + 1)
        } else if self.current().kind() == TokenKind::Identifier
            && matches!(self.current().raw(self.source), b"disjoint" | b"len")
            && self.nth_significant(1).kind() == TokenKind::Punctuation(Punctuation::LeftParen)
        {
            self.logical_range_call(nesting)?
        } else if self.current().kind() == TokenKind::Identifier
            && self.current().raw(self.source) == b"alive"
            && self.nth_significant(1).kind() == TokenKind::Punctuation(Punctuation::LeftParen)
        {
            self.logical_alive_call(nesting)?
        } else if self.current().kind() == TokenKind::Identifier
            && matches!(
                self.current().raw(self.source),
                b"initialized" | b"readable" | b"writable"
            )
            && self.nth_significant(1).kind() == TokenKind::Punctuation(Punctuation::LeftParen)
        {
            self.logical_memory_call(nesting)?
        } else if self.current().kind() == TokenKind::Identifier
            && self.nth_significant(1).kind() == TokenKind::Punctuation(Punctuation::LeftParen)
        {
            self.logical_call(nesting)?
        } else if self.current().kind() == TokenKind::Punctuation(Punctuation::Star)
            && self.nth_significant(1).kind() == TokenKind::Keyword(Keyword::Result)
        {
            let start = self.bump().span().start();
            let end = self.bump().span().end();
            let span = super::span(start, end);
            (
                E {
                    span,
                    kind: K::Value(AstExpression {
                        span,
                        kind: AstExpressionKind::Load {
                            pointer: "result".into(),
                        },
                    }),
                },
                1,
            )
        } else if self.current().kind() == TokenKind::Keyword(Keyword::Result) {
            let value = self.parse_name_or_place(self.current(), nesting, true)?;
            (
                E {
                    span: value.span,
                    kind: K::Value(value),
                },
                1,
            )
        } else {
            let value = self.parse_primary(nesting, false)?;
            (
                E {
                    span: value.span,
                    kind: K::Value(value),
                },
                1,
            )
        };
        while let TokenKind::Punctuation(operator) = self.current().kind() {
            let precedence = match operator {
                Punctuation::LogicalOr => 1,
                Punctuation::LogicalAnd => 2,
                Punctuation::EqualEqual
                | Punctuation::NotEqual
                | Punctuation::Less
                | Punctuation::LessEqual
                | Punctuation::Greater
                | Punctuation::GreaterEqual => 3,
                Punctuation::Plus | Punctuation::Minus => 4,
                Punctuation::Star => 5,
                _ => break,
            };
            if precedence < min {
                break;
            }
            if precedence == 3
                && !grouped
                && matches!(
                    left.kind,
                    K::Binary {
                        operator: Punctuation::EqualEqual
                            | Punctuation::NotEqual
                            | Punctuation::Less
                            | Punctuation::LessEqual
                            | Punctuation::Greater
                            | Punctuation::GreaterEqual,
                        ..
                    }
                )
            {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "comparison operators cannot be chained",
                ));
            }
            self.bump();
            grouped = false;
            let (right, right_height) = self.logical(precedence + 1, nesting + 1)?;
            height = height.max(right_height) + 1;
            if height >= MAX_EXPRESSION_NESTING {
                return Err(FrontendFailure::unsupported(
                    left.span,
                    "logical expression node depth budget exceeded",
                ));
            }
            left = E {
                span: span(left.span.start(), right.span.end()),
                kind: K::Binary {
                    operator,
                    left: Box::new(left),
                    right: Box::new(right),
                },
            };
        }
        Ok((left, height))
    }
}

impl Parser<'_, '_> {
    pub(super) fn parse_predicate(
        &mut self,
    ) -> Result<super::super::AstPredicate, FrontendFailure> {
        let start = self.bump().span().start();
        let name = self.expect(TokenKind::Identifier, "expected predicate name")?;
        self.expect_punctuation(Punctuation::LeftParen, "expected predicate parameters")?;
        let parameters = self.parse_parameters()?;
        self.expect_punctuation(
            Punctuation::LeftBrace,
            "expected predicate representation body",
        )?;
        let mut witnesses = Vec::new();
        while self.current().kind() == TokenKind::Keyword(Keyword::Exists) {
            let begin = self.bump().span().start();
            if witnesses.len() >= 32 {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "predicate witness budget exceeded",
                ));
            }
            let name = self.expect(TokenKind::Identifier, "expected existential binding name")?;
            self.expect_punctuation(Punctuation::Colon, "expected witness type")?;
            let ty = self.parse_type(0)?;
            let value = if self.at_punctuation(Punctuation::Equal) {
                self.bump();
                Some(self.parse_logical_expression()?)
            } else {
                None
            };
            let end = self
                .expect_punctuation(Punctuation::Semicolon, "expected `;` after witness")?
                .span()
                .end();
            witnesses.push(super::super::AstPredicateWitness {
                name: self.identifier_text(name),
                ty,
                value,
                span: span(begin, end),
            });
        }
        let mut clauses = Vec::new();
        while !self.at_punctuation(Punctuation::RightBrace) {
            if clauses.len() >= 96 {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "predicate body budget exceeded",
                ));
            }
            clauses.push(self.parse_logical_expression()?);
            self.expect_punctuation(
                Punctuation::Semicolon,
                "expected `;` after predicate clause",
            )?;
        }
        let end = self.bump().span().end();
        Ok(super::super::AstPredicate {
            name: self.identifier_text(name),
            parameters,
            clauses,
            witnesses,
            span: span(start, end),
        })
    }

    pub(super) fn parse_predicate_action(&mut self) -> Result<AstStatement, FrontendFailure> {
        let word = self.bump();
        let operation = match word.raw(self.source) {
            b"fold" => super::super::AstPredicateOperation::Fold,
            b"unfold" => super::super::AstPredicateOperation::Unfold,
            _ => super::super::AstPredicateOperation::Finish,
        };
        let predicate = self.parse_module_path()?;
        self.expect_punctuation(Punctuation::LeftParen, "expected predicate bindings")?;
        let mut locals = Vec::new();
        while !self.at_punctuation(Punctuation::RightParen) {
            if locals.len() >= 64 {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "predicate argument budget exceeded",
                ));
            }
            locals.push(self.logical_expression_delimited(true)?);
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
        }
        self.expect_punctuation(
            Punctuation::RightParen,
            "expected `)` after predicate bindings",
        )?;
        let mut witnesses = Vec::new();
        if self.current().kind() == TokenKind::Identifier
            && self.current().raw(self.source) == b"with"
        {
            if operation != super::super::AstPredicateOperation::Fold {
                return Err(FrontendFailure::elaboration(
                    self.current().span(),
                    "only fold accepts explicit witnesses",
                ));
            }
            self.bump();
            self.expect_punctuation(Punctuation::LeftParen, "expected `(` after with")?;
            while !self.at_punctuation(Punctuation::RightParen) {
                if witnesses.len() >= 32 {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "witness budget exceeded",
                    ));
                }
                let token =
                    self.expect(TokenKind::Identifier, "expected existential binder name")?;
                let name = self.identifier_text(token);
                self.expect_punctuation(Punctuation::Equal, "expected `=` after witness name")?;
                let value = self.logical_expression_delimited(true)?;
                witnesses.push((name, value));
                if !self.at_punctuation(Punctuation::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect_punctuation(Punctuation::RightParen, "expected `)` after witnesses")?;
        }
        let opened = if self.current().kind() == TokenKind::Keyword(Keyword::As) {
            if operation != super::super::AstPredicateOperation::Unfold {
                return Err(FrontendFailure::elaboration(
                    self.current().span(),
                    "only unfold introduces opened bindings",
                ));
            }
            self.bump();
            self.expect_punctuation(Punctuation::LeftParen, "expected `(` after as")?;
            let mut names = Vec::new();
            while !self.at_punctuation(Punctuation::RightParen) {
                if names.len() >= 32 {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "opened binder budget exceeded",
                    ));
                }
                let token = self.expect(TokenKind::Identifier, "expected opened binder name")?;
                names.push(self.identifier_text(token));
                if !self.at_punctuation(Punctuation::Comma) {
                    break;
                }
                self.bump();
            }
            self.expect_punctuation(
                Punctuation::RightParen,
                "expected `)` after opened bindings",
            )?;
            Some(names)
        } else {
            None
        };
        let end = self
            .expect_punctuation(
                Punctuation::Semicolon,
                "expected `;` after predicate effect",
            )?
            .span()
            .end();
        Ok(AstStatement {
            kind: AstStatementKind::Predicate {
                operation,
                predicate,
                locals,
                witnesses,
                opened,
            },
            span: span(word.span().start(), end),
        })
    }
}

// Compatibility for existing consumers of ordinary-shaped builtin calls. This
// only constructs syntax; it never evaluates an operand or lowers runtime code.
fn legacy_call_argument(expression: &E) -> Option<AstExpression> {
    use crate::frontend::AstIntegerPredicate as C;
    let kind = match &expression.kind {
        K::Value(value) => return Some(value.clone()),
        K::Binary {
            operator: Punctuation::Plus,
            left,
            right,
        } => AstExpressionKind::Add(vec![
            legacy_call_argument(left)?,
            legacy_call_argument(right)?,
        ]),
        K::Binary {
            operator,
            left,
            right,
        } => {
            let predicate = match operator {
                Punctuation::EqualEqual => C::Equal,
                Punctuation::NotEqual => C::NotEqual,
                Punctuation::Less => C::LessThan,
                Punctuation::LessEqual => C::LessOrEqual,
                Punctuation::Greater => C::GreaterThan,
                Punctuation::GreaterEqual => C::GreaterOrEqual,
                _ => return None,
            };
            AstExpressionKind::Compare {
                predicate,
                left: Box::new(legacy_call_argument(left)?),
                right: Box::new(legacy_call_argument(right)?),
                operation_span: expression.span,
            }
        }
        _ => return None,
    };
    Some(AstExpression {
        span: expression.span,
        kind,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_logical_calls_and_groups_respect_the_budget_on_a_normal_stack() {
        std::thread::Builder::new()
            .name("logical-nesting".into())
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                for prefix in ["old(", "("] {
                    for (depth, accepted) in [(96, true), (256, false)] {
                        let expression = format!("{}x{}", prefix.repeat(depth), ")".repeat(depth));
                        let source = SourceFile::from_text(
                            "logical-nesting.nera",
                            format!("fn f(x:u64)->u64 ensures {expression}==x; {{return x;}}"),
                        );
                        let lexed = crate::lex(&source);
                        assert_eq!(parse(&source, lexed.tokens(), false).is_ok(), accepted);
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn predicate_action_and_witness_lists_accept_logical_argument_delimiters() {
        let source = SourceFile::from_text(
            "predicate-lists.nera",
            r#"
            fn main()->u64 {
                fold Ready(p,n+1usize,flag&&true) with (low=n,high=n+1usize);
                unfold Ready(p,n+1usize,flag&&true) as (a,b);
                finish Ready(p,n+1usize,flag&&true);
                return 0;
            }
        "#,
        );
        let lexed = crate::lex(&source);
        assert!(parse(&source, lexed.tokens(), false).is_ok());
    }

    #[test]
    fn logical_argument_delimiters_do_not_admit_unsupported_operators() {
        for action in [
            "fold Ready(p,n%2usize);",
            "fold Ready(p) with (low=n,high=n%2usize);",
            "fold Ready(p,,n);",
        ] {
            let source = SourceFile::from_text(
                "bad-predicate-list.nera",
                format!("fn main()->u64 {{{action} return 0;}}"),
            );
            let lexed = crate::lex(&source);
            assert!(parse(&source, lexed.tokens(), false).is_err(), "{action}");
        }
    }
}
