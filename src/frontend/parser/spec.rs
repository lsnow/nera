//! Bounded logical precedence parsing, independent of runtime arithmetic.
use super::*;
use crate::frontend::{AstLogicalExpression as E, AstLogicalExpressionKind as K};

impl Parser<'_, '_> {
    pub(super) fn parse_logical_expression(&mut self) -> Result<E, FrontendFailure> {
        let (expression, _) = self.logical(0, 0)?;
        if is_deferred_expression_continuation(self.current().kind()) {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "logical expression feature is outside the supported theory",
            ));
        }
        Ok(expression)
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
        } else if self.current().kind() == TokenKind::Identifier
            && self.current().raw(self.source) == b"alive"
            && self.nth_significant(1).kind() == TokenKind::Punctuation(Punctuation::LeftParen)
        {
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
        } else if self.current().kind() == TokenKind::Identifier
            && matches!(
                self.current().raw(self.source),
                b"initialized" | b"readable" | b"writable"
            )
            && self.nth_significant(1).kind() == TokenKind::Punctuation(Punctuation::LeftParen)
        {
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
