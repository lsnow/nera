//! Incremental Nera surface parser and unsupported-feature boundary.

use super::{
    AstBlock, AstEnum, AstEnumTupleField, AstEnumVariant, AstEnumVariantPayload, AstExpression,
    AstExpressionKind, AstFieldInitializer, AstFile, AstFunction, AstIntegerPredicate, AstMatchArm,
    AstNamedPattern, AstParameter, AstPattern, AstPatternKind, AstPlace, AstPlaceProjection,
    AstStatement, AstStatementKind, AstStruct, AstStructField, AstType, AstVariantInitializer,
    AstVariantPatternPayload, CstFunction, FrontendFailure, ParsedFile, span,
};
use super::{AstConstExpression, AstGenericArgument, AstGenericParameter};
use crate::lexer::{Keyword, Punctuation, Token, TokenKind};
use crate::{ByteSpan, SourceFile};
mod spec;

/// A finite parser budget turns adversarial nesting into a diagnostic, not a process abort.
// A parenthesized expression crosses several precedence frames before this
// counter advances. Keep the semantic limit below the native test-thread
// stack budget even as individual AST variants grow.
pub(super) const MAX_EXPRESSION_NESTING: usize = 128;
const MAX_BLOCK_NESTING: usize = 256;

struct ParsedBlock {
    ast: AstBlock,
    closing_token_index: usize,
}

pub(super) fn parse(
    source: &SourceFile,
    tokens: &[Token],
    module_input: bool,
) -> Result<ParsedFile, FrontendFailure> {
    Parser::new(source, tokens).parse_file(module_input)
}

struct Parser<'source, 'tokens> {
    source: &'source SourceFile,
    tokens: &'tokens [Token],
    cursor: usize,
    pending: Option<Token>,
}

impl<'source, 'tokens> Parser<'source, 'tokens> {
    fn new(source: &'source SourceFile, tokens: &'tokens [Token]) -> Self {
        Self {
            source,
            tokens,
            cursor: 0,
            pending: None,
        }
    }

    fn parse_file(mut self, module_input: bool) -> Result<ParsedFile, FrontendFailure> {
        self.skip_trivia();
        if self.current().kind() == TokenKind::Eof && !module_input {
            return Err(FrontendFailure::syntax(
                self.current().span(),
                "expected at least one function",
            ));
        }
        let file_start = self.current().span().start();
        let module = if self.current().kind() == TokenKind::Keyword(Keyword::Module) {
            self.bump();
            let path = self.parse_module_path()?;
            self.expect_punctuation(Punctuation::Semicolon, "expected `;` after module path")?;
            Some(path)
        } else {
            None
        };
        let mut imports = Vec::new();
        while self.current().kind() == TokenKind::Keyword(Keyword::Use) {
            let start = self.bump().span().start();
            let path = self.parse_module_path()?;
            let end = self
                .expect_punctuation(
                    Punctuation::Semicolon,
                    "expected `;` after import (only single-item imports are supported)",
                )?
                .span()
                .end();
            imports.push((path, span(start, end)));
        }
        let mut public = std::collections::BTreeSet::new();
        let mut cst = Vec::new();
        let mut structs = Vec::new();
        let mut enums = Vec::new();
        let mut functions = Vec::new();
        while self.current().kind() != TokenKind::Eof {
            let is_public = self.current().kind() == TokenKind::Keyword(Keyword::Pub);
            if is_public {
                self.bump();
            }
            match self.current().kind() {
                TokenKind::Keyword(Keyword::Struct) => {
                    let item = self.parse_struct()?;
                    if is_public {
                        public.insert(item.name.clone());
                    }
                    structs.push(item);
                }
                TokenKind::Keyword(Keyword::Enum) => {
                    let item = self.parse_enum()?;
                    if is_public {
                        public.insert(item.name.clone());
                    }
                    enums.push(item);
                }
                TokenKind::Keyword(Keyword::Fn) => {
                    let (cst_function, ast_function) = self.parse_function()?;
                    if is_public {
                        public.insert(ast_function.name.clone());
                    }
                    cst.push(cst_function);
                    functions.push(ast_function);
                }
                TokenKind::Keyword(_) => {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "only struct, enum and function items are supported; re-exports and other item kinds are deferred",
                    ));
                }
                _ => {
                    return Err(FrontendFailure::syntax(
                        self.current().span(),
                        "expected `struct` or `fn`",
                    ));
                }
            }
        }
        if functions.is_empty() && module.is_none() && !module_input {
            return Err(FrontendFailure::syntax(
                self.current().span(),
                "expected at least one function",
            ));
        }
        let file_span = span(file_start, self.current().span().start());
        Ok(ParsedFile {
            cst,
            ast: AstFile {
                module,
                imports,
                public,
                structs,
                enums,
                functions,
                span: file_span,
            },
        })
    }

    fn parse_module_path(&mut self) -> Result<String, FrontendFailure> {
        let first = self.expect(TokenKind::Identifier, "expected path identifier")?;
        let mut path = self.identifier_text(first);
        while self.at_punctuation(Punctuation::PathSeparator) {
            self.bump();
            if matches!(
                self.current().kind(),
                TokenKind::Punctuation(Punctuation::Star | Punctuation::LeftBrace)
            ) {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "wildcard and group imports are not supported",
                ));
            }
            let next = self.expect(
                TokenKind::Identifier,
                "expected path identifier; wildcard/group imports are not supported",
            )?;
            path.push_str("::");
            path.push_str(&self.identifier_text(next));
        }
        Ok(path)
    }

    fn parse_enum(&mut self) -> Result<AstEnum, FrontendFailure> {
        let start = self.bump().span().start();
        let name_token = self.expect(TokenKind::Identifier, "expected enum name")?;
        let name = self.identifier_text(name_token);
        let generics = self.parse_generics()?;
        self.expect_punctuation(Punctuation::LeftBrace, "expected `{` after enum name")?;
        let mut variants = Vec::new();
        while !self.at_punctuation(Punctuation::RightBrace) {
            if self.current().kind() == TokenKind::Eof {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "unterminated enum declaration",
                ));
            }
            let variant = self.expect(TokenKind::Identifier, "expected enum variant name")?;
            let payload = if self.at_punctuation(Punctuation::LeftParen) {
                self.bump();
                let mut fields = Vec::new();
                while !self.at_punctuation(Punctuation::RightParen) {
                    let field_start = self.current().span().start();
                    let ty = self.parse_type(0)?;
                    fields.push(AstEnumTupleField {
                        ty,
                        span: span(field_start, self.current().span().start()),
                    });
                    if !self.at_punctuation(Punctuation::Comma) {
                        break;
                    }
                    self.bump();
                }
                self.expect_punctuation(
                    Punctuation::RightParen,
                    "expected `)` after enum tuple payload",
                )?;
                AstEnumVariantPayload::Tuple(fields)
            } else if self.at_punctuation(Punctuation::LeftBrace) {
                self.bump();
                let mut fields = Vec::new();
                while !self.at_punctuation(Punctuation::RightBrace) {
                    let field = self.expect(TokenKind::Identifier, "expected enum field name")?;
                    self.expect_punctuation(Punctuation::Colon, "expected `:` after field name")?;
                    let ty = self.parse_type(0)?;
                    let end = self
                        .expect_punctuation(Punctuation::Comma, "expected `,` after enum field")?
                        .span()
                        .end();
                    fields.push(AstStructField {
                        name: self.identifier_text(field),
                        ty,
                        span: span(field.span().start(), end),
                    });
                }
                self.bump();
                AstEnumVariantPayload::Named(fields)
            } else {
                AstEnumVariantPayload::Unit
            };
            let end = self
                .expect_punctuation(Punctuation::Comma, "expected `,` after enum variant")?
                .span()
                .end();
            variants.push(AstEnumVariant {
                name: self.identifier_text(variant),
                payload,
                span: span(variant.span().start(), end),
            });
        }
        if variants.is_empty() {
            return Err(FrontendFailure::syntax(
                self.current().span(),
                "enum declaration requires at least one variant",
            ));
        }
        let end = self.bump().span().end();
        Ok(AstEnum {
            name,
            generics,
            variants,
            span: span(start, end),
        })
    }

    fn parse_struct(&mut self) -> Result<AstStruct, FrontendFailure> {
        let start = self.bump().span().start();
        let name_token = self.expect(TokenKind::Identifier, "expected struct name")?;
        let name = self.identifier_text(name_token);
        let generics = self.parse_generics()?;
        self.expect_punctuation(Punctuation::LeftBrace, "expected `{` after struct name")?;
        let mut fields = Vec::new();
        while !self.at_punctuation(Punctuation::RightBrace) {
            if self.current().kind() == TokenKind::Eof {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "unterminated struct declaration",
                ));
            }
            if self.current().kind() == TokenKind::Keyword(Keyword::Invariant) {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "struct invariants are not supported by stage 6.5.8",
                ));
            }
            let field_name = self.expect(TokenKind::Identifier, "expected struct field name")?;
            self.expect_punctuation(Punctuation::Colon, "expected `:` after field name")?;
            let ty = self.parse_type(0)?;
            let end = self
                .expect_punctuation(Punctuation::Comma, "expected `,` after struct field")?
                .span()
                .end();
            fields.push(AstStructField {
                name: self.identifier_text(field_name),
                ty,
                span: span(field_name.span().start(), end),
            });
        }
        let end = self.bump().span().end();
        Ok(AstStruct {
            name,
            generics,
            fields,
            span: span(start, end),
        })
    }

    fn parse_function(&mut self) -> Result<(CstFunction, AstFunction), FrontendFailure> {
        let first_index = self.cursor;
        let first = self.current();
        if first.kind() != TokenKind::Keyword(Keyword::Fn) {
            if matches!(first.kind(), TokenKind::Keyword(_)) {
                return Err(FrontendFailure::unsupported(
                    first.span(),
                    "only private function items are supported by the current frontend",
                ));
            }
            return Err(FrontendFailure::syntax(first.span(), "expected `fn`"));
        }
        let start = self.bump().span().start();
        let name_token = self.expect(TokenKind::Identifier, "expected function name")?;
        let name = self.identifier_text(name_token);

        let generics = self.parse_generics()?;
        self.expect_punctuation(Punctuation::LeftParen, "expected `(` after function name")?;
        let parameters = self.parse_parameters()?;

        let return_type = if self.at_punctuation(Punctuation::Arrow) {
            self.bump();
            self.parse_type(0)?
        } else {
            AstType::Unit
        };
        if self.current().kind() == TokenKind::Keyword(Keyword::Where)
            && self.nth_significant(1).kind() == TokenKind::Lifetime
        {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "explicit lifetime where clauses were removed; borrow dependencies are inferred, and stronger interface constraints require a stage 8 contract",
            ));
        }
        if matches!(
            self.current().kind(),
            TokenKind::Keyword(
                Keyword::Requires
                    | Keyword::Ensures
                    | Keyword::Reads
                    | Keyword::Writes
                    | Keyword::Decreases
                    | Keyword::Where
            )
        ) {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "contracts and where clauses are not supported by Core0",
            ));
        }
        let body = self.parse_block(0, 0)?;
        if block_falls_through(&body.ast) {
            return Err(FrontendFailure::syntax(
                body.ast.span,
                "function body may fall through without `return`",
            ));
        }
        let function_span = span(start, body.ast.span.end());
        Ok((
            CstFunction {
                span: function_span,
                name_span: name_token.span(),
                body_span: body.ast.span,
                token_range: first_index..body.closing_token_index + 1,
            },
            AstFunction {
                name,
                generics,
                parameters,
                return_type,
                body: body.ast,
                span: function_span,
            },
        ))
    }

    fn parse_parameters(&mut self) -> Result<Vec<AstParameter>, FrontendFailure> {
        let mut parameters = Vec::new();
        while !self.at_punctuation(Punctuation::RightParen) {
            let name = self.expect(TokenKind::Identifier, "expected parameter name")?;
            self.expect_punctuation(Punctuation::Colon, "expected `:` after parameter name")?;
            let ty = self.parse_type(0)?;
            let parameter_span = span(name.span().start(), self.current().span().start());
            parameters.push(AstParameter {
                name: self.identifier_text(name),
                ty,
                span: parameter_span,
            });
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
            if self.at_punctuation(Punctuation::RightParen) {
                break;
            }
        }
        self.expect_punctuation(
            Punctuation::RightParen,
            "expected `)` after function parameters",
        )?;
        Ok(parameters)
    }

    fn parse_type(&mut self, nesting: usize) -> Result<AstType, FrontendFailure> {
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "type nesting exceeds the frontend limit",
            ));
        }
        let token = self.current();
        match token.kind() {
            TokenKind::Punctuation(Punctuation::Amp) => {
                self.bump();
                if self.current().kind() == TokenKind::Lifetime {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "explicit lifetime annotations were removed; write `&T` or `&mut T` and let borrow dependencies be inferred",
                    ));
                }
                let mutable = self.current().kind() == TokenKind::Keyword(Keyword::Mut);
                if mutable {
                    self.bump();
                }
                let pointee = self.parse_type(nesting + 1)?;
                if matches!(pointee, AstType::Reference { .. }) {
                    return Err(FrontendFailure::unsupported(
                        token.span(),
                        "nested reference types require reborrow support from a later stage",
                    ));
                }
                Ok(AstType::Reference {
                    pointee: Box::new(pointee),
                    mutable,
                })
            }
            TokenKind::Identifier | TokenKind::Keyword(Keyword::Ptr) => {
                match token.raw(self.source) {
                    b"u64" => {
                        self.bump();
                        Ok(AstType::U64)
                    }
                    b"usize" => {
                        self.bump();
                        Ok(AstType::Usize)
                    }
                    b"bool" => {
                        self.bump();
                        Ok(AstType::Bool)
                    }
                    b"Own" | b"ptr" => {
                        let raw = token.raw(self.source);
                        self.bump();
                        self.expect_punctuation(Punctuation::Less, "expected `<` in pointer type")?;
                        let pointee =
                            self.expect(TokenKind::Identifier, "expected pointer element type")?;
                        if pointee.raw(self.source) != b"u64" {
                            return Err(FrontendFailure::unsupported(
                                pointee.span(),
                                "the current pointer slice only supports pointers to `u64`",
                            ));
                        }
                        self.expect_punctuation(
                            Punctuation::Greater,
                            "expected `>` in pointer type",
                        )?;
                        Ok(if raw == b"Own" {
                            AstType::OwnU64
                        } else {
                            AstType::RawU64
                        })
                    }
                    _ => {
                        self.bump();
                        let name = self.identifier_text(token);
                        if self.at_punctuation(Punctuation::Less) {
                            Ok(AstType::Applied {
                                name,
                                arguments: self.parse_generic_arguments(nesting + 1)?,
                            })
                        } else {
                            Ok(AstType::Named(name))
                        }
                    }
                }
            }
            TokenKind::Punctuation(Punctuation::LeftParen) => {
                self.bump();
                if self.at_punctuation(Punctuation::RightParen) {
                    self.bump();
                    return Ok(AstType::Unit);
                }
                let mut elements = Vec::new();
                let mut saw_comma = false;
                loop {
                    elements.push(self.parse_type(nesting + 1)?);
                    if !self.at_punctuation(Punctuation::Comma) {
                        break;
                    }
                    saw_comma = true;
                    self.bump();
                    if self.at_punctuation(Punctuation::RightParen) {
                        break;
                    }
                }
                self.expect_punctuation(Punctuation::RightParen, "expected `)` after tuple type")?;
                if elements.len() == 1 && !saw_comma {
                    return Err(FrontendFailure::syntax(
                        token.span(),
                        "one-element tuple types require a trailing comma",
                    ));
                }
                Ok(AstType::Tuple(elements))
            }
            TokenKind::Punctuation(Punctuation::LeftBracket) => {
                self.bump();
                let element = self.parse_type(nesting + 1)?;
                if self.at_punctuation(Punctuation::RightBracket) {
                    self.bump();
                    return Ok(AstType::Slice {
                        element: Box::new(element),
                    });
                }
                self.expect_punctuation(
                    Punctuation::Semicolon,
                    "expected `]` for a slice type or `;` in an array type",
                )?;
                let length = self.parse_const_expression()?;
                self.expect_punctuation(
                    Punctuation::RightBracket,
                    "expected `]` after array type",
                )?;
                Ok(match length {
                    AstConstExpression::Literal(length) => AstType::Array {
                        element: Box::new(element),
                        length,
                    },
                    length => AstType::ConstArray {
                        element: Box::new(element),
                        length,
                    },
                })
            }
            _ if starts_type(token.kind()) => Err(FrontendFailure::unsupported(
                token.span(),
                "this source type is outside the stage 6.5.8 concrete slice",
            )),
            _ => Err(FrontendFailure::syntax(token.span(), "expected type")),
        }
    }

    fn parse_block(
        &mut self,
        depth: usize,
        loop_depth: usize,
    ) -> Result<ParsedBlock, FrontendFailure> {
        if depth >= MAX_BLOCK_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "block nesting exceeds the frontend limit",
            ));
        }
        let start = self
            .expect_punctuation(Punctuation::LeftBrace, "expected `{` to start block")?
            .span()
            .start();
        let mut statements = Vec::new();
        let mut falls_through = true;
        while !self.at_punctuation(Punctuation::RightBrace) {
            if self.current().kind() == TokenKind::Eof {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "unterminated block",
                ));
            }
            if !falls_through {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "unreachable statement after unconditional control-flow exit",
                ));
            }
            let statement = self.parse_statement(depth, loop_depth)?;
            falls_through = statement_falls_through(&statement);
            statements.push(statement);
        }
        let closing_token_index = self.cursor;
        let end = self.bump().span().end();
        Ok(ParsedBlock {
            ast: AstBlock {
                statements,
                span: span(start, end),
            },
            closing_token_index,
        })
    }

    fn parse_statement(
        &mut self,
        block_depth: usize,
        loop_depth: usize,
    ) -> Result<AstStatement, FrontendFailure> {
        match self.current().kind() {
            TokenKind::Keyword(Keyword::Let) => self.parse_let(),
            TokenKind::Keyword(Keyword::Assert) => {
                let start = self.bump().span().start();
                let expression = self.parse_logical_expression()?;
                let end = self
                    .expect_punctuation(Punctuation::Semicolon, "expected `;` after assert")?
                    .span()
                    .end();
                Ok(AstStatement {
                    kind: AstStatementKind::Assert { expression },
                    span: span(start, end),
                })
            }
            TokenKind::Keyword(Keyword::Return) => self.parse_return(),
            TokenKind::Keyword(Keyword::If) => self.parse_if(block_depth, loop_depth),
            TokenKind::Keyword(Keyword::While) => self.parse_while(block_depth, loop_depth),
            TokenKind::Keyword(Keyword::For) => self.parse_for(block_depth, loop_depth),
            TokenKind::Keyword(Keyword::Match) => self.parse_match(block_depth, loop_depth),
            TokenKind::Keyword(Keyword::Break | Keyword::Continue) => {
                self.parse_loop_exit(loop_depth)
            }
            TokenKind::Punctuation(Punctuation::LeftBrace) => {
                let block = self.parse_block(block_depth + 1, loop_depth)?.ast;
                let span = block.span;
                Ok(AstStatement {
                    kind: AstStatementKind::Block { block },
                    span,
                })
            }
            TokenKind::Punctuation(Punctuation::Star) if self.is_store_start() => {
                self.parse_store()
            }
            TokenKind::Identifier if self.is_assignment_start() => self.parse_assignment(),
            TokenKind::Identifier if self.looks_like_generic_application() => self.parse_evaluate(),
            TokenKind::Identifier
                if self.current().raw(self.source) == b"free"
                    && self.nth_significant(1).kind()
                        == TokenKind::Punctuation(Punctuation::LeftParen) =>
            {
                self.parse_free()
            }
            TokenKind::Identifier
                if self.nth_significant(1).kind()
                    == TokenKind::Punctuation(Punctuation::LeftParen) =>
            {
                self.parse_evaluate()
            }
            kind if starts_full_expression(kind) => Err(FrontendFailure::unsupported(
                self.current().span(),
                "expression statements are not supported by Core0",
            )),
            TokenKind::Keyword(_) => Err(FrontendFailure::unsupported(
                self.current().span(),
                "this statement is not supported by Core0",
            )),
            _ => Err(FrontendFailure::syntax(
                self.current().span(),
                "expected a Core0 statement",
            )),
        }
    }

    fn parse_if(
        &mut self,
        block_depth: usize,
        loop_depth: usize,
    ) -> Result<AstStatement, FrontendFailure> {
        let start = self.bump().span().start();
        let condition = self.parse_expression_before_block()?;
        let then_block = self.parse_block(block_depth + 1, loop_depth)?.ast;
        let else_block = if self.current().kind() == TokenKind::Keyword(Keyword::Else) {
            self.bump();
            if self.current().kind() == TokenKind::Keyword(Keyword::If) {
                let nested = self.parse_if(block_depth + 1, loop_depth)?;
                Some(AstBlock {
                    span: nested.span,
                    statements: vec![nested],
                })
            } else if self.at_punctuation(Punctuation::LeftBrace) {
                Some(self.parse_block(block_depth + 1, loop_depth)?.ast)
            } else {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "expected `if` or `{` after `else`",
                ));
            }
        } else {
            None
        };
        let end = else_block
            .as_ref()
            .map_or(then_block.span.end(), |block| block.span.end());
        Ok(AstStatement {
            kind: AstStatementKind::If {
                condition,
                then_block,
                else_block,
            },
            span: span(start, end),
        })
    }

    fn parse_while(
        &mut self,
        block_depth: usize,
        loop_depth: usize,
    ) -> Result<AstStatement, FrontendFailure> {
        let start = self.bump().span().start();
        let condition = self.parse_expression_before_block()?;
        let body = self.parse_block(block_depth + 1, loop_depth + 1)?.ast;
        let statement_span = span(start, body.span.end());
        Ok(AstStatement {
            kind: AstStatementKind::While { condition, body },
            span: statement_span,
        })
    }

    fn parse_for(
        &mut self,
        block_depth: usize,
        loop_depth: usize,
    ) -> Result<AstStatement, FrontendFailure> {
        let start_span = self.bump().span().start();
        if starts_deferred_pattern(self.current().kind()) {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "destructuring for-loop bindings are not supported by stage 6.3.7",
            ));
        }
        let binding_token = self.expect(TokenKind::Identifier, "expected binding after `for`")?;
        let binding = self.identifier_text(binding_token);
        self.expect(
            TokenKind::Keyword(Keyword::In),
            "expected `in` after for-loop binding",
        )?;
        let start = self.parse_expression_before_range()?;
        if self.at_punctuation(Punctuation::RangeInclusive) {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "inclusive for ranges are not supported by stage 6.3.7",
            ));
        }
        if self.at_punctuation(Punctuation::LeftBrace) {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "iterator for-loops are not supported by stage 6.3.7",
            ));
        }
        self.expect_punctuation(Punctuation::Range, "expected `..` in for-loop range")?;
        let end = self.parse_expression_before_block()?;
        let body = self.parse_block(block_depth + 1, loop_depth + 1)?.ast;
        Ok(AstStatement {
            span: span(start_span, body.span.end()),
            kind: AstStatementKind::For {
                binding,
                binding_span: binding_token.span(),
                start,
                end,
                body,
            },
        })
    }

    fn parse_match(
        &mut self,
        block_depth: usize,
        loop_depth: usize,
    ) -> Result<AstStatement, FrontendFailure> {
        let start = self.bump().span().start();
        let scrutinee = self.parse_expression_before_block()?;
        self.expect_punctuation(Punctuation::LeftBrace, "expected `{` after match value")?;
        let mut arms = Vec::new();
        while !self.at_punctuation(Punctuation::RightBrace) {
            if self.current().kind() == TokenKind::Eof {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "expected `}` after match arms",
                ));
            }
            let pattern = self.parse_match_pattern()?;
            let arm_start = pattern.span.start();
            let guard = if self.current().kind() == TokenKind::Keyword(Keyword::If) {
                self.bump();
                Some(self.parse_expression(0)?)
            } else {
                None
            };
            self.expect_punctuation(Punctuation::FatArrow, "expected `=>` after match pattern")?;
            let body = self.parse_block(block_depth + 1, loop_depth)?.ast;
            let arm_span = span(arm_start, body.span.end());
            arms.push(AstMatchArm {
                pattern,
                guard,
                body,
                span: arm_span,
            });
            self.expect_punctuation(Punctuation::Comma, "expected `,` after match arm")?;
        }
        if arms.is_empty() {
            return Err(FrontendFailure::syntax(
                self.current().span(),
                "match requires at least one arm",
            ));
        }
        let close = self.bump();
        Ok(AstStatement {
            span: span(start, close.span().end()),
            kind: AstStatementKind::Match { scrutinee, arms },
        })
    }

    fn parse_match_pattern(&mut self) -> Result<AstPattern, FrontendFailure> {
        self.parse_pattern(0)
    }

    fn parse_pattern(&mut self, nesting: usize) -> Result<AstPattern, FrontendFailure> {
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "pattern nesting exceeds the frontend limit",
            ));
        }
        let token = self.current();
        let kind = match token.kind() {
            TokenKind::Underscore => {
                self.bump();
                AstPatternKind::Wildcard
            }
            TokenKind::IntegerLiteral => {
                self.bump();
                let (value, _) = parse_core_integer(token.raw(self.source)).map_err(|failure| {
                    FrontendFailure {
                        span: token.span(),
                        ..failure
                    }
                })?;
                AstPatternKind::Integer(value)
            }
            TokenKind::Keyword(Keyword::True | Keyword::False) => {
                self.bump();
                AstPatternKind::Bool(token.kind() == TokenKind::Keyword(Keyword::True))
            }
            TokenKind::Identifier
                if self.nth_significant(1).kind()
                    == TokenKind::Punctuation(Punctuation::PathSeparator) =>
            {
                return self.parse_variant_pattern(nesting);
            }
            TokenKind::Identifier => {
                self.bump();
                AstPatternKind::Binding(self.identifier_text(token))
            }
            TokenKind::Punctuation(Punctuation::LeftParen | Punctuation::LeftBracket) => {
                return Err(FrontendFailure::unsupported(
                    token.span(),
                    "tuple and array match patterns are not supported by stage 6.5.9",
                ));
            }
            _ => {
                return Err(FrontendFailure::syntax(
                    token.span(),
                    "expected `_`, an integer, or a boolean match pattern",
                ));
            }
        };
        Ok(AstPattern {
            kind,
            span: token.span(),
        })
    }

    fn parse_variant_pattern(&mut self, nesting: usize) -> Result<AstPattern, FrontendFailure> {
        let owner = self.bump();
        let start = owner.span().start();
        self.expect_punctuation(
            Punctuation::PathSeparator,
            "expected `::` in variant pattern",
        )?;
        let variant = self.expect(TokenKind::Identifier, "expected enum variant name")?;
        let payload = if self.at_punctuation(Punctuation::LeftParen) {
            self.bump();
            let mut fields = Vec::new();
            while !self.at_punctuation(Punctuation::RightParen) {
                fields.push(self.parse_pattern(nesting + 1)?);
                if !self.at_punctuation(Punctuation::Comma) {
                    break;
                }
                self.bump();
            }
            let close = self.expect_punctuation(
                Punctuation::RightParen,
                "expected `)` after variant pattern",
            )?;
            let pattern_span = span(start, close.span().end());
            return Ok(AstPattern {
                kind: AstPatternKind::Variant {
                    enum_name: self.identifier_text(owner),
                    variant_name: self.identifier_text(variant),
                    payload: AstVariantPatternPayload::Tuple(fields),
                },
                span: pattern_span,
            });
        } else if self.at_punctuation(Punctuation::LeftBrace) {
            self.bump();
            let mut fields = Vec::new();
            while !self.at_punctuation(Punctuation::RightBrace) {
                let field = self.expect(TokenKind::Identifier, "expected variant pattern field")?;
                self.expect_punctuation(Punctuation::Colon, "expected `:` after pattern field")?;
                let child = self.parse_pattern(nesting + 1)?;
                let field_span = span(field.span().start(), child.span.end());
                fields.push(AstNamedPattern {
                    name: self.identifier_text(field),
                    pattern: child,
                    span: field_span,
                });
                if !self.at_punctuation(Punctuation::Comma) {
                    break;
                }
                self.bump();
            }
            let close = self.expect_punctuation(
                Punctuation::RightBrace,
                "expected `}` after variant pattern",
            )?;
            let pattern_span = span(start, close.span().end());
            return Ok(AstPattern {
                kind: AstPatternKind::Variant {
                    enum_name: self.identifier_text(owner),
                    variant_name: self.identifier_text(variant),
                    payload: AstVariantPatternPayload::Named(fields),
                },
                span: pattern_span,
            });
        } else {
            AstVariantPatternPayload::Unit
        };
        Ok(AstPattern {
            kind: AstPatternKind::Variant {
                enum_name: self.identifier_text(owner),
                variant_name: self.identifier_text(variant),
                payload,
            },
            span: span(start, variant.span().end()),
        })
    }

    fn parse_loop_exit(&mut self, loop_depth: usize) -> Result<AstStatement, FrontendFailure> {
        let token = self.bump();
        if loop_depth == 0 {
            return Err(FrontendFailure::syntax(
                token.span(),
                "loop exit is only valid inside a loop",
            ));
        }
        let kind = match token.kind() {
            TokenKind::Keyword(Keyword::Break) => AstStatementKind::Break,
            TokenKind::Keyword(Keyword::Continue) => AstStatementKind::Continue,
            _ => unreachable!("caller selected a loop-exit keyword"),
        };
        let semicolon =
            self.expect_punctuation(Punctuation::Semicolon, "expected `;` after loop exit")?;
        Ok(AstStatement {
            kind,
            span: span(token.span().start(), semicolon.span().end()),
        })
    }

    fn is_store_start(&self) -> bool {
        self.nth_significant(1).kind() == TokenKind::Identifier
            && self.nth_significant(2).kind() == TokenKind::Punctuation(Punctuation::Equal)
    }

    fn is_assignment_start(&self) -> bool {
        if self.current().kind() != TokenKind::Identifier {
            return false;
        }
        let mut lookahead = 1;
        loop {
            match self.nth_significant(lookahead).kind() {
                TokenKind::Punctuation(Punctuation::Equal) => return true,
                TokenKind::Punctuation(Punctuation::Dot) => {
                    if !matches!(
                        self.nth_significant(lookahead + 1).kind(),
                        TokenKind::Identifier | TokenKind::IntegerLiteral
                    ) {
                        return false;
                    }
                    lookahead += 2;
                }
                TokenKind::Punctuation(Punctuation::LeftBracket) => {
                    lookahead += 1;
                    let mut depth = 1usize;
                    while depth > 0 {
                        match self.nth_significant(lookahead).kind() {
                            TokenKind::Eof | TokenKind::Punctuation(Punctuation::Semicolon) => {
                                return false;
                            }
                            TokenKind::Punctuation(
                                Punctuation::LeftBracket | Punctuation::LeftParen,
                            ) => depth += 1,
                            TokenKind::Punctuation(
                                Punctuation::RightBracket | Punctuation::RightParen,
                            ) => depth -= 1,
                            _ => {}
                        }
                        lookahead += 1;
                    }
                }
                _ => return false,
            }
        }
    }

    fn parse_let(&mut self) -> Result<AstStatement, FrontendFailure> {
        let start = self.bump().span().start();
        let mutable = self.current().kind() == TokenKind::Keyword(Keyword::Mut);
        if mutable {
            self.bump();
        }
        if starts_deferred_pattern(self.current().kind()) {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "binding patterns are not supported by Core0",
            ));
        }
        let name_token = self.expect(TokenKind::Identifier, "expected binding name after `let`")?;
        let name = self.identifier_text(name_token);
        let annotation = if self.at_punctuation(Punctuation::Colon) {
            self.bump();
            Some(self.parse_type(0)?)
        } else {
            None
        };
        if matches!(
            self.current().kind(),
            TokenKind::Punctuation(
                Punctuation::LeftParen
                    | Punctuation::LeftBrace
                    | Punctuation::LeftBracket
                    | Punctuation::PathSeparator
            )
        ) {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "binding patterns are not supported by Core0",
            ));
        }
        if self.at_punctuation(Punctuation::Semicolon) {
            let semicolon = self.bump();
            let declaration_span = span(start, semicolon.span().end());
            if !mutable {
                return Err(FrontendFailure::syntax(
                    declaration_span,
                    "deferred local declarations require `mut`",
                ));
            }
            let annotation = annotation.ok_or_else(|| {
                FrontendFailure::syntax(
                    declaration_span,
                    "deferred local declarations require an explicit type",
                )
            })?;
            return Ok(AstStatement {
                kind: AstStatementKind::Declare { name, annotation },
                span: declaration_span,
            });
        }
        self.expect_punctuation(Punctuation::Equal, "expected `=` in binding")?;
        let value = self.parse_expression(0)?;
        let semicolon =
            self.expect_punctuation(Punctuation::Semicolon, "expected `;` after binding")?;
        Ok(AstStatement {
            kind: AstStatementKind::Let {
                name,
                mutable,
                annotation,
                value,
            },
            span: span(start, semicolon.span().end()),
        })
    }

    fn parse_assignment(&mut self) -> Result<AstStatement, FrontendFailure> {
        let destination = self.parse_place(0)?;
        self.expect_punctuation(Punctuation::Equal, "expected `=` in assignment")?;
        let value = self.parse_expression(0)?;
        let semicolon =
            self.expect_punctuation(Punctuation::Semicolon, "expected `;` after assignment")?;
        Ok(AstStatement {
            span: span(destination.span.start(), semicolon.span().end()),
            kind: AstStatementKind::Assign { destination, value },
        })
    }

    fn parse_evaluate(&mut self) -> Result<AstStatement, FrontendFailure> {
        let expression = self.parse_expression(0)?;
        if !matches!(
            expression.kind,
            AstExpressionKind::Call { .. } | AstExpressionKind::GenericCall { .. }
        ) {
            return Err(FrontendFailure::unsupported(
                expression.span,
                "only direct calls may currently be used as expression statements",
            ));
        }
        let semicolon = self.expect_punctuation(
            Punctuation::Semicolon,
            "expected `;` after expression statement",
        )?;
        Ok(AstStatement {
            span: span(expression.span.start(), semicolon.span().end()),
            kind: AstStatementKind::Evaluate { expression },
        })
    }

    fn parse_store(&mut self) -> Result<AstStatement, FrontendFailure> {
        let start = self.bump().span().start();
        let pointer_token = self.expect(TokenKind::Identifier, "expected pointer after `*`")?;
        let pointer = self.identifier_text(pointer_token);
        self.expect_punctuation(Punctuation::Equal, "expected `=` in store")?;
        let value = self.parse_expression(0)?;
        let semicolon =
            self.expect_punctuation(Punctuation::Semicolon, "expected `;` after store")?;
        Ok(AstStatement {
            kind: AstStatementKind::Store { pointer, value },
            span: span(start, semicolon.span().end()),
        })
    }

    fn parse_free(&mut self) -> Result<AstStatement, FrontendFailure> {
        let start = self.bump().span().start();
        self.expect_punctuation(Punctuation::LeftParen, "expected `(` after `free`")?;
        let pointer_token = match self.current().kind() {
            TokenKind::Identifier => self.bump(),
            _ => {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "Core0 only supports `free(IDENT)`",
                ));
            }
        };
        let pointer = self.identifier_text(pointer_token);
        if !self.at_punctuation(Punctuation::RightParen)
            && is_deferred_expression_continuation(self.current().kind())
        {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "Core0 only supports `free(IDENT)`",
            ));
        }
        self.expect_punctuation(Punctuation::RightParen, "expected `)` after pointer")?;
        let semicolon =
            self.expect_punctuation(Punctuation::Semicolon, "expected `;` after `free`")?;
        Ok(AstStatement {
            kind: AstStatementKind::Free { pointer },
            span: span(start, semicolon.span().end()),
        })
    }

    fn parse_return(&mut self) -> Result<AstStatement, FrontendFailure> {
        let start = self.bump().span().start();
        let value = if self.at_punctuation(Punctuation::Semicolon) {
            None
        } else {
            Some(self.parse_expression(0)?)
        };
        let semicolon =
            self.expect_punctuation(Punctuation::Semicolon, "expected `;` after return")?;
        Ok(AstStatement {
            kind: AstStatementKind::Return { value },
            span: span(start, semicolon.span().end()),
        })
    }

    fn parse_expression(&mut self, nesting: usize) -> Result<AstExpression, FrontendFailure> {
        self.parse_expression_with_terminator(nesting, false, false, false)
    }

    fn parse_expression_before_block(&mut self) -> Result<AstExpression, FrontendFailure> {
        self.parse_expression_with_terminator(0, true, false, false)
    }

    fn parse_expression_before_range(&mut self) -> Result<AstExpression, FrontendFailure> {
        self.parse_expression_with_terminator(0, true, false, true)
    }

    fn parse_call_argument(&mut self, nesting: usize) -> Result<AstExpression, FrontendFailure> {
        self.parse_expression_with_terminator(nesting, false, true, false)
    }

    fn parse_expression_with_terminator(
        &mut self,
        nesting: usize,
        allow_left_brace: bool,
        allow_comma: bool,
        allow_range: bool,
    ) -> Result<AstExpression, FrontendFailure> {
        let left = self.parse_addition(nesting, allow_left_brace)?;
        let expression = if let Some(predicate) = comparison_predicate(self.current().kind()) {
            let operation_span = self.bump().span();
            let right = self.parse_addition(nesting, allow_left_brace)?;
            let expression_span = span(left.span.start(), right.span.end());
            if comparison_predicate(self.current().kind()).is_some() {
                return Err(FrontendFailure::syntax(
                    self.current().span(),
                    "comparison operators cannot be chained",
                ));
            }
            AstExpression {
                kind: AstExpressionKind::Compare {
                    predicate,
                    left: Box::new(left),
                    right: Box::new(right),
                    operation_span,
                },
                span: expression_span,
            }
        } else {
            left
        };
        if is_deferred_expression_continuation(self.current().kind())
            && !(allow_left_brace && self.at_punctuation(Punctuation::LeftBrace))
            && !(allow_comma && self.at_punctuation(Punctuation::Comma))
            && !(allow_range
                && matches!(
                    self.current().kind(),
                    TokenKind::Punctuation(Punctuation::Range | Punctuation::RangeInclusive)
                ))
        {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "this expression feature is valid Nera syntax but is not supported by the current frontend",
            ));
        }
        Ok(expression)
    }

    fn parse_addition(
        &mut self,
        nesting: usize,
        allow_left_brace: bool,
    ) -> Result<AstExpression, FrontendFailure> {
        let first = self.parse_primary(nesting, allow_left_brace)?;
        let mut operands = vec![first];
        while self.at_punctuation(Punctuation::Plus) {
            self.bump();
            operands.push(self.parse_primary(nesting, allow_left_brace)?);
        }
        if operands.len() == 1 {
            Ok(operands.pop().expect("one expression operand"))
        } else {
            let expression_span = span(
                operands.first().expect("non-empty").span.start(),
                operands.last().expect("non-empty").span.end(),
            );
            Ok(AstExpression {
                kind: AstExpressionKind::Add(operands),
                span: expression_span,
            })
        }
    }

    fn parse_primary(
        &mut self,
        nesting: usize,
        allow_left_brace: bool,
    ) -> Result<AstExpression, FrontendFailure> {
        let token = self.current();
        match token.kind() {
            TokenKind::IntegerLiteral => {
                self.bump();
                let (value, suffix) =
                    parse_integer(token.raw(self.source)).map_err(|failure| FrontendFailure {
                        span: token.span(),
                        ..failure
                    })?;
                Ok(AstExpression {
                    kind: AstExpressionKind::Integer {
                        value,
                        explicit_u64: suffix == Some(IntegerSuffix::U64),
                        explicit_usize: suffix == Some(IntegerSuffix::Usize),
                    },
                    span: token.span(),
                })
            }
            TokenKind::Keyword(Keyword::True | Keyword::False) => {
                self.bump();
                Ok(AstExpression {
                    kind: AstExpressionKind::Bool(
                        token.kind() == TokenKind::Keyword(Keyword::True),
                    ),
                    span: token.span(),
                })
            }
            TokenKind::Identifier
                if token.raw(self.source) == b"alloc"
                    && self.nth_significant(1).kind()
                        == TokenKind::Punctuation(Punctuation::Less) =>
            {
                self.parse_allocate()
            }
            TokenKind::Identifier
                if self.nth_significant(1).kind()
                    == TokenKind::Punctuation(Punctuation::PathSeparator) =>
            {
                self.parse_variant_expression(nesting)
            }
            TokenKind::Identifier
                if self.nth_significant(1).kind()
                    == TokenKind::Punctuation(Punctuation::LeftParen) =>
            {
                self.parse_call(nesting)
            }
            TokenKind::Identifier if self.looks_like_generic_application() => {
                self.parse_generic_expression(nesting)
            }
            TokenKind::Identifier => self.parse_name_or_place(token, nesting, allow_left_brace),
            TokenKind::Punctuation(Punctuation::Star) => {
                let start = self.bump().span().start();
                if self.current().kind() != TokenKind::Identifier {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "Core0 only supports dereferencing a named pointer",
                    ));
                }
                let pointer = self.bump();
                Ok(AstExpression {
                    kind: AstExpressionKind::Load {
                        pointer: self.identifier_text(pointer),
                    },
                    span: span(start, pointer.span().end()),
                })
            }
            TokenKind::Punctuation(Punctuation::Amp) => self.parse_borrow(nesting),
            TokenKind::Punctuation(Punctuation::LeftParen) => self.parse_parenthesized(nesting),
            TokenKind::Punctuation(Punctuation::LeftBracket) => self.parse_array_literal(nesting),
            kind if starts_full_expression(kind) => Err(FrontendFailure::unsupported(
                token.span(),
                "this expression is valid Nera syntax but is not supported by Core0",
            )),
            _ => Err(FrontendFailure::syntax(
                token.span(),
                "expected a Core0 expression",
            )),
        }
    }

    fn parse_name_or_place(
        &mut self,
        token: Token,
        nesting: usize,
        allow_left_brace: bool,
    ) -> Result<AstExpression, FrontendFailure> {
        self.bump();
        let name = self.identifier_text(token);
        if self.at_punctuation(Punctuation::LeftBrace) && !allow_left_brace {
            self.parse_struct_literal(name, token.span().start(), nesting)
        } else if matches!(
            self.current().kind(),
            TokenKind::Punctuation(Punctuation::Dot | Punctuation::LeftBracket)
        ) {
            let place = self.parse_place_after_base(name, token.span(), nesting)?;
            Ok(AstExpression {
                span: place.span,
                kind: AstExpressionKind::Place(place),
            })
        } else {
            Ok(AstExpression {
                kind: AstExpressionKind::Name(name),
                span: token.span(),
            })
        }
    }

    fn parse_parenthesized(&mut self, nesting: usize) -> Result<AstExpression, FrontendFailure> {
        let token = self.current();
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                token.span(),
                "expression nesting exceeds the frontend limit",
            ));
        }
        let start = self.bump().span().start();
        if self.at_punctuation(Punctuation::RightParen) {
            let close = self.bump();
            return Ok(AstExpression {
                kind: AstExpressionKind::Unit,
                span: span(start, close.span().end()),
            });
        }
        let first = self.parse_call_argument(nesting + 1)?;
        if !self.at_punctuation(Punctuation::Comma) {
            let close =
                self.expect_punctuation(Punctuation::RightParen, "expected `)` after expression")?;
            let mut expression = first;
            expression.span = span(start, close.span().end());
            return Ok(expression);
        }
        self.bump();
        let mut elements = vec![first];
        while !self.at_punctuation(Punctuation::RightParen) {
            elements.push(self.parse_call_argument(nesting + 1)?);
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
        }
        let close =
            self.expect_punctuation(Punctuation::RightParen, "expected `)` after tuple literal")?;
        Ok(AstExpression {
            kind: AstExpressionKind::Tuple(elements),
            span: span(start, close.span().end()),
        })
    }

    fn parse_struct_literal(
        &mut self,
        name: String,
        start: usize,
        nesting: usize,
    ) -> Result<AstExpression, FrontendFailure> {
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "expression nesting exceeds the frontend limit",
            ));
        }
        self.expect_punctuation(Punctuation::LeftBrace, "expected `{` in struct literal")?;
        let mut fields = Vec::new();
        while !self.at_punctuation(Punctuation::RightBrace) {
            let field = self.expect(TokenKind::Identifier, "expected struct literal field")?;
            self.expect_punctuation(Punctuation::Colon, "expected `:` after field name")?;
            let value = self.parse_call_argument(nesting + 1)?;
            let field_span = span(field.span().start(), value.span.end());
            fields.push(AstFieldInitializer {
                name: self.identifier_text(field),
                value,
                span: field_span,
            });
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
        }
        let close =
            self.expect_punctuation(Punctuation::RightBrace, "expected `}` after struct literal")?;
        Ok(AstExpression {
            kind: AstExpressionKind::Struct { name, fields },
            span: span(start, close.span().end()),
        })
    }

    fn parse_variant_expression(
        &mut self,
        nesting: usize,
    ) -> Result<AstExpression, FrontendFailure> {
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "expression nesting exceeds the frontend limit",
            ));
        }
        let owner = self.bump();
        let start = owner.span().start();
        self.expect_punctuation(Punctuation::PathSeparator, "expected `::` in enum variant")?;
        let variant = self.expect(TokenKind::Identifier, "expected enum variant name")?;
        let (payload, end) = if self.at_punctuation(Punctuation::LeftParen) {
            self.bump();
            let mut values = Vec::new();
            while !self.at_punctuation(Punctuation::RightParen) {
                values.push(self.parse_call_argument(nesting + 1)?);
                if !self.at_punctuation(Punctuation::Comma) {
                    break;
                }
                self.bump();
            }
            let close = self.expect_punctuation(
                Punctuation::RightParen,
                "expected `)` after enum variant arguments",
            )?;
            (AstVariantInitializer::Tuple(values), close.span().end())
        } else if self.at_punctuation(Punctuation::LeftBrace) {
            self.bump();
            let mut fields = Vec::new();
            while !self.at_punctuation(Punctuation::RightBrace) {
                let field = self.expect(TokenKind::Identifier, "expected enum variant field")?;
                self.expect_punctuation(Punctuation::Colon, "expected `:` after field name")?;
                let value = self.parse_call_argument(nesting + 1)?;
                fields.push(AstFieldInitializer {
                    name: self.identifier_text(field),
                    span: span(field.span().start(), value.span.end()),
                    value,
                });
                if !self.at_punctuation(Punctuation::Comma) {
                    break;
                }
                self.bump();
            }
            let close = self.expect_punctuation(
                Punctuation::RightBrace,
                "expected `}` after enum variant fields",
            )?;
            (AstVariantInitializer::Named(fields), close.span().end())
        } else {
            (AstVariantInitializer::Unit, variant.span().end())
        };
        Ok(AstExpression {
            kind: AstExpressionKind::EnumVariant {
                enum_name: self.identifier_text(owner),
                variant_name: self.identifier_text(variant),
                payload,
            },
            span: span(start, end),
        })
    }

    fn parse_array_literal(&mut self, nesting: usize) -> Result<AstExpression, FrontendFailure> {
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "expression nesting exceeds the frontend limit",
            ));
        }
        let start = self.bump().span().start();
        if self.at_punctuation(Punctuation::RightBracket) {
            let close = self.bump();
            return Ok(AstExpression {
                kind: AstExpressionKind::Array(Vec::new()),
                span: span(start, close.span().end()),
            });
        }
        let first = self.parse_call_argument(nesting + 1)?;
        if self.at_punctuation(Punctuation::Semicolon) {
            self.bump();
            let length = self.parse_const_expression()?;
            let close = self.expect_punctuation(
                Punctuation::RightBracket,
                "expected `]` after array repetition",
            )?;
            return Ok(AstExpression {
                kind: match length {
                    AstConstExpression::Literal(length) => AstExpressionKind::ArrayRepeat {
                        value: Box::new(first),
                        length,
                    },
                    length => AstExpressionKind::ConstRepeat {
                        value: Box::new(first),
                        length,
                    },
                },
                span: span(start, close.span().end()),
            });
        }
        let mut elements = vec![first];
        while self.at_punctuation(Punctuation::Comma) {
            self.bump();
            if self.at_punctuation(Punctuation::RightBracket) {
                break;
            }
            elements.push(self.parse_call_argument(nesting + 1)?);
        }
        let close = self.expect_punctuation(
            Punctuation::RightBracket,
            "expected `]` after array literal",
        )?;
        Ok(AstExpression {
            kind: AstExpressionKind::Array(elements),
            span: span(start, close.span().end()),
        })
    }

    fn parse_place(&mut self, nesting: usize) -> Result<AstPlace, FrontendFailure> {
        if self.at_punctuation(Punctuation::Star) {
            let start = self.bump().span().start();
            let base = self.expect(TokenKind::Identifier, "expected pointer name after `*`")?;
            let base_span = base.span();
            let mut place = self.parse_place_after_base(
                self.identifier_text(base),
                span(start, base_span.end()),
                nesting,
            )?;
            place.projections.insert(
                0,
                AstPlaceProjection::Dereference {
                    span: span(start, base_span.end()),
                },
            );
            return Ok(place);
        }
        let base = self.expect(TokenKind::Identifier, "expected place base")?;
        self.parse_place_after_base(self.identifier_text(base), base.span(), nesting)
    }

    fn parse_borrow(&mut self, nesting: usize) -> Result<AstExpression, FrontendFailure> {
        let start = self.bump().span().start();
        let raw = self.current().kind() == TokenKind::Keyword(Keyword::Raw);
        if raw {
            self.bump();
        }
        if self.current().kind() == TokenKind::Lifetime {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "explicit lifetime annotations were removed; write an ordinary borrow and let its dependency be inferred",
            ));
        }
        let mutable = self.current().kind() == TokenKind::Keyword(Keyword::Mut);
        if mutable {
            self.bump();
        }
        let place = self.parse_place(nesting + 1)?;
        Ok(AstExpression {
            span: span(start, place.span.end()),
            kind: if raw {
                AstExpressionKind::RawAddress { place, mutable }
            } else {
                AstExpressionKind::Borrow { place, mutable }
            },
        })
    }

    fn parse_place_after_base(
        &mut self,
        base: String,
        base_span: ByteSpan,
        nesting: usize,
    ) -> Result<AstPlace, FrontendFailure> {
        let mut projections = Vec::new();
        let mut end = base_span.end();
        loop {
            if self.at_punctuation(Punctuation::Dot) {
                let start = self.bump().span().start();
                let token = self.current();
                match token.kind() {
                    TokenKind::Identifier => {
                        self.bump();
                        end = token.span().end();
                        projections.push(AstPlaceProjection::Field {
                            name: self.identifier_text(token),
                            span: span(start, end),
                        });
                    }
                    TokenKind::IntegerLiteral => {
                        self.bump();
                        let (index, suffix) =
                            parse_integer(token.raw(self.source)).map_err(|failure| {
                                FrontendFailure {
                                    span: token.span(),
                                    ..failure
                                }
                            })?;
                        if suffix.is_some() {
                            return Err(FrontendFailure::elaboration(
                                token.span(),
                                "tuple element index must be unsuffixed",
                            ));
                        }
                        end = token.span().end();
                        projections.push(AstPlaceProjection::TupleElement {
                            index,
                            span: span(start, end),
                        });
                    }
                    _ => {
                        return Err(FrontendFailure::syntax(
                            token.span(),
                            "expected field name or tuple index after `.`",
                        ));
                    }
                }
            } else if self.at_punctuation(Punctuation::LeftBracket) {
                let start = self.bump().span().start();
                if self.at_punctuation(Punctuation::RangeInclusive) {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "inclusive slice ranges are not supported",
                    ));
                }
                let first = if self.at_punctuation(Punctuation::Range) {
                    None
                } else {
                    Some(self.parse_expression_with_terminator(nesting + 1, false, false, true)?)
                };
                if self.at_punctuation(Punctuation::RangeInclusive) {
                    return Err(FrontendFailure::unsupported(
                        self.current().span(),
                        "inclusive slice ranges are not supported",
                    ));
                }
                let is_slice = self.at_punctuation(Punctuation::Range);
                if is_slice {
                    self.bump();
                    if self.at_punctuation(Punctuation::RangeInclusive) {
                        return Err(FrontendFailure::unsupported(
                            self.current().span(),
                            "inclusive slice ranges are not supported",
                        ));
                    }
                }
                let range_end = if is_slice && !self.at_punctuation(Punctuation::RightBracket) {
                    Some(self.parse_expression(nesting + 1)?)
                } else {
                    None
                };
                let close = self.expect_punctuation(
                    Punctuation::RightBracket,
                    "expected `]` after index or slice expression",
                )?;
                end = close.span().end();
                if is_slice {
                    projections.push(AstPlaceProjection::Slice {
                        start: first.map(Box::new),
                        end: range_end.map(Box::new),
                        span: span(start, end),
                    });
                } else {
                    projections.push(AstPlaceProjection::Index {
                        index: Box::new(first.ok_or_else(|| {
                            FrontendFailure::syntax(
                                span(start, end),
                                "index expression cannot be empty",
                            )
                        })?),
                        span: span(start, end),
                    });
                }
            } else {
                break;
            }
        }
        Ok(AstPlace {
            base,
            projections,
            span: span(base_span.start(), end),
        })
    }

    fn parse_allocate(&mut self) -> Result<AstExpression, FrontendFailure> {
        let start = self.bump().span().start();
        self.expect_punctuation(Punctuation::Less, "expected `<` after `alloc`")?;
        let element_type = self.parse_type(0)?;
        self.expect_punctuation(
            Punctuation::Greater,
            "expected `>` after allocation element type",
        )?;
        self.expect_punctuation(Punctuation::LeftParen, "expected `(` after allocation type")?;
        if self.current().kind() != TokenKind::IntegerLiteral {
            if starts_full_expression(self.current().kind()) {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "Core0 allocation count must be an integer literal",
                ));
            }
            return Err(FrontendFailure::syntax(
                self.current().span(),
                "expected literal allocation count",
            ));
        }
        let count_token = self.bump();
        let (count, _) = parse_core_integer(count_token.raw(self.source)).map_err(|failure| {
            FrontendFailure {
                span: count_token.span(),
                ..failure
            }
        })?;
        if !self.at_punctuation(Punctuation::RightParen)
            && !matches!(
                self.current().kind(),
                TokenKind::Eof
                    | TokenKind::Punctuation(Punctuation::Semicolon | Punctuation::RightBrace)
            )
        {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "Core0 allocation count must be a single integer literal",
            ));
        }
        let close = self.expect_punctuation(
            Punctuation::RightParen,
            "expected `)` after allocation count",
        )?;
        Ok(AstExpression {
            kind: AstExpressionKind::Allocate {
                element_type,
                count,
            },
            span: span(start, close.span().end()),
        })
    }

    fn parse_call(&mut self, nesting: usize) -> Result<AstExpression, FrontendFailure> {
        if nesting >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "expression nesting exceeds the Core0 frontend limit",
            ));
        }
        let callee = self.bump();
        let start = callee.span().start();
        self.expect_punctuation(Punctuation::LeftParen, "expected `(` after callee")?;
        let mut arguments = Vec::new();
        while !self.at_punctuation(Punctuation::RightParen) {
            arguments.push(self.parse_call_argument(nesting + 1)?);
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
            if self.at_punctuation(Punctuation::RightParen) {
                break;
            }
        }
        let close =
            self.expect_punctuation(Punctuation::RightParen, "expected `)` after call arguments")?;
        Ok(AstExpression {
            kind: AstExpressionKind::Call {
                callee: self.identifier_text(callee),
                arguments,
            },
            span: span(start, close.span().end()),
        })
    }

    fn identifier_text(&self, token: Token) -> String {
        std::str::from_utf8(token.raw(self.source))
            .expect("Core0 identifiers were checked as ASCII")
            .to_owned()
    }

    fn parse_generics(&mut self) -> Result<Vec<AstGenericParameter>, FrontendFailure> {
        if !self.at_punctuation(Punctuation::Less) {
            return Ok(Vec::new());
        }
        self.bump();
        let mut parameters = Vec::new();
        let mut names = std::collections::BTreeSet::new();
        loop {
            let token = self.current();
            let parameter = if token.kind() == TokenKind::Lifetime {
                return Err(FrontendFailure::unsupported(
                    token.span(),
                    "explicit lifetime binders were removed; keep only type/const parameters and let borrow dependencies be inferred",
                ));
            } else if token.kind() == TokenKind::Keyword(Keyword::Const) {
                self.bump();
                let name = self.expect(TokenKind::Identifier, "expected const parameter name")?;
                self.expect_punctuation(Punctuation::Colon, "const parameter requires `: usize`")?;
                let ty = self.parse_type(0)?;
                if ty != AstType::Usize {
                    return Err(FrontendFailure::unsupported(
                        token.span(),
                        "const parameters currently require usize",
                    ));
                }
                AstGenericParameter::Const(self.identifier_text(name))
            } else {
                let name = self.expect(TokenKind::Identifier, "expected generic parameter")?;
                AstGenericParameter::Type(self.identifier_text(name))
            };
            if matches!(parameter.name(), "u64" | "usize" | "bool" | "Own" | "ptr") {
                return Err(FrontendFailure::elaboration(
                    token.span(),
                    "generic binder cannot shadow a builtin type",
                ));
            }
            if !names.insert(parameter.name().to_owned()) {
                return Err(FrontendFailure::elaboration(
                    token.span(),
                    "duplicate generic binder",
                ));
            }
            if parameters.len() >= 32 {
                return Err(FrontendFailure::unsupported(
                    token.span(),
                    "generic binder budget exceeded",
                ));
            }
            parameters.push(parameter);
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
        }
        self.expect_punctuation(
            Punctuation::Greater,
            "expected `>` after generic parameters",
        )?;
        Ok(parameters)
    }

    fn parse_const_expression(&mut self) -> Result<AstConstExpression, FrontendFailure> {
        let mut operands = Vec::new();
        loop {
            let token = self.current();
            let operand = match token.kind() {
                TokenKind::IntegerLiteral => {
                    self.bump();
                    let (value, suffix) =
                        parse_integer(token.raw(self.source)).map_err(|f| FrontendFailure {
                            span: token.span(),
                            ..f
                        })?;
                    if suffix.is_some() {
                        return Err(FrontendFailure::elaboration(
                            token.span(),
                            "const expression literals must be unsuffixed",
                        ));
                    }
                    AstConstExpression::Literal(value)
                }
                TokenKind::Identifier => {
                    self.bump();
                    AstConstExpression::Name(self.identifier_text(token))
                }
                _ => {
                    return Err(FrontendFailure::unsupported(
                        token.span(),
                        "const expressions support only literals, const binders and checked addition",
                    ));
                }
            };
            if operands.len() >= 128 {
                return Err(FrontendFailure::unsupported(
                    token.span(),
                    "const expression budget exceeded",
                ));
            }
            operands.push(operand);
            if !self.at_punctuation(Punctuation::Plus) {
                break;
            }
            self.bump();
        }
        Ok(if operands.len() == 1 {
            operands.pop().unwrap()
        } else {
            AstConstExpression::Add(operands)
        })
    }

    fn parse_generic_arguments(
        &mut self,
        depth: usize,
    ) -> Result<Vec<AstGenericArgument>, FrontendFailure> {
        if depth >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "generic argument nesting budget exceeded",
            ));
        }
        self.expect_punctuation(Punctuation::Less, "expected `<` before generic arguments")?;
        let mut arguments = Vec::new();
        loop {
            let argument = if self.current().kind() == TokenKind::IntegerLiteral
                || (self.current().kind() == TokenKind::Identifier
                    && self.nth_significant(1).kind() == TokenKind::Punctuation(Punctuation::Plus))
            {
                AstGenericArgument::Const(self.parse_const_expression()?)
            } else {
                AstGenericArgument::Type(self.parse_type(depth + 1)?)
            };
            arguments.push(argument);
            if arguments.len() > 32 {
                return Err(FrontendFailure::unsupported(
                    self.current().span(),
                    "generic argument budget exceeded",
                ));
            }
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
        }
        self.expect_punctuation(Punctuation::Greater, "expected `>` after generic arguments")?;
        Ok(arguments)
    }

    fn looks_like_generic_application(&self) -> bool {
        if self.nth_significant(1).kind() != TokenKind::Punctuation(Punctuation::Less) {
            return false;
        }
        let mut depth = 0i32;
        let mut brackets = 0i32;
        for i in 1..512 {
            match self.nth_significant(i).kind() {
                TokenKind::Punctuation(Punctuation::Less) => depth += 1,
                TokenKind::Punctuation(Punctuation::Greater) => depth -= 1,
                TokenKind::Punctuation(Punctuation::ShiftRight) => depth -= 2,
                TokenKind::Punctuation(Punctuation::LeftBracket) => brackets += 1,
                TokenKind::Punctuation(Punctuation::RightBracket) => brackets -= 1,
                TokenKind::Punctuation(Punctuation::Semicolon) if brackets == 0 => return false,
                TokenKind::Eof | TokenKind::Punctuation(Punctuation::RightBrace) => return false,
                _ => {}
            }
            if depth <= 0 {
                return depth == 0
                    && matches!(
                        self.nth_significant(i + 1).kind(),
                        TokenKind::Punctuation(Punctuation::LeftParen | Punctuation::LeftBrace)
                    );
            }
        }
        false
    }

    fn parse_generic_expression(&mut self, depth: usize) -> Result<AstExpression, FrontendFailure> {
        if depth >= MAX_EXPRESSION_NESTING {
            return Err(FrontendFailure::unsupported(
                self.current().span(),
                "generic expression nesting budget exceeded",
            ));
        }
        let token = self.bump();
        let name = self.identifier_text(token);
        let types = self.parse_generic_arguments(depth + 1)?;
        if self.at_punctuation(Punctuation::LeftBrace) {
            let mut expression =
                self.parse_struct_literal(name.clone(), token.span().start(), depth)?;
            let AstExpressionKind::Struct { fields, .. } = expression.kind else {
                unreachable!()
            };
            expression.kind = AstExpressionKind::GenericStruct {
                name,
                types,
                fields,
            };
            return Ok(expression);
        }
        self.expect_punctuation(Punctuation::LeftParen, "expected `(` after generic callee")?;
        let mut arguments = Vec::new();
        while !self.at_punctuation(Punctuation::RightParen) {
            arguments.push(self.parse_call_argument(depth + 1)?);
            if !self.at_punctuation(Punctuation::Comma) {
                break;
            }
            self.bump();
        }
        let close =
            self.expect_punctuation(Punctuation::RightParen, "expected `)` after call arguments")?;
        Ok(AstExpression {
            kind: AstExpressionKind::GenericCall {
                callee: name,
                types,
                arguments,
            },
            span: span(token.span().start(), close.span().end()),
        })
    }

    fn expect(
        &mut self,
        expected: TokenKind,
        message: &'static str,
    ) -> Result<Token, FrontendFailure> {
        if self.current().kind() != expected {
            return Err(FrontendFailure::syntax(self.current().span(), message));
        }
        Ok(self.bump())
    }

    fn expect_punctuation(
        &mut self,
        expected: Punctuation,
        message: &'static str,
    ) -> Result<Token, FrontendFailure> {
        if expected == Punctuation::Greater {
            let token = self.current();
            let remainder = match token.kind() {
                TokenKind::Punctuation(Punctuation::ShiftRight) => Some(Punctuation::Greater),
                TokenKind::Punctuation(Punctuation::ShiftRightEqual) => {
                    Some(Punctuation::GreaterEqual)
                }
                TokenKind::Punctuation(Punctuation::GreaterEqual) => Some(Punctuation::Equal),
                _ => None,
            };
            if let Some(remainder) = remainder {
                self.bump();
                self.pending = Some(Token::new(
                    TokenKind::Punctuation(remainder),
                    span(token.span().start() + 1, token.span().end()),
                ));
                return Ok(Token::new(
                    TokenKind::Punctuation(Punctuation::Greater),
                    span(token.span().start(), token.span().start() + 1),
                ));
            }
        }
        self.expect(TokenKind::Punctuation(expected), message)
    }

    fn at_punctuation(&self, punctuation: Punctuation) -> bool {
        self.current().kind() == TokenKind::Punctuation(punctuation)
    }

    fn current(&self) -> Token {
        self.pending.unwrap_or(self.tokens[self.cursor])
    }

    fn nth_significant(&self, requested: usize) -> Token {
        let mut found = 0;
        for token in self.pending.iter().chain(self.tokens[self.cursor..].iter()) {
            if token.kind().is_trivia() {
                continue;
            }
            if found == requested {
                return *token;
            }
            found += 1;
        }
        *self.tokens.last().expect("lexer always emits EOF")
    }

    fn bump(&mut self) -> Token {
        let token = self.current();
        if self.pending.take().is_some() {
            return token;
        }
        if token.kind() != TokenKind::Eof {
            self.cursor += 1;
            self.skip_trivia();
        }
        token
    }

    fn skip_trivia(&mut self) {
        while self
            .tokens
            .get(self.cursor)
            .is_some_and(|token| token.kind().is_trivia())
        {
            self.cursor += 1;
        }
    }
}

fn comparison_predicate(kind: TokenKind) -> Option<AstIntegerPredicate> {
    match kind {
        TokenKind::Punctuation(Punctuation::EqualEqual) => Some(AstIntegerPredicate::Equal),
        TokenKind::Punctuation(Punctuation::NotEqual) => Some(AstIntegerPredicate::NotEqual),
        TokenKind::Punctuation(Punctuation::Less) => Some(AstIntegerPredicate::LessThan),
        TokenKind::Punctuation(Punctuation::LessEqual) => Some(AstIntegerPredicate::LessOrEqual),
        TokenKind::Punctuation(Punctuation::Greater) => Some(AstIntegerPredicate::GreaterThan),
        TokenKind::Punctuation(Punctuation::GreaterEqual) => {
            Some(AstIntegerPredicate::GreaterOrEqual)
        }
        _ => None,
    }
}

fn block_falls_through(block: &AstBlock) -> bool {
    block.statements.last().is_none_or(statement_falls_through)
}

fn statement_falls_through(statement: &AstStatement) -> bool {
    match &statement.kind {
        AstStatementKind::Return { .. } | AstStatementKind::Break | AstStatementKind::Continue => {
            false
        }
        AstStatementKind::Block { block } => block_falls_through(block),
        AstStatementKind::Match { arms, .. } => {
            arms.iter().any(|arm| block_falls_through(&arm.body))
        }
        AstStatementKind::If {
            then_block,
            else_block: Some(else_block),
            ..
        } => block_falls_through(then_block) || block_falls_through(else_block),
        AstStatementKind::Assert { .. }
        | AstStatementKind::Declare { .. }
        | AstStatementKind::Let { .. }
        | AstStatementKind::Assign { .. }
        | AstStatementKind::Store { .. }
        | AstStatementKind::Free { .. }
        | AstStatementKind::Evaluate { .. }
        | AstStatementKind::For { .. }
        | AstStatementKind::While { .. }
        | AstStatementKind::If {
            else_block: None, ..
        } => true,
    }
}

fn starts_full_expression(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Identifier
            | TokenKind::IntegerLiteral
            | TokenKind::FloatLiteral
            | TokenKind::CharLiteral
            | TokenKind::ByteCharLiteral
            | TokenKind::StringLiteral
            | TokenKind::ByteStringLiteral
            | TokenKind::Lifetime
            | TokenKind::Keyword(Keyword::True | Keyword::False | Keyword::Null | Keyword::Move)
            | TokenKind::Punctuation(
                Punctuation::LeftParen
                    | Punctuation::LeftBracket
                    | Punctuation::Star
                    | Punctuation::Minus
                    | Punctuation::Bang
                    | Punctuation::Tilde
                    | Punctuation::Amp
            )
    )
}

fn starts_type(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Identifier
            | TokenKind::Keyword(Keyword::Ptr | Keyword::Fn)
            | TokenKind::Punctuation(
                Punctuation::Amp | Punctuation::LeftBracket | Punctuation::LeftParen
            )
    )
}

fn starts_deferred_pattern(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Underscore
            | TokenKind::IntegerLiteral
            | TokenKind::CharLiteral
            | TokenKind::ByteCharLiteral
            | TokenKind::Keyword(Keyword::True | Keyword::False)
            | TokenKind::Punctuation(
                Punctuation::LeftParen | Punctuation::LeftBracket | Punctuation::Amp
            )
    )
}

fn is_deferred_expression_continuation(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Keyword(Keyword::As)
            | TokenKind::Punctuation(
                Punctuation::LeftParen
                    | Punctuation::LeftBrace
                    | Punctuation::LeftBracket
                    | Punctuation::Comma
                    | Punctuation::Dot
                    | Punctuation::Question
                    | Punctuation::Plus
                    | Punctuation::Minus
                    | Punctuation::Star
                    | Punctuation::Slash
                    | Punctuation::Percent
                    | Punctuation::Amp
                    | Punctuation::Pipe
                    | Punctuation::Caret
                    | Punctuation::Less
                    | Punctuation::Greater
                    | Punctuation::Range
                    | Punctuation::RangeInclusive
                    | Punctuation::LogicalAnd
                    | Punctuation::LogicalOr
                    | Punctuation::EqualEqual
                    | Punctuation::NotEqual
                    | Punctuation::LessEqual
                    | Punctuation::GreaterEqual
                    | Punctuation::ShiftLeft
                    | Punctuation::ShiftRight
                    | Punctuation::Arrow
                    | Punctuation::PathSeparator
            )
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IntegerSuffix {
    U64,
    Usize,
}

fn parse_integer(raw: &[u8]) -> Result<(u64, Option<IntegerSuffix>), FrontendFailure> {
    let text = std::str::from_utf8(raw).expect("integer token is ASCII");
    const OTHER_SUFFIXES: [&str; 8] = ["isize", "i16", "i32", "i64", "u16", "u32", "i8", "u8"];
    if OTHER_SUFFIXES.iter().any(|suffix| text.ends_with(suffix)) {
        return Err(FrontendFailure::unsupported(
            ByteSpan::empty(),
            "integer literals in the current surface slice can only use `u64` or `usize`",
        ));
    }
    let (body, suffix) = if let Some(body) = text.strip_suffix("usize") {
        (body, Some(IntegerSuffix::Usize))
    } else if let Some(body) = text.strip_suffix("u64") {
        (body, Some(IntegerSuffix::U64))
    } else {
        (text, None)
    };
    let (digits, radix) = if let Some(rest) = body.strip_prefix("0x") {
        (rest, 16)
    } else if let Some(rest) = body.strip_prefix("0o") {
        (rest, 8)
    } else if let Some(rest) = body.strip_prefix("0b") {
        (rest, 2)
    } else {
        (body, 10)
    };
    let normalized: String = digits
        .chars()
        .filter(|character| *character != '_')
        .collect();
    let value = u64::from_str_radix(&normalized, radix).map_err(|_| {
        FrontendFailure::elaboration(
            ByteSpan::empty(),
            "integer literal does not fit in Core0 `u64`",
        )
    })?;
    Ok((value, suffix))
}

fn parse_core_integer(raw: &[u8]) -> Result<(u64, bool), FrontendFailure> {
    let (value, suffix) = parse_integer(raw)?;
    if suffix == Some(IntegerSuffix::Usize) {
        return Err(FrontendFailure::unsupported(
            ByteSpan::empty(),
            "this integer position requires `u64` or an unsuffixed literal",
        ));
    }
    Ok((value, suffix == Some(IntegerSuffix::U64)))
}
