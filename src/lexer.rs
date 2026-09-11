//! Byte-oriented, lossless tokenization for Nera source files.

mod number;

use crate::{ByteSpan, Diagnostic, SourceFile};

/// A reserved Nera word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Keyword {
    As,
    Assert,
    Break,
    Const,
    Continue,
    Decreases,
    Else,
    Enum,
    Ensures,
    Exists,
    Extern,
    False,
    Fn,
    For,
    Forall,
    Ghost,
    If,
    In,
    Invariant,
    Let,
    Match,
    Module,
    Move,
    Mut,
    Null,
    Proof,
    Ptr,
    Pub,
    Raw,
    Reads,
    Region,
    Requires,
    Result,
    Return,
    SelfValue,
    Spawn,
    Static,
    Struct,
    Theorem,
    True,
    Trusted,
    Type,
    Use,
    Where,
    While,
    Writes,
}

/// Punctuation after maximal-munch tokenization.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Punctuation {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Comma,
    Semicolon,
    Colon,
    Dot,
    Question,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Pipe,
    Caret,
    Bang,
    Tilde,
    Less,
    Greater,
    Equal,
    PathSeparator,
    Arrow,
    FatArrow,
    Range,
    RangeInclusive,
    LogicalAnd,
    LogicalOr,
    EqualEqual,
    NotEqual,
    LessEqual,
    GreaterEqual,
    ShiftLeft,
    ShiftRight,
    PlusEqual,
    MinusEqual,
    StarEqual,
    SlashEqual,
    PercentEqual,
    AmpEqual,
    PipeEqual,
    CaretEqual,
    ShiftLeftEqual,
    ShiftRightEqual,
}

/// The reason an error token was emitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LexErrorKind {
    InvalidUtf8,
    UnexpectedBom,
    NulByte,
    InvalidWhitespace,
    UnterminatedBlockComment,
    InvalidNumber,
    InvalidLiteral,
    UnexpectedByte,
}

/// A lossless lexical token. Its raw spelling is always read from its span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TokenKind {
    InitialBom,
    Whitespace,
    LineComment,
    BlockComment,
    Identifier,
    Underscore,
    IntegerLiteral,
    FloatLiteral,
    CharLiteral,
    ByteCharLiteral,
    StringLiteral,
    ByteStringLiteral,
    Lifetime,
    Keyword(Keyword),
    Punctuation(Punctuation),
    Error(LexErrorKind),
    Eof,
}

impl TokenKind {
    /// Returns whether this token is ignored by the parser but retained by the CST.
    #[must_use]
    pub const fn is_trivia(self) -> bool {
        matches!(
            self,
            Self::InitialBom | Self::Whitespace | Self::LineComment | Self::BlockComment
        )
    }
}

/// A token and its half-open source byte span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Token {
    kind: TokenKind,
    span: ByteSpan,
}

impl Token {
    #[must_use]
    pub const fn new(kind: TokenKind, span: ByteSpan) -> Self {
        Self { kind, span }
    }

    #[must_use]
    pub const fn kind(self) -> TokenKind {
        self.kind
    }

    #[must_use]
    pub const fn span(self) -> ByteSpan {
        self.span
    }

    /// Returns the exact source bytes covered by this token.
    #[must_use]
    pub fn raw(self, source: &SourceFile) -> &[u8] {
        &source.bytes()[Range::from(self.span)]
    }
}

use std::ops::Range;

/// A lexical diagnostic with a stable machine-readable class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexIssue {
    kind: LexErrorKind,
    diagnostic: Diagnostic,
}

impl LexIssue {
    #[must_use]
    pub const fn kind(&self) -> LexErrorKind {
        self.kind
    }

    #[must_use]
    pub const fn diagnostic(&self) -> &Diagnostic {
        &self.diagnostic
    }
}

/// Complete output of the lossless lexer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lexed {
    tokens: Vec<Token>,
    issues: Vec<LexIssue>,
}

impl Lexed {
    #[must_use]
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    #[must_use]
    pub fn issues(&self) -> &[LexIssue] {
        &self.issues
    }

    /// Checks the central lossless-token invariant used by tests and fuzzing.
    #[must_use]
    pub fn has_bounded_contiguous_spans(&self, source_len: usize) -> bool {
        let Some((eof, body)) = self.tokens.split_last() else {
            return false;
        };
        if eof.kind != TokenKind::Eof
            || eof.span.start() != source_len
            || eof.span.end() != source_len
        {
            return false;
        }

        let mut expected_start = 0;
        for token in body {
            if token.span.start() != expected_start
                || token.span.end() > source_len
                || token.span.is_empty()
            {
                return false;
            }
            expected_start = token.span.end();
        }
        expected_start == source_len
    }
}

/// Tokenizes arbitrary source bytes without replacing invalid UTF-8.
#[must_use]
pub fn lex(source: &SourceFile) -> Lexed {
    Lexer::new(source.bytes()).run()
}

struct Lexer<'source> {
    bytes: &'source [u8],
    offset: usize,
    tokens: Vec<Token>,
    issues: Vec<LexIssue>,
}

impl<'source> Lexer<'source> {
    fn new(bytes: &'source [u8]) -> Self {
        Self {
            bytes,
            offset: 0,
            tokens: Vec::new(),
            issues: Vec::new(),
        }
    }

    fn run(mut self) -> Lexed {
        while self.offset < self.bytes.len() {
            self.scan_one();
        }
        self.push(TokenKind::Eof, self.offset, self.offset);
        Lexed {
            tokens: self.tokens,
            issues: self.issues,
        }
    }

    fn scan_one(&mut self) {
        let start = self.offset;

        if self.bytes[start..].starts_with(&[0xef, 0xbb, 0xbf]) {
            self.offset += 3;
            if start == 0 {
                self.push(TokenKind::InitialBom, start, self.offset);
            } else {
                self.error(LexErrorKind::UnexpectedBom, start, self.offset);
            }
            return;
        }

        match self.bytes[start] {
            b' ' | b'\t' | b'\n' => self.scan_whitespace(),
            b'\r' if self.bytes.get(start + 1) == Some(&b'\n') => self.scan_whitespace(),
            b'\r' => {
                self.offset += 1;
                self.error(LexErrorKind::InvalidWhitespace, start, self.offset);
            }
            0 => {
                self.offset += 1;
                self.error(LexErrorKind::NulByte, start, self.offset);
            }
            b'/' if self.bytes.get(start + 1) == Some(&b'/') => self.scan_line_comment(),
            b'/' if self.bytes.get(start + 1) == Some(&b'*') => self.scan_block_comment(),
            b'b' if matches!(self.bytes.get(start + 1), Some(b'\'' | b'"')) => {
                self.scan_quoted(true)
            }
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.scan_ascii_identifier(),
            b'0'..=b'9' => self.scan_number(),
            b'\'' => self.scan_apostrophe(),
            b'"' => self.scan_quoted(false),
            byte if punctuation(byte).is_some() => self.scan_punctuation(),
            byte if byte >= 0x80 => self.scan_unicode_or_invalid(),
            _ => {
                self.offset += 1;
                self.error(LexErrorKind::UnexpectedByte, start, self.offset);
            }
        }
    }

    fn scan_whitespace(&mut self) {
        let start = self.offset;
        while self.offset < self.bytes.len() {
            match self.bytes[self.offset] {
                b' ' | b'\t' | b'\n' => self.offset += 1,
                b'\r' if self.bytes.get(self.offset + 1) == Some(&b'\n') => self.offset += 2,
                _ => break,
            }
        }
        self.push(TokenKind::Whitespace, start, self.offset);
    }

    fn scan_line_comment(&mut self) {
        let start = self.offset;
        self.offset += 2;
        while !matches!(self.bytes.get(self.offset), None | Some(b'\n' | b'\r')) {
            self.offset += 1;
        }
        self.push_text_checked(TokenKind::LineComment, start, self.offset);
    }

    fn scan_block_comment(&mut self) {
        let start = self.offset;
        self.offset += 2;
        let mut depth = 1_usize;
        while self.offset < self.bytes.len() {
            if self.bytes[self.offset..].starts_with(b"/*") {
                depth += 1;
                self.offset += 2;
            } else if self.bytes[self.offset..].starts_with(b"*/") {
                depth -= 1;
                self.offset += 2;
                if depth == 0 {
                    self.push_text_checked(TokenKind::BlockComment, start, self.offset);
                    return;
                }
            } else {
                self.offset += 1;
            }
        }
        self.error(LexErrorKind::UnterminatedBlockComment, start, self.offset);
    }

    fn scan_ascii_identifier(&mut self) {
        let start = self.offset;
        self.offset += 1;
        while self
            .bytes
            .get(self.offset)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        {
            self.offset += 1;
        }

        let raw = &self.bytes[start..self.offset];
        let kind = if raw == b"_" {
            TokenKind::Underscore
        } else if let Some(keyword) = keyword(raw) {
            TokenKind::Keyword(keyword)
        } else {
            TokenKind::Identifier
        };
        self.push(kind, start, self.offset);
    }

    fn scan_number(&mut self) {
        let start = self.offset;
        let (end, class) = number::scan(self.bytes, start);
        self.offset = end;
        match class {
            Some(number::NumberClass::Integer) => {
                self.push(TokenKind::IntegerLiteral, start, self.offset)
            }
            Some(number::NumberClass::Float) => {
                self.push(TokenKind::FloatLiteral, start, self.offset)
            }
            None => self.error(LexErrorKind::InvalidNumber, start, self.offset),
        }
    }

    fn scan_apostrophe(&mut self) {
        let start = self.offset;
        match apostrophe_form(self.bytes, start) {
            ApostropheForm::Quoted(end) => {
                self.offset = end;
                if let Some(kind) = global_text_error(&self.bytes[start..end]) {
                    self.error(kind, start, end);
                } else if validate_quoted(&self.bytes[start..end], false, true) {
                    self.push(TokenKind::CharLiteral, start, end);
                } else {
                    self.error(LexErrorKind::InvalidLiteral, start, end);
                }
            }
            ApostropheForm::Lifetime(end) => {
                self.offset = end;
                self.push_text_checked(TokenKind::Lifetime, start, end);
            }
            ApostropheForm::Invalid(end) => {
                self.offset = end;
                self.error(LexErrorKind::InvalidLiteral, start, end);
            }
        }
    }

    fn scan_quoted(&mut self, byte_literal: bool) {
        let start = self.offset;
        let quote_index = start + usize::from(byte_literal);
        let quote = self.bytes[quote_index];
        let end = if quote == b'\'' {
            match apostrophe_form(self.bytes, quote_index) {
                ApostropheForm::Quoted(end) => end,
                ApostropheForm::Lifetime(end) | ApostropheForm::Invalid(end) => {
                    self.offset = end;
                    self.error(LexErrorKind::InvalidLiteral, start, end);
                    return;
                }
            }
        } else {
            let Some(end) = quoted_end(self.bytes, quote_index, quote) else {
                self.offset = unterminated_quoted_end(self.bytes, quote_index + 1);
                self.error(LexErrorKind::InvalidLiteral, start, self.offset);
                return;
            };
            end
        };
        self.offset = end;
        let is_char = quote == b'\'';
        if let Some(kind) = global_text_error(&self.bytes[start..end]) {
            self.error(kind, start, end);
            return;
        }
        if !validate_quoted(&self.bytes[start..end], byte_literal, is_char) {
            self.error(LexErrorKind::InvalidLiteral, start, end);
            return;
        }
        let kind = match (byte_literal, is_char) {
            (false, false) => TokenKind::StringLiteral,
            (false, true) => TokenKind::CharLiteral,
            (true, false) => TokenKind::ByteStringLiteral,
            (true, true) => TokenKind::ByteCharLiteral,
        };
        self.push(kind, start, end);
    }

    fn scan_punctuation(&mut self) {
        let start = self.offset;
        let (punctuation, width) = longest_punctuation(&self.bytes[start..]);
        self.offset += width;
        self.push(TokenKind::Punctuation(punctuation), start, self.offset);
    }

    fn scan_unicode_or_invalid(&mut self) {
        let start = self.offset;
        let Some((first, width)) = decode_scalar(&self.bytes[start..]) else {
            self.offset += invalid_utf8_width(&self.bytes[start..]);
            self.error(LexErrorKind::InvalidUtf8, start, self.offset);
            return;
        };
        if first == '\u{feff}' {
            self.offset += width;
            self.error(LexErrorKind::UnexpectedBom, start, self.offset);
            return;
        }
        if first.is_whitespace() {
            self.offset += width;
            self.error(LexErrorKind::InvalidWhitespace, start, self.offset);
            return;
        }

        self.offset += width;
        while self.offset < self.bytes.len() {
            let byte = self.bytes[self.offset];
            if byte.is_ascii_alphanumeric() || byte == b'_' {
                self.offset += 1;
            } else if byte < 0x80 {
                break;
            } else if let Some((scalar, scalar_width)) = decode_scalar(&self.bytes[self.offset..]) {
                if scalar.is_whitespace() || scalar == '\u{feff}' {
                    break;
                }
                self.offset += scalar_width;
            } else {
                break;
            }
        }
        self.push(TokenKind::Identifier, start, self.offset);
    }

    fn push_text_checked(&mut self, kind: TokenKind, start: usize, end: usize) {
        if let Some(error) = global_text_error(&self.bytes[start..end]) {
            self.error(error, start, end);
            return;
        }
        self.push(kind, start, end);
    }

    fn push(&mut self, kind: TokenKind, start: usize, end: usize) {
        let span = ByteSpan::new(start, end).expect("lexer constructs ordered spans");
        self.tokens.push(Token::new(kind, span));
    }

    fn error(&mut self, kind: LexErrorKind, start: usize, end: usize) {
        let span = ByteSpan::new(start, end).expect("lexer constructs ordered spans");
        self.tokens.push(Token::new(TokenKind::Error(kind), span));
        self.issues.push(LexIssue {
            kind,
            diagnostic: Diagnostic::error(lex_error_message(kind)).with_primary_span(span),
        });
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ApostropheForm {
    Quoted(usize),
    Lifetime(usize),
    Invalid(usize),
}

fn apostrophe_form(bytes: &[u8], quote_index: usize) -> ApostropheForm {
    let content_start = quote_index + 1;
    let Some(&first) = bytes.get(content_start) else {
        return ApostropheForm::Invalid(content_start);
    };
    if matches!(first, b'\n' | b'\r' | 0) {
        return ApostropheForm::Invalid(content_start);
    }
    if first == b'\\' {
        return quoted_end(bytes, quote_index, b'\'').map_or_else(
            || ApostropheForm::Invalid(unterminated_quoted_end(bytes, content_start)),
            ApostropheForm::Quoted,
        );
    }
    if is_identifier_candidate_byte(first) {
        let mut end = content_start;
        while bytes
            .get(end)
            .is_some_and(|byte| is_identifier_candidate_byte(*byte))
        {
            end += 1;
        }
        return if bytes.get(end) == Some(&b'\'') {
            ApostropheForm::Quoted(end + 1)
        } else {
            ApostropheForm::Lifetime(end)
        };
    }

    let Some((_, width)) = decode_scalar(&bytes[content_start..]) else {
        return ApostropheForm::Invalid(
            content_start + invalid_utf8_width(&bytes[content_start..]),
        );
    };
    let scalar_end = content_start + width;
    if bytes.get(scalar_end) == Some(&b'\'') {
        ApostropheForm::Quoted(scalar_end + 1)
    } else {
        ApostropheForm::Invalid(scalar_end)
    }
}

fn quoted_end(bytes: &[u8], quote_index: usize, quote: u8) -> Option<usize> {
    let mut offset = quote_index + 1;
    let mut escaped = false;
    while let Some(&byte) = bytes.get(offset) {
        if !escaped && byte == quote {
            return Some(offset + 1);
        }
        if !escaped && matches!(byte, b'\n' | b'\r' | 0) {
            return None;
        }
        escaped = !escaped && byte == b'\\';
        offset += 1;
    }
    None
}

fn unterminated_quoted_end(bytes: &[u8], mut offset: usize) -> usize {
    while let Some(&byte) = bytes.get(offset) {
        if matches!(byte, b'\n' | b'\r') {
            break;
        }
        offset += 1;
    }
    offset
}

fn validate_quoted(raw: &[u8], byte_literal: bool, require_one_scalar: bool) -> bool {
    if std::str::from_utf8(raw).is_err() {
        return false;
    }
    let prefix = usize::from(byte_literal);
    if raw.len() < prefix + 2 {
        return false;
    }
    let content = &raw[prefix + 1..raw.len() - 1];
    let mut offset = 0;
    let mut scalars = 0_usize;
    while offset < content.len() {
        let byte = content[offset];
        if matches!(byte, b'\n' | b'\r' | 0) {
            return false;
        }
        if byte != b'\\' {
            let Some((scalar, width)) = decode_scalar(&content[offset..]) else {
                return false;
            };
            if byte_literal && !scalar.is_ascii() {
                return false;
            }
            scalars += 1;
            offset += width;
            continue;
        }

        offset += 1;
        let Some(&escape) = content.get(offset) else {
            return false;
        };
        match escape {
            b'\\' | b'"' | b'\'' | b'n' | b'r' | b't' | b'0' => offset += 1,
            b'x' => {
                if content
                    .get(offset + 1)
                    .is_none_or(|byte| !byte.is_ascii_hexdigit())
                    || content
                        .get(offset + 2)
                        .is_none_or(|byte| !byte.is_ascii_hexdigit())
                {
                    return false;
                }
                offset += 3;
            }
            b'u' if !byte_literal && content.get(offset + 1) == Some(&b'{') => {
                let digits_start = offset + 2;
                let mut end = digits_start;
                while content.get(end).is_some_and(u8::is_ascii_hexdigit) {
                    end += 1;
                }
                if end == digits_start || end - digits_start > 6 || content.get(end) != Some(&b'}')
                {
                    return false;
                }
                let Ok(hex) = std::str::from_utf8(&content[digits_start..end]) else {
                    return false;
                };
                let Ok(value) = u32::from_str_radix(hex, 16) else {
                    return false;
                };
                if char::from_u32(value).is_none() {
                    return false;
                }
                offset = end + 1;
            }
            _ => return false,
        }
        scalars += 1;
    }
    !require_one_scalar || scalars == 1
}

fn global_text_error(raw: &[u8]) -> Option<LexErrorKind> {
    if std::str::from_utf8(raw).is_err() {
        Some(LexErrorKind::InvalidUtf8)
    } else if raw.contains(&0) {
        Some(LexErrorKind::NulByte)
    } else if raw.windows(3).any(|window| window == [0xef, 0xbb, 0xbf]) {
        Some(LexErrorKind::UnexpectedBom)
    } else {
        None
    }
}

fn decode_scalar(bytes: &[u8]) -> Option<(char, usize)> {
    let width = utf8_width(*bytes.first()?);
    if width == 0 || bytes.len() < width {
        return None;
    }
    let text = std::str::from_utf8(&bytes[..width]).ok()?;
    Some((text.chars().next()?, width))
}

fn invalid_utf8_width(bytes: &[u8]) -> usize {
    match std::str::from_utf8(bytes).expect_err("caller starts at invalid UTF-8") {
        error if error.valid_up_to() > 0 => 1,
        error => error.error_len().unwrap_or(bytes.len()).min(bytes.len()),
    }
}

const fn utf8_width(first: u8) -> usize {
    match first {
        0x00..=0x7f => 1,
        0xc2..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf4 => 4,
        _ => 0,
    }
}

fn is_identifier_candidate_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte >= 0x80
}

fn longest_punctuation(bytes: &[u8]) -> (Punctuation, usize) {
    const MULTI: [(&[u8], Punctuation); 23] = [
        (b"<<=", Punctuation::ShiftLeftEqual),
        (b">>=", Punctuation::ShiftRightEqual),
        (b"..=", Punctuation::RangeInclusive),
        (b"::", Punctuation::PathSeparator),
        (b"->", Punctuation::Arrow),
        (b"=>", Punctuation::FatArrow),
        (b"..", Punctuation::Range),
        (b"&&", Punctuation::LogicalAnd),
        (b"||", Punctuation::LogicalOr),
        (b"==", Punctuation::EqualEqual),
        (b"!=", Punctuation::NotEqual),
        (b"<=", Punctuation::LessEqual),
        (b">=", Punctuation::GreaterEqual),
        (b"<<", Punctuation::ShiftLeft),
        (b">>", Punctuation::ShiftRight),
        (b"+=", Punctuation::PlusEqual),
        (b"-=", Punctuation::MinusEqual),
        (b"*=", Punctuation::StarEqual),
        (b"/=", Punctuation::SlashEqual),
        (b"%=", Punctuation::PercentEqual),
        (b"&=", Punctuation::AmpEqual),
        (b"|=", Punctuation::PipeEqual),
        (b"^=", Punctuation::CaretEqual),
    ];
    for (spelling, punctuation) in MULTI {
        if !spelling.is_empty() && bytes.starts_with(spelling) {
            return (punctuation, spelling.len());
        }
    }
    (
        punctuation(bytes[0]).expect("caller checked punctuation"),
        1,
    )
}

const fn punctuation(byte: u8) -> Option<Punctuation> {
    Some(match byte {
        b'(' => Punctuation::LeftParen,
        b')' => Punctuation::RightParen,
        b'{' => Punctuation::LeftBrace,
        b'}' => Punctuation::RightBrace,
        b'[' => Punctuation::LeftBracket,
        b']' => Punctuation::RightBracket,
        b',' => Punctuation::Comma,
        b';' => Punctuation::Semicolon,
        b':' => Punctuation::Colon,
        b'.' => Punctuation::Dot,
        b'?' => Punctuation::Question,
        b'+' => Punctuation::Plus,
        b'-' => Punctuation::Minus,
        b'*' => Punctuation::Star,
        b'/' => Punctuation::Slash,
        b'%' => Punctuation::Percent,
        b'&' => Punctuation::Amp,
        b'|' => Punctuation::Pipe,
        b'^' => Punctuation::Caret,
        b'!' => Punctuation::Bang,
        b'~' => Punctuation::Tilde,
        b'<' => Punctuation::Less,
        b'>' => Punctuation::Greater,
        b'=' => Punctuation::Equal,
        _ => return None,
    })
}

fn keyword(raw: &[u8]) -> Option<Keyword> {
    Some(match raw {
        b"as" => Keyword::As,
        b"assert" => Keyword::Assert,
        b"break" => Keyword::Break,
        b"const" => Keyword::Const,
        b"continue" => Keyword::Continue,
        b"decreases" => Keyword::Decreases,
        b"else" => Keyword::Else,
        b"enum" => Keyword::Enum,
        b"ensures" => Keyword::Ensures,
        b"exists" => Keyword::Exists,
        b"extern" => Keyword::Extern,
        b"false" => Keyword::False,
        b"fn" => Keyword::Fn,
        b"for" => Keyword::For,
        b"forall" => Keyword::Forall,
        b"ghost" => Keyword::Ghost,
        b"if" => Keyword::If,
        b"in" => Keyword::In,
        b"invariant" => Keyword::Invariant,
        b"let" => Keyword::Let,
        b"match" => Keyword::Match,
        b"module" => Keyword::Module,
        b"move" => Keyword::Move,
        b"mut" => Keyword::Mut,
        b"null" => Keyword::Null,
        b"proof" => Keyword::Proof,
        b"ptr" => Keyword::Ptr,
        b"pub" => Keyword::Pub,
        b"raw" => Keyword::Raw,
        b"reads" => Keyword::Reads,
        b"region" => Keyword::Region,
        b"requires" => Keyword::Requires,
        b"result" => Keyword::Result,
        b"return" => Keyword::Return,
        b"self" => Keyword::SelfValue,
        b"spawn" => Keyword::Spawn,
        b"static" => Keyword::Static,
        b"struct" => Keyword::Struct,
        b"theorem" => Keyword::Theorem,
        b"true" => Keyword::True,
        b"trusted" => Keyword::Trusted,
        b"type" => Keyword::Type,
        b"use" => Keyword::Use,
        b"where" => Keyword::Where,
        b"while" => Keyword::While,
        b"writes" => Keyword::Writes,
        _ => return None,
    })
}

const fn lex_error_message(kind: LexErrorKind) -> &'static str {
    match kind {
        LexErrorKind::InvalidUtf8 => "source contains invalid UTF-8",
        LexErrorKind::UnexpectedBom => "UTF-8 BOM is only allowed at the start of a file",
        LexErrorKind::NulByte => "source contains a NUL byte",
        LexErrorKind::InvalidWhitespace => "whitespace is not allowed by the Nera source profile",
        LexErrorKind::UnterminatedBlockComment => "unterminated block comment",
        LexErrorKind::InvalidNumber => "invalid numeric literal",
        LexErrorKind::InvalidLiteral => "invalid or unterminated quoted literal",
        LexErrorKind::UnexpectedByte => "byte cannot start a Nera token",
    }
}

#[cfg(test)]
mod tests {
    use super::{Keyword, LexErrorKind, Punctuation, TokenKind, lex};
    use crate::SourceFile;

    fn kinds(text: &str) -> Vec<TokenKind> {
        lex(&SourceFile::from_text("test.nera", text))
            .tokens()
            .iter()
            .map(|token| token.kind())
            .collect()
    }

    #[test]
    fn lexes_core_tokens_and_retains_trivia() {
        assert_eq!(
            kinds("fn f() { /* x */ return; }"),
            vec![
                TokenKind::Keyword(Keyword::Fn),
                TokenKind::Whitespace,
                TokenKind::Identifier,
                TokenKind::Punctuation(Punctuation::LeftParen),
                TokenKind::Punctuation(Punctuation::RightParen),
                TokenKind::Whitespace,
                TokenKind::Punctuation(Punctuation::LeftBrace),
                TokenKind::Whitespace,
                TokenKind::BlockComment,
                TokenKind::Whitespace,
                TokenKind::Keyword(Keyword::Return),
                TokenKind::Punctuation(Punctuation::Semicolon),
                TokenKind::Whitespace,
                TokenKind::Punctuation(Punctuation::RightBrace),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn punctuation_uses_maximal_munch() {
        assert_eq!(
            kinds("..= >>= :: ->"),
            vec![
                TokenKind::Punctuation(Punctuation::RangeInclusive),
                TokenKind::Whitespace,
                TokenKind::Punctuation(Punctuation::ShiftRightEqual),
                TokenKind::Whitespace,
                TokenKind::Punctuation(Punctuation::PathSeparator),
                TokenKind::Whitespace,
                TokenKind::Punctuation(Punctuation::Arrow),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn number_boundaries_and_errors_follow_the_spec() {
        assert_eq!(
            kinds("1.0 1..2 0xff 42u64 0b102"),
            vec![
                TokenKind::FloatLiteral,
                TokenKind::Whitespace,
                TokenKind::IntegerLiteral,
                TokenKind::Punctuation(Punctuation::Range),
                TokenKind::IntegerLiteral,
                TokenKind::Whitespace,
                TokenKind::IntegerLiteral,
                TokenKind::Whitespace,
                TokenKind::IntegerLiteral,
                TokenKind::Whitespace,
                TokenKind::Error(LexErrorKind::InvalidNumber),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn numeric_operators_are_not_absorbed_after_hex_or_suffix_text() {
        assert_eq!(
            kinds("0xbe+1 1usize+2 0xff.0"),
            vec![
                TokenKind::IntegerLiteral,
                TokenKind::Punctuation(Punctuation::Plus),
                TokenKind::IntegerLiteral,
                TokenKind::Whitespace,
                TokenKind::IntegerLiteral,
                TokenKind::Punctuation(Punctuation::Plus),
                TokenKind::IntegerLiteral,
                TokenKind::Whitespace,
                TokenKind::IntegerLiteral,
                TokenKind::Punctuation(Punctuation::Dot),
                TokenKind::IntegerLiteral,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn adjacent_lifetimes_do_not_form_a_char_candidate() {
        assert_eq!(
            kinds("'a, 'b"),
            vec![
                TokenKind::Lifetime,
                TokenKind::Punctuation(Punctuation::Comma),
                TokenKind::Whitespace,
                TokenKind::Lifetime,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn nested_comments_and_literals_are_lossless() {
        let source =
            SourceFile::from_text("test.nera", "/* outer /* inner */ */ 'é' b'\\xff' \"x\\n\"");
        let lexed = lex(&source);
        assert!(lexed.issues().is_empty());
        assert!(lexed.has_bounded_contiguous_spans(source.len()));
    }

    #[test]
    fn arbitrary_invalid_bytes_are_covered_by_error_tokens() {
        let source = SourceFile::new("invalid.nera", [0xff, b' ', 0, 0xe2, 0x82]);
        let lexed = lex(&source);
        assert_eq!(lexed.issues().len(), 3);
        assert!(lexed.has_bounded_contiguous_spans(source.len()));
    }

    #[test]
    fn non_ascii_candidate_is_not_a_lexical_error() {
        let source = SourceFile::from_text("test.nera", "名字");
        let lexed = lex(&source);
        assert!(lexed.issues().is_empty());
        assert_eq!(lexed.tokens()[0].kind(), TokenKind::Identifier);
    }

    #[test]
    fn comments_cannot_hide_globally_invalid_source_bytes() {
        for bytes in [
            b"// nul \0".as_slice(),
            b"/* bom \xef\xbb\xbf */".as_slice(),
            b"// invalid \xff".as_slice(),
        ] {
            let source = SourceFile::new("invalid.nera", bytes);
            let lexed = lex(&source);
            assert_eq!(lexed.issues().len(), 1);
            assert!(lexed.has_bounded_contiguous_spans(source.len()));
        }
    }
}
