//! Source text belongs to the preview, never to a path re-opened by the renderer.
use crate::{ByteSpan, SourceFile};
use std::fmt::Write;

pub(super) struct SourceLines<'a> {
    source: &'a SourceFile,
    starts: Vec<usize>,
}

/// Escape controls (including terminal escapes); tabs use four visible spaces.
pub(super) fn visible(text: &str) -> String {
    text.chars()
        .flat_map(|c| match c {
            '\t' => "    ".chars().collect::<Vec<_>>(),
            c if c.is_control() => c.escape_default().collect(),
            c => vec![c],
        })
        .collect()
}

impl<'a> SourceLines<'a> {
    pub(super) fn new(source: &'a SourceFile) -> Self {
        let mut starts = vec![0];
        starts.extend(
            source
                .bytes()
                .iter()
                .enumerate()
                .filter_map(|(i, b)| (*b == b'\n').then_some(i + 1)),
        );
        Self { source, starts }
    }

    pub(super) fn render(&self, out: &mut String, span: ByteSpan) {
        let path = visible(&self.source.path().to_string_lossy());
        if span.end() > self.source.len() {
            writeln!(
                out,
                "  --> {path}: bytes {}..{} (source position unavailable: out of range)",
                span.start(),
                span.end()
            )
            .unwrap();
            return;
        }
        let start_line = self.starts.partition_point(|&s| s <= span.start()) - 1;
        let last_byte = if span.is_empty() {
            span.start()
        } else {
            span.end() - 1
        };
        let end_line = self.starts.partition_point(|&s| s <= last_byte) - 1;
        let Ok(text) = self.source.text() else {
            writeln!(
                out,
                "  --> {path}:{}:{} (byte column; invalid UTF-8; bytes {}..{})",
                start_line + 1,
                span.start() - self.starts[start_line] + 1,
                span.start(),
                span.end()
            )
            .unwrap();
            let end = self
                .starts
                .get(start_line + 1)
                .copied()
                .unwrap_or(self.source.len());
            let escaped: String = self.source.bytes()[self.starts[start_line]..end]
                .iter()
                .flat_map(|b| std::ascii::escape_default(*b))
                .map(char::from)
                .collect();
            writeln!(out, "  | {escaped}").unwrap();
            return;
        };
        if !text.is_char_boundary(span.start()) || !text.is_char_boundary(span.end()) {
            writeln!(
                out,
                "  --> {path}: bytes {}..{} (character position unavailable: non-boundary span)",
                span.start(),
                span.end()
            )
            .unwrap();
            return;
        }
        let column = text[self.starts[start_line]..span.start()].chars().count() + 1;
        writeln!(
            out,
            "  --> {path}:{}:{column} (bytes {}..{})",
            start_line + 1,
            span.start(),
            span.end()
        )
        .unwrap();
        for line in start_line..=end_line {
            // Show both ends of long constructs without flooding a default report.
            if line > start_line + 1 && line < end_line {
                if line == start_line + 2 {
                    writeln!(out, "  | ...").unwrap();
                }
                continue;
            }
            let start = self.starts[line];
            let end = self.starts.get(line + 1).copied().unwrap_or(text.len());
            let contents = text[start..end].trim_end_matches(['\r', '\n']);
            let from = span.start().saturating_sub(start).min(contents.len());
            let to = span.end().saturating_sub(start).min(contents.len());
            let padding = visible(&contents[..from]).chars().count();
            let width = visible(&contents[from..to]).chars().count().max(1);
            writeln!(out, "  {} | {}", line + 1, visible(contents)).unwrap();
            writeln!(out, "    | {}{}", " ".repeat(padding), "^".repeat(width)).unwrap();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn render(text: &str, start: usize, end: usize) -> String {
        let source = SourceFile::from_text("位置.nera", text);
        let mut out = String::new();
        SourceLines::new(&source).render(&mut out, ByteSpan::new(start, end).unwrap());
        out
    }
    #[test]
    fn unicode_crlf_multiline_tabs_and_eof_use_original_bytes() {
        let out = render("名\t字\r\nnext\n", 4, 13);
        assert!(out.contains("位置.nera:1:3 (bytes 4..13)"), "{out}");
        assert!(out.contains("1 | 名    字"));
        assert!(out.contains("2 | next"));
        assert!(render("x\n", 2, 2).contains(":2:1 (bytes 2..2)"));
        assert!(render("", 0, 0).contains(":1:1 (bytes 0..0)"));
    }
    #[test]
    fn invalid_ranges_and_controls_are_not_guessed_or_interpreted() {
        assert!(render("名", 1, 2).contains("non-boundary span"));
        assert!(render("x", 0, 5).contains("out of range"));
        assert!(!render("\x1b[31m", 0, 1).contains('\x1b'));
        let source = SourceFile::new("bad", vec![0xff, b'\n']);
        let mut out = String::new();
        SourceLines::new(&source).render(&mut out, ByteSpan::new(0, 1).unwrap());
        assert!(out.contains("invalid UTF-8"));
        assert!(out.contains("\\xff"));
    }
}
