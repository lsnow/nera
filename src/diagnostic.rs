//! Common diagnostic data shared by compiler phases.

use std::ops::Range;

/// A half-open byte range in the original, potentially non-UTF-8 source bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteSpan {
    start: usize,
    end: usize,
}

impl ByteSpan {
    /// The canonical empty span used when no source position is available.
    #[must_use]
    pub const fn empty() -> Self {
        Self { start: 0, end: 0 }
    }

    /// Creates a byte span, returning `None` when its bounds are reversed.
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Option<Self> {
        if start <= end {
            Some(Self { start, end })
        } else {
            None
        }
    }

    #[must_use]
    pub const fn start(self) -> usize {
        self.start
    }

    #[must_use]
    pub const fn end(self) -> usize {
        self.end
    }

    #[must_use]
    pub const fn len(self) -> usize {
        self.end - self.start
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Returns whether `child` lies wholly within this half-open span.
    #[must_use]
    pub const fn contains(self, child: Self) -> bool {
        self.start <= child.start && child.end <= self.end
    }
}

impl From<ByteSpan> for Range<usize> {
    fn from(span: ByteSpan) -> Self {
        span.start..span.end
    }
}

/// Compatibility helper for phase-local validators that use function syntax.
/// New code should prefer [`ByteSpan::contains`].
#[must_use]
pub(crate) const fn span_contains(parent: ByteSpan, child: ByteSpan) -> bool {
    parent.contains(child)
}

/// Diagnostic severity independent of a particular renderer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
    Error,
    Warning,
    Note,
    Help,
}

/// A compiler diagnostic with an optional primary source span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    severity: Severity,
    message: String,
    primary_span: Option<ByteSpan>,
}

impl Diagnostic {
    #[must_use]
    pub fn new(severity: Severity, message: impl Into<String>) -> Self {
        Self {
            severity,
            message: message.into(),
            primary_span: None,
        }
    }

    #[must_use]
    pub fn error(message: impl Into<String>) -> Self {
        Self::new(Severity::Error, message)
    }

    #[must_use]
    pub fn warning(message: impl Into<String>) -> Self {
        Self::new(Severity::Warning, message)
    }

    #[must_use]
    pub fn note(message: impl Into<String>) -> Self {
        Self::new(Severity::Note, message)
    }

    #[must_use]
    pub fn help(message: impl Into<String>) -> Self {
        Self::new(Severity::Help, message)
    }

    #[must_use]
    pub const fn with_primary_span(mut self, span: ByteSpan) -> Self {
        self.primary_span = Some(span);
        self
    }

    #[must_use]
    pub const fn severity(&self) -> Severity {
        self.severity
    }

    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    #[must_use]
    pub const fn primary_span(&self) -> Option<ByteSpan> {
        self.primary_span
    }
}

#[cfg(test)]
mod tests {
    use super::{ByteSpan, Diagnostic, Severity};

    #[test]
    fn byte_span_rejects_reversed_bounds() {
        assert_eq!(ByteSpan::new(4, 3), None);
    }

    #[test]
    fn byte_span_empty_and_containment_are_canonical() {
        let outer = ByteSpan::new(2, 8).expect("valid span");
        let inner = ByteSpan::new(3, 8).expect("valid span");
        let crossing = ByteSpan::new(1, 4).expect("valid span");

        assert_eq!(ByteSpan::empty(), ByteSpan::new(0, 0).expect("valid span"));
        assert!(outer.contains(inner));
        assert!(!outer.contains(crossing));
    }

    #[test]
    fn diagnostic_can_carry_a_primary_span() {
        let span = ByteSpan::new(1, 4).expect("valid span");
        let diagnostic = Diagnostic::error("unexpected token").with_primary_span(span);

        assert_eq!(diagnostic.severity(), Severity::Error);
        assert_eq!(diagnostic.message(), "unexpected token");
        assert_eq!(diagnostic.primary_span(), Some(span));
    }

    #[test]
    fn convenience_constructors_cover_every_severity() {
        let diagnostics = [
            Diagnostic::error("error"),
            Diagnostic::warning("warning"),
            Diagnostic::note("note"),
            Diagnostic::help("help"),
        ];

        assert_eq!(
            diagnostics.map(|diagnostic| diagnostic.severity()),
            [
                Severity::Error,
                Severity::Warning,
                Severity::Note,
                Severity::Help,
            ]
        );
    }
}
