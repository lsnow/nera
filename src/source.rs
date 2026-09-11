//! Source file ownership and loading.

mod database;
pub use database::{SourceDatabase, SourceDatabaseError, SourceInput};

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::str::Utf8Error;

/// An owned source file presented to the compiler frontend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceFile {
    path: PathBuf,
    bytes: Vec<u8>,
}

impl SourceFile {
    /// Loads a source file without validating or replacing its bytes.
    pub fn load(path: impl AsRef<Path>) -> io::Result<Self> {
        let path = path.as_ref();
        let bytes = fs::read(path)?;

        Ok(Self::new(path, bytes))
    }

    /// Creates an in-memory source file from unvalidated bytes.
    pub fn new(path: impl Into<PathBuf>, bytes: impl Into<Vec<u8>>) -> Self {
        Self {
            path: path.into(),
            bytes: bytes.into(),
        }
    }

    /// Creates an in-memory source file from known UTF-8 text.
    pub fn from_text(path: impl Into<PathBuf>, text: impl AsRef<str>) -> Self {
        Self::new(path, text.as_ref().as_bytes())
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns a UTF-8 view when the complete source is valid UTF-8.
    ///
    /// The lexer, rather than the file loader, is responsible for turning an
    /// error from this validation into a source diagnostic.
    pub fn text(&self) -> Result<&str, Utf8Error> {
        std::str::from_utf8(&self.bytes)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::SourceFile;
    use std::path::Path;

    #[test]
    fn in_memory_source_uses_utf8_byte_length() {
        let source = SourceFile::from_text("example.nera", "let 名字 = 1;");

        assert_eq!(source.path(), Path::new("example.nera"));
        assert_eq!(source.len(), source.text().expect("valid UTF-8").len());
        assert!(source.len() > source.text().expect("valid UTF-8").chars().count());
    }

    #[test]
    fn invalid_utf8_is_preserved_for_the_lexer() {
        let bytes = vec![b'f', b'n', b' ', 0xff, b';'];
        let source = SourceFile::new("invalid.nera", bytes.clone());

        assert_eq!(source.bytes(), bytes);
        assert!(source.text().is_err());
    }
}
