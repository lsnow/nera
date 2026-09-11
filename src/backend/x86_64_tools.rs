use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

static TEMPORARY_NONCE: AtomicU64 = AtomicU64::new(0);

/// System programs used after pure assembly emission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64SystemToolchain {
    assembler: OsString,
    linker_driver: OsString,
}

impl Default for X86_64SystemToolchain {
    fn default() -> Self {
        Self::new("as", "cc")
    }
}

impl X86_64SystemToolchain {
    #[must_use]
    pub fn new(assembler: impl Into<OsString>, linker_driver: impl Into<OsString>) -> Self {
        Self {
            assembler: assembler.into(),
            linker_driver: linker_driver.into(),
        }
    }

    #[must_use]
    pub fn assembler(&self) -> &OsStr {
        &self.assembler
    }

    #[must_use]
    pub fn linker_driver(&self) -> &OsStr {
        &self.linker_driver
    }

    /// Writes an assembly artifact without invoking a system program.
    pub fn write_assembly(&self, assembly: &str, output: &Path) -> Result<(), X86_64ToolError> {
        fs::write(output, assembly.as_bytes()).map_err(|error| {
            io_error(
                X86_64ToolStage::WriteAssembly,
                X86_64ToolOperation::WriteOutput,
                error,
                Vec::new(),
                output,
            )
        })?;
        require_output_file(X86_64ToolStage::WriteAssembly, Vec::new(), output)
    }

    /// Runs `as --64 -o OUTPUT -` and supplies assembly through stdin.
    pub fn assemble(&self, assembly: &str, output: &Path) -> Result<(), X86_64ToolError> {
        let arguments = vec![
            OsString::from("--64"),
            OsString::from("-o"),
            output.as_os_str().to_owned(),
            OsString::from("-"),
        ];
        run_tool(
            X86_64ToolStage::Assemble,
            &self.assembler,
            arguments,
            Some(assembly.as_bytes()),
            output,
        )
    }

    /// Runs the system C driver so CRT, libc and the dynamic loader remain a
    /// platform-toolchain concern rather than being hard-coded by Nera.
    pub fn link(&self, object: &Path, output: &Path) -> Result<(), X86_64ToolError> {
        let arguments = vec![
            OsString::from("-pie"),
            OsString::from("-o"),
            output.as_os_str().to_owned(),
            object.as_os_str().to_owned(),
        ];
        run_tool(
            X86_64ToolStage::Link,
            &self.linker_driver,
            arguments,
            None,
            output,
        )
    }

    /// Assembles into a private temporary object and links an ELF executable.
    pub fn build_executable(&self, assembly: &str, output: &Path) -> Result<(), X86_64ToolError> {
        let temporary = TemporaryObject::create()?;
        self.assemble(assembly, temporary.object())?;
        self.link(temporary.object(), output)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64ToolStage {
    WriteAssembly,
    Assemble,
    Link,
    TemporaryObject,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64ToolOperation {
    CreateTemporaryDirectory,
    Spawn,
    WriteToolInput,
    Wait,
    WriteOutput,
    InspectOutput,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64ToolErrorKind {
    Io {
        operation: X86_64ToolOperation,
        error_kind: io::ErrorKind,
        message: String,
    },
    CommandFailed {
        exit_code: Option<i32>,
    },
    MissingOutput,
    TemporaryDirectoryExhausted,
}

/// Complete system-tool failure, including the exact argv and stderr bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64ToolError {
    stage: X86_64ToolStage,
    kind: X86_64ToolErrorKind,
    command: Vec<OsString>,
    stderr: Vec<u8>,
    output: PathBuf,
}

impl X86_64ToolError {
    #[must_use]
    pub const fn stage(&self) -> X86_64ToolStage {
        self.stage
    }

    #[must_use]
    pub const fn kind(&self) -> &X86_64ToolErrorKind {
        &self.kind
    }

    #[must_use]
    pub fn command(&self) -> &[OsString] {
        &self.command
    }

    #[must_use]
    pub fn stderr(&self) -> &[u8] {
        &self.stderr
    }

    #[must_use]
    pub fn output(&self) -> &Path {
        &self.output
    }
}

impl fmt::Display for X86_64ToolError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "x86_64 {:?} failed", self.stage)?;
        match &self.kind {
            X86_64ToolErrorKind::Io {
                operation,
                error_kind,
                message,
            } => write!(
                formatter,
                " during {operation:?}: {message} ({error_kind:?})"
            )?,
            X86_64ToolErrorKind::CommandFailed { exit_code } => match exit_code {
                Some(code) => write!(formatter, " with exit status {code}")?,
                None => formatter.write_str(" after termination by signal")?,
            },
            X86_64ToolErrorKind::MissingOutput => {
                formatter.write_str(" because the expected output was not created")?;
            }
            X86_64ToolErrorKind::TemporaryDirectoryExhausted => {
                formatter.write_str(" because no unique temporary directory could be created")?;
            }
        }
        if !self.command.is_empty() {
            formatter.write_str("; command:")?;
            for argument in &self.command {
                write!(formatter, " {:?}", argument)?;
            }
        }
        write!(formatter, "; output: {}", self.output.display())
    }
}

impl Error for X86_64ToolError {}

fn run_tool(
    stage: X86_64ToolStage,
    tool: &OsStr,
    arguments: Vec<OsString>,
    input: Option<&[u8]>,
    expected_output: &Path,
) -> Result<(), X86_64ToolError> {
    let command_line = std::iter::once(tool.to_owned())
        .chain(arguments.iter().cloned())
        .collect::<Vec<_>>();
    let mut command = Command::new(tool);
    command
        .args(&arguments)
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::null())
        .stderr(Stdio::piped());
    let mut child = command.spawn().map_err(|error| {
        io_error(
            stage,
            X86_64ToolOperation::Spawn,
            error,
            command_line.clone(),
            expected_output,
        )
    })?;

    let input_writer = if let Some(input) = input {
        let mut stdin = child.stdin.take().expect("piped stdin is available");
        let input = input.to_vec();
        Some(thread::spawn(move || stdin.write_all(&input)))
    } else {
        None
    };
    let output = child.wait_with_output();
    let input_error = input_writer.and_then(|writer| match writer.join() {
        Ok(result) => result.err(),
        Err(_) => Some(io::Error::other("tool stdin writer thread panicked")),
    });
    let output = output.map_err(|error| {
        io_error(
            stage,
            X86_64ToolOperation::Wait,
            error,
            command_line.clone(),
            expected_output,
        )
    })?;
    if !output.status.success() {
        return Err(X86_64ToolError {
            stage,
            kind: X86_64ToolErrorKind::CommandFailed {
                exit_code: output.status.code(),
            },
            command: command_line,
            stderr: output.stderr,
            output: expected_output.to_owned(),
        });
    }
    if let Some(error) = input_error {
        return Err(io_error(
            stage,
            X86_64ToolOperation::WriteToolInput,
            error,
            command_line,
            expected_output,
        ));
    }
    require_output_file(stage, command_line, expected_output)
}

fn require_output_file(
    stage: X86_64ToolStage,
    command: Vec<OsString>,
    output: &Path,
) -> Result<(), X86_64ToolError> {
    match fs::metadata(output) {
        Ok(metadata) if metadata.is_file() => Ok(()),
        Ok(_) => Err(X86_64ToolError {
            stage,
            kind: X86_64ToolErrorKind::MissingOutput,
            command,
            stderr: Vec::new(),
            output: output.to_owned(),
        }),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Err(X86_64ToolError {
            stage,
            kind: X86_64ToolErrorKind::MissingOutput,
            command,
            stderr: Vec::new(),
            output: output.to_owned(),
        }),
        Err(error) => Err(io_error(
            stage,
            X86_64ToolOperation::InspectOutput,
            error,
            command,
            output,
        )),
    }
}

fn io_error(
    stage: X86_64ToolStage,
    operation: X86_64ToolOperation,
    error: io::Error,
    command: Vec<OsString>,
    output: &Path,
) -> X86_64ToolError {
    X86_64ToolError {
        stage,
        kind: X86_64ToolErrorKind::Io {
            operation,
            error_kind: error.kind(),
            message: error.to_string(),
        },
        command,
        stderr: Vec::new(),
        output: output.to_owned(),
    }
}

struct TemporaryObject {
    directory: PathBuf,
    object: PathBuf,
}

impl TemporaryObject {
    fn create() -> Result<Self, X86_64ToolError> {
        let root = std::env::temp_dir();
        for _ in 0..128 {
            let nonce = TEMPORARY_NONCE.fetch_add(1, Ordering::Relaxed);
            let directory = root.join(format!("nera-native-{}-{nonce}", std::process::id()));
            match create_private_directory(&directory) {
                Ok(()) => {
                    return Ok(Self {
                        object: directory.join("program.o"),
                        directory,
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(io_error(
                        X86_64ToolStage::TemporaryObject,
                        X86_64ToolOperation::CreateTemporaryDirectory,
                        error,
                        Vec::new(),
                        &directory,
                    ));
                }
            }
        }
        Err(X86_64ToolError {
            stage: X86_64ToolStage::TemporaryObject,
            kind: X86_64ToolErrorKind::TemporaryDirectoryExhausted,
            command: Vec::new(),
            stderr: Vec::new(),
            output: root,
        })
    }

    fn object(&self) -> &Path {
        &self.object
    }
}

#[cfg(unix)]
fn create_private_directory(path: &Path) -> io::Result<()> {
    use std::os::unix::fs::DirBuilderExt;

    let mut builder = fs::DirBuilder::new();
    builder.mode(0o700).create(path)
}

#[cfg(not(unix))]
fn create_private_directory(path: &Path) -> io::Result<()> {
    fs::create_dir(path)
}

impl Drop for TemporaryObject {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.object);
        let _ = fs::remove_dir(&self.directory);
    }
}
