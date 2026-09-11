use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use nera::backend::{
    X86_64_UNKNOWN_LINUX_GNU, X86_64SystemToolchain, X86_64ToolErrorKind, X86_64ToolOperation,
    X86_64ToolStage,
};
use nera::{FrontendStatus, SourceFile, analyze};

static TEST_NONCE: AtomicU64 = AtomicU64::new(0);
// Some overlay filesystems transiently reject concurrently created executable
// scripts with ETXTBSY. Serialization keeps this system-tool test deterministic.
static SCRIPT_TOOL_TEST: Mutex<()> = Mutex::new(());

#[test]
fn emitter_is_deterministic_and_covers_runtime_symbols() {
    let source = SourceFile::new(
        "memory.nera",
        include_bytes!("../spec/cases/vir/memory.nera"),
    );
    let frontend = analyze(&source);
    assert_eq!(frontend.status(), FrontendStatus::AcceptedProposal);
    let resolved = frontend
        .vir()
        .expect("accepted source has VIR")
        .resolve()
        .expect("the corpus has no unresolved calls");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("all VIR instructions are selectable");
    let assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("the compiler-owned machine plan is encodable");

    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .emit_assembly(&machine)
            .expect("emission is deterministic"),
        assembly
    );
    assert!(assembly.starts_with(
        ".intel_syntax noprefix\n.extern aligned_alloc\n.extern free\n.extern abort\n.text\n"
    ));
    assert!(assembly.contains(".Lnera_v0_fn_0:\n"));
    assert!(assembly.contains("call _nera_alloc_or_abort\n"));
    assert!(assembly.contains("call free@PLT\n"));
    assert!(assembly.contains("_nera_alloc_or_abort:\n"));
    assert!(assembly.contains("jc .Lnera_v0_alloc_or_abort_failure\n"));
    assert!(assembly.contains("call aligned_alloc@PLT\n"));
    assert!(assembly.contains("call abort@PLT\n    ud2\n"));
    assert!(assembly.contains(".globl main\n.type main, @function\nmain:\n"));
    assert!(assembly.ends_with(".section .note.GNU-stack,\"\",@progbits\n"));
    assert!(
        !assembly.contains("memory"),
        "user symbols are not emitted raw"
    );
}

#[test]
fn toolchain_preserves_argv_boundaries_and_builds_each_layer() {
    let _script_tool_guard = SCRIPT_TOOL_TEST
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let temporary = TestDirectory::create("tool success");
    let assembler = temporary.script(
        "fake assembler",
        r#"#!/bin/sh
set -eu
test "$1" = "--64"
test "$2" = "-o"
output=$3
test "$4" = "-"
test "$(cat)" = "assembly-payload"
printf object-payload > "$output"
"#,
    );
    let linker = temporary.script(
        "fake linker",
        r#"#!/bin/sh
set -eu
test "$1" = "-pie"
test "$2" = "-o"
output=$3
object=$4
test "$(cat "$object")" = "object-payload"
printf executable-payload > "$output"
"#,
    );
    let tools = X86_64SystemToolchain::new(assembler, linker);

    let assembly_output = temporary.path().join("artifact ; still one arg.s");
    tools
        .write_assembly("assembly-payload", &assembly_output)
        .expect("plain assembly output succeeds");
    assert_eq!(
        fs::read(&assembly_output).expect("assembly artifact exists"),
        b"assembly-payload"
    );

    let object_output = temporary.path().join("artifact ; still one arg.o");
    tools
        .assemble("assembly-payload", &object_output)
        .expect("fake assembler accepts exact argv");
    assert_eq!(
        fs::read(&object_output).expect("object artifact exists"),
        b"object-payload"
    );

    let executable_output = temporary.path().join("artifact ; still one arg");
    tools
        .build_executable("assembly-payload", &executable_output)
        .expect("fake assembler and linker accept exact argv");
    assert_eq!(
        fs::read(&executable_output).expect("executable artifact exists"),
        b"executable-payload"
    );
}

#[test]
fn tool_failures_preserve_stderr_and_detect_missing_output() {
    let _script_tool_guard = SCRIPT_TOOL_TEST
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let temporary = TestDirectory::create("tool failure");
    let failing = temporary.script(
        "failing assembler",
        r#"#!/bin/sh
cat >/dev/null
printf 'first diagnostic\nsecond diagnostic' >&2
exit 7
"#,
    );
    let unused_linker = temporary.script("unused linker", "#!/bin/sh\nexit 99\n");
    let tools = X86_64SystemToolchain::new(&failing, &unused_linker);
    let output = temporary.path().join("failure.o");
    let error = tools
        .assemble("invalid", &output)
        .expect_err("nonzero assembler exit must fail");
    assert_eq!(error.stage(), X86_64ToolStage::Assemble);
    assert_eq!(
        error.kind(),
        &X86_64ToolErrorKind::CommandFailed { exit_code: Some(7) }
    );
    assert_eq!(error.stderr(), b"first diagnostic\nsecond diagnostic");
    assert_eq!(error.command()[0], failing.as_os_str());
    assert!(error.to_string().contains("exit status 7"));

    let silent = temporary.script("silent assembler", "#!/bin/sh\ncat >/dev/null\nexit 0\n");
    let tools = X86_64SystemToolchain::new(&silent, &unused_linker);
    let missing = temporary.path().join("missing.o");
    let error = tools
        .assemble("valid-looking", &missing)
        .expect_err("success without output must fail");
    assert_eq!(error.kind(), &X86_64ToolErrorKind::MissingOutput);
    assert_eq!(error.output(), missing);

    let absent = temporary.path().join("assembler does not exist");
    let tools = X86_64SystemToolchain::new(&absent, &unused_linker);
    let error = tools
        .assemble("anything", &temporary.path().join("never-created.o"))
        .expect_err("a missing system tool must be diagnosed");
    assert!(matches!(
        error.kind(),
        X86_64ToolErrorKind::Io {
            operation: X86_64ToolOperation::Spawn,
            error_kind: std::io::ErrorKind::NotFound,
            ..
        }
    ));
}

#[test]
fn cli_builds_assembly_and_refuses_to_overwrite_the_source() {
    let temporary = TestDirectory::create("cli");
    let source = temporary.path().join("input.nera");
    fs::write(&source, include_bytes!("../spec/cases/vir/memory.nera"))
        .expect("test source can be written");
    let assembly = temporary.path().join("output.s");
    let output = Command::new(env!("CARGO_BIN_EXE_nera"))
        .arg("build")
        .arg("--emit")
        .arg("asm")
        .arg(&source)
        .arg("-o")
        .arg(&assembly)
        .output()
        .expect("nera CLI starts");
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("status: built (unverified)"));
    assert!(String::from_utf8_lossy(&output.stdout).contains("emit: asm"));
    assert!(
        fs::read_to_string(&assembly)
            .expect("assembly was written")
            .contains(".note.GNU-stack")
    );

    let original = fs::read(&source).expect("source still exists");
    let output = Command::new(env!("CARGO_BIN_EXE_nera"))
        .arg("build")
        .arg("--emit")
        .arg("asm")
        .arg(&source)
        .arg("-o")
        .arg(&source)
        .output()
        .expect("nera CLI starts");
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("same file"));
    assert_eq!(
        fs::read(&source).expect("source was not overwritten"),
        original
    );
}

struct TestDirectory {
    path: PathBuf,
}

impl TestDirectory {
    fn create(name: &str) -> Self {
        let root = std::env::temp_dir();
        for _ in 0..128 {
            let nonce = TEST_NONCE.fetch_add(1, Ordering::Relaxed);
            let path = root.join(format!(
                "nera-native-test-{}-{nonce}-{name}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self { path },
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("cannot create test directory: {error}"),
            }
        }
        panic!("cannot find a unique test directory")
    }

    fn path(&self) -> &Path {
        &self.path
    }

    #[cfg(unix)]
    fn script(&self, name: &str, contents: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;

        let path = self.path.join(name);
        fs::write(&path, contents).expect("test tool can be written");
        let mut permissions = fs::metadata(&path).expect("test tool exists").permissions();
        permissions.set_mode(0o700);
        fs::set_permissions(&path, permissions).expect("test tool can be made executable");
        // Overlay filesystems can retain a just-closed writable script for a
        // short interval and reject exec with ETXTBSY. The production tools
        // are stable executables; only this dynamically written test fixture
        // needs a small publication delay.
        std::thread::sleep(Duration::from_millis(10));
        path
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
