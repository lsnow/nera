use std::ffi::OsStr;
use std::fs;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static NONCE: AtomicU64 = AtomicU64::new(0);
pub struct Fixture(pub PathBuf);
impl Fixture {
    pub fn new() -> Self {
        for _ in 0..128 {
            let path = std::env::temp_dir().join(format!(
                "nera-verify-cli-{}-{}",
                std::process::id(),
                NONCE.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("cannot create test directory: {e}"),
            }
        }
        panic!("cannot reserve test directory");
    }
    pub fn file(&self, name: impl AsRef<OsStr>, bytes: impl AsRef<[u8]>) -> PathBuf {
        let path = self.0.join(name.as_ref());
        fs::write(&path, bytes).unwrap();
        path
    }
    pub fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_nera"));
        command.current_dir(&self.0).stdin(Stdio::null());
        command
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Drain both pipes concurrently; explain output may exceed pipe capacity.
/// The deadline catches accidental execution of the divergent fixture.
pub fn run(command: &mut Command) -> Output {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let drain = |mut pipe: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            pipe.read_to_end(&mut bytes).unwrap();
            bytes
        })
    };
    let stdout = drain(Box::new(child.stdout.take().unwrap()));
    let stderr = drain(Box::new(child.stderr.take().unwrap()));
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut timed_out = false;
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            timed_out = true;
            child.kill().unwrap();
            break child.wait().unwrap();
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = Output {
        status,
        stdout: stdout.join().unwrap(),
        stderr: stderr.join().unwrap(),
    };
    assert!(!timed_out, "verify process exceeded deadline: {output:?}");
    output
}
