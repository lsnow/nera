use nera::SourceFile;
use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};

pub const LIBRARY: &str = include_str!("../../spec/cases/modules/arena/arena.nera");
pub const FORWARD: &str = include_str!("../../spec/cases/modules/arena/forward.nera");
pub const APP: &str = include_str!("../../spec/cases/modules/arena/app.nera");

pub fn session(library: &str, forward: &str, app: &str) -> CompilerSession {
    session_entry(library, forward, app, "app::main")
}

pub fn session_entry(library: &str, forward: &str, app: &str, entry: &str) -> CompilerSession {
    let inputs = [("arena", library), ("forward", forward), ("app", app)]
        .into_iter()
        .map(|(name, text)| {
            SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
        })
        .collect();
    CompilerSession::modules(
        SourceDatabase::new(inputs).unwrap(),
        Default::default(),
        entry,
    )
    .unwrap()
}

// Two finite source constant instances, not language-level const generics.
// The executable reserve proof still receives arbitrary count and cursor.
pub fn instance(capacity: usize) -> (String, String, String) {
    assert!(matches!(capacity, 6 | 8));
    let library = LIBRARY
        .replace(";6]", &format!(";{capacity}]"))
        .replace("6usize", &format!("{capacity}usize"));
    let forward = FORWARD.replace("6usize", &format!("{capacity}usize"));
    let app = APP.replace("6usize", &format!("{capacity}usize")).replace(
        "fill(&mut *arena,5usize,30)",
        &format!("fill(&mut *arena,{}usize,30)", capacity - 1),
    );
    (library, forward, app)
}

pub const ENTRIES: [&str; 5] = [
    "app::main",
    "app::lifecycle",
    "app::empty",
    "app::exhaustion",
    "app::reset_reuse",
];
