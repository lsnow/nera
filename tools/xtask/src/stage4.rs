use std::error::Error;
use std::fs;
use std::path::Path;

use nera::{FrontendStatus, SourceFile, analyze};

struct CorpusEntry {
    source: &'static str,
    snapshot: &'static str,
}

const CORPUS: &[CorpusEntry] = &[
    CorpusEntry {
        source: "spec/cases/verify/native-address-model.nera",
        snapshot: "spec/cases/vir/native-address-model.vir",
    },
    CorpusEntry {
        source: "spec/cases/verify/provenance-flow.nera",
        snapshot: "spec/cases/vir/provenance-flow.vir",
    },
    CorpusEntry {
        source: "spec/cases/verify/pointer-comparison.nera",
        snapshot: "spec/cases/vir/pointer-comparison.vir",
    },
    CorpusEntry {
        source: "spec/cases/verify/pointer-domain.nera",
        snapshot: "spec/cases/vir/pointer-domain.vir",
    },
    CorpusEntry {
        source: "spec/cases/verify/raw-address.nera",
        snapshot: "spec/cases/vir/raw-address.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/memory.nera",
        snapshot: "spec/cases/vir/memory.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/unit.nera",
        snapshot: "spec/cases/vir/unit.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/uninitialized-read.nera",
        snapshot: "spec/cases/vir/uninitialized-read.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/out-of-bounds-access.nera",
        snapshot: "spec/cases/vir/out-of-bounds-access.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/pointer-offset-out-of-bounds.nera",
        snapshot: "spec/cases/vir/pointer-offset-out-of-bounds.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/misaligned-access.nera",
        snapshot: "spec/cases/vir/misaligned-access.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/double-free.nera",
        snapshot: "spec/cases/vir/double-free.vir",
    },
    CorpusEntry {
        source: "spec/cases/vir/allocation-failure.nera",
        snapshot: "spec/cases/vir/allocation-failure.vir",
    },
    CorpusEntry {
        source: "spec/cases/verify/uaf.nera",
        snapshot: "spec/cases/vir/uaf.vir",
    },
    CorpusEntry {
        source: "spec/cases/aggregate/surface.nera",
        snapshot: "spec/cases/aggregate/surface.vir",
    },
];

pub(crate) fn generate(root: &Path) -> Result<(), Box<dyn Error>> {
    for entry in CORPUS {
        let path = root.join(entry.snapshot);
        fs::write(&path, expected_snapshot(root, entry)?)?;
        println!("generated {}", path.display());
    }
    Ok(())
}

pub(crate) fn check(root: &Path) -> Result<(), Box<dyn Error>> {
    for entry in CORPUS {
        let snapshot_path = root.join(entry.snapshot);
        let actual = fs::read_to_string(&snapshot_path)?;
        let expected = expected_snapshot(root, entry)?;
        if actual != expected {
            return Err(format!(
                "{} does not match {}; run 'cargo run -p xtask -- generate-vir'",
                snapshot_path.display(),
                root.join(entry.source).display()
            )
            .into());
        }
    }
    println!("VIR corpus snapshots are current");
    Ok(())
}

fn expected_snapshot(root: &Path, entry: &CorpusEntry) -> Result<String, Box<dyn Error>> {
    let source_path = root.join(entry.source);
    let source = SourceFile::new(entry.source, fs::read(&source_path)?);
    let output = analyze(&source);
    if output.status() != FrontendStatus::AcceptedProposal {
        return Err(format!(
            "{} is not accepted by the Rust frontend: {:?}",
            source_path.display(),
            output.issues()
        )
        .into());
    }
    Ok(output
        .vir()
        .ok_or_else(|| format!("{} produced no validated VIR", source_path.display()))?
        .stable_dump())
}
