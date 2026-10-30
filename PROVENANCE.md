# Source provenance

This standalone release repository was exported from Nera source commit:

```text
7e387d375411d86641d97d3f5da019eb48372ad5
```

The release has an independent Git history. It contains the Rust compiler,
tests, executable examples, licenses, and the public language reference.

The export intentionally excludes development plans, historical prototypes,
private tooling configuration, and generated build artifacts. Release-specific
changes provide version metadata, public documentation, and a documentation-free
release test gate.

## Subsequent source synchronization

The finite resource abstraction update was applied from source commit:

```text
44ea02238818fb2557310cd343a318949b1055a8
```

All changes under `src/`, `tests/`, `spec/`, and `tools/` in that commit are
included. The English public reference and release notes are adapted separately;
development plans and historical acceptance documents remain excluded. The
standalone release gate and release package metadata are preserved.

Validation on 2026-10-30: the standalone `cargo run -p xtask -- check-rust` gate
passed with 2,174 workspace tests (zero failures or ignored tests), 20,000
frontend fuzz iterations, 20,000 verifier fuzz iterations, strict Clippy and
Rustdoc, formatting, and VIR snapshots. The three-module arena was also checked
through the CLI (15 Closed summaries, 1,803 proven obligations, no explicit
trust entries) and returned 49 in the interpreter.
