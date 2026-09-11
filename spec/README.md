# Conformance corpus

This directory contains machine-readable capability data and positive and
negative source programs used by the compiler, verifier, interpreter, native
backend, and integration tests.

The files under `cases/` are test fixtures, not tutorials. For introductory
examples, start with the repository README and `examples/demo/`.

Run the complete release gate with:

```sh
cargo run -p xtask -- check-rust
```
