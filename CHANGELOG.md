# Changelog

All notable changes to the public Nera preview are documented here.

## Unreleased

- Changed `assert` to evaluate ordinary boolean expressions at runtime. A false
  condition reports an interpreter error or aborts a native executable.
- Removed the source-level static assertion entrypoint without adding a `prove`
  statement. Contracts, loop invariants, and internal Spec verification remain.
- Updated assertion tests, examples, and the public language reference.

## 0.0.1

- Added an experimental systems-language frontend with structs, enums, arrays,
  slices, control flow, modules, and bounded type/const generics.
- Added ownership, implicit borrow relationships, reborrowing, raw addresses,
  allocation, explicit release, partial initialization, and partial moves.
- Added fail-closed, path-sensitive memory-safety verification across functions,
  loops, branches, and recursive call groups.
- Added source-oriented diagnostics and deterministic verification reports.
- Added an interpreter and direct x86_64 Linux assembly, object, and executable
  output through system tools.
- Added deterministic regression and fuzz test suites.

This release does not provide a formally proved compiler or verified native
artifacts.
