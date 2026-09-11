# Changelog

All notable changes to the public Nera preview are documented here.

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
