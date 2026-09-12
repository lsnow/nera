# Nera

Nera is an experimental systems programming language that combines low-level
memory control with compile-time memory-safety verification. Its syntax is
deliberately familiar to C and Rust programmers, while ordinary code does not
expose named lifetime parameters.

Version 0.0.1 is a technology preview. It is useful for exploring the language,
the verifier, and the direct x86_64 Linux backend, but it is not production-ready.

## Highlights

- Ownership, moves, shared borrows, mutable borrows, and reborrows.
- Inferred borrow relationships; source code uses `&T` and `&mut T` without
  spelling lifetime names.
- Path-sensitive checks across branches and loops.
- Detection of use-after-free, double free, conflicting aliases,
  uninitialized access, out-of-bounds access, and invalid pointer use.
- Partial initialization and partial moves for structs, tuples, arrays, and
  enums.
- Fixed arrays, slices, structs, enums, pattern matching, and bounded
  type/const generics.
- Closed multi-file programs with explicit module mappings.
- An interpreter and a direct x86_64 Linux backend using the system assembler
  and linker.

## How verification works

The compiler first parses and type-checks the complete program. The verifier
then tracks ownership, active borrows, initialization, allocation identity,
pointer origin, and accessed memory ranges along every reachable control-flow
path. Numeric facts are used to prove bounds and non-overlap. Function results
and memory effects are summarized so callers can be checked without treating a
function call as an opaque operation.

Every memory operation creates a safety condition. Verification succeeds only
when all conditions are proven. A contradiction, an unsupported construct, an
analysis limit, or an unknown result is rejected rather than silently accepted.

`nera verify` reports a result relative to the compiler's stated capability
profile and trust boundary. The compiler and native backend are not formally
proved, and native executables are currently reported as **unverified**.

## Examples

### Ownership and explicit allocation

```nera
fn main() -> u64 {
    let value = alloc<u64>(1);
    *value = 42;
    let loaded = *value;
    free(value);
    return loaded;
}
```

The owning pointer is consumed by `free`. Reading it afterward would be
rejected as a use-after-free.

### Borrow inference

```nera
fn choose(flag: bool, left: &u64, right: &u64) -> &u64 {
    if flag {
        return left;
    } else {
        return right;
    }
}
```

The returned reference is tied to the selected input automatically. No named
lifetime syntax is required.

### Arrays, slices, and checked indexing

```nera
fn main() -> u64 {
    let values = [10, 20, 30, 40];
    let view = &values[1..3];
    return view[0] + view[1];
}
```

Verification proves that both the slice range and subsequent indexes remain
inside the original array.

### Enums and pattern matching

```nera
enum Message {
    Empty,
    Number(u64),
}

fn main() -> u64 {
    let message = Message::Number(42);
    match message {
        Message::Empty => { return 0; },
        Message::Number(value) => { return value; },
    }
}
```

More complete examples are available in
[`examples/demo`](examples/demo) and [`spec/cases`](spec/cases).

## Requirements

- x86_64 Linux.
- Rust 1.88 or newer.
- GNU `as` and a C compiler capable of linking PIE executables for native
  output.

No Lean installation, LLVM, or Cranelift is required.

## Build

```sh
cargo build --release --bin nera
./target/release/nera --version
```

Expected output:

```text
nera 0.0.1
```

## Verify and run the demo

```sh
./target/release/nera verify \
  --module app=examples/demo/app.nera \
  --module values=examples/demo/values.nera \
  --module borrow=examples/demo/borrow.nera \
  --module ownership=examples/demo/ownership.nera \
  --entry app::main

./target/release/nera run \
  --module app=examples/demo/app.nera \
  --module values=examples/demo/values.nera \
  --module borrow=examples/demo/borrow.nera \
  --module ownership=examples/demo/ownership.nera \
  --entry app::main
```

Verification should report `Checked`; execution should report `return: 42`.

To build a native executable:

```sh
./target/release/nera build \
  --module app=examples/demo/app.nera \
  --module values=examples/demo/values.nera \
  --module borrow=examples/demo/borrow.nera \
  --module ownership=examples/demo/ownership.nera \
  --entry app::main \
  --emit exe -o nera-demo

./nera-demo
printf 'exit=%s\n' "$?"
```

The expected exit status is 42.

## Test

Run the Rust test suite:

```sh
cargo test --workspace
```

Run the complete release gate, including formatting, tests, deterministic
frontend and verifier fuzzing, Clippy, documentation checks, native differential
tests, and checked-in snapshot validation:

```sh
cargo run -p xtask -- check-rust
```

The complete gate requires x86_64 Linux.

## Command-line interface

```text
nera frontend <SOURCE>
nera verify [--explain] <SOURCE>
nera run <SOURCE>
nera build --emit <asm|obj|exe> <SOURCE> -o <OUTPUT>
nera <frontend|verify|run|build> --module NAME=PATH ... --entry MODULE::FUNCTION
```

`frontend` checks that a source program is accepted and type-correct; it is not
a memory-safety verdict. `verify` performs static verification without executing
the program. `run` uses the interpreter, and `build` emits native artifacts.

## Current limitations

- Only `u64`, `usize`, and `bool` are available as scalar source types.
- Raw and owning pointer allocation is currently limited to `u64` elements.
- Arithmetic is intentionally small: addition and comparisons are supported.
- Modules form one closed source set; package discovery and separate linking are
  not implemented.
- Generic code is checked through concrete instances; traits are not available.
- Concurrency, exception unwinding, FFI, MMIO, floating-point expressions, and
  general-purpose optimization are not implemented.
- The compiler, verifier, interpreter, and backend are not formally proved.

The accepted source language is documented in the
[`Nera Language Reference`](docs/language-spec.md).

## License

Nera is available under the MIT License. See [`LICENSE`](LICENSE).
