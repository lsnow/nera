# Stage 1–8 examples

These small programs illustrate the implementation milestones using the **current
compiler**. They are not historical toolchain snapshots or a claim that every
planned feature in a stage is available. Each file is standalone.

| Stage | Example | What it demonstrates | Expected `verify` result |
| --- | --- | --- | --- |
| 1 — Memory model | [memory.nera](memory.nera) | Allocate, initialize, read, and free one cell. | `Checked` |
| 2 — Frontend | [frontend.nera](frontend.nera) | Comments, identifiers, literals, expressions, and source analysis. | `Checked` |
| 3 — Frozen frontend prototype | [core-subset.nera](core-subset.nera) | A straight-line program in the prototype's source subset. | `Checked` by the current verifier, **not** historical certification |
| 4 — Execution and native backend | [execution.nera](execution.nera) | Pointer byte offsets, two initialized cells, interpreter/native execution. | `Checked` |
| 5 — Resource verifier | [use-after-free.nera](use-after-free.nera) | Deliberately read an allocation after freeing it. | **`Unproved`, exit 1** |
| 6 — Structured data and control flow | [structured-data.nera](structured-data.nera) | Structs, arrays, enums, function calls, and pattern matching. | `Checked` |
| 7 — Ordinary safe code | [inferred-borrows.nera](inferred-borrows.nera) | A local mutable borrow, a returned shared slice, inferred dependencies, and last-use restoration. | `Checked` |
| 8 — Explicit proof annotations | [loop-contracts.nera](loop-contracts.nera) | Preconditions and invariants for a growing initialized prefix, plus a local liveness assertion. | `Checked` |

All seven positive examples return **42**. Stage 5 is an intentional negative
example, not a broken installation. Stage 1 illustrates the memory lifecycle,
not all faults in the model. Stages 1 and 3 originally involved Lean prototypes;
these commands neither run Lean nor certify those historical proofs. No Lean
installation is required. Stage 8 demonstrates the implemented 8.1–8.3 subset,
not future user-defined predicates or independent module proofs.

## Build and inspect

Run all commands from the repository root. Rust 1.88 or newer is required.

```sh
cargo build --bin nera
./target/debug/nera frontend examples/frontend.nera
```

`frontend` reports accepted source and compiler representations. It is useful
for inspecting stages 2–4, but frontend acceptance alone does not establish
memory safety: even the stage 5 negative example passes this command.

## Verify and interpret

```sh
./target/debug/nera verify examples/loop-contracts.nera
./target/debug/nera run examples/loop-contracts.nera
```

Expect `Checked` from `verify` and `return: 42` from `run`. Substitute any positive
file from the table to try another stage. The interpreter command exits with 0
on successful execution; the program's returned value is printed, not used as
the command's exit status.

To inspect the negative example:

```sh
./target/debug/nera verify --explain examples/use-after-free.nera
printf 'verifier exit=%s\n' "$?"
```

Expect `Unproved`, failed safety conditions at the read after `free`, and exit
status 1. Do not build and execute this deliberately invalid source natively.

`run` and `build` are unverified execution paths; they do not first enforce a
successful `verify`. Assertions and invariants are erased, not runtime traps.
Verification is relative to the current supported model and trust boundary; it
is not a proof of compiler correctness, native code correctness, or termination.

## Build a native executable

On x86_64 Linux, install GNU `as` and a C compiler/linker capable of producing
PIE executables. No LLVM or Cranelift is required.

```sh
./target/debug/nera verify examples/execution.nera
./target/debug/nera build examples/execution.nera \
  --emit exe -o target/execution-example
./target/execution-example
printf 'native exit=%s\n' "$?"
```

Expect native exit status **42**, which is the program's result. A shell running
with `set -e` treats this nonzero status as failure; disable it for the execution
line or explicitly capture the status. The build still labels its artifact
unverified even after a separate successful verification.

## Check all examples

```sh
cargo test --test examples
```

This focused smoke test checks frontend acceptance for all eight files, their
documented verification outcomes, and the interpreter result for each positive
example. It does not run the full compiler suite, Lean, fuzzing, or native tests.
