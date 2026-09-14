# Nera Language Reference

Version: 0.0.1 preview

Status: experimental, implementation-defined where noted

This document describes the source language accepted by Nera 0.0.1. It is a
user-facing reference, not a compiler architecture document. Features that are
reserved for future versions are identified explicitly.

## 1. Language model

Nera is a systems programming language with explicit control over allocation,
ownership, borrowing, and raw addresses. A program can be parsed and executed
without being accepted as memory-safe. Static verification is a separate,
fail-closed operation.

The following commands have distinct meanings:

- `nera frontend` checks syntax, names, types, and supported source features.
- `nera verify` attempts to prove every generated memory-safety condition and
  supported local assertion.
- `nera run` executes the program with the interpreter and reports it as
  unverified.
- `nera build` emits assembly, an object file, or an executable and reports the
  artifact as unverified.

A `Checked` verification result means that all obligations were proven under
the reported capability profile and trust boundary. It is not a proof of the
compiler or native backend.

## 2. Source files

Source files use UTF-8. The current parser accepts ASCII identifiers. Identifiers
are case-sensitive and have this form:

```text
identifier = (ASCII letter | "_") (ASCII letter | digit | "_")* ;
```

The single underscore `_` is a wildcard or discard token, not an identifier.

A source file may declare one module, followed by imports and items:

```nera
module app;

use math::sum;

pub fn main() -> u64 {
    return sum(20, 22);
}
```

The module declaration is optional for a single-file program. In a multi-file
program, files are supplied explicitly with `--module NAME=PATH`. Imports name
one item; wildcard and grouped imports are not supported.

Only functions, structs, and enums are source items in this preview. Prefix an
item with `pub` to make it available to another supplied module.

## 3. Whitespace and comments

Spaces, tabs, LF, and CRLF separate tokens but do not end statements or define
blocks. Blocks always use braces, and simple statements always end with a
semicolon.

```nera
// line comment

/* block comment */

/* block comments may be
   /* nested */
*/
```

An unterminated block comment is an error.

## 4. Names and reserved words

The following words are reserved and cannot be used as identifiers:

```text
as assert break const continue decreases else enum ensures exists extern false
fn for forall ghost if in invariant let match module move mut null proof ptr pub
raw reads region requires result return self spawn static struct theorem true
trusted type use where while writes
```

Some reserved words do not yet have an accepted source construct. Reserving them
prevents future language additions from changing tokenization.

## 5. Literals

The accepted value literals are unsigned integer literals and booleans:

```nera
0
42
1_000
0xff
0o755
0b1010
42u64
4usize
true
false
```

Digit separators must occur between digits. Decimal literals other than zero do
not begin with `0`.

The lexer recognizes floating-point, character, byte, and string literal forms,
but they are not accepted as program expressions in version 0.0.1.

## 6. Types

### 6.1 Scalar and unit types

The accepted scalar source types are:

```text
u64
usize
bool
```

The unit type is written `()`.

### 6.2 Tuples, arrays, and slices

```nera
(u64, bool)      // tuple
(u64,)           // one-element tuple
[u64; 4]         // fixed-size array
[u64]            // slice type; used behind a reference
```

Array lengths are unsuffixed constants or checked additions of constant
parameters and literals.

### 6.3 References

```nera
&u64
&mut u64
&[u64]
&mut [u64]
```

`&T` is a shared reference and `&mut T` is an exclusive reference. Named
lifetime parameters are intentionally absent from ordinary Nera source. The
compiler infers which input borrow or local storage a reference depends on.

### 6.4 Owning and raw pointers

```nera
Own<u64>
ptr<u64>
```

`Own<u64>` carries ownership of an allocation and is move-only. `ptr<u64>` is a
non-owning raw pointer. Pointer element types are limited to `u64` in this
preview.

### 6.5 Named and generic types

A struct or enum name introduces a nominal type. Type and const arguments use
angle brackets:

```nera
Buffer<u64, 4>
```

## 7. Structs and enums

Struct fields are comma-terminated:

```nera
struct Pair {
    left: u64,
    right: u64,
}

fn make_pair() -> Pair {
    return Pair { left: 20, right: 22 };
}
```

Enums support unit, tuple, and named-field variants:

```nera
enum Message {
    Empty,
    Number(u64),
    Pair { left: u64, right: u64, },
}
```

Generic declarations may bind types and `usize` constants:

```nera
struct Buffer<T, const N: usize> {
    values: [T; N],
}
```

Trait bounds, default arguments, and named lifetime binders are not supported.

## 8. Functions

Functions use `fn`, typed parameters, an optional return type, and a braced
body:

```nera
fn add(left: u64, right: u64) -> u64 {
    return left + right;
}

fn do_nothing() {
    return;
}
```

Generic functions use type and const parameters:

```nera
fn repeat<T, const N: usize>(value: T) -> [T; N] {
    return [value; N];
}
```

Version 0.0.1 checks concrete generic instances reachable from the selected
entry point. It does not claim validity for every possible substitution.

Calls are direct and may include explicit generic arguments:

```nera
let pair = add(20, 22);
let values = repeat<u64, 4>(7);
```

Methods, closures, function pointers, overloads, and traits are not supported.

## 9. Bindings and assignment

Immutable and mutable locals are declared with `let`:

```nera
let answer = 42;
let mut count: u64 = 0;
count = count + 1;
```

An uninitialized local must be mutable and must have an explicit type:

```nera
let mut pending: u64;
pending = 42;
return pending;
```

Reading `pending` before the assignment is rejected by verification. Structs,
tuples, arrays, and enums may be initialized or moved by component when the
remaining component state is unambiguous.

Assignments target places such as locals, fields, tuple positions, indexed
elements, and dereferenced pointers:

```nera
pair.left = 20;
values[1] = 22;
*pointer = 42;
```

## 10. Expressions

Version 0.0.1 accepts the following expression families:

- integer and boolean literals;
- local names and place expressions;
- tuple, array, struct, and enum construction;
- direct calls and explicit generic calls;
- dereference with `*name`;
- shared, mutable, and raw address expressions;
- addition;
- one comparison using `==`, `!=`, `<`, `<=`, `>`, or `>=`.

Examples:

```nera
let tuple = (20, true);
let values = [10, 20, 30, 40];
let repeated = [7; 4];
let total = values[0] + values[1];
let in_range = index < 4;
```

Comparisons do not chain. Subtraction, multiplication, division, logical
operators, casts, and general unary operators are reserved but not accepted as
source expressions in this preview.

## 11. Places and projections

A place denotes storage rather than merely a computed value:

```text
name
place.field
place.0
place[index]
place[start..end]
*name
```

Field and tuple projections select a fixed component. Index and range
projections use a runtime value. Slice ranges are half-open: `start..end`
contains `start` and excludes `end`.

Every index or range access must be proven inside the storage from which it was
derived. Empty one-past-the-end slices are allowed; one-past-the-end element
access is not.

## 12. Borrowing

Create shared and exclusive references with `&` and `&mut`:

```nera
let shared = &value;
let exclusive = &mut value;
let field = &pair.left;
let middle = &values[1..3];
```

Shared borrows may coexist when they refer to compatible storage. An exclusive
borrow prevents conflicting access for as long as that borrow remains live.
The compiler determines a borrow's last relevant use and restores access to the
parent storage afterward.

Reborrowing is expressed with the same syntax:

```nera
let first = &mut value;
let second = &mut *first;
*second = 42;
```

References returned from functions retain their dependency on input storage.
If a function may return one of several inputs, branch conditions are considered
when checking later uses.

## 13. Raw addresses

Raw address expressions do not create ordinary borrow exclusivity:

```nera
let read_address = &raw value;
let write_address = &raw mut value;
let field_address = &raw pair.left;
let pointee_address = &raw *pointer;
```

A raw address does not own storage and does not keep an allocation alive. Static
verification still tracks the address origin, allocation identity, bounds, and
access permissions. Converting an address into permission to access unrelated
or expired storage is rejected.

## 14. Allocation and release

Version 0.0.1 provides built-in allocation for `u64` elements:

```nera
let pointer = alloc<u64>(1);
*pointer = 42;
let value = *pointer;
free(pointer);
```

`alloc<u64>(N)` creates a fresh owning pointer. The count is currently an
integer literal. Newly allocated elements are uninitialized. `free(pointer)`
consumes an owning pointer; freeing it twice or using it afterward is rejected.

Owning values that remain live at the end of their scope are dropped. Moving an
owner transfers that responsibility to the destination or callee.

## 15. Control flow

### 15.1 Conditional statements

```nera
if condition {
    then_call();
} else if other {
    other_call();
} else {
    fallback();
}
```

Conditions have type `bool`. Each reachable branch is checked with the facts
established by its condition.

### 15.2 While loops

```nera
while index < end {
    index = index + 1;
}
```

Loop checking must reach a stable safe state within the configured analysis
limits. If it cannot, verification fails with an unknown or unsupported result.

### 15.3 Range loops

```nera
for index in 0..4 {
    sum = sum + values[index];
}
```

Only half-open numeric ranges are supported. General iterator loops and
inclusive ranges are not supported.

### 15.4 Break and continue

`break;` and `continue;` are valid only inside `while` and `for` loops.

### 15.5 Match

`match` is a statement whose arms contain blocks and end with commas:

```nera
match message {
    Message::Empty => { return 0; },
    Message::Number(value) => { return value; },
    _ => { return 1; },
}
```

Patterns may be wildcards, bindings, integer or boolean literals, and enum
variants with tuple or named payloads. Match guards use `if` before `=>`.
Tuple and array destructuring patterns are not supported.

## 16. Moves, copies, and initialization

Scalar integers, booleans, shared references, and aggregates containing only
copyable fields can be copied. Owning pointers, mutable references, and
aggregates containing them are move-only.

After a move, the source cannot be read, freed, or moved again until its missing
component is initialized again where that operation is supported.

The verifier tracks initialization separately for fields and fixed aggregate
elements. Reading an uninitialized or moved component is rejected even if other
components are initialized.

## 17. Verification behavior

Verification covers memory safety and supported local assertions, not general
functional correctness. The current memory checks include:

- allocation liveness and single ownership;
- use-after-free and double-free prevention;
- initialized reads and valid stores;
- shared and exclusive borrow compatibility;
- reference escape and returned-reference dependencies;
- pointer origin and allocation identity;
- field, element, slice, and strided-range bounds;
- non-overlap where simultaneous mutable access requires it;
- consistency of resource state at control-flow joins and loops;
- memory effects that cross function calls, including recursive call groups
  within configured limits.

The verifier has three logical outcomes for an individual condition: proven,
refuted, or unknown. Only proven conditions contribute to a successful
`Checked` result. Unsupported source constructs and exceeded budgets fail
closed.

The language does not require explicit contracts for ordinary safe code in this
release. Local assertions and bounded function contracts are supported as
described below. Proof blocks remain reserved and unsupported.

### 17.1 Static local assertions

```nera
fn main() -> u64 {
    let mut value = 1;
    assert value == 1;
    value = 2;
    assert value < 4 && !(value == 3);
    let p = alloc<u64>(1);
    assert alive(p.region);
    *p = value;
    assert initialized(p, 0..1);
    free(p);
    return value;
}
```

`assert logical-expression;` creates a static condition at that statement.
It observes the values and memory state at that position, including preceding
assignments and releases. It must hold on every reachable branch represented
at that point. A successful assertion does not create permissions or become an
unchecked assumption for later statements.

Supported pure expressions use `bool`, `u64`, and 64-bit `usize` constants,
parameters, and available local values:

- parentheses and `!`;
- `&&` and `||`;
- `==`, `!=`, `<`, `<=`, `>`, and `>=`;
- checked `+`, `-`, and multiplication by a literal constant.

Precedence from strongest to weakest is `!`, `*`, `+ -`, comparisons,
`&&`, then `||`. Comparisons cannot be chained without parentheses.
Arithmetic operands must have the same type; a directly participating
unsuffixed integer literal may adopt the other operand's word type. General
contextual typing of compound constant expressions is not supported.
Logical arithmetic does not wrap. Overflow or an undefined expression cannot
establish a proof; boolean short-circuiting can avoid an unused operand.

The following standalone resource observations are also accepted:

| Expression | Meaning |
| --- | --- |
| `alive(p.region)` | The allocation observed through `p` is currently live. |
| `initialized(p)` | The first element at `p` is initialized. |
| `initialized(p, begin..end)` | The half-open element range relative to `p` is initialized. |

Here `p` is a local pointer, owner, or reference name. Initialization
observations currently support `bool` and `u64` elements. Element offsets
are checked when scaled to bytes; dynamic ranges require sufficient existing
facts to determine their initialization. Resource observations cannot yet be
combined with boolean operators. A user declaration shadowing one of these
builtin names is not interpreted as a logical builtin.

Assertions do not evaluate ordinary calls, allocate, borrow, or read fields or
pointer contents. For example, `assert *p == 42;` is unsupported. Some local
values that reside in addressable storage, or whose values were not retained
across a control-flow join, cannot yet be observed; the compiler rejects these
cases explicitly. Assertions do not extend a borrow's lifetime.

Assertions and contracts can occur in closed multi-file programs and concrete
generic instances. Loop invariants, `proof`/`ghost`, and source quantifiers
remain unsupported.

`verify` exits with status 0 for a checked program, 1 for an unproved program,
and 2 for rejected source. Failed conditions distinguish insufficient facts,
false predicates, resource conflicts, unsupported reasoning, and exhausted
budgets where applicable. The compiler and verifier remain part of the trust
boundary.

`run` and `build` erase assertions and remain unverified, even if an assertion
is false. A static assertion is not a runtime bounds check or trap.

### 17.2 Function contracts and frames

Clauses appear between a function signature and its body, each ending in `;`:

```nera
fn successor(value: u64) -> u64
requires value <= 41;
ensures result == old(value) + 1;
reads ();
writes ();
{
    return value + 1;
}
```

Every caller must establish `requires` for the actual arguments. The body must
establish `ensures` at every reachable normal return before callers may rely
on it. Repeated clauses are conjunctive. An entry function cannot assume an
arbitrary precondition without a caller. Allocation failure does not establish
a normal-return guarantee.

Pure clauses support `bool`, `u64`, and 64-bit `usize`. Parameter names in a
postcondition denote entry values; `result` denotes the returned value and
`old(parameter)` explicitly denotes its entry value. Parameters are immutable;
use a local variable for updates. Importing preconditions is limited to
supported boolean conditions and conjunctions of parameter/constant comparisons.
General disjunctive preconditions are not supported.

Bounded scalar memory observations include supported dereferences, fields and
indices, with `old` referring to the entry observation. `len` observes slice
length. These observations require real access authority and tracked contents;
they are not a general logical heap or unrestricted pointer-valued snapshot.

Resource clauses use `readable(p, begin..end)` or `writable(p, begin..end)`
over half-open element ranges. They check and transfer existing resources,
never manufacture permission. Conflicting exclusive claims cannot be combined.
Return resources must agree with the actual result and inferred borrow source;
contracts cannot authorize a dangling reference or upgrade a shared borrow.

`reads` and `writes` bound observable effects independently. Supported targets
include scalar dereferences and bounded parameter-relative ranges. `reads ();`
and `writes ();` explicitly declare empty footprints. Omitting a clause instead
uses inferred effects; it is not equivalent to an empty declaration. A frame
does not itself grant permission to access or free memory. Range checks and
old observations bind to entry state, not arbitrary post-call heap identities.

Recursive functions may use checked contracts within the bounded recursive
analysis. All affected bodies and recursive calls must pass before guarantees
are published. This is not a termination proof and does not support arbitrary
input/output relations. Modules still form one closed source set; contracts
are not standalone proof artifacts that can be imported without implementations.

The current arena example separates scalar capacity checks from exclusive
slice transfers. General heap-cursor postconditions, some newly returned
subslice combinations, and early restoration of a parent after a returned
borrow's last use remain unsupported or conservatively rejected. Such failures
must not be interpreted as a successful memory-safety proof.

Contracts, like assertions, are erased by `run` and `build`; native artifacts
remain unverified. A `Checked` result does not formally prove the compiler.

## 18. Compact grammar

This grammar is descriptive. Lexical precedence and diagnostic recovery are
implementation-defined in the preview.

```text
file          = [ module-decl ] { use-decl } { item } ;
module-decl   = "module" path ";" ;
use-decl      = "use" path ";" ;
path          = identifier { "::" identifier } ;

item          = [ "pub" ] ( struct | enum | function ) ;
struct        = "struct" identifier [ generics ]
                "{" { identifier ":" type "," } "}" ;
enum          = "enum" identifier [ generics ]
                "{" variant { variant } "}" ;
variant       = identifier
                [ "(" [ type { "," type } [ "," ] ] ")"
                | "{" { identifier ":" type "," } "}" ] "," ;

function      = "fn" identifier [ generics ]
                "(" [ parameter { "," parameter } [ "," ] ] ")"
                [ "->" type ] { contract-clause } block ;
contract-clause = ( "requires" | "ensures" ) contract-expression ";"
                | ( "reads" | "writes" ) footprint ";" ;
contract-expression = logical-expression | resource-claim ;
resource-claim = ( "readable" | "writable" ) "(" identifier ","
                 logical-expression ".." logical-expression ")" ;
footprint     = "(" ")" | place | place "[" logical-expression ".."
                logical-expression "]" ;
parameter     = identifier ":" type ;
generics      = "<" generic { "," generic } ">" ;
generic       = identifier | "const" identifier ":" "usize" ;

type          = "u64" | "usize" | "bool" | "()"
              | "&" [ "mut" ] type
              | "Own" "<" "u64" ">"
              | "ptr" "<" "u64" ">"
              | identifier [ "<" arguments ">" ]
              | "(" type "," [ type { "," type } [ "," ] ] ")"
              | "[" type ( "]" | ";" const-expr "]" ) ;

block         = "{" { statement } "}" ;
statement     = let-statement | assignment | call ";" | free-statement
              | return-statement | if-statement | while-statement
              | for-statement | match-statement | "break" ";"
              | "continue" ";" | assert-statement | block ;
assert-statement = "assert" logical-expression ";" ;
let-statement = "let" [ "mut" ] identifier [ ":" type ]
                [ "=" expression ] ";" ;
return-statement = "return" [ expression ] ";" ;
if-statement  = "if" expression block
                [ "else" ( if-statement | block ) ] ;
while-statement = "while" expression block ;
for-statement = "for" identifier "in" expression ".." expression block ;

expression    = primary [ comparison primary ] ;
primary       = atom { "+" atom } ;
comparison    = "==" | "!=" | "<" | "<=" | ">" | ">=" ;
logical-expression = pure-logical-expression | resource-observation ;
(* The bounded logical operators and observations are specified in 17.1. *)
```

## 19. Preview limits

The following are outside the version 0.0.1 accepted source language:

- named lifetime syntax;
- signed integers and floating-point expressions;
- general arithmetic and bitwise expressions;
- traits, methods, closures, and operator overloading;
- package discovery, independent compilation, and dynamic linking;
- concurrency, atomics, exceptions, and unwinding;
- FFI, inline assembly, MMIO, and device-memory semantics;
- general user-defined allocators and arbitrary pointer element types;
- a stable ABI or standard library;
- verified native executable artifacts;
- a formal proof of compiler correctness.

These limits are part of the preview contract: an implementation must reject an
unsupported construct rather than infer that it is safe.
