# safe_cpp

`safe_cpp` is a Clang-based proof-of-concept C++ memory-safety checker. Its
default mode analyzes the supplied source files as one closed program and
rejects programs outside a deliberately small policy. A clean result means
that the checker accepted the represented program under this policy; it is
not a proof about omitted files, linked libraries, generated code, or arbitrary
C++ behavior.

## Build and run

```sh
cmake -S . -B build
cmake --build build -j2
./build/mir-builder main.cpp library.cpp -- -std=c++17
```

To use a Clang compilation database, give its build directory with `-p` and
list the translation units to check:

```sh
./build/mir-builder -p build main.cpp library.cpp
```

Use `./build/mir-builder --help` to see the Clang Tooling options. The checker
has no legacy mode or checker-specific summary flags.

Pass every implementation file that belongs to the program in the same
invocation. Clang compilation arguments follow `--`. Header definitions may
be seen from multiple translation units; MIR bodies are deduplicated by Clang
USR before whole-program analysis. The program must define exactly one
zero-argument `int main()`.

The strict whole-program profile is the default. It checks every lowered body
for MIR structure and local definite initialization, infers returned-loan
origins over the combined call graph, then checks loans using control-flow
dataflow and backward liveness. Any unsupported syntax, unresolved user call,
MIR failure, or borrow conflict makes the command fail. Unknown effects are
not accepted as warnings in this mode.

## Opt-in `safe_cpp` dialect

Put `#pragma safe_cpp` at the start of every analyzed translation unit to opt in
to the `safe_cpp` dialect. A mixed invocation, where only some translation
units carry the pragma, is rejected. Without the pragma, the existing strict
profile continues to reject reference parameters and results.

In the dialect, ordinary C++ reference parameters and results are represented
in MIR. The checker infers return origins from function bodies and propagates
them through calls. References to local objects may not escape through a
reference return. Record values and mutable references are consumed as moves;
scalar values and shared references remain copyable. Moves out of projected
fields are rejected until field-sensitive move paths are implemented.
Unreachable CFG blocks with statements are
rejected. Places accessed through an unresolved reference dereference are
treated as potentially aliasing any local, so this mode can conservatively
reject some valid C++ programs while preserving the affine aliasing rule.

## Accepted subset

The initial policy is intentionally conservative. It is intended for small
programs whose state is owned by stack locals and ordinary C++ objects:

- Scalar values and simple records with ordinary fields.
- Local references whose referents stay initialized and alive for every use.
- Direct, non-virtual calls with definitions among the supplied source files.
- A limited two-phase borrow for mutable method receivers, allowing shared
  reads while the receiver is reserved and before the mutating call activates.
- Branches and loops represented by the current MIR lowerer.
- Trivial destruction and body-defined nontrivial destructors for named
  locals, when their effects can be represented in MIR.

The checker rejects these features in user code:

- Raw pointers and array function parameters or results; reference parameters
  and results are available only under `#pragma safe_cpp`. Pointer/reference/
  array fields, member pointers, and address-taking remain unsupported.
- Global or static storage, arrays and subscripting, range-for, unions,
  `volatile`, mutable fields, virtual methods, function/class templates,
  lambdas, indirect calls, and casts that can forge aliases.
- Exceptions and catch handlers, manual `new`/`delete`, unsupported MIR
  statements or expressions, and calls without a body in the supplied files.
- A program with no unique `int main()` entry point.

Outside the opt-in dialect, the profile disallows pointer and reference
parameters and returns. Raw pointers remain disallowed in both modes. The
restrictions are policy checks in addition to lowering checks. If a feature is
not modeled, it must be rejected before a clean result is reported.

## Rust model used as a reference

The NLL draft represents reference locals and borrow expressions with region
variables. It seeds regions from MIR-point liveness, generates location-aware
outlives constraints for reference assignments, reborrows, calls, and returns,
and solves them by fixed-point propagation over points reachable within the
target region. Possible returned origins are inferred across the call graph;
when multiple reference parameters can reach a result, the checker keeps their
union. Functions infer per-parameter read/write effects through direct calls
to a fixed point. Destructor checking uses the same summaries, including
nested member destructors; a missing or indirect effect summary falls back to
a conservative deep write. Infinite `for (;;)` loops carry a false unwind
edge for analysis.

See the Rust compiler guide's [MIR dataflow](https://rustc-dev-guide.rust-lang.org/mir/dataflow.html),
[region inference](https://rustc-dev-guide.rust-lang.org/borrow-check/region-inference.html),
and [move and initialization analysis](https://rustc-dev-guide.rust-lang.org/borrow-check/moves-and-initialization.html).

This remains a draft for the project's supported C++ MIR subset, not a complete
Rust implementation. Rust's `may_dangle` type rules do not map directly to C++.
Nontrivial temporaries, effects through unsupported indirect/virtual calls,
every form of infinite-loop false edge, drop flags, and field-sensitive move
paths remain outside the modeled subset. Local definite initialization is tracked
per MIR local, so field-by-field initialization can be rejected. The strict
profile rejects major aliasing features to keep unmodeled C++ behavior out of
accepted programs.

## Supported invocation paths

There is one checker mode: strict whole-program analysis. For one source file:

```sh
./build/mir-builder main.cpp -- -std=c++17
```

For a program split across translation units, pass every implementation file
in the same invocation:

```sh
./build/mir-builder main.cpp ownership.cpp algorithms.cpp -- -std=c++17
```

The checker collects MIR bodies across those files, resolves direct user-code
calls against that combined set, deduplicates header-defined bodies by Clang
USR, and then runs the initialization verifier and borrow checker. Every
program must provide one zero-argument `int main()`. Clang flags and include
paths belong after `--`, for example:

```sh
./build/mir-builder main.cpp library.cpp -- -std=c++20 -Iinclude
```

### Headers and linked libraries

Definitions in included project headers are parsed as part of each translation
unit. Inline function bodies in those headers can be lowered and checked when
they fit the supported subset; repeated bodies are deduplicated by Clang USR.
The checker also examines user declarations from included headers, so an
unsupported declaration there can reject the program even if that declaration
is not called.

The checker does not inspect object files or libraries passed to a linker. A
call to a user function must resolve to a definition among the analyzed
translation units or visible, analyzable project-header definitions. Linking
an external library does not provide that definition to the checker, so such a
call is rejected as unresolved. System-library calls can also fail this
closed-world check. To analyze a library implementation, pass its source files
to `mir-builder` along with the program sources and ensure the whole set stays
within the accepted subset. Otherwise, that library boundary is not verified
by this tool.

The output always contains MIR for analyzed bodies when whole-program policy
checks permit analysis to continue. A borrow conflict prints `BORROW ERROR`
and exits nonzero. `whole-program profile: OK` means the represented program
passed this checker; `FAIL` means it did not. Policy or parsing failures can
stop analysis before MIR or borrow diagnostics are produced.

`test_whole_program.cpp` is a runnable negative example: it writes to a value
while a local reference to it is still live. Run it to see the borrow checker
reject the program:

```sh
./build/mir-builder test_whole_program.cpp -- -std=c++17
```

`test_nll.cpp`, `test.cpp`, and the summary sidecar examples use features the
strict profile rejects. They are not valid inputs to this whole-program mode.
There is no per-translation-unit or sidecar-summary CLI mode.

## Tests

```sh
ctest --test-dir build --output-on-failure
```

The suite exercises MIR invariants, a strict borrow-checker conflict,
cross-translation-unit calls, unresolved-call rejection, and raw-pointer policy
rejection.

## CMake sample integration

`examples/cmake-check` shows how to make the checker a required CMake build
step for a small accepted program. Configure it from the repository root with:

```sh
cmake -S examples/cmake-check -B build/cmake-check \
  -DSAFE_CPP_CHECKER="$PWD/build/mir-builder"
cmake --build build/cmake-check -j2
./build/cmake-check/sample
```

The sample uses two translation units and calls
`counter.push(counter.size())`. The MIR output shows `reserve_mut`, the shared
`size()` call, and then activation at `push()`. The checker must pass before
CMake compiles and links the executable. The normal C++ compiler still does
code generation; this is a checker integration example, not a replacement
compiler toolchain.
