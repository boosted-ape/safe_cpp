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

## Accepted subset

The initial policy is intentionally conservative. It is intended for small
programs whose state is owned by stack locals and ordinary C++ objects:

- Scalar values and simple records with ordinary fields.
- Local references whose referents stay initialized and alive for every use.
- Direct, non-virtual calls with definitions among the supplied source files.
- A limited two-phase borrow for mutable method receivers, allowing shared
  reads while the receiver is reserved and before the mutating call activates.
- Branches and loops represented by the current MIR lowerer.
- Trivial destruction and ordinary value copying/moving supported by the
  lowerer and verifier.

The checker rejects these features in user code:

- Raw pointers, pointer/reference/array function parameters or results,
  pointer/reference/array fields, member pointers, and address-taking.
- Global or static storage, arrays and subscripting, range-for, unions,
  `volatile`, mutable fields, virtual methods, function/class templates,
  lambdas, indirect calls, and casts that can forge aliases.
- Exceptions and catch handlers, manual `new`/`delete`, unsupported MIR
  statements or expressions, and calls without a body in the supplied files.
- A program with no unique `int main()` entry point.

The profile currently disallows pointer and reference parameters and returns,
so interprocedural aliasing can only arise from references to local objects
and implicit method receivers. The restrictions are policy checks in addition
to lowering checks. If a feature is not modeled, it must be rejected before a
clean result is reported.

## Rust model used as a reference

The implementation takes several structural ideas from Rust's MIR borrow
checker: control-flow graphs are the analysis unit, loan origins propagate
through assignments and calls, loans remain live through their reachable uses,
and accesses are compared with loans at MIR locations. See the Rust compiler
guide's [MIR dataflow](https://rustc-dev-guide.rust-lang.org/mir/dataflow.html),
[region inference](https://rustc-dev-guide.rust-lang.org/borrow-check/region-inference.html),
and [move and initialization analysis](https://rustc-dev-guide.rust-lang.org/borrow-check/moves-and-initialization.html).

This is not rustc's borrow checker. In particular, safe C++ object semantics,
drop flags, field-sensitive move paths, destructor effects, aliasing through
the ABI, and the full Rust region constraint system are not implemented. Local
definite initialization is tracked per MIR local, not per field; this can
reject valid field-by-field initialization. Borrow liveness is based on local
use/def facts, so it is a conservative prototype rather than a formal model
of all C++ lifetime rules. The strict profile rejects several major aliasing
features to keep those gaps outside its accepted subset.

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
