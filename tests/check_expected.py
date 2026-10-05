#!/usr/bin/env python3
"""Exercise the strict whole-program checker and its closed-world boundary."""

import pathlib
import subprocess
import sys
import tempfile


exe = pathlib.Path(sys.argv[1]).resolve()
root = pathlib.Path(sys.argv[2]).resolve()


def run(paths, cwd=root):
    return subprocess.run(
        [str(exe), *map(str, paths), "--", "-std=c++17"],
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


borrow_failure = run([root / "test_whole_program.cpp"])
assert borrow_failure.returncode != 0, borrow_failure.stdout
assert "BORROW ERROR in main" in borrow_failure.stdout, borrow_failure.stdout
assert "whole-program profile: FAIL" in borrow_failure.stdout, borrow_failure.stdout

two_phase = run([
    root / "examples/cmake-check/main.cpp",
    root / "examples/cmake-check/counter.cpp",
])
assert two_phase.returncode == 0, two_phase.stdout
assert "reserve_mut" in two_phase.stdout and "[two-phase reserve bb" in two_phase.stdout, two_phase.stdout
assert "whole-program profile: OK" in two_phase.stdout, two_phase.stdout

with tempfile.TemporaryDirectory(prefix="safe-cpp-whole-") as temp:
    temp = pathlib.Path(temp)
    lib = temp / "lib.cpp"
    main = temp / "main.cpp"
    lib.write_text("int twice(int x) { return x + x; }\n")
    main.write_text("int twice(int); int main() { return twice(2) - 4; }\n")
    accepted = run([main, lib], cwd=temp)
    assert accepted.returncode == 0 and "whole-program profile: OK" in accepted.stdout, accepted.stdout

    unresolved_source = temp / "unresolved.cpp"
    unresolved_source.write_text("int external(int); int main() { return external(1); }\n")
    unresolved = run([unresolved_source], cwd=temp)
    assert unresolved.returncode != 0 and "provide its definition" in unresolved.stdout, unresolved.stdout

    raw_source = temp / "raw.cpp"
    raw_source.write_text("int main() { int x = 0; int* p = &x; return *p; }\n")
    raw = run([raw_source], cwd=temp)
    assert raw.returncode != 0 and "forbids raw pointers" in raw.stdout, raw.stdout

print("whole-program acceptance/rejection tests passed")
