#!/usr/bin/env python3
# cppsh's tests without lit: each RUN line of clang/test/Interpreter/cppsh/*.cpp
# run through bash, %s the test, %t a scratch path, cppsh and FileCheck the
# build's. For a build configured without clang's tests (no lit site config).
#
#   clang/tools/cppsh/utils/run-tests.py [BUILD_DIR] [TEST...]
import concurrent.futures
import glob
import os
import shutil
import subprocess
import sys
import tempfile
import time

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, "..", "..", "..", ".."))
args = sys.argv[1:]
build = os.path.abspath(args.pop(0)) if args and os.path.isdir(args[0]) else os.path.join(root, "build")
tests = args or sorted(glob.glob(os.path.join(root, "clang", "test", "Interpreter", "cppsh", "*.cpp")))
cppsh = os.path.join(build, "bin", "cppsh")
filecheck = os.path.join(build, "bin", "FileCheck")
for tool in (cppsh, filecheck):
    if not os.path.exists(tool):
        sys.exit(f"missing {tool} (ninja -C {build} {os.path.basename(tool)})")

def run_one(test):
    """One test's RUN lines, in order: (passed, what it printed where not, seconds)."""
    started = time.monotonic()
    test = os.path.abspath(test)
    runs, line = [], ""
    for text in open(test):
        if "RUN:" not in text:
            continue
        part = text.split("RUN:", 1)[1].strip()
        if part.endswith("\\"):
            line += part[:-1] + " "
            continue
        runs.append(line + part)
        line = ""
    scratch = tempfile.mkdtemp(prefix="cppsh-test-")
    try:
        for run in runs:
            cmd = (run.replace("%t", os.path.join(scratch, "t")).replace("%s", test)
                      .replace("FileCheck", filecheck))
            # `not cppsh ...`: a script that fails on purpose -- only the last
            # command of a pipe counts here, as bash has it without pipefail.
            cmd = " ".join(cppsh if word == "cppsh" else word
                           for word in cmd.split(" ") if word != "not")
            result = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True)
            if result.returncode != 0:
                return False, f"  $ {run}\n{result.stdout}{result.stderr}", time.monotonic() - started
        return True, "", time.monotonic() - started
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


# The tests at once, each its own cppsh processes: a core each.
failed = []
jobs = int(os.environ.get("CPPSH_TEST_JOBS", os.cpu_count() or 1))
with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
    for test, (ok, why, seconds) in zip(tests, pool.map(run_one, tests)):
        print(f"{'PASS' if ok else 'FAIL'} {os.path.basename(test)} ({seconds:.2f} s)")
        if not ok:
            print(why)
            failed.append(test)
print(f"\n{len(tests) - len(failed)} passed, {len(failed)} failed")
sys.exit(1 if failed else 0)
