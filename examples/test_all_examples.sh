#!/bin/bash

# Snapshot-tests every examples/*.clem by compiling it to a native binary and
# running that binary directly (not via `clemento run`, which mixes cargo/clang
# noise into stderr and masks signal exits). For each example we validate:
#   - stdout  against  <name>.output   (required)
#   - stderr  against  <name>.stderr   (optional — checked only if present)
#   - exit    against  <name>.exit     (optional — defaults to 0)
# Compilation uses a *relative* path so source locations baked into the binary
# (e.g. `todo`/`panic` messages) are stable across machines.

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Get the directory of this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "Testing all .clem examples..."
echo "Project root: $PROJECT_ROOT"
echo "Examples directory: $SCRIPT_DIR"
echo

# Change to project root for cargo commands (and so relative paths resolve).
cd "$PROJECT_ROOT" || exit 1

tmp_out="$(mktemp)"
tmp_err="$(mktemp)"
# Always clean up temp files and any shared build artifacts on exit.
cleanup() {
    rm -f "$tmp_out" "$tmp_err"
    rm -f "$SCRIPT_DIR/clem_runtime.c" "$SCRIPT_DIR/clem.h"
}
trap cleanup EXIT

# Trim trailing whitespace from every line of a file; command substitution then
# strips trailing newlines, so comparisons are insensitive to both.
trim() { sed 's/[[:space:]]*$//' "$1"; }

# Find all .clem files in the examples directory
for clem_file in "$SCRIPT_DIR"/*.clem; do
    # Skip if no .clem files found
    if [ ! -f "$clem_file" ]; then
        echo "No .clem files found in examples directory"
        exit 1
    fi

    basename_file=$(basename "$clem_file" .clem)
    relative_path="examples/$basename_file.clem"
    binary="$SCRIPT_DIR/$basename_file"
    expected_stdout_file="$SCRIPT_DIR/$basename_file.output"
    expected_stderr_file="$SCRIPT_DIR/$basename_file.stderr"
    expected_exit_file="$SCRIPT_DIR/$basename_file.exit"

    # The .output (stdout) snapshot is the minimum required to test an example.
    if [ ! -f "$expected_stdout_file" ]; then
        echo -e "${YELLOW}WARNING:${NC} No expected output file found for $basename_file.clem (expected: $basename_file.output)"
        continue
    fi

    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    echo -n "Testing $basename_file.clem... "

    # Remove any stale artifacts, then compile fresh.
    rm -f "$binary" "$binary.ll"
    rm -rf "$binary.dSYM"
    if ! cargo run --quiet -- compile -p "$relative_path" -L "$PROJECT_ROOT" >/dev/null 2>&1; then
        echo -e "${RED}FAIL (compile error)${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        continue
    fi

    # Run the binary directly, capturing stdout, stderr, and the true exit code.
    "$binary" >"$tmp_out" 2>"$tmp_err"
    actual_exit=$?

    failures=""

    actual_stdout=$(trim "$tmp_out")
    expected_stdout=$(trim "$expected_stdout_file")
    if [ "$actual_stdout" != "$expected_stdout" ]; then
        failures+=$'\n'"  stdout mismatch:"$'\n'"    expected:"$'\n'"$(echo "$expected_stdout" | sed 's/^/      /')"$'\n'"    actual:"$'\n'"$(echo "$actual_stdout" | sed 's/^/      /')"
    fi

    if [ -f "$expected_stderr_file" ]; then
        actual_stderr=$(trim "$tmp_err")
        expected_stderr=$(trim "$expected_stderr_file")
        if [ "$actual_stderr" != "$expected_stderr" ]; then
            failures+=$'\n'"  stderr mismatch:"$'\n'"    expected:"$'\n'"$(echo "$expected_stderr" | sed 's/^/      /')"$'\n'"    actual:"$'\n'"$(echo "$actual_stderr" | sed 's/^/      /')"
        fi
    fi

    expected_exit=0
    if [ -f "$expected_exit_file" ]; then
        expected_exit=$(tr -d '[:space:]' < "$expected_exit_file")
    fi
    if [ "$actual_exit" != "$expected_exit" ]; then
        failures+=$'\n'"  exit code mismatch: expected $expected_exit, got $actual_exit"
    fi

    if [ -z "$failures" ]; then
        echo -e "${GREEN}PASS${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        echo -e "${RED}FAIL${NC}"
        echo "$failures"
        echo
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi

    # Clean per-example build artifacts.
    rm -f "$binary" "$binary.ll"
    rm -rf "$binary.dSYM"
done

echo
echo "Test Summary:"
echo "============="
echo "Total tests: $TOTAL_TESTS"
echo -e "Passed: ${GREEN}$PASSED_TESTS${NC}"
echo -e "Failed: ${RED}$FAILED_TESTS${NC}"

if [ $FAILED_TESTS -eq 0 ]; then
    echo -e "${GREEN}All tests passed!${NC}"
    exit 0
else
    echo -e "${RED}$FAILED_TESTS test(s) failed.${NC}"
    exit 1
fi
