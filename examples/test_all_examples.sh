#!/bin/bash

set -e

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

# Change to project root for cargo commands
cd "$PROJECT_ROOT"

# Find all .clem files in the examples directory
for clem_file in "$SCRIPT_DIR"/*.clem; do
    # Skip if no .clem files found
    if [ ! -f "$clem_file" ]; then
        echo "No .clem files found in examples directory"
        exit 1
    fi

    # Extract filename without extension
    basename_file=$(basename "$clem_file" .clem)
    expected_output_file="$SCRIPT_DIR/$basename_file.output"

    # Check if corresponding .output file exists
    if [ ! -f "$expected_output_file" ]; then
        echo -e "${YELLOW}WARNING:${NC} No expected output file found for $basename_file.clem (expected: $basename_file.output)"
        continue
    fi

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    echo -n "Testing $basename_file.clem... "

    # Run the .clem file and capture output, filtering out cargo build messages
    if actual_output=$(cargo run -- run -p "examples/$basename_file.clem" 2>/dev/null); then
        # Trim trailing whitespace from both outputs
        actual_output=$(echo "$actual_output" | sed 's/[[:space:]]*$//')
        expected_output=$(cat "$expected_output_file" | sed 's/[[:space:]]*$//')

        # Compare with expected output
        if [ "$actual_output" = "$expected_output" ]; then
            echo -e "${GREEN}PASS${NC}"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            echo -e "${RED}FAIL${NC}"
            echo "  Expected output:"
            echo "$expected_output" | sed 's/^/    /'
            echo "  Actual output:"
            echo "$actual_output" | sed 's/^/    /'
            echo
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    else
        echo -e "${RED}FAIL (execution error)${NC}"
        echo "  Error running cargo command"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
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
