#!/bin/bash
set -e

# Code coverage analysis script
# Generates HTML coverage reports showing which code paths are executed

echo "=== Code Coverage Analysis ==="
echo ""

# Check if coverage binary exists
BINARY="${1:-bin/moac-coverage}"
if [ ! -f "$BINARY" ]; then
    echo "Error: Coverage binary not found: $BINARY"
    echo "Build it first with: make coverage"
    echo ""
    echo "Usage: $0 [binary] [args...]"
    echo "Example: $0 bin/moac-coverage"
    exit 1
fi

shift 2>/dev/null || true
ARGS="$@"

# Clean previous coverage data
echo "Cleaning previous coverage data..."
find . -name "*.gcda" -delete 2>/dev/null || true
rm -rf coverage-html 2>/dev/null || true

echo "Running coverage-instrumented binary: $BINARY $ARGS"
echo ""

# Run the coverage-instrumented binary
$BINARY $ARGS || {
    echo "Warning: Binary exited with non-zero status, but coverage data may still be useful"
}

echo ""
echo "Generating coverage reports..."
echo ""

# Generate coverage report with gcovr
if command -v gcovr &> /dev/null; then
    echo "Using gcovr for coverage report..."

    # Text summary (use llvm-cov for clang compatibility)
    gcovr -r . --exclude 'astonia_net/.*' --exclude 'bin/.*' --gcov-executable "llvm-cov gcov" --print-summary

    # Create output directory for HTML report
    mkdir -p coverage-html

    # HTML report
    gcovr -r . --exclude 'astonia_net/.*' --exclude 'bin/.*' --gcov-executable "llvm-cov gcov" --html --html-details -o coverage-html/index.html

    echo ""
    echo "=== Coverage Report Generated ==="
    echo "HTML report: coverage-html/index.html"
    echo "Open with: firefox coverage-html/index.html"
    echo ""
else
    echo "Warning: gcovr not found, using lcov instead..."

    # Generate coverage data with lcov
    lcov --capture --directory . --output-file coverage.info
    lcov --remove coverage.info '/usr/*' 'astonia_net/*' --output-file coverage-filtered.info

    # Generate HTML report
    genhtml coverage-filtered.info --output-directory coverage-html

    echo ""
    echo "=== Coverage Report Generated ==="
    echo "HTML report: coverage-html/index.html"
    echo "Open with: firefox coverage-html/index.html"
    echo ""
fi

# Show coverage summary
if [ -f coverage-html/index.html ]; then
    echo "✓ Coverage analysis complete!"
else
    echo "⚠ Coverage report generation may have failed"
fi
