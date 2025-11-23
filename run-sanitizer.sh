#!/bin/bash
set -e

# AddressSanitizer/UBSan runner script
# Detects memory errors, leaks, and undefined behavior at runtime
# Much faster than Valgrind with similar capabilities

echo "=== AddressSanitizer/UBSan Runner ==="
echo ""

# Check if sanitizer binary exists
BINARY="${1:-bin/moac-sanitizer}"
if [ ! -f "$BINARY" ]; then
    echo "Error: Sanitizer binary not found: $BINARY"
    echo "Build it first with: make sanitizer"
    echo ""
    echo "Usage: $0 [binary] [args...]"
    echo "Example: $0 bin/moac-sanitizer"
    exit 1
fi

shift 2>/dev/null || true
ARGS="$@"

# Configure sanitizer options
export ASAN_OPTIONS="
    detect_leaks=1:\
    check_initialization_order=1:\
    detect_stack_use_after_return=1:\
    strict_init_order=1:\
    verbosity=1:\
    log_path=asan-report.txt
"

export UBSAN_OPTIONS="
    print_stacktrace=1:\
    log_path=ubsan-report.txt
"

echo "Running: $BINARY $ARGS"
echo "AddressSanitizer output: asan-report.txt.*"
echo "UBSan output: ubsan-report.txt.*"
echo ""

# Run the sanitizer-instrumented binary
$BINARY $ARGS

echo ""
echo "=== Sanitizer Run Complete ==="
echo ""

# Show summary if reports exist
if ls asan-report.txt.* 1> /dev/null 2>&1; then
    echo "AddressSanitizer detected issues:"
    cat asan-report.txt.*
else
    echo "✓ No AddressSanitizer issues detected"
fi

if ls ubsan-report.txt.* 1> /dev/null 2>&1; then
    echo ""
    echo "UBSan detected issues:"
    cat ubsan-report.txt.*
else
    echo "✓ No UBSan issues detected"
fi
