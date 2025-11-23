#!/bin/bash
set -e

# Valgrind helper script with common configurations
# Tests for memory leaks, invalid memory access, and undefined behavior

echo "=== Valgrind Memory Analysis ==="
echo ""

# Check if binary exists
BINARY="${1:-bin/moac}"
if [ ! -f "$BINARY" ]; then
    echo "Error: Binary not found: $BINARY"
    echo "Usage: $0 [binary] [args...]"
    echo "Example: $0 bin/moac"
    exit 1
fi

shift 2>/dev/null || true
ARGS="$@"

# Valgrind configuration
VALGRIND_OPTS="
    --leak-check=full
    --show-leak-kinds=all
    --track-origins=yes
    --verbose
    --log-file=valgrind-report.txt
    --suppressions=/dev/null
"

echo "Running: valgrind $BINARY $ARGS"
echo "Output will be written to: valgrind-report.txt"
echo ""

# Run valgrind
valgrind $VALGRIND_OPTS $BINARY $ARGS

echo ""
echo "=== Valgrind Complete ==="
echo "Report saved to: valgrind-report.txt"
echo ""
echo "Quick summary:"
grep -E "definitely lost|indirectly lost|possibly lost|still reachable|ERROR SUMMARY" valgrind-report.txt || echo "No leaks found"
