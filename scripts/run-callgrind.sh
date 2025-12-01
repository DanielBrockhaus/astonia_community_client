#!/bin/bash
set -e

# CPU Profiling with Valgrind Callgrind
# Slower than perf but works on all platforms and gives instruction counts
# Great for finding exactly where CPU time is spent

echo "=== CPU Profiling with Callgrind ==="
echo ""

# Check if valgrind is available
if ! command -v valgrind &> /dev/null; then
    echo "Error: valgrind not found. Install it first."
    exit 1
fi

# Check if binary exists
BINARY="${1:-bin/moac}"
if [ ! -f "$BINARY" ]; then
    echo "Error: Binary not found: $BINARY"
    echo ""
    echo "Usage: $0 [binary] [args...]"
    echo "Example: $0 bin/moac"
    echo ""
    echo "Tip: Build with debug symbols for better results:"
    echo "  make clean && make linux DEBUG=-g"
    exit 1
fi

shift 2>/dev/null || true
ARGS=("$@")

echo "Binary: $BINARY"
echo "Args: $ARGS"
echo ""
echo "WARNING: Callgrind slows down execution 10-50x"
echo "Run a short test scenario to get meaningful data"
echo ""

# Clean old results
rm -f callgrind.out.*

# Run callgrind
echo "Running callgrind profiler..."
valgrind --tool=callgrind \
    --callgrind-out-file=callgrind.out \
    --collect-jumps=yes \
    --collect-systime=yes \
    --cache-sim=yes \
    $BINARY "${ARGS[@]}"

echo ""
echo "=== Profiling Complete ==="
echo ""

# Find the output file
OUTFILE=$(ls -t callgrind.out.* 2>/dev/null | head -1)
if [ -z "$OUTFILE" ]; then
    OUTFILE="callgrind.out"
fi

# Generate text report
echo "Top CPU-consuming functions (by instruction count):"
echo ""
callgrind_annotate --auto=yes --threshold=99.9 $OUTFILE | head -100

echo ""
echo "=== Analysis Tools ==="
echo ""
echo "1. Interactive visualization (KCachegrind - GUI required):"
echo "   kcachegrind $OUTFILE"
echo ""
echo "2. Text report with source annotations:"
echo "   callgrind_annotate --auto=yes $OUTFILE"
echo ""
echo "3. Function-by-function analysis:"
echo "   callgrind_annotate $OUTFILE src/gui/gui.c"
echo ""
echo "Profile data saved to: $OUTFILE"
echo ""
echo "=== What to Look For ==="
echo "- 'Ir' column shows instruction count (higher = slower)"
echo "- Focus on functions with high Ir that you wrote"
echo "- Check for unexpected loops or repeated work"
echo "- Look at cache misses (Dr/Dw) for memory-bound code"
