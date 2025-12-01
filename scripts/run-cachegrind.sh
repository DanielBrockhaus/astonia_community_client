#!/bin/bash
set -e

# Cache Profiling with Valgrind Cachegrind
# Simulates CPU cache behavior to find cache misses
# Cache misses are a major cause of slowdowns in modern CPUs

echo "=== Cache Profiling with Cachegrind ==="
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
    exit 1
fi

shift 2>/dev/null || true
ARGS=("$@")

echo "Binary: $BINARY"
echo "Args: $ARGS"
echo ""
echo "Cachegrind will simulate L1/L2/L3 cache behavior"
echo ""

# Clean old results
rm -f cachegrind.out.*

# Run cachegrind
echo "Running cachegrind profiler..."
valgrind --tool=cachegrind \
    --cachegrind-out-file=cachegrind.out \
    --cache-sim=yes \
    --branch-sim=yes \
    $BINARY "${ARGS[@]}"

echo ""
echo "=== Profiling Complete ==="
echo ""

# Find the output file
OUTFILE=$(ls -t cachegrind.out.* 2>/dev/null | head -1)
if [ -z "$OUTFILE" ]; then
    OUTFILE="cachegrind.out"
fi

# Generate text report
echo "Cache statistics:"
echo ""
cg_annotate --auto=yes $OUTFILE | head -150

echo ""
echo "=== Analysis Tools ==="
echo ""
echo "1. Interactive visualization (KCachegrind - GUI required):"
echo "   kcachegrind $OUTFILE"
echo ""
echo "2. Detailed text report:"
echo "   cg_annotate --auto=yes $OUTFILE"
echo ""
echo "3. Per-file analysis:"
echo "   cg_annotate $OUTFILE src/gui/gui.c"
echo ""
echo "Profile data saved to: $OUTFILE"
echo ""
echo "=== What to Look For ==="
echo "- D1mr/D1mw: L1 data cache misses (read/write)"
echo "- I1mr: L1 instruction cache misses"
echo "- LLr/LLw: Last-level (L3) cache misses - very expensive!"
echo "- High cache miss rates indicate poor data locality"
echo "- Look for structs with poor layout or random access patterns"
echo "- Consider data structure reorganization or prefetching"
