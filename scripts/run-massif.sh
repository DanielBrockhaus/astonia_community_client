#!/bin/bash
set -e

# Memory Profiling with Valgrind Massif
# Shows heap memory usage over time
# Finds memory leaks and excessive allocations

echo "=== Memory Profiling with Massif ==="
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
echo "Massif will track heap allocations and show memory usage over time"
echo ""

# Clean old results
rm -f massif.out.*

# Run massif
echo "Running massif memory profiler..."
valgrind --tool=massif \
    --massif-out-file=massif.out \
    --stacks=yes \
    --time-unit=ms \
    --detailed-freq=1 \
    --max-snapshots=100 \
    $BINARY "${ARGS[@]}"

echo ""
echo "=== Profiling Complete ==="
echo ""

# Find the output file
OUTFILE=$(ls -t massif.out.* 2>/dev/null | head -1)
if [ -z "$OUTFILE" ]; then
    OUTFILE="massif.out"
fi

# Generate text report
echo "Memory usage summary:"
echo ""
ms_print $OUTFILE | head -200

echo ""
echo "=== Analysis Tools ==="
echo ""
echo "1. Detailed text report:"
echo "   ms_print $OUTFILE"
echo ""
echo "2. Interactive visualization (massif-visualizer - GUI required):"
echo "   massif-visualizer $OUTFILE"
echo ""
echo "Profile data saved to: $OUTFILE"
echo ""
echo "=== What to Look For ==="
echo "- Peak memory usage - is it growing unbounded?"
echo "- Which functions allocate the most memory?"
echo "- Are there memory spikes? What causes them?"
echo "- Check for unnecessary allocations in loops"
echo "- Look for cached data that could be freed earlier"
