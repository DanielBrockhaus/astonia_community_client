#!/bin/bash
set -e

# CPU Profiling with perf (Linux performance counters)
# This is the fastest and most accurate profiler for Linux
# Finds which functions use the most CPU time

echo "=== CPU Profiling with perf ==="
echo ""

# Check if perf is available
if ! command -v perf &> /dev/null; then
    echo "Error: perf not found. Install with:"
    echo "  sudo apt-get install linux-tools-common linux-tools-generic"
    echo "  or: sudo pacman -S perf"
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

# Record performance data
echo "Recording performance data..."
echo "Press Ctrl+C in the application when you want to stop profiling"
echo ""

# Run perf record with:
# - Call graph recording (-g) for function call hierarchy
# - High frequency sampling (-F 997) to catch more detail
# - Record all events (not just the main thread)
sudo perf record -g -F 997 --call-graph dwarf -o perf.data -- $BINARY "${ARGS[@]}"

echo ""
echo "=== Profiling Complete ==="
echo ""

# Generate text report
echo "Top CPU-consuming functions:"
echo ""
sudo perf report --stdio -i perf.data -n --sort comm,dso,symbol | head -50

echo ""
echo "=== Analysis Tools ==="
echo ""
echo "1. Interactive TUI (terminal UI):"
echo "   sudo perf report -i perf.data"
echo ""
echo "2. Annotated source code:"
echo "   sudo perf annotate -i perf.data"
echo ""
echo "3. Call graph (flamegraph - requires flamegraph.pl):"
echo "   sudo perf script -i perf.data | flamegraph.pl > perf-flamegraph.svg"
echo ""
echo "4. Export for visualization:"
echo "   sudo perf script -i perf.data > perf.script"
echo ""
echo "Performance data saved to: perf.data"
echo ""
echo "=== What to Look For ==="
echo "- Functions with high 'overhead %' are CPU bottlenecks"
echo "- Look for unexpected functions consuming CPU"
echo "- Check if rendering/network/logic is balanced"
echo "- Optimize the top 3-5 functions for biggest impact"
