#!/bin/bash
set -e

# Script to run clang-tidy with proper compilation database
# This ensures clang-tidy knows about all includes, flags, and defines

echo "=== Clang-Tidy Runner ==="
echo ""

# Check if compile_commands.json exists
if [ ! -f "compile_commands.json" ]; then
    echo "No compile_commands.json found. Generating it..."
    echo "Running: make clean && bear -- make linux"
    make clean
    bear -- make linux
    echo ""
fi

# By default, uses .clang-tidy config file (conservative checks)
# Can override with CHECKS environment variable
if [ -n "$CHECKS" ]; then
    CHECKS_ARG="-checks=$CHECKS"
    echo "Using custom checks: $CHECKS"
else
    CHECKS_ARG=""
    echo "Using .clang-tidy config file"
fi

# Choose mode
MODE="${1:-check}"

case "$MODE" in
    check)
        echo "Running clang-tidy in check mode (no fixes)..."
        find src -type f -name "*.c" -print0 | \
            xargs -0 clang-tidy -p . $CHECKS_ARG
        ;;
    fix)
        echo "Running clang-tidy in fix mode..."
        find src -type f -name "*.c" -print0 | \
            xargs -0 clang-tidy -p . -fix-errors $CHECKS_ARG
        ;;
    regen)
        echo "Regenerating compile_commands.json..."
        make clean
        bear -- make linux
        echo "Done. Run '$0 check' or '$0 fix' to analyze code."
        ;;
    *)
        echo "Usage: $0 [check|fix|regen]"
        echo ""
        echo "  check - Run clang-tidy without fixing (default)"
        echo "  fix   - Run clang-tidy and apply fixes"
        echo "  regen - Regenerate compile_commands.json"
        echo ""
        echo "Environment variables:"
        echo "  CHECKS - Override check filters (default: use .clang-tidy config)"
        echo ""
        echo "Examples:"
        echo "  $0 check                    # Check using .clang-tidy config"
        echo "  $0 fix                      # Fix using .clang-tidy config"
        echo "  CHECKS='bugprone-*' $0 fix  # Fix only bugprone issues"
        exit 1
        ;;
esac

echo ""
echo "Done!"
