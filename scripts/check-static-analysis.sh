#!/bin/bash
set -e

# Static analysis script for C code
# Runs clang-tidy and cppcheck
# Used by both CI pipeline and local development
# Exit code 0 = no issues, 1 = issues found

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$PROJECT_ROOT"

echo "========================================"
echo "  Static Analysis"
echo "========================================"
echo ""

FAILED=0
LOG_DIR="build/logs"
mkdir -p "$LOG_DIR"

# ============================================================================
# clang-tidy Static Analysis
# ============================================================================
echo ">>> Running clang-tidy Static Analysis"

if ! command -v clang-tidy >/dev/null 2>&1; then
    echo "WARNING: clang-tidy not installed, skipping"
    echo "Install with: sudo apt-get install clang-tidy"
    echo ""
elif ! command -v bear >/dev/null 2>&1; then
    echo "WARNING: bear not installed, skipping clang-tidy"
    echo "Install with: sudo apt-get install bear"
    echo ""
else
    # Generate compile_commands.json if missing
    if [ ! -f "compile_commands.json" ]; then
        echo "Generating compile_commands.json..."
        make clean >/dev/null 2>&1 || true
        bear -- make >/dev/null 2>&1 || true
    fi

    if [ ! -f "compile_commands.json" ]; then
        echo "ERROR: Failed to generate compile_commands.json"
        echo "Try running: bear -- make"
        FAILED=1
    else
        echo "Running clang-tidy analysis..."
        find src -type f -name "*.c" -print0 | \
            xargs -0 clang-tidy > "$LOG_DIR/clang-tidy.log" 2>&1 || true

        if grep -qE "warning:|error:" "$LOG_DIR/clang-tidy.log"; then
            echo "  ⚠ Issues found:"
            grep -E "warning:|error:" "$LOG_DIR/clang-tidy.log" | head -20
            TOTAL=$(grep -cE "warning:|error:" "$LOG_DIR/clang-tidy.log" || echo "0")
            if [ "$TOTAL" -gt 20 ]; then
                echo "... and $((TOTAL - 20)) more"
            fi
            echo "  → Full report: $LOG_DIR/clang-tidy.log"
            # Note: clang-tidy issues are warnings, not failures
            echo "  (clang-tidy warnings don't fail the build)"
        else
            echo "  ✓ No issues found"
            rm -f "$LOG_DIR/clang-tidy.log"
        fi
    fi
fi
echo ""

# ============================================================================
# cppcheck Analysis
# ============================================================================
echo ">>> Running cppcheck Analysis"

if ! command -v cppcheck >/dev/null 2>&1; then
    echo "WARNING: cppcheck not installed, skipping"
    echo "Install with: sudo apt-get install cppcheck"
    echo ""
else
    cppcheck --enable=warning,performance,portability \
        --inline-suppr \
        --suppress=missingIncludeSystem \
        --suppress=unknownMacro \
        -Iinclude \
        -Isrc \
        -DPARANOIA= \
        src/ > "$LOG_DIR/cppcheck.log" 2>&1 || true

    if grep -qE "(error|warning):" "$LOG_DIR/cppcheck.log"; then
        echo "  ✗ cppcheck found issues:"
        grep -E "(error|warning):" "$LOG_DIR/cppcheck.log" | head -20
        TOTAL=$(grep -cE "(error|warning):" "$LOG_DIR/cppcheck.log" || echo "0")
        if [ "$TOTAL" -gt 20 ]; then
            echo "... and $((TOTAL - 20)) more"
        fi
        echo "  → Full report: $LOG_DIR/cppcheck.log"
        FAILED=1
    else
        echo "  ✓ No issues found"
        rm -f "$LOG_DIR/cppcheck.log"
    fi
fi
echo ""

# ============================================================================
# Summary
# ============================================================================
if [ $FAILED -eq 1 ]; then
    echo "========================================"
    echo "  ✗ Static Analysis FAILED"
    echo "========================================"
    exit 1
else
    echo "========================================"
    echo "  ✓ Static Analysis PASSED"
    echo "========================================"
    exit 0
fi
