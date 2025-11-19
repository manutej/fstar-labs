#!/bin/bash
# Verify All F* Course Materials
# Tests all .fst files (exercises and solutions)

set -e

echo "=== F* Labs Verification Script ==="
echo ""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
passed=0
failed=0
total=0

# Check F* is available
if ! command -v fstar.exe &> /dev/null; then
    echo -e "${RED}ERROR: fstar.exe not found in PATH${NC}"
    echo "Please run ./scripts/install_fstar.sh first"
    exit 1
fi

echo "Using F*:"
fstar.exe --version
echo ""

# Verification function
verify_file() {
    local file=$1
    local label=$2

    echo -n "Testing $label... "
    ((total++))

    # Try to verify (timeout 60 seconds)
    if timeout 60 fstar.exe --cache_checked_modules "$file" &> /tmp/fstar_output.txt; then
        echo -e "${GREEN}✓ PASS${NC}"
        ((passed++))
        return 0
    else
        echo -e "${RED}✗ FAIL${NC}"
        ((failed++))

        # Show first 20 lines of error
        echo -e "${YELLOW}Error output:${NC}"
        head -20 /tmp/fstar_output.txt | sed 's/^/  /'
        echo ""
        return 1
    fi
}

# Create verification log
LOG_FILE="verification_log_$(date +%Y%m%d_%H%M%S).txt"
echo "Verification Log - $(date)" > "$LOG_FILE"
echo "==================" >> "$LOG_FILE"
echo "" >> "$LOG_FILE"

#==============================================================================
# PART 1: Solution Files (Must be 100% correct)
#==============================================================================

echo -e "${BLUE}=== PART 1: Solution Files (Must Pass) ===${NC}"
echo ""

echo "Testing Week 1 solutions..."
verify_file "instructor_guide/solutions/week_01_all_solutions.fst" "Week 1 Solutions" | tee -a "$LOG_FILE"

echo "Testing Week 2 solutions..."
verify_file "instructor_guide/solutions/week_02_all_solutions.fst" "Week 2 Solutions" | tee -a "$LOG_FILE"

echo ""

#==============================================================================
# PART 2: Exercise Templates (Should typecheck with admits)
#==============================================================================

echo -e "${BLUE}=== PART 2: Exercise Templates ===${NC}"
echo ""

echo "Testing Week 1 exercises..."
for exercise in exercises/week_01/*.fst; do
    basename=$(basename "$exercise")
    verify_file "$exercise" "Week 1: $basename" | tee -a "$LOG_FILE"
done

echo ""
echo "Testing Week 2 exercises..."
for exercise in exercises/week_02/*.fst; do
    basename=$(basename "$exercise")
    verify_file "$exercise" "Week 2: $basename" | tee -a "$LOG_FILE"
done

echo ""

#==============================================================================
# Summary
#==============================================================================

echo -e "${BLUE}=== Verification Summary ===${NC}"
echo ""
echo "Total files tested: $total"
echo -e "  ${GREEN}Passed: $passed${NC}"
echo -e "  ${RED}Failed: $failed${NC}"

if [ $failed -eq 0 ]; then
    echo ""
    echo -e "${GREEN}✓✓✓ ALL TESTS PASSED! ✓✓✓${NC}"
    echo "All course materials verify correctly with F*."
    exit 0
else
    echo ""
    echo -e "${RED}✗✗✗ SOME TESTS FAILED ✗✗✗${NC}"
    echo "Please fix the errors above before releasing materials."
    echo "Detailed log saved to: $LOG_FILE"
    exit 1
fi
