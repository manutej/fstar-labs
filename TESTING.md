# F* Labs Testing and Quality Assurance Framework

**Status**: This document establishes testing protocols to ensure all course materials contain working, verified F* code.

**Critical Issue**: As of Week 2 completion, course materials have **not been verified with actual F* toolchain**. This document provides the roadmap to achieve full verification.

---

## Testing Philosophy

**Core Principle**: Every code example in this course must:
1. Typecheck with F* (or explicitly be marked as "student exercise with admits")
2. Demonstrate a clear learning objective
3. Show concrete value of formal verification over traditional approaches
4. Be tested in isolation and as part of larger exercises

---

## Current Verification Status

### Week 1 Materials

| File | Status | Notes |
|------|--------|-------|
| `exercises/week_01/exercise_1_1.fst` | ⚠️ UNTESTED | Contains admits - needs student template testing |
| `exercises/week_01/exercise_1_2.fst` | ⚠️ UNTESTED | Contains admits - needs student template testing |
| `exercises/week_01/exercise_1_3.fst` | ⚠️ UNTESTED | Uses `assume val` for string functions |
| `solutions/week_01_all_solutions.fst` | ⚠️ UNTESTED | Should typecheck fully - HIGH PRIORITY |
| Teaching notes code snippets | ⚠️ UNTESTED | Inline examples need extraction and verification |

### Week 2 Materials

| File | Status | Notes |
|------|--------|-------|
| `exercises/week_02/exercise_2_1.fst` | ⚠️ UNTESTED | Fibonacci - simple, likely works |
| `exercises/week_02/exercise_2_2.fst` | ⚠️ UNTESTED | McCarthy 91 - lexicographic ordering |
| `exercises/week_02/exercise_2_3.fst` | ⚠️ UNTESTED | Reverse involution - FIXED but needs verification |
| `exercises/week_02/exercise_2_4.fst` | ⚠️ UNTESTED | Map length - depends on FStar.List.Tot |
| `exercises/week_02/exercise_2_5.fst` | ⚠️ UNTESTED | Flatten - uses append_assoc |
| `exercises/week_02/mini_project_merge_sort.fst` | ⚠️ UNTESTED | Complex - 433 lines - CRITICAL to verify |
| `solutions/week_02_all_solutions.fst` | ⚠️ UNTESTED | 976 lines - MUST typecheck fully |

**Risk Assessment**: 🔴 HIGH - Teaching unverified formal verification course is ironic and risky

---

## Testing Levels

### Level 1: Syntax Validation ✓ (Partially Complete)

**What**: Code follows F* syntax rules
**How**:
- Manual code review by agents with F* knowledge
- Pattern matching against F* grammar
- Checking for common syntax errors

**Status**:
- ✓ Week 1 reviewed by human and agents
- ✓ Week 2 reviewed by 4 parallel agents
- ⚠️ No automated syntax checking

### Level 2: Type Checking ⚠️ (NOT COMPLETE)

**What**: Code typechecks with F* compiler
**How**:
```bash
fstar.exe --cache_checked_modules exercises/week_01/exercise_1_1.fst
```

**Status**:
- ❌ F* not installed in current environment
- ❌ No CI pipeline for automated checking
- ❌ Zero files have been verified to typecheck

**BLOCKER**: Need F* toolchain installation

### Level 3: Pedagogical Value ✓ (Partially Complete)

**What**: Code demonstrates clear learning objective
**How**: Manual review of:
- Does exercise teach stated objective?
- Is progression logical?
- Are examples realistic?

**Status**:
- ✓ Week 1 reviewed (pedagogical agent scored 75%)
- ✓ Week 2 reviewed (pedagogical agent scored 75%)
- ✓ Alignment to COURSE_OUTLINE verified (100%)

### Level 4: Student Testing ❌ (NOT STARTED)

**What**: Actual students can complete exercises
**How**: Pilot testing with volunteers
**Status**: Not yet available

---

## Immediate Action Plan

### Phase 1: Setup F* Testing Environment (HIGH PRIORITY)

**Goal**: Get F* toolchain working to verify course materials

**Steps**:
1. **Install F* and Z3**:
   ```bash
   # Option A: Docker container
   docker pull fstar/fstar:latest
   docker run -it -v $(pwd):/home/fstar fstar/fstar:latest

   # Option B: Binary installation
   # Download from https://github.com/FStarLang/FStar/releases
   # Extract and add to PATH

   # Option C: Build from source
   git clone https://github.com/FStarLang/FStar.git
   cd FStar && make
   ```

2. **Verify Installation**:
   ```bash
   fstar.exe --version
   z3 --version
   ```

3. **Create Test Harness**:
   ```bash
   # Script to test all .fst files
   ./scripts/test_all_exercises.sh
   ```

**Expected Outcome**: All solution files typecheck without errors

**Estimated Time**: 2-4 hours

---

### Phase 2: Verify All Solutions Files

**Goal**: Ensure instructor solutions are 100% correct

**Priority Order**:
1. `solutions/week_01_all_solutions.fst` (500 lines)
2. `solutions/week_02_all_solutions.fst` (976 lines)

**Process**:
```bash
# Test Week 1 solutions
fstar.exe --cache_checked_modules \
  instructor_guide/solutions/week_01_all_solutions.fst

# Expected: "Verified module Week01Solutions"
# If errors: Fix immediately before proceeding
```

**Success Criteria**:
- Zero type errors
- All lemmas verify
- All test cases pass

**Estimated Time**: 1-2 hours per week

---

### Phase 3: Verify Student Exercise Templates

**Goal**: Ensure exercises typecheck with `admit()` placeholders

**Why**: Students should have working starting points

**Process**:
```bash
# Each exercise should typecheck with admits
for exercise in exercises/week_01/*.fst; do
  echo "Testing $exercise"
  fstar.exe "$exercise" || echo "FAILED: $exercise"
done
```

**Common Issues to Check**:
- Missing `open` statements
- Incorrect module names
- Type signature mismatches
- Assumed functions not declared

**Estimated Time**: 30 minutes per exercise

---

### Phase 4: Extract and Verify Teaching Note Snippets

**Goal**: Ensure lecture examples actually work

**Challenge**: Teaching notes contain inline F* code blocks that aren't files

**Solution**:
1. Extract all ```fsharp code blocks from teaching notes
2. Create temporary `.fst` files for each
3. Verify they typecheck
4. Mark which snippets are "pedagogical sketches" vs "runnable"

**Script** (to be created):
```bash
# Extract code blocks from markdown
./scripts/extract_and_test_snippets.sh \
  instructor_guide/week_01_teaching_notes.md
```

**Estimated Time**: 1 hour per week

---

### Phase 5: Create Continuous Integration Pipeline

**Goal**: Automated testing on every commit

**Setup** (GitHub Actions):
```yaml
# .github/workflows/verify-fstar.yml
name: Verify F* Course Materials

on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    container: fstar/fstar:latest

    steps:
      - uses: actions/checkout@v2

      - name: Verify Week 1 Solutions
        run: |
          fstar.exe instructor_guide/solutions/week_01_all_solutions.fst

      - name: Verify Week 2 Solutions
        run: |
          fstar.exe instructor_guide/solutions/week_02_all_solutions.fst

      - name: Verify All Exercises Typecheck
        run: |
          ./scripts/test_all_exercises.sh
```

**Estimated Time**: 2-3 hours to set up

---

## Quality Gates for Future Weeks

**Before marking any week as "complete", must satisfy**:

### ✓ Mandatory Gates (MUST PASS)

1. **All solution files typecheck with F***
   - Zero errors from `fstar.exe solutions/week_0X_all_solutions.fst`

2. **All exercise templates typecheck with admits**
   - Students get working starting points

3. **Parallel agent review completed**
   - Pedagogical consistency ≥ 75%
   - Technical accuracy ≥ 85%
   - Assessment alignment ≥ 80%
   - Completeness = 100%

4. **All code snippets in teaching notes are marked**
   - Either ✓ VERIFIED or ⚠️ PEDAGOGICAL SKETCH

5. **No confabulation**
   - All statistics cited or marked as estimates
   - All claims traceable to BIBLIOGRAPHY.md

### ⚠️ Recommended Gates (SHOULD PASS)

1. **At least one exercise manually tested by non-author**
   - Fresh perspective catches ambiguities

2. **Timing estimates validated**
   - 90-minute lectures should fit in 90 minutes

3. **Difficulty progression verified**
   - Each exercise builds on previous
   - No sudden jumps in complexity

---

## Defect Tracking

**Template for reporting issues**:

```markdown
### Issue: [Brief Description]

**File**: `path/to/file.fst:line_number`
**Severity**: 🔴 CRITICAL / 🟡 MODERATE / 🟢 MINOR
**Type**: Syntax Error / Type Error / Pedagogical / Other

**Description**:
What's wrong and why it matters

**Reproduction**:
```bash
fstar.exe path/to/file.fst
# Error: ...
```

**Fix**:
What needs to change

**Impact**:
How many students/exercises affected
```

**Current Known Issues**: None logged (because we haven't tested!)

---

## Testing Tools and Scripts

### `scripts/test_all_exercises.sh`

```bash
#!/bin/bash
# Test all .fst files in exercises/ and solutions/

set -e  # Exit on first error

echo "=== Testing F* Course Materials ==="
echo ""

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

passed=0
failed=0
skipped=0

# Test solutions first (must be perfect)
echo "=== Testing Solution Files ==="
for solution in instructor_guide/solutions/*.fst; do
  echo -n "Testing $(basename $solution)... "
  if fstar.exe --cache_checked_modules "$solution" 2>&1 | grep -q "Verified"; then
    echo -e "${GREEN}✓ PASS${NC}"
    ((passed++))
  else
    echo -e "${RED}✗ FAIL${NC}"
    ((failed++))
    echo "  Error output:"
    fstar.exe "$solution" 2>&1 | tail -20 | sed 's/^/    /'
  fi
done

echo ""
echo "=== Testing Exercise Templates ==="
for exercise in exercises/week_*/*.fst; do
  echo -n "Testing $(basename $exercise)... "
  # Exercises with admits should still typecheck
  if fstar.exe "$exercise" 2>&1 | grep -q -E "(Verified|1 warning)"; then
    echo -e "${GREEN}✓ PASS${NC}"
    ((passed++))
  else
    echo -e "${RED}✗ FAIL${NC}"
    ((failed++))
    echo "  Error output:"
    fstar.exe "$exercise" 2>&1 | tail -10 | sed 's/^/    /'
  fi
done

echo ""
echo "=== Summary ==="
echo -e "${GREEN}Passed: $passed${NC}"
echo -e "${RED}Failed: $failed${NC}"
echo -e "${YELLOW}Skipped: $skipped${NC}"

if [ $failed -gt 0 ]; then
  echo -e "\n${RED}TESTING FAILED${NC}"
  exit 1
else
  echo -e "\n${GREEN}ALL TESTS PASSED${NC}"
  exit 0
fi
```

### `scripts/extract_code_blocks.py`

```python
#!/usr/bin/env python3
"""
Extract F* code blocks from markdown teaching notes and verify them.
"""

import re
import sys
import subprocess
from pathlib import Path

def extract_fsharp_blocks(markdown_file):
    """Extract all ```fsharp code blocks from markdown."""
    content = Path(markdown_file).read_text()

    # Match ```fsharp ... ``` blocks
    pattern = r'```fsharp\n(.*?)```'
    blocks = re.findall(pattern, content, re.DOTALL)

    return blocks

def create_test_module(code_blocks, output_file):
    """Create a single .fst file from all code blocks."""
    header = """module ExtractedSnippets

open FStar.List.Tot

// This file is auto-generated from teaching notes
// It tests that all code snippets are valid F*

"""

    full_code = header + "\n\n".join(code_blocks)
    Path(output_file).write_text(full_code)

    return output_file

def verify_with_fstar(fst_file):
    """Run fstar.exe on the file."""
    try:
        result = subprocess.run(
            ['fstar.exe', fst_file],
            capture_output=True,
            text=True,
            timeout=60
        )
        return result.returncode == 0, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return False, "", "Timeout after 60s"

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: extract_code_blocks.py <teaching_notes.md>")
        sys.exit(1)

    md_file = sys.argv[1]
    blocks = extract_fsharp_blocks(md_file)

    print(f"Extracted {len(blocks)} code blocks from {md_file}")

    if blocks:
        test_file = "/tmp/extracted_snippets.fst"
        create_test_module(blocks, test_file)

        print(f"Testing {test_file}...")
        success, stdout, stderr = verify_with_fstar(test_file)

        if success:
            print("✓ All snippets verified!")
            sys.exit(0)
        else:
            print("✗ Verification failed:")
            print(stderr)
            sys.exit(1)
```

---

## Value Demonstration Checklist

**Every exercise must clearly show WHY formal verification matters**

For each exercise, document:

### ✓ The Bug It Prevents

**Bad Example**: "Exercise 2.1: Implement Fibonacci"
- Doesn't show value - could be any programming course

**Good Example**: "Exercise 2.1: Prove Fibonacci Terminates"
- Shows value: Many recursive algorithms have termination bugs
- Real-world impact: Infinite loops in production code
- F* advantage: Catch at compile time, not after deployment

### ✓ The Alternative Approach Comparison

**For each exercise, document**:
- **Traditional approach**: Runtime checks, testing, defensive programming
- **F* approach**: Compile-time proof
- **Concrete benefit**: What class of bugs eliminated? Performance impact?

**Example** (Exercise 1.1):
```markdown
## Why This Exercise Matters

**Bug Class**: Division by zero crashes
**Traditional approach**:
  - Runtime check: `if (b == 0) throw Exception`
  - Cost: Every call pays runtime check overhead
  - Problem: Still crashes if check forgotten

**F* approach**:
  - Refinement type: `type nonzero = x:int{x <> 0}`
  - Cost: Zero runtime overhead (proof erased)
  - Guarantee: Division by zero impossible - proven at compile time

**Real-world impact**:
  - Ariane 5 rocket explosion (1996): $370M loss from integer overflow
  - Similar type-level guarantees could have prevented this
```

### ✓ The Concrete Learning Outcome

**Each exercise must enable students to**:
- State what they learned (not just "I did it")
- Apply the technique to new problems
- Explain the value to a non-expert

**Assessment question** (in reflection):
> "Explain to a Python developer why refinement types are better than runtime assertions for preventing division by zero."

**Good answer should include**:
- Compile-time vs runtime checking
- Performance benefits (no overhead)
- Correctness guarantees (proven, not tested)
- Maintenance benefits (types checked on refactoring)

---

## Next Steps for Quality Assurance

**Immediate** (this session):
1. Create `TESTING.md` (this file) ✓
2. Create `scripts/test_all_exercises.sh`
3. Document verification status in this file
4. Add quality gates to development workflow

**Next session** (requires F* installation):
1. Install F* toolchain
2. Verify all Week 1 solutions
3. Verify all Week 2 solutions
4. Fix any type errors discovered
5. Create bug tracker for issues

**Before Week 3 development**:
1. Establish CI pipeline
2. Test all existing materials
3. Document any pedagogical sketches vs verified code
4. Create "value demonstration" checklist for each exercise

**Ongoing**:
- Every new week must pass quality gates
- All commits run automated verification
- Monthly review of testing coverage

---

## Status Summary

**Last Updated**: Week 2 completion (2025-11-19)

**Verification Coverage**:
- 0 / 11 F* files verified to typecheck ⚠️
- 2 / 2 weeks reviewed by parallel agents ✓
- 0 / 2 weeks pilot tested with students ⚠️

**Critical Path**:
1. Install F* toolchain
2. Verify solutions files
3. Fix any discovered errors
4. Document verification status

**Risk Level**: 🔴 HIGH - Teaching unverified verification course
**Mitigation**: Implement Phase 1-3 before releasing to students

---

## References

- [F* Installation Guide](https://github.com/FStarLang/FStar/blob/master/INSTALL.md)
- [F* Tutorial](https://fstar-lang.org/tutorial/)
- [Continuous Integration Best Practices](https://fstar-lang.org/tutorial/part4/part4_verification_in_ci.html)
- BIBLIOGRAPHY.md - Course research citations

