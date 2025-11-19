# Week 1 Grading Rubric
## Introduction to F* and Type Safety (L1 - Novice)

**Total Points**: 100 points
- Exercises 1.1-1.3: 60 points
- Mini-Project (Safe Calculator): 40 points

---

## Exercise 1.1: Safe Division Function (10 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **NonZero Type Definition** | 5 | Correctly defines refinement type `x:int{x <> 0}` |
| **safe_divide Implementation** | 3 | Implements `a / b` with correct type signature |
| **Reflection Questions** | 2 | Thoughtful answers demonstrating understanding |

### Detailed Rubric

#### NonZero Type Definition (5 points)
- **5 points**: Perfect definition `type nonzero = x:int{x <> 0}`
- **4 points**: Correct predicate but minor syntax issue (e.g., capitalization)
- **3 points**: Correct idea but wrong syntax (e.g., missing braces)
- **2 points**: Shows understanding but significant errors
- **1 point**: Attempted but fundamentally incorrect
- **0 points**: Not attempted or completely wrong

#### safe_divide Implementation (3 points)
- **3 points**: Correct implementation `a / b` with proper signature
- **2 points**: Correct logic but signature issues
- **1 point**: Attempted but doesn't typecheck
- **0 points**: Not attempted

#### Reflection Questions (2 points)
- **2 points**: All three questions answered thoughtfully with correct understanding
- **1 point**: Partial understanding or incomplete answers
- **0 points**: No answers or completely incorrect

### Common Deductions

- **-1 point**: Using `!=` instead of `<>` (wrong syntax, but shows understanding)
- **-2 points**: Missing type annotation on `b` parameter
- **-1 point**: Poor code formatting or missing comments

### Sample Answers (Full Credit)

**Q1: Why does F* reject `safe_divide 10 0`?**
> F* requires that 0 has type `nonzero`, which means proving `0 <> 0`. This is false, so F* rejects the code at compile time before it can run and crash.

**Q2: How is this different from runtime checks?**
> Runtime checks happen during program execution and can fail, causing exceptions. F*'s refinement types are verified at compile time, so invalid code never compiles. This provides mathematical certainty, not just testing.

**Q3: What happens after extraction?**
> Refinement types are erased during extraction. The extracted OCaml/F# code is just `let safe_divide a b = a / b` with no runtime checks, because F* already proved safety.

---

## Exercise 1.2: Validated Input Parsing (20 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **age Type** | 3 | Defines `x:int{x >= 0 && x <= 150}` |
| **clamp Function** | 8 | Correct implementation with proper signature |
| **positive Type** | 3 | Defines `x:int{x > 0}` |
| **bounded100 & increment_wrap** | 4 | Both correctly implemented |
| **Reflection Questions** | 2 | Demonstrates understanding of control flow reasoning |

### Detailed Rubric

#### clamp Function (8 points) - **This is the key assessment item**

- **8 points**: Perfect implementation with correct signature and all branches
- **7 points**: Correct logic but minor type annotation issues
- **6 points**: Correct implementation but missing or incorrect precondition
- **5 points**: Correct logic in branches but postcondition issues
- **4 points**: Partially correct (e.g., only 2 of 3 branches work)
- **3 points**: Right idea but significant errors
- **2 points**: Attempted but doesn't typecheck
- **1 point**: Minimal attempt
- **0 points**: Not attempted

**Common Issues**:
- Missing precondition `max >= min`: Deduct 2 points
- Incorrect postcondition syntax: Deduct 1 point
- Logic errors in branches: Deduct 2 points per branch
- Using unnecessary `assert` (correct but redundant): No deduction (actually shows good thinking!)

#### Reflection Questions (2 points)

Must demonstrate understanding of:
1. How F* uses control flow for proof (Q1)
2. Why precondition is necessary (Q2)
3. What error occurs without precondition (Q3)

- **2 points**: All three answered correctly with insight
- **1 point**: Partial understanding
- **0 points**: No understanding demonstrated

---

## Exercise 1.3: ETL Pipeline (30 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **parse_csv** | 7 | Parses CSV string into list of (string, string) pairs |
| **validate_rows** | 10 | Validates and converts to (string, nat) pairs |
| **rows_to_json** | 5 | Converts validated data to JSON string |
| **etl_pipeline** | 5 | Correctly composes all three functions |
| **Reflection Questions** | 3 | Understands option types and composition |

### Detailed Rubric

#### validate_rows (10 points) - **Most complex component**

- **10 points**: Fully correct with proper option handling
- **9 points**: Correct logic, minor issues
- **8 points**: Correct but inefficient or overly complex
- **7 points**: Mostly correct but edge case handling issues
- **6 points**: Core logic correct but option handling flawed
- **5 points**: Basic structure correct but significant bugs
- **4 points**: Partial implementation with `admit()` but good comments
- **3 points**: Shows understanding but largely incomplete
- **2 points**: Attempted but major misunderstanding
- **1 point**: Minimal attempt
- **0 points**: Not attempted

**Partial Credit Guidelines**:
- Used `admit()` with comment explaining approach: 50% of points
- Correct type signature but incomplete implementation: 40%
- Implementation doesn't typecheck but logic is sound: 60-70%
- Creative alternative solution (e.g., using fold): Full credit if correct!

#### parse_csv (7 points)

- **7 points**: Fully functional parser
- **6 points**: Works but minor edge case issues
- **5 points**: Basic functionality present
- **4 points**: Partial with admits
- **3 points**: Attempted but incomplete
- **0-2 points**: Not functional

#### rows_to_json (5 points)

- **5 points**: Correct JSON formatting
- **4 points**: Minor formatting issues but conceptually correct
- **3 points**: Basic structure but format wrong
- **2 points**: Attempted but major issues
- **0-1 points**: Not functional

#### etl_pipeline Composition (5 points)

- **5 points**: Correct use of `>>=` or equivalent composition
- **4 points**: Correct logic but style issues
- **3 points**: Works but doesn't use composition effectively
- **2 points**: Partially working composition
- **1 point**: Attempted
- **0 points**: Not attempted

#### Reflection Questions (3 points)

Key concepts to assess:
- Understanding why `option` is needed (Q1)
- Understanding type safety in composition (Q2)
- Tracing execution flow (Q3)
- Extension thinking (Q4 - bonus!)

- **3 points**: Excellent understanding of all concepts
- **2 points**: Good understanding, minor gaps
- **1 point**: Basic understanding
- **0 points**: No understanding demonstrated

---

## Mini-Project: Safe Calculator (40 points)

**Due**: Friday 11:59 PM
**Submission**: Git repository URL with commit history

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **Division Safety** | 15 | Uses refinement types to prevent division by zero |
| **eval Function** | 10 | Correctly implements all operations (+, -, *, /) |
| **REPL Interface** | 8 | Interactive loop with input parsing |
| **Error Handling** | 5 | Graceful handling of parse errors and div-by-zero |
| **Code Quality** | 2 | Clean code, comments, good structure |
| **Extra Credit** | +5 | Parentheses or operator precedence support |

### Detailed Rubric

#### Division Safety (15 points) - **Core requirement**

**Rubric**:
- **15 points**: Uses `nonzero` or equivalent refinement type to make division safe
- **12 points**: Division safety via option return type (less elegant but works)
- **10 points**: Runtime check with error handling (not using refinement types)
- **7 points**: Division implemented but no safety guarantees
- **3 points**: Division attempted but crashes on zero
- **0 points**: Division not implemented

**What we're looking for**:
```fsharp
type nonzero = x:int{x <> 0}

let div (a:int) (b:nonzero) : int = a / b

// OR alternative with option:
let div_safe (a:int) (b:int) : option int =
  if b = 0 then None else Some (a / b)
```

**Deductions**:
- No refinement type: -5 points
- Runtime crash possible: -10 points
- Incorrect error message: -1 point

#### eval Function (10 points)

**Rubric**:
- **10 points**: All four operations correct with proper types
- **8 points**: All operations work, minor type issues
- **6 points**: 3/4 operations correct
- **4 points**: 2/4 operations correct
- **2 points**: Basic structure present
- **0 points**: Not implemented

**Expected signature**:
```fsharp
type op = Add | Sub | Mul | Div

val eval : int -> op -> int -> option int
```

#### REPL Interface (8 points)

**Rubric**:
- **8 points**: Full interactive loop with prompt, input, output
- **6 points**: Basic loop works but UX issues
- **4 points**: Loop present but buggy
- **2 points**: Attempted but non-functional
- **0 points**: No REPL

**Must have**:
- Prompt for user input
- Parse input into operation
- Call eval and display result
- Loop until exit command

#### Error Handling (5 points)

**Rubric**:
- **5 points**: All errors handled gracefully with clear messages
- **4 points**: Most errors handled
- **3 points**: Basic error handling
- **1-2 points**: Minimal error handling
- **0 points**: No error handling

**Error cases**:
1. Division by zero: Clear message
2. Parse error (invalid input): Informative message
3. Invalid operator: Handled
4. Non-numeric input: Handled

#### Code Quality (2 points)

- **2 points**: Clean, well-commented, good structure
- **1 point**: Functional but messy
- **0 points**: Very poor quality

**Criteria**:
- Meaningful variable names
- Comments explaining key functions
- Logical code organization
- No dead code

#### Extra Credit: Advanced Features (+5 points max)

**Parentheses support**: +3 points
```
> (10 + 5) * 2
30
```

**Operator precedence**: +2 points
```
> 10 + 5 * 2
20  (not 30!)
```

**Both**: +5 points

**Note**: Extra credit can bring total above 40, but week total caps at 100

---

## Grading Process

### Auto-Grading (Exercises 1.1-1.3)

```bash
# Run auto-grader (pytest-based)
cd instructor_guide/rubrics/autograder
pytest week_01_tests.py -v

# Generates:
# - week_01_scores.csv (per-student breakdown)
# - week_01_report.html (detailed feedback)
```

**What auto-grader checks**:
- Type signatures correct
- Code typechecks with F*
- Test cases pass
- Basic functionality present

**Manual review still needed for**:
- Code quality
- Reflection questions
- Creative solutions
- Partial credit decisions

### Manual Grading (Mini-Project)

**Time estimate**: 15-20 minutes per project

**Process**:
1. Clone student repository
2. Check commit history (red flag if no history)
3. Run F* verification: `fstar.exe calculator.fst`
4. Test REPL manually:
   - Try normal operations
   - Try division by zero
   - Try parse errors
5. Read code for quality and understanding
6. Fill out rubric scoresheet

**Red flags** (investigate for plagiarism):
- No git commits until final submission
- Identical to another student's code
- Student can't explain their code in office hours
- Code uses techniques not covered in class

### Calibration

**Target class average**: 65-75% for Week 1

If average is:
- **> 80%**: Exercises may be too easy; increase difficulty
- **< 60%**: May be too hard; add more scaffolding or office hours support

**Expected distribution**:
- 90-100%: 10-15% of students (exceptional)
- 75-89%: 25-30% (strong)
- 60-74%: 40-50% (satisfactory)
- 50-59%: 10-15% (needs support)
- < 50%: < 5% (serious struggles)

---

## Feedback Guidelines

### What to emphasize in feedback

**For struggling students (< 60%)**:
- Encourage office hours attendance
- Point to specific SKILL.md sections
- Suggest forming study group
- Note: "Refinement types are challenging; struggle is normal!"

**For satisfactory students (60-75%)**:
- Reinforce correct concepts
- Point out areas for improvement
- Suggest extension exercises

**For strong students (> 75%)**:
- Acknowledge excellent work
- Suggest advanced readings
- Offer extension challenges
- Consider recruiting as TA/helper

### Common feedback snippets

**For Exercise 1.1**:
- ✅ "Great use of refinement types to prevent runtime errors!"
- ✅ "Your reflection answers show excellent understanding of compile-time vs. runtime safety"
- ⚠️ "Remember to use `<>` for 'not equal' in F*, not `!=`"
- ⚠️ "Try explaining in your own words why F* rejects division by zero"

**For Exercise 1.2**:
- ✅ "Excellent understanding of how F* tracks control flow information!"
- ✅ "Your clamp implementation is clean and correct"
- ⚠️ "The precondition `max >= min` is necessary - try removing it to see why!"
- ⚠️ "Consider: what is F* proving in each branch of the if-then-else?"

**For Exercise 1.3**:
- ✅ "Nice use of monadic composition with `>>=`!"
- ✅ "Your helper functions show good decomposition skills"
- ⚠️ "Think about what happens when validate_rows returns None - does the pipeline handle it?"
- ⚠️ "Option types represent failure - make sure to handle both Some and None cases"

**For Mini-Project**:
- ✅ "Excellent use of refinement types for division safety!"
- ✅ "Your REPL interface is polished and user-friendly"
- ⚠️ "Consider using refinement types instead of runtime checks for safety guarantees"
- ⚠️ "Your error messages could be more informative - tell users *why* their input failed"

---

## Academic Integrity

### Collaboration Policy

**Allowed**:
- Discussing approaches and concepts with classmates
- Helping each other debug type errors
- Sharing links to F* documentation or Stack Overflow
- Working together in study groups to understand concepts

**Not Allowed**:
- Sharing code directly (copy-paste)
- Writing code together (pair programming on assignments)
- Using solutions from previous years or online
- Submitting code you don't understand

**Gray area**:
- Explaining your approach in detail to a classmate
  - Verdict: OK if they implement it themselves
- Looking at a classmate's code to understand an approach
  - Verdict: Not OK - ask them to explain verbally instead

### Detecting Violations

**Red flags**:
1. **No git history**: Code appears in one commit
2. **Identical solutions**: Exact same variable names, structure, comments
3. **Can't explain**: Student can't walk through their own code
4. **Beyond scope**: Uses techniques not taught in class

**Investigation process**:
1. Email student asking them to explain their code
2. Optional: Quick office hours meeting (5-10 min)
3. If still suspicious, compare with other submissions
4. Follow institution's academic integrity policy

**Penalties** (adjust to your institution):
- First offense: Zero on assignment, warning
- Second offense: Fail the course
- Egregious cases: Report to dean

---

## Appendix: Sample Scoring

### Example 1: Strong Student

**Student**: Alice (scored 88/100)

| Component | Score | Max | Notes |
|-----------|-------|-----|-------|
| Exercise 1.1 | 10 | 10 | Perfect |
| Exercise 1.2 | 19 | 20 | Minor syntax issue in bounded100 |
| Exercise 1.3 | 28 | 30 | validate_rows slightly inefficient but correct |
| Mini-Project | 38 | 40 | Excellent, missing only extra credit |

**Feedback**: "Excellent work, Alice! Your understanding of refinement types is strong. Consider exploring the extra credit challenges for deeper mastery."

### Example 2: Satisfactory Student

**Student**: Bob (scored 67/100)

| Component | Score | Max | Notes |
|-----------|-------|-----|-------|
| Exercise 1.1 | 8 | 10 | Reflection answers weak |
| Exercise 1.2 | 14 | 20 | clamp missing precondition, didn't understand why |
| Exercise 1.3 | 20 | 30 | Used admits with good comments |
| Mini-Project | 32 | 40 | Works but runtime checks instead of refinement types |

**Feedback**: "Good effort, Bob! You've grasped the basics. Come to office hours to discuss refinement types vs. runtime checks - this is a key concept. Your admits in 1.3 show good understanding even where implementation is incomplete."

### Example 3: Struggling Student

**Student**: Charlie (scored 48/100)

| Component | Score | Max | Notes |
|-----------|-------|-----|-------|
| Exercise 1.1 | 6 | 10 | Definition incorrect, but shows understanding |
| Exercise 1.2 | 8 | 20 | Only age and positive types correct |
| Exercise 1.3 | 10 | 30 | Mostly admits, basic structure present |
| Mini-Project | 24 | 40 | Works but many type errors, no safety guarantees |

**Feedback**: "Charlie, you're struggling with refinement types - this is normal for Week 1! Please attend office hours this week. Let's work through clamp together. Your mini-project shows good problem-solving, but we need to build up your F* skills. Consider forming a study group with classmates."

---

**End of Week 1 Rubric**

See also:
- `week_01_teaching_notes.md` - Detailed lesson plans
- `solutions/week_01_all_solutions.fst` - Complete solutions with pedagogical notes
- `autograder/week_01_tests.py` - Auto-grading scripts
