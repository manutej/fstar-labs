# Week 2 Grading Rubric
## Lists, Options, and Total Functions (L1 Complete → L2 Start)

**Total Points**: 100 points
- Exercises 2.1-2.5: 60 points
- Mini-Project (Verified Merge Sort): 40 points

**Key Transition**: Week 2 completes L1 (Novice) and begins L2 (Apprentice). Students transition from SMT-based automatic proofs to manual inductive proofs.

---

## Exercise 2.1: Verified Fibonacci (10 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **fibonacci Implementation** | 6 | Correct recursive implementation with proper base cases |
| **decreases Clause** | 3 | Explicit `decreases n` for termination |
| **Reflection Questions** | 1 | Understanding of termination proofs |

### Detailed Rubric

#### fibonacci Implementation (6 points)

- **6 points**: Perfect implementation with both base cases (n=0, n=1) and correct recursion
- **5 points**: Correct logic but minor syntax issues
- **4 points**: One base case missing or incorrect value
- **3 points**: Recursion correct but both base cases have issues
- **2 points**: Basic structure present but significant errors
- **1 point**: Attempted but doesn't typecheck
- **0 points**: Not attempted

**Expected solution structure**:
```fsharp
let rec fibonacci (n:nat) : nat
  decreases n
= if n = 0 then 0
  else if n = 1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)
```

#### decreases Clause (3 points)

- **3 points**: Correct `decreases n` with understanding of why it's needed
- **2 points**: Present but misplaced or slightly incorrect
- **1 point**: Attempted but doesn't work
- **0 points**: Missing entirely

#### Reflection Questions (1 point)

- **1 point**: Demonstrates understanding of why F* needs termination proofs
- **0 points**: No understanding or not answered

### Common Deductions

- **-2 points**: Missing second base case (will cause runtime errors)
- **-1 point**: Inefficient recursion noted but not corrected (acceptable for this exercise)
- **-1 point**: Using `int` instead of `nat` (works but less precise)

### Sample Answers (Full Credit)

**Q: Why does F* require the `decreases` clause here?**
> F* requires proof that fibonacci terminates. The `decreases n` tells F* that n gets smaller on each recursive call. Since we check n > 1 before recursing and n is a natural number, it must eventually reach the base cases.

---

## Exercise 2.2: McCarthy 91 Function (15 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **mccarthy91 Implementation** | 10 | Correct nested recursion with conditionals |
| **decreases Clause** | 4 | Proper termination metric (tricky!) |
| **Reflection Questions** | 1 | Understanding of non-obvious termination |

### Detailed Rubric

#### mccarthy91 Implementation (10 points) - **This is challenging**

- **10 points**: Fully correct implementation matching spec
- **9 points**: Correct logic, minor issues
- **8 points**: Correct branches but recursion issues
- **7 points**: Mostly correct but edge cases wrong
- **6 points**: Basic structure correct, significant bugs
- **5 points**: Partial implementation with `admit()` and good comments
- **4 points**: Shows understanding but incomplete
- **3 points**: Attempted but major errors
- **2 points**: Minimal attempt
- **1 point**: Copied structure without understanding
- **0 points**: Not attempted

**Expected solution**:
```fsharp
let rec mccarthy91 (n:int) : int
  decreases (101 - n)  // Key insight!
= if n > 100 then n - 10
  else mccarthy91 (mccarthy91 (n + 11))
```

**Why this is hard**: The termination metric is non-obvious. Many students will struggle.

#### decreases Clause (4 points)

- **4 points**: Correct `decreases (101 - n)` or equivalent
- **3 points**: Correct idea but slightly wrong (e.g., `decreases (100 - n)`)
- **2 points**: Attempted but incorrect metric (e.g., just `decreases n`)
- **1 point**: Present but doesn't work
- **0 points**: Missing

**Teaching note**: This is the learning objective! Many students will get 2-3 points here.

#### Reflection Questions (1 point)

- **1 point**: Explains why `101 - n` works as decreasing metric
- **0 points**: No understanding demonstrated

### Common Deductions

- **-3 points**: Using simple `decreases n` (won't typecheck)
- **-2 points**: Incorrect base case boundary (e.g., `n >= 100`)
- **-1 point**: Correct implementation but can't explain termination

### Partial Credit Guidelines

- Used `admit()` with comment explaining approach: 50% of implementation points
- Correct structure but wrong `decreases`: 60% of implementation points
- Implementation works on test cases but typechecking fails: 70% of implementation points

### Sample Answer (Full Credit)

**Q: Why does `decreases (101 - n)` work?**
> When n > 100, we return immediately (no recursion). When n ≤ 100, we call mccarthy91(n+11). Since n ≤ 100, we have n+11 ≤ 111, so 101-(n+11) ≥ 101-111 = -10. But the nested call eventually reaches n > 100, and the outer call's argument (n+11) is closer to 101 than n was. The metric 101-n decreases because the function "climbs" toward 101.

**Note**: We accept partial explanations for full credit - this is subtle!

---

## Exercise 2.3: Prove Reverse Involution (15 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **reverse_reverse Proof** | 10 | Structural induction proof using helper lemmas |
| **Helper Lemmas** | 4 | Understanding need for reverse_append, etc. |
| **Reflection Questions** | 1 | Understanding of proof decomposition |

### Detailed Rubric

#### reverse_reverse Proof (10 points) - **Key L2 assessment**

- **10 points**: Fully correct proof with all helper lemmas
- **9 points**: Correct proof structure, minor issues
- **8 points**: Correct induction but missing one helper lemma call
- **7 points**: Correct base and inductive cases, incomplete helper usage
- **6 points**: Correct proof structure with `admit()` for stuck points
- **5 points**: Inductive structure correct, proof logic flawed
- **4 points**: Attempted induction, significant gaps
- **3 points**: Shows understanding but largely incomplete
- **2 points**: Minimal attempt at structural induction
- **1 point**: No understanding of induction
- **0 points**: Not attempted

**Expected solution**:
```fsharp
val reverse_append: #a:Type -> xs:list a -> ys:list a ->
  Lemma (reverse (append xs ys) == append (reverse ys) (reverse xs))

val reverse_singleton: #a:Type -> x:a ->
  Lemma (reverse [x] == [x])

let rec reverse_reverse #a xs =
  match xs with
  | [] -> ()
  | hd :: tl ->
      reverse_reverse tl;
      reverse_append (reverse tl) [hd];
      reverse_singleton hd;
      ()
```

#### Helper Lemmas (4 points)

- **4 points**: Identifies and proves/uses both necessary helper lemmas
- **3 points**: Uses provided helper lemmas correctly
- **2 points**: Attempts to use helpers but incorrectly
- **1 point**: Recognizes need for helpers but can't apply
- **0 points**: No helper lemmas attempted

#### Reflection Questions (1 point)

- **1 point**: Explains why helper lemmas were necessary
- **0 points**: No understanding

### Common Deductions

- **-2 points**: Correct structure but missing helper lemma calls
- **-3 points**: Trying to prove without helper lemmas (won't work)
- **-1 point**: Using `admit()` for main proof but helpers correct (acceptable for learning)

### Partial Credit Guidelines

This is an **intentionally challenging** exercise. Partial credit is generous:
- Correct inductive structure (match with base/recursive cases): 40% of proof points
- Attempted helper lemmas even if not fully correct: +30%
- Used `admit()` with thoughtful comments: 50% of proof points
- Correct proof with provided helper lemmas: 90% (full credit if helpers were provided)

### Sample Answer (Full Credit)

**Q: Why can't F* prove `reverse_reverse` without helper lemmas?**
> In the inductive case, we have `reverse (reverse (hd :: tl))` which expands to `reverse (append (reverse tl) [hd])`. F* doesn't automatically know how `reverse` and `append` interact. We need to explicitly prove `reverse_append` to tell F* that `reverse (append xs ys) == append (reverse ys) (reverse xs)`. This is the nature of inductive proofs - we must provide the intermediate steps.

---

## Exercise 2.4: Map Preserves Length (10 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **map_length Proof** | 8 | Simpler inductive proof (no helper lemmas needed) |
| **Reflection Questions** | 2 | Understanding of structural induction pattern |

### Detailed Rubric

#### map_length Proof (8 points)

- **8 points**: Fully correct proof with structural induction
- **7 points**: Correct proof, minor syntax issues
- **6 points**: Correct induction structure, proof incomplete
- **5 points**: Base and inductive cases present, logic errors
- **4 points**: Attempted induction, significant errors
- **3 points**: Shows understanding but incomplete
- **2 points**: Minimal attempt
- **1 point**: No understanding of induction
- **0 points**: Not attempted

**Expected solution**:
```fsharp
val map_length: #a:Type -> #b:Type -> f:(a -> b) -> xs:list a ->
  Lemma (length (map f xs) == length xs)

let rec map_length #a #b f xs =
  match xs with
  | [] -> ()
  | hd :: tl ->
      map_length f tl;
      ()
```

**Why simpler**: No helper lemmas needed! SMT handles the arithmetic.

#### Reflection Questions (2 points)

- **2 points**: Explains why this was easier than reverse_reverse
- **1 point**: Partial understanding
- **0 points**: No understanding

### Common Deductions

- **-1 point**: Forgetting to apply induction hypothesis (recursive call)
- **-2 points**: Not using pattern matching (trying to prove directly)

### Sample Answer (Full Credit)

**Q: Why is this proof simpler than `reverse_reverse`?**
> This proof doesn't need helper lemmas because the property is "obviously" true to the SMT solver. After we apply the induction hypothesis, F* can see that:
> - `length (map f (hd::tl)) = 1 + length (map f tl)` [by definition of map and length]
> - `= 1 + length tl` [by IH]
> - `= length (hd::tl)` [by definition of length]
> The arithmetic is straightforward for SMT, unlike the reverse/append interaction.

---

## Exercise 2.5: Flatten Append (10 points)

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **flatten_append Proof** | 8 | Uses provided append_assoc helper |
| **Reflection Questions** | 2 | Understanding when helper lemmas are needed |

### Detailed Rubric

#### flatten_append Proof (8 points)

- **8 points**: Fully correct proof using `append_assoc` helper
- **7 points**: Correct proof, minor issues
- **6 points**: Correct structure, incomplete helper usage
- **5 points**: Induction correct, helper lemma application wrong
- **4 points**: Basic inductive structure, significant gaps
- **3 points**: Attempted with understanding
- **2 points**: Minimal attempt
- **1 point**: No understanding
- **0 points**: Not attempted

**Expected solution**:
```fsharp
let rec flatten_append #a xss yss =
  match xss with
  | [] -> ()
  | xs :: xss' ->
      flatten_append xss' yss;
      append_assoc xs (flatten xss') (flatten yss);
      ()
```

#### Reflection Questions (2 points)

- **2 points**: Explains how `append_assoc` was used and why it was needed
- **1 point**: Partial understanding
- **0 points**: No understanding

### Common Deductions

- **-2 points**: Not using `append_assoc` (proof will fail)
- **-1 point**: Calling `append_assoc` but with wrong arguments

### Sample Answer (Full Credit)

**Q: How did the `append_assoc` helper lemma help?**
> In the inductive case, we have `flatten (append (xs::xss') yss) = append xs (flatten (append xss' yss))`. By IH, `flatten (append xss' yss) = append (flatten xss') (flatten yss)`. So we get `append xs (append (flatten xss') (flatten yss))`. We need to show this equals `append (append xs (flatten xss')) (flatten yss)`. The helper lemma `append_assoc` proves exactly this associativity property.

---

## Mini-Project: Verified Merge Sort (40 points)

**Due**: Friday 11:59 PM
**Submission**: Git repository URL with commit history

### Criteria

| Component | Points | Description |
|-----------|--------|-------------|
| **merge Implementation** | 10 | Combines two sorted lists into sorted result |
| **merge_sort Implementation** | 10 | Recursive sorting with proper termination |
| **merge_sort_sorted Proof** | 15 | Main correctness proof |
| **Code Quality** | 5 | Structure, comments, helper lemmas |
| **Extra Credit: Permutation** | +5 | Prove merge_sort is a permutation |

### Detailed Rubric

#### merge Implementation (10 points) - **Core algorithm**

**Rubric**:
- **10 points**: Fully correct merge with proper termination and logic
- **9 points**: Correct merge logic, minor issues
- **8 points**: Works correctly but missing `decreases` or type annotations
- **7 points**: Correct for most cases, edge case bugs
- **6 points**: Basic structure correct, significant logic errors
- **5 points**: Partial implementation with `admit()`
- **4 points**: Attempted but doesn't typecheck
- **3 points**: Basic understanding shown
- **2 points**: Minimal attempt
- **0-1 points**: Not attempted or completely wrong

**What we're looking for**:
```fsharp
let rec merge (xs ys: list int) : list int
  decreases %[xs; ys]  // Lexicographic ordering
= match xs, ys with
  | [], _ -> ys
  | _, [] -> xs
  | hd1::tl1, hd2::tl2 ->
      if hd1 <= hd2
      then hd1 :: merge tl1 ys
      else hd2 :: merge xs tl2
```

**Key requirements**:
- Handles both empty list cases
- Compares heads and recurses correctly
- Terminates (lexicographic decreases on both lists)
- Returns sorted result when inputs are sorted

**Deductions**:
- Missing `decreases` clause: -2 points
- Incorrect comparison (e.g., `<` instead of `<=`): -1 point
- Edge cases not handled: -2 points per case
- Doesn't maintain sortedness: -5 points

#### merge_sort Implementation (10 points)

**Rubric**:
- **10 points**: Fully correct merge_sort with proper split and termination
- **9 points**: Correct logic, minor issues
- **8 points**: Works but missing proper `decreases` on list length
- **7 points**: Correct idea but implementation bugs
- **6 points**: Basic recursive structure, significant errors
- **5 points**: Partial implementation with `admit()`
- **4 points**: Attempted but doesn't typecheck
- **3 points**: Shows understanding of merge sort
- **2 points**: Minimal attempt
- **0-1 points**: Not attempted

**Expected approach**:
```fsharp
let rec split (#a:Type) (xs:list a) : list a * list a =
  match xs with
  | [] -> [], []
  | [x] -> [x], []
  | hd1::hd2::tl ->
      let l, r = split tl in
      hd1::l, hd2::r

let rec merge_sort (xs:list int) : list int
  decreases (length xs)
= match xs with
  | [] -> []
  | [_] -> xs
  | _ ->
      let l, r = split xs in
      merge (merge_sort l) (merge_sort r)
```

**Key requirements**:
- Base cases: empty and singleton lists
- Splits list into two parts
- Recursively sorts both halves
- Merges sorted halves
- Termination proof (length decreases)

**Deductions**:
- Incorrect split (unbalanced): -2 points
- Missing base cases: -3 points
- No termination proof: -2 points
- Doesn't call merge correctly: -3 points

#### merge_sort_sorted Proof (15 points) - **Main verification goal**

**Rubric**:
- **15 points**: Fully correct proof with all necessary helper lemmas
- **13-14 points**: Correct proof, minor gaps filled with `admit()`
- **11-12 points**: Major proof structure correct, some helper lemmas missing
- **9-10 points**: Proof attempted with good understanding but incomplete
- **7-8 points**: Basic proof structure, many admits or gaps
- **5-6 points**: Partial proof showing understanding of approach
- **3-4 points**: Attempted but significant misunderstanding
- **1-2 points**: Minimal attempt
- **0 points**: Not attempted

**Helper lemmas typically needed**:
```fsharp
// 1. merge preserves sortedness
val merge_sorted: xs:list int -> ys:list int ->
  Lemma (requires sorted xs /\ sorted ys)
        (ensures sorted (merge xs ys))

// 2. singleton lists are sorted
val singleton_sorted: x:int ->
  Lemma (sorted [x])

// 3. empty list is sorted
val empty_sorted: unit ->
  Lemma (sorted [])
```

**Grading helper lemmas**:
- All helper lemmas identified and proved: Full points
- Helper lemmas stated but some use `admit()`: -2 points per admitted lemma
- Missing necessary helper lemma: -4 points per missing lemma
- Helper lemma incorrect but shows understanding: -2 points

**Deductions**:
- Using `admit()` in main proof: -3 points
- Not using structural induction: -5 points
- Incomplete case analysis: -3 points per missing case
- Circular reasoning in proof: -8 points (serious error)

#### Code Quality (5 points)

**Rubric**:
- **5 points**: Excellent structure, clear comments, well-organized helper lemmas
- **4 points**: Good quality, minor improvements possible
- **3 points**: Adequate, some messy parts
- **2 points**: Poor organization or minimal comments
- **1 point**: Very messy, hard to follow
- **0 points**: Unreadable or no effort

**Criteria**:
- Meaningful variable names
- Comments explaining proof strategy
- Helper lemmas in logical order
- No dead code or excessive `admit()`
- Clear module structure

#### Extra Credit: Permutation Proof (+5 points max)

**Rubric**:
- **+5 points**: Fully correct permutation proof
- **+4 points**: Correct with minor admits
- **+3 points**: Good attempt, partial proof
- **+2 points**: Basic structure correct
- **+1 point**: Attempted with understanding
- **0 points**: Not attempted or no understanding

**What we're looking for**:
```fsharp
val merge_sort_perm: xs:list int ->
  Lemma (permutation xs (merge_sort xs))

// Requires additional helper lemmas:
// - merge is a permutation
// - split preserves elements
// - permutation is transitive
```

**Note**: This is significantly harder! Only strong students will complete.

**Total with extra credit**: Student can earn up to 45/40 on mini-project, but week total still caps at 100.

---

## Grading Process

### Auto-Grading (Exercises 2.1-2.5)

```bash
# Run auto-grader
cd instructor_guide/rubrics/autograder
pytest week_02_tests.py -v

# Generates:
# - week_02_scores.csv (per-student breakdown)
# - week_02_report.html (detailed feedback)
```

**What auto-grader checks**:
- F* typechecks successfully
- Required functions/lemmas are present
- Basic test cases pass
- `decreases` clauses present

**Manual review still needed for**:
- Proof quality and understanding
- Helper lemma design
- Reflection questions
- Creative solutions
- Partial credit decisions

**Time estimate for exercises**: 10-12 minutes per student

### Manual Grading (Mini-Project)

**Time estimate**: 20-25 minutes per project

**Process**:
1. **Clone repository** (1 min)
   ```bash
   git clone <student-repo>
   cd verified-merge-sort
   ```

2. **Check commit history** (2 min)
   ```bash
   git log --oneline
   # Red flag: Single commit or commits only at deadline
   # Good sign: Multiple commits over several days
   ```

3. **Verify typechecking** (3 min)
   ```bash
   fstar.exe MergeSort.fst
   # Should verify without errors
   # Note admits and their locations
   ```

4. **Test functionality** (4 min)
   ```fsharp
   #push-options "--warn_error -272"  // Allow testing
   let test1 = merge_sort [3; 1; 4; 1; 5; 9; 2; 6]
   let test2 = merge_sort []
   let test3 = merge_sort [1]
   let test4 = merge_sort [5; 4; 3; 2; 1]
   ```

5. **Review proofs** (8 min)
   - Check merge_sort_sorted structure
   - Evaluate helper lemmas
   - Note use of `admit()` vs. real proofs
   - Assess proof decomposition strategy

6. **Code quality review** (3 min)
   - Comments and documentation
   - Helper lemma organization
   - Code clarity

7. **Fill out scoresheet** (4 min)

**Red flags** (investigate for plagiarism):
- No git commits until final hour
- Identical helper lemmas to another student (especially with same names)
- Proof structure too advanced for L2 level
- Student can't explain their proof strategy in office hours
- Comments copy-pasted from external sources

### Calibration

**Target class average**: 70-78% for Week 2

Week 2 is harder than Week 1 (L1 → L2 transition). Expect:
- **Exercise 2.2 (McCarthy 91)**: Average ~11/15 (challenging termination)
- **Exercise 2.3 (Reverse)**: Average ~10/15 (needs helper lemmas)
- **Mini-Project**: Average ~28/40 (main proof is hard)

**Expected distribution**:
- 90-100%: 5-10% (exceptional students, likely completed extra credit)
- 75-89%: 20-25% (strong, completed main proof)
- 60-74%: 40-50% (satisfactory, partial proofs with some admits)
- 50-59%: 15-20% (struggled but showed understanding)
- < 50%: < 10% (needs significant support)

If average is:
- **> 85%**: Excellent! Students mastering L2 transition
- **65-78%**: Target range (appropriate difficulty)
- **< 60%**: Too hard, consider:
  - Providing more helper lemma hints
  - Extended office hours
  - Additional scaffolding in exercises

---

## Feedback Guidelines

### What to emphasize in feedback

**For struggling students (< 60%)**:
- "Week 2 is a big jump from Week 1 - this is normal!"
- Point to specific proof patterns in EXAMPLES.md
- Encourage office hours for 1:1 proof walkthrough
- Note: "Using `admit()` strategically shows good engineering sense"
- Suggest: "Try proving helper lemmas separately first"

**For satisfactory students (60-75%)**:
- Acknowledge correct proof structure
- Point out where helper lemmas could improve proofs
- Suggest removing `admit()` incrementally
- Encourage: "You're on the right track with induction!"

**For strong students (> 75%)**:
- Praise proof decomposition strategy
- Suggest extension: "Try the permutation proof!"
- Offer advanced readings on proof automation
- Consider recruiting for peer tutoring

### Common feedback snippets

**For Exercise 2.1 (Fibonacci)**:
- ✅ "Great use of `decreases` clause! You understand termination."
- ✅ "Both base cases correct - good attention to detail."
- ⚠️ "You're missing the n=1 base case - this will give wrong results."
- ⚠️ "Try adding `decreases n` to help F* prove termination."

**For Exercise 2.2 (McCarthy 91)**:
- ✅ "Excellent! The `decreases (101 - n)` metric is non-obvious."
- ✅ "Good attempt - this is one of the hardest exercises in Week 2."
- ⚠️ "The metric `decreases n` won't work here. Think about what increases toward 101."
- ⚠️ "Your implementation is correct, but F* needs help with termination. Try `decreases (101 - n)`."

**For Exercise 2.3 (Reverse)**:
- ✅ "Excellent proof decomposition! Your helper lemmas are well-chosen."
- ✅ "Good use of `reverse_append` - you identified the key helper lemma."
- ⚠️ "You need a helper lemma about how reverse and append interact."
- ⚠️ "Your inductive structure is correct, but F* can't prove the step without helper lemmas."
- 💡 "Try proving: `reverse (append xs ys) == append (reverse ys) (reverse xs)` as a helper."

**For Exercise 2.4 (Map length)**:
- ✅ "Perfect! This proof shows you understand the induction pattern."
- ✅ "Nice - you're getting comfortable with structural induction."
- ⚠️ "Don't forget to apply the induction hypothesis (recursive call to map_length)."

**For Exercise 2.5 (Flatten)**:
- ✅ "Great use of `append_assoc` helper! You understand proof composition."
- ⚠️ "You need to invoke `append_assoc` with the right arguments in the inductive case."
- 💡 "When stuck, try writing out what you know vs. what you need to prove."

**For Mini-Project**:
- ✅ "Outstanding work! Your proof decomposition is sophisticated."
- ✅ "Excellent helper lemmas - you're thinking like a proof engineer!"
- ✅ "Great commit history - shows thoughtful development process."
- ⚠️ "Your merge works but needs `decreases %[xs; ys]` for termination."
- ⚠️ "The main proof needs `merge_sorted` helper lemma - try proving merge preserves sortedness."
- ⚠️ "Consider breaking `merge_sort_sorted` into smaller helper lemmas."
- 🎯 "Challenge: Can you remove the `admit()` in the inductive case by adding a helper?"

---

## Academic Integrity

### Collaboration Policy

**Allowed**:
- Discussing proof strategies and approaches
- Helping each other debug F* type errors
- Sharing insight about which helper lemmas are needed
- Working together to understand structural induction
- Studying example proofs together

**Not Allowed**:
- Sharing complete proofs or code
- Copy-pasting helper lemmas
- Writing proofs together (pair programming)
- Using solutions from previous years or online
- Submitting code with `admit()` without trying to prove

**Gray area**:
- "I needed a helper lemma about reverse and append"
  - Verdict: OK to share this insight
- Showing your helper lemma statement to a classmate
  - Verdict: OK if they prove it themselves
- Showing your complete proof
  - Verdict: Not OK - explain strategy verbally instead

### Detecting Violations

**Red flags for mini-project**:
1. **No git history**: All code in one commit
2. **Identical helper lemmas**: Same names, same order, same structure
3. **Suspiciously advanced**: Using tactics or proof techniques not covered
4. **Can't explain**: Student can't walk through their proof in office hours
5. **Inconsistent quality**: Simple exercises wrong but complex project perfect

**Investigation process**:
1. Compare with other submissions (automated similarity check)
2. Email student asking them to explain their proof strategy
3. Optional: 10-minute office hours meeting to walk through proof
4. Check git history for development process
5. If plagiarism confirmed, follow institution's academic integrity policy

**Specific checks for Week 2**:
```bash
# Check for identical helper lemma names across submissions
grep "val.*Lemma" */MergeSort.fst | sort | uniq -c | sort -rn

# Check commit timestamps
git log --all --pretty=format:"%h %an %ai %s" > commit_analysis.txt
```

**Penalties** (adjust to your institution):
- First offense: Zero on assignment, required meeting, notation in record
- Second offense: Zero on all Week 2 work, academic integrity hearing
- Egregious cases (e.g., purchased solution): Fail course, report to dean

---

## Appendix: Sample Scoring

### Example 1: Exceptional Student

**Student**: Alice (scored 95/100)

| Component | Score | Max | Notes |
|-----------|-------|-----|-------|
| Exercise 2.1 | 10 | 10 | Perfect |
| Exercise 2.2 | 14 | 15 | McCarthy 91 correct but weak reflection |
| Exercise 2.3 | 15 | 15 | Excellent helper lemmas |
| Exercise 2.4 | 10 | 10 | Perfect |
| Exercise 2.5 | 10 | 10 | Perfect |
| **Exercises Total** | **59** | **60** | |
| merge implementation | 10 | 10 | Perfect |
| merge_sort implementation | 10 | 10 | Perfect |
| merge_sort_sorted proof | 15 | 15 | All helper lemmas proved |
| Code quality | 5 | 5 | Excellent organization |
| Extra credit (permutation) | 5 | 5 | Completed! |
| **Mini-Project Total** | **45** | **40** | (+5 extra credit) |
| **Week 2 Total** | **95*** | **100** | (*Capped at 100) |

**Feedback**: "Exceptional work, Alice! Your proof decomposition skills are advanced. You've mastered the L1→L2 transition. The permutation proof shows deep understanding. Consider looking into proof automation (tactics) as an extension topic."

### Example 2: Strong Student

**Student**: Bob (scored 82/100)

| Component | Score | Max | Notes |
|-----------|-------|-----|-------|
| Exercise 2.1 | 10 | 10 | Perfect |
| Exercise 2.2 | 12 | 15 | Correct code, struggled with termination metric |
| Exercise 2.3 | 13 | 15 | Used helper lemmas correctly but one minor gap |
| Exercise 2.4 | 10 | 10 | Perfect |
| Exercise 2.5 | 9 | 10 | Small error in append_assoc application |
| **Exercises Total** | **54** | **60** | |
| merge implementation | 9 | 10 | Missing decreases initially (fixed) |
| merge_sort implementation | 10 | 10 | Perfect |
| merge_sort_sorted proof | 12 | 15 | Main proof correct, one admit in helper |
| Code quality | 4 | 5 | Good comments, minor organization issues |
| **Mini-Project Total** | **35** | **40** | |
| **Week 2 Total** | **89** | **100** | |

**Feedback**: "Strong work, Bob! You've grasped structural induction well. Your McCarthy 91 solution works correctly - the termination metric is tricky. In your merge_sort proof, try removing that one `admit()` by adding a helper about split preserving properties. You're on track for L2 mastery!"

### Example 3: Satisfactory Student

**Student**: Carol (scored 68/100)

| Component | Score | Max | Notes |
|-----------|-------|-----|-------|
| Exercise 2.1 | 9 | 10 | Correct but missing reflection |
| Exercise 2.2 | 9 | 15 | Implementation works, wrong decreases clause |
| Exercise 2.3 | 10 | 15 | Good structure, used admits for helper lemmas |
| Exercise 2.4 | 8 | 10 | Correct proof, syntax issues |
| Exercise 2.5 | 7 | 10 | Attempted but incomplete helper usage |
| **Exercises Total** | **43** | **60** | |
| merge implementation | 8 | 10 | Works but edge case issues |
| merge_sort implementation | 8 | 10 | Correct idea, minor bugs |
| merge_sort_sorted proof | 8 | 15 | Several admits, correct structure |
| Code quality | 3 | 5 | Adequate but could be clearer |
| **Mini-Project Total** | **27** | **40** | |
| **Week 2 Total** | **70** | **100** | |

**Feedback**: "Good effort, Carol! You're grasping the key concepts. The L1→L2 transition is challenging. Let's work on removing those `admit()` statements - come to office hours and we'll walk through `reverse_append` together. Your proof structures show good understanding; now let's fill in the details. Consider reviewing the EXAMPLES.md proof patterns."

### Example 4: Struggling Student

**Student**: David (scored 52/100)

| Component | Score | Max | Notes |
|-----------|-------|-----|-------|
| Exercise 2.1 | 7 | 10 | Implementation correct, missing decreases |
| Exercise 2.2 | 6 | 15 | Attempted but doesn't typecheck |
| Exercise 2.3 | 6 | 15 | Induction structure but no helper lemmas |
| Exercise 2.4 | 5 | 10 | Partial proof |
| Exercise 2.5 | 4 | 10 | Attempted, significant gaps |
| **Exercises Total** | **28** | **60** | |
| merge implementation | 6 | 10 | Basic structure, several errors |
| merge_sort implementation | 5 | 10 | Attempted but bugs prevent verification |
| merge_sort_sorted proof | 4 | 15 | Attempted but mostly admits |
| Code quality | 2 | 5 | Messy, minimal comments |
| **Mini-Project Total** | **17** | **40** | |
| **Week 2 Total** | **45** | **100** | |

**Feedback**: "David, Week 2 is tough - you're not alone in struggling with the L1→L2 transition. Please come to office hours this week (required). Let's work through structural induction together. Your attempts show effort, but we need to build understanding of proof patterns. Focus on Exercises 2.1 and 2.4 first (simpler proofs), then we'll tackle the harder ones together. The teaching team is here to help!"

**Instructor note**: Schedule meeting with David. Possible interventions: Study group assignment, additional resources, check if prerequisite knowledge is solid.

---

## Appendix: Common Student Questions

### "Why do I need `decreases` if F* can figure it out?"

**Answer**: F* can infer simple structural decreases (like on lists), but for complex recursion (McCarthy 91, Ackermann), you must provide the metric. Being explicit also helps document termination reasoning.

### "Can I use `admit()` in my mini-project?"

**Answer**: Strategic use of `admit()` is acceptable while developing, but your final submission should minimize admits. Each `admit()` loses points. If you're stuck, use `admit()` and explain in comments what you're trying to prove - partial credit available!

### "How do I know what helper lemmas I need?"

**Answer**:
1. Try to prove the main lemma
2. When F* says "Could not prove X", ask "What would let me prove X?"
3. That's your helper lemma!
4. Prove it separately, then use it in main proof

### "My proof works in my head but F* rejects it. Why?"

**Answer**: F* needs explicit steps that you might skip mentally. Use helper lemmas to make intermediate steps explicit. Try adding `assert` statements to see what F* knows at each point.

### "Is it cheating to look at FStar.List.Tot for ideas?"

**Answer**: No! Looking at library code for inspiration is good learning. But you must write and understand your own proofs. Citing your sources in comments is professional.

### "How much time should the mini-project take?"

**Answer**: Plan for 6-8 hours total:
- Implementation: 2-3 hours
- Main proof: 3-4 hours
- Helper lemmas: 2-3 hours
- Debugging: 1-2 hours

Start early! Proof development takes iteration.

---

## Appendix: Instructor Calibration Notes

### First time teaching Week 2?

**Before the week**:
- [ ] Do the mini-project yourself (budget 3-4 hours)
- [ ] Identify 3-4 helper lemmas students will need
- [ ] Prepare hint progression (reveal more if class struggles)
- [ ] Set up extra office hours Thu/Fri for mini-project help

**Difficulty calibration**:
- Exercise 2.2 (McCarthy 91): Expect 40% to struggle significantly
- Exercise 2.3 (Reverse): Expect 60% to use admits for helpers
- Mini-project main proof: Expect 50% to have significant admits

**Adjustment strategies**:
- Too hard: Provide helper lemma statements as hints
- Too easy: Add extra credit challenge (permutation proof)
- Mixed: Offer "proof sketch" option (structured comments + admits)

### Grading time budget

For a class of 30 students:
- Exercise auto-grading: 30 min (automated)
- Exercise manual review: 5 hours (10 min/student)
- Mini-project grading: 12.5 hours (25 min/student)
- **Total**: ~18 hours

**Time-saving tips**:
- Use rubric scoresheets (checkboxes)
- Group similar errors in feedback
- Record screencast of common issues (share with all)
- Recruit TA/grader for implementation testing

---

**End of Week 2 Rubric**

See also:
- `week_02_teaching_notes.md` - Detailed lesson plans
- `solutions/week_02_all_solutions.fst` - Complete solutions with pedagogical notes
- `autograder/week_02_tests.py` - Auto-grading scripts
- `EXAMPLES.md` (lines 50-150) - List proof examples
- `SKILL.md` (section 4) - Totality and effects reference
