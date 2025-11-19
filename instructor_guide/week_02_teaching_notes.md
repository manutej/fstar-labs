# Week 2 Teaching Notes: Lists, Options, and Total Functions
## Level 1 (Novice Complete) → Level 2 (Apprentice Start)

**Week Theme**: Transition from refinement types to inductive reasoning
**Learning Goal**: By end of Week 2, students understand totality, can work with lists, and write simple lemmas
**Assessment**: Mini-project (verified merge sort) due Friday

---

## Overview

### Week 2 Learning Objectives

By the end of Week 2, students will be able to:
1. **Write total functions** with `decreases` clauses for termination
2. **Work with inductive data types** (lists, options, recursive types)
3. **Apply structural recursion** to define functions on lists
4. **State simple lemmas** about recursive functions
5. **Prove lemmas** using structural induction
6. **Understand the `Tot` effect** and why totality matters
7. **Complete mini-project**: Verified merge sort with correctness proof

**Note**: This week **completes L1 (Novice)** and **begins L2 (Apprentice)**. Students transition from SMT-based automatic proofs to manual inductive proofs.

### Pre-Week Preparation (for Instructor)

**Before Week 2 starts:**
- [ ] Grade Week 1 mini-projects (safe calculator)
- [ ] Review common mistakes from Week 1 to address Monday
- [ ] Prepare list examples (review EXAMPLES.md lines 50-120)
- [ ] Test merge sort project yourself (3-4 hours)
- [ ] Set up Week 2 auto-grader for Exercises 2.1-2.5
- [ ] Review structural induction pedagogy (see BIBLIOGRAPHY.md Source 1)

**Teaching Materials Needed:**
- Lecture slides: `slides/week_02_day_04.md` through `week_02_day_06.md`
- Exercise starters: `exercises/week_02/`
- Solutions (instructor only): `instructor_guide/solutions/week_02_all_solutions.fst`
- Rubric: `instructor_guide/rubrics/week_02_rubric.md`

---

## Day 4 (Monday): Total Functions and Termination

### Learning Objectives
1. Explain why F* requires proofs of termination
2. Use `decreases` clauses for recursive functions
3. Identify structural vs. non-structural recursion patterns
4. Convert partial functions to total functions with `Tot` effect

### Lecture Structure (90 minutes)

#### [0-15 min] Review Week 1 + Mini-Project Showcase

**Quick Poll** (3 min):
```
"How did the safe calculator project go?"
 - Finished and working: [count hands]
 - Mostly working but bugs: [count hands]
 - Struggled significantly: [count hands]

"What was hardest?"
 - Division safety implementation
 - REPL/parsing
 - Error handling
 - Time management
```

**Mini-Project Showcase** (10 min):
- Pick 2-3 interesting student solutions to show (with permission)
- Highlight different approaches (refinement types vs. option returns)
- Common excellent features: Good error messages, creative extras
- Common issues: Forgetting to use `nonzero` type, parse errors not handled

**Transition** (2 min):
"Week 1: We used refinement types and SMT to prevent errors at compile time.
Week 2: We learn about **totality** - proving functions always terminate.
This is the foundation for all formal verification!"

#### [15-40 min] The Halting Problem and Totality

**Motivating Question** (5 min):
"Why can't F* verify this function?"

```fsharp
let rec loop () = loop ()
// Error: "Could not prove termination"
```

Ask students: "What's wrong with this code?"
- Answer: Infinite loop! Never terminates.

**The Halting Problem** (10 min):

Brief explanation (accessible, not deep CS theory):
- In general, we **can't** decide if arbitrary programs terminate
- Alan Turing proved this in 1936 (Halting Problem)
- BUT: For **most useful programs**, we CAN prove termination
- F* requires termination proofs for soundness

**Why Totality Matters for Verification** (10 min):

```fsharp
// Claim: This function is safe (no division by zero)
let bad_divide (x:int) : int =
  let rec loop () = loop () in
  x / 0  // Never reached! But also "safe" since unreachable?
```

**The problem**: If we allow non-terminating functions:
- We can "prove" anything (including false statements!)
- Logic becomes unsound
- Verification becomes meaningless

**F*'s solution**: Require termination proofs for all functions in `Tot` effect.

**Discussion Prompt** (5 min):
"When might we WANT non-terminating programs?"
- Expected answers: Servers, operating systems, infinite streams
- F*'s answer: Use `Dv` (divergence) effect explicitly
- Default is `Tot` (total, always terminates)

#### [40-65 min] Decreasing Metrics for Recursion

**Concept Introduction** (10 min):

"How does F* know a recursive function terminates?"

**Answer: Decreasing metrics**

```fsharp
let rec factorial (n:nat) : nat =
  if n = 0 then 1 else n * factorial (n - 1)
// F* infers: 'n' decreases each recursive call
```

**Behind the scenes**:
- F* checks: `n - 1 < n` (argument gets smaller)
- Recursion stops when `n = 0` (base case)
- Therefore: Function terminates!

**Explicit `decreases` Clause** (15 min):

Live coding:

```fsharp
// Explicit decreasing metric
let rec sum_up_to (n:nat) : nat
  decreases n  // Tell F* what decreases
= if n = 0 then 0 else n + sum_up_to (n - 1)

// Why we need this sometimes:
let rec ackermann (m:nat) (n:nat) : nat
  decreases %[m; n]  // Lexicographic ordering!
= if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))
```

**Key points**:
- `decreases n`: Explicitly state what decreases
- `decreases %[m; n]`: Lexicographic (m first, then n)
- F* checks metric decreases on **every recursive call**

**Common Patterns** (5 min):

1. **Structural recursion** (on lists, trees):
   - Metric: size of data structure
   - F* infers automatically!

2. **Numeric recursion** (on nat, int):
   - Metric: numeric value
   - Usually inferred, sometimes need explicit `decreases`

3. **Well-founded recursion** (custom relations):
   - Metric: custom well-founded relation
   - Week 4 topic (preview only)

#### [65-85 min] Exercise 2.1: Verified Fibonacci

**Exercise Introduction** (5 min):

"Your first termination proof! Implement Fibonacci with explicit `decreases`."

**Exercise 2.1 Specification:**
```fsharp
module Exercise2_1

// TODO: Implement fibonacci with decreases clause
val fibonacci: nat -> nat
let rec fibonacci n =
  decreases n  // TODO: Add this!
  (* YOUR CODE HERE *)
  // Hint: fib(0) = 0, fib(1) = 1, fib(n) = fib(n-1) + fib(n-2)

// Test cases (should typecheck and compute correct values):
let test1 = fibonacci 0  // Should be 0
let test2 = fibonacci 1  // Should be 1
let test3 = fibonacci 5  // Should be 5
let test4 = fibonacci 10 // Should be 55
```

**Instructions** (5 min):
- Work individually (10 min to attempt)
- Key challenge: Making sure recursion terminates
- Common mistake: Forgetting base cases
- Hint: You need TWO base cases (0 and 1)

**Work Time** (10 min):
- Students work, instructor circulates
- Common issue: "F* says 'Could not prove termination'"
  - Solution: Check base cases cover all possibilities
  - Make sure n > 1 before recursive call

**Debrief** (5 min):
- Show solution (or ask student to share)
- Explain why `decreases n` works
- Note: This is inefficient (exponential time) - we'll optimize later!

#### [85-90 min] Homework Assignment and Preview

**Homework** (5 min):
- Complete Exercise 2.1 (if not finished)
- Start Exercise 2.2 (McCarthy 91 function - challenging!)
- Read: SKILL.md section 4 (totality and effects)

**Preview Tomorrow** (Day 5):
- Inductive data types: lists!
- Structural recursion patterns
- First lemma: `length (append xs ys) == length xs + length ys`

---

### After Class

**Grading Notes**:
- Exercise 2.1: Most students should complete in class or shortly after
- Watch for: Students who struggle with recursion (offer extra support)

**Common Errors to Watch For**:
- Missing base cases (function doesn't cover all inputs)
- Incorrect base case values
- Not understanding what `decreases` does (offer 1:1 explanation)

---

## Day 5 (Tuesday): Lists and Structural Induction (L2 Start)

### Learning Objectives
1. Define inductive data types (lists, options, trees)
2. Write structurally recursive functions on lists
3. State simple lemmas about list functions
4. Use `Tot` effect for pure computations
5. Understand the **transition from L1 to L2**

**IMPORTANT**: This is the **beginning of L2 (Apprentice)**. Students are transitioning from refinement types (L1) to inductive proofs (L2).

### Lecture Structure (90 minutes)

#### [0-10 min] Termination Quiz + Transition to L2

**Quick Quiz** (5 min):

5 questions on paper or online:
1. Why does F* require termination proofs? (Answer: Soundness)
2. What does `decreases n` mean? (Answer: Metric that decreases each recursive call)
3. True/False: All recursive functions need explicit `decreases`. (Answer: False, F* often infers)
4. What happens if F* can't prove termination? (Answer: Type error, won't compile)
5. Give an example of a non-terminating function. (Answer: `let rec loop () = loop ()`)

**Transition to L2** (5 min):

"So far (L1 Novice): We used refinement types and SMT to prove simple properties.

Today (L2 Apprentice): We learn **inductive reasoning** - proving properties by structure.

Key difference:
- L1: SMT does the proving automatically
- L2: WE write the proofs (with some SMT help)

This is a big step! Struggle is expected and normal."

#### [10-35 min] List Type Definition and Recursion Patterns

**Inductive Data Types** (10 min):

```fsharp
// How lists are defined in F* (simplified)
type list a =
  | Nil : list a                    // Empty list
  | Cons : hd:a -> tl:list a -> list a  // Head + tail

// Syntactic sugar:
// []        means Nil
// x :: xs   means Cons x xs
// [1; 2; 3] means 1 :: 2 :: 3 :: []
```

**Key concept**: Lists are defined **inductively** (recursively).
- Base case: `Nil` (empty list)
- Inductive case: `Cons hd tl` (head + tail)

**Why this matters for proofs**: We'll prove properties **the same way**:
- Prove for base case (Nil)
- Prove for inductive case (Cons hd tl), assuming property holds for `tl`

**Structural Recursion Patterns** (15 min):

Live coding - show multiple examples:

```fsharp
module ListExamples
open FStar.List.Tot

// Pattern 1: Computing a value
let rec length (#a:Type) (xs:list a) : nat =
  match xs with
  | [] -> 0
  | hd :: tl -> 1 + length tl

// Pattern 2: Transforming a list
let rec map (#a #b:Type) (f:a -> b) (xs:list a) : list b =
  match xs with
  | [] -> []
  | hd :: tl -> f hd :: map f tl

// Pattern 3: Combining elements
let rec append (#a:Type) (xs ys:list a) : list a =
  match xs with
  | [] -> ys
  | hd :: tl -> hd :: append tl ys

// Pattern 4: Filtering
let rec filter (#a:Type) (f:a -> bool) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd :: tl -> if f hd then hd :: filter f tl else filter f tl
```

**Pause for Questions** (3 min)

**Common Pattern: All follow same structure**:
1. Match on list
2. Base case: `[]` → simple result
3. Recursive case: `hd :: tl` → combine `hd` with result of recursive call on `tl`

#### [35-60 min] First Lemma: Length of Append

**Transition to Proofs** (5 min):

"Now we want to PROVE properties of our functions.

Example claim: `length (append xs ys) == length xs + length ys`

How do we prove this? **Structural induction!**"

**Structural Induction Explained** (10 min):

Mathematical induction recap (brief):
- Prove P(0)
- Prove P(n) → P(n+1)
- Conclude: P holds for all n

Structural induction (on lists):
- Prove P([]) (base case)
- Prove P(hd :: tl), assuming P(tl) holds (inductive case)
- Conclude: P holds for all lists

**Live Coding: First Lemma** (10 min):

```fsharp
// Lemma: length of append is sum of lengths
val length_append: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) == length xs + length ys)

let rec length_append #a xs ys =
  match xs with
  | [] ->
      // Base case: length (append [] ys) == length [] + length ys
      // LHS: length (append [] ys) = length ys (by def of append)
      // RHS: length [] + length ys = 0 + length ys = length ys (by def of length)
      // Equal! QED for base case.
      ()
  | hd :: tl ->
      // Inductive case: length (append (hd::tl) ys) == length (hd::tl) + length ys
      // Induction hypothesis: length (append tl ys) == length tl + length ys
      length_append tl ys;  // Apply IH (recursive call!)
      // Now F* knows: length (append tl ys) == length tl + length ys
      // LHS: length (append (hd::tl) ys)
      //    = length (hd :: append tl ys)  [by def of append]
      //    = 1 + length (append tl ys)     [by def of length]
      //    = 1 + length tl + length ys     [by IH]
      // RHS: length (hd::tl) + length ys
      //    = (1 + length tl) + length ys   [by def of length]
      //    = 1 + length tl + length ys     [arithmetic]
      // Equal! QED.
      ()
```

**Key insights for students**:
1. Lemma has type `Lemma (property)`
2. Body is a proof (returns unit `()`)
3. Recursive call `length_append tl ys` applies induction hypothesis
4. F* + SMT handle arithmetic automatically
5. `()` at end means "proof complete"

**Pause for Questions** (5 min)

#### [60-80 min] Exercise 2.3: Prove Reverse Involution

**Exercise Introduction** (5 min):

"Now YOU write a proof! Prove that reversing twice gives back the original list."

**Exercise 2.3 Specification:**
```fsharp
module Exercise2_3
open FStar.List.Tot

// Reverse function (provided - you'll prove property about it)
let rec reverse (#a:Type) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]

// TODO: Prove that reverse is an involution (reverse twice = identity)
val reverse_reverse: #a:Type -> xs:list a ->
  Lemma (reverse (reverse xs) == xs)

let rec reverse_reverse #a xs =
  (* YOUR CODE HERE *)
  // Hints:
  // - Use structural induction (match on xs)
  // - Base case: reverse (reverse []) == []
  // - Inductive case: reverse (reverse (hd::tl)) == hd::tl
  // - You'll need helper lemmas! (We'll provide hints)
```

**Instructions** (5 min):
- Work in pairs (10 min to attempt)
- This is HARD! You'll likely get stuck.
- Key learning: What helper lemmas do you need?
- Don't worry if you can't finish - we'll solve together

**Work Time** (10 min):
- Students work, instructor circulates
- Expected struggle: "How do I prove this??"
- Hint if stuck: "What property of reverse and append do you need?"
- Very few will complete this - that's OK!

**Debrief** (5 min):
- Show that this needs helper lemmas
- Explain: "This is why proof engineering is hard!"
- Preview: Tomorrow we'll learn proof decomposition strategies
- For now: It's OK to use `admit()` as placeholder

#### [70-80 min] Simpler Example: Map Preserves Length

**Motivation** (2 min):
"Exercise 2.3 was hard! Let's look at a simpler proof to build confidence."

**Introduce Map** (3 min):
```fsharp
// The map function (in FStar.List.Tot)
let rec map (#a #b:Type) (f:a -> b) (xs:list a) : list b =
  match xs with
  | [] -> []
  | hd :: tl -> f hd :: map f tl
```

**Property: Map Preserves Length** (5 min):
```fsharp
// Claim: Mapping over a list doesn't change its length
val map_length: #a:Type -> #b:Type -> f:(a -> b) -> xs:list a ->
  Lemma (length (map f xs) == length xs)

// Proof by structural induction (show skeleton):
let rec map_length #a #b f xs =
  match xs with
  | [] -> ()  // Base case: length (map f []) == length [] (both 0)
  | hd :: tl ->
      map_length f tl;  // IH: length (map f tl) == length tl
      ()  // Inductive: length (f hd :: map f tl) == 1 + length tl
```

**Key Pattern** (2 min):
- Similar structure to reverse_reverse
- But simpler! No helper lemmas needed.
- SMT can prove inductive case automatically
- Exercise 2.4 asks you to complete this proof

#### [80-90 min] Homework and Preview

**Homework** (10 min):
- Complete Exercise 2.3 (attempt! Use `admit()` if stuck)
- Exercise 2.4: Prove `map` preserves length (simpler than 2.3)
- Read: EXAMPLES.md section on list proofs (lines 85-150)
- **Think about**: What helper lemmas might `reverse_reverse` need?

**Preview Tomorrow** (Day 6):
- Proof engineering: How to decompose complex proofs
- Helper lemmas and proof strategies
- Case analysis and pattern matching in proofs
- Kick off mini-project: Verified merge sort!

---

### After Class

**Grading Notes**:
- Exercise 2.3: DO NOT expect students to finish this!
- Goal: Expose them to the challenge, build motivation for Day 6
- Partial credit for attempting the structure

**Common Errors**:
- Not using `match` (trying to prove without induction)
- Not understanding what `Lemma` type means
- Confusion about recursive proofs ("Why am I calling the lemma inside itself?")

**For Tomorrow**:
- Prepare solution to Exercise 2.3 with full explanation
- Have 2-3 helper lemmas ready to show

---

## Day 6 (Wednesday): Lemmas and Proof Engineering

### Learning Objectives
1. Structure proofs using helper lemmas
2. Apply induction hypotheses correctly
3. Debug proof failures with `admit()`
4. Understand SMT vs. manual proof trade-offs
5. Begin mini-project (verified merge sort)

### Lecture Structure (90 minutes)

#### [0-20 min] Common Proof Mistakes from Homework

**Open Discussion** (10 min):
"Who struggled with Exercise 2.3 (reverse_reverse)? What was hardest?"

Expected responses:
- "I don't know where to start"
- "I wrote the match but then got stuck"
- "F* gives errors I don't understand"
- "Why doesn't F* just prove it automatically?"

**Address Each Concern** (10 min):

**Concern 1: "Don't know where to start"**
Solution: Template for inductive proofs:
```fsharp
let rec my_lemma xs =
  match xs with
  | [] -> ()  // Base case: often trivial
  | hd :: tl ->
      my_lemma tl;  // Apply IH
      ()  // Prove inductive case
```

**Concern 2: "F* doesn't prove it automatically"**
Answer: Some properties need helper lemmas. SMT can't see everything.

**Concern 3: "Don't understand F* errors"**
We'll practice error-driven proof development today.

#### [20-45 min] Proof Decomposition Strategies

**The Problem** (5 min):

```fsharp
// This doesn't work (proof fails):
let rec reverse_reverse #a xs =
  match xs with
  | [] -> ()
  | hd :: tl ->
      reverse_reverse tl;
      ()  // ERROR: "Could not prove post-condition"
```

**Why?** F* doesn't automatically know properties of `append`.

**The Solution: Helper Lemmas** (10 min):

Strategy: Identify what F* needs to know.

In `reverse (reverse (hd :: tl))`, we get:
- `reverse (append (reverse tl) [hd])`

What property of `reverse` and `append` would help?

**Helper Lemma 1**: Distribution of reverse over append:
```fsharp
val reverse_append: #a:Type -> xs:list a -> ys:list a ->
  Lemma (reverse (append xs ys) == append (reverse ys) (reverse xs))
```

Show students how to prove this (or provide it).

**Helper Lemma 2**: Reverse of singleton:
```fsharp
val reverse_singleton: #a:Type -> x:a ->
  Lemma (reverse [x] == [x])
let reverse_singleton #a x = ()  // Trivial!
```

**Now the Main Proof Works** (10 min):

```fsharp
let rec reverse_reverse #a xs =
  match xs with
  | [] -> ()
  | hd :: tl ->
      reverse_reverse tl;  // IH: reverse (reverse tl) == tl
      reverse_append (reverse tl) [hd];  // Helper lemma 1
      reverse_singleton hd;  // Helper lemma 2
      // Now F* can prove the goal!
      ()
```

**Key Insight**: Proof engineering = finding right helper lemmas.

**Proof Decomposition Heuristic** (5 min):

1. Try to prove directly
2. If fails, look at F* error: "Could not prove X"
3. Ask: "What would let me prove X?"
4. Extract that as a helper lemma
5. Prove helper lemma separately
6. Use helper lemma in main proof

#### [45-70 min] Exercise 2.5: Flatten Associativity

**Exercise Introduction** (5 min):

"Practice proof decomposition with a new example!"

**Exercise 2.5 Specification:**
```fsharp
module Exercise2_5
open FStar.List.Tot

// Flatten a list of lists
let rec flatten (#a:Type) (xss:list (list a)) : list a =
  match xss with
  | [] -> []
  | xs :: xss' -> append xs (flatten xss')

// TODO: Prove flatten distributes over append of list-of-lists
val flatten_append: #a:Type -> xss:list (list a) -> yss:list (list a) ->
  Lemma (flatten (append xss yss) == append (flatten xss) (flatten yss))

let rec flatten_append #a xss yss =
  (* YOUR CODE HERE *)
  // Hints:
  // - Structural induction on xss
  // - You'll need a helper lemma about append associativity!
  // - Helper: append (append xs ys) zs == append xs (append ys zs)
```

**Helper Lemma (Provided)**:
```fsharp
// Append is associative (provided for you)
val append_assoc: #a:Type -> xs:list a -> ys:list a -> zs:list a ->
  Lemma (append (append xs ys) zs == append xs (append ys zs))
let rec append_assoc #a xs ys zs =
  match xs with
  | [] -> ()
  | hd :: tl -> append_assoc tl ys zs; ()
```

**Instructions** (5 min):
- Work individually or in pairs
- 15 minutes to attempt
- Use the helper lemma `append_assoc` in your proof
- Structure: match on xss, apply IH in recursive case

**Work Time** (15 min):
- Students work
- Instructor helps students who get stuck
- Encourage use of `admit()` to narrow down stuck points

**Debrief** (5 min):
- Show solution walkthrough
- Emphasize: How helper lemma was used
- Point out: Where F* needed help vs. where SMT handled things

#### [70-85 min] Week 2 Mini-Project: Verified Merge Sort

**Mini-Project Announcement** (15 min):

"Your biggest challenge yet: Prove merge sort correct!"

**Project Specification:**
```fsharp
module VerifiedMergeSort

// Part 1: Implement merge (combine two sorted lists)
val merge: list int -> list int -> list int

// Part 2: Implement merge_sort
val merge_sort: list int -> list int

// Part 3: Prove merge_sort produces sorted output
val sorted: list int -> bool  // Provided

val merge_sort_sorted: xs:list int ->
  Lemma (sorted (merge_sort xs))

// Part 4 (Extra Credit): Prove merge_sort is a permutation
val permutation: list int -> list int -> bool  // Provided

val merge_sort_perm: xs:list int ->
  Lemma (permutation xs (merge_sort xs))
```

**Requirements**:
- Implement merge and merge_sort (with `decreases` for termination)
- Prove `merge_sort_sorted` (main proof)
- Extra credit: Prove `merge_sort_perm` (harder!)

**Due**: Friday 11:59 PM

**Grading Rubric**: See `rubrics/week_02_mini_project_rubric.md`

**Tips**:
- Start with implementation (get it working first)
- Then add proofs incrementally
- Use helper lemmas liberally!
- `admit()` is your friend while developing

#### [85-90 min] Homework and Week 2 Wrap-Up

**Homework** (5 min):
- Complete Exercise 2.5 (if not finished)
- Start mini-project (at least get merge and merge_sort implemented)
- Read: EXAMPLES.md section on sorting algorithms

**Week 2 Summary**:
- ✅ Totality and termination (`decreases`)
- ✅ Lists and structural recursion
- ✅ Lemmas and inductive proofs
- ✅ Proof decomposition strategies

**Looking Ahead**:
- Week 3: Dependent types (length-indexed vectors)
- Week 4: More advanced induction (well-founded recursion, mutual recursion)
- Midterm: End of Week 4

---

### After Class

**Grading Notes**:
- Exercise 2.5: Most should finish with the provided helper lemma
- Mini-project: This is challenging! Expect wide range of completion levels
- Provide office hours for merge sort help

**Common Errors**:
- Not understanding how to use helper lemmas
- Trying to prove everything in one lemma (not decomposing)
- Confusion about when to use `admit()` vs. when proof is actually complete

---

## Week 2 Wrap-Up

### Key Concepts Covered
- ✅ Total functions with `decreases` clauses
- ✅ Inductive data types (lists, options)
- ✅ Structural recursion patterns
- ✅ Lemmas with `Lemma` type
- ✅ Structural induction proofs
- ✅ Helper lemmas and proof decomposition

### Transition: L1 → L2

**L1 (Novice) Complete**:
Students can now:
- Define and use refinement types
- Leverage SMT for automatic proofs
- Write total functions with termination proofs

**L2 (Apprentice) Started**:
Students are learning:
- Inductive proofs (not just SMT automation)
- Lemma statements and applications
- Proof decomposition strategies

**Next**: Week 3 deepens L2 with dependent types and indexed families.

### Common Misconceptions to Address

**Misconception 1**: "Lemmas are just functions"
- **Reality**: Lemmas are proofs. Type `Lemma P` means "proof of P"
- **Correction**: Emphasize: return value `()` is proof artifact, property is in type

**Misconception 2**: "F* should prove everything automatically"
- **Reality**: SMT has limits. Complex properties need manual proofs.
- **Correction**: Show examples where SMT fails, manual proof succeeds

**Misconception 3**: "Recursive proofs are the same as recursive functions"
- **Reality**: Similar structure, different purpose
- **Correction**: Functions compute values. Proofs establish properties.

**Misconception 4**: "Helper lemmas are 'cheating'"
- **Reality**: Proof decomposition is good engineering!
- **Correction**: Show that complex proofs are built from simple lemmas

### Assessment Checklist

By end of Week 2, students should:
- [ ] Understand why totality matters
- [ ] Can write `decreases` clauses
- [ ] Can define simple recursive functions on lists
- [ ] Can state lemmas about list functions
- [ ] Attempted inductive proofs (even if incomplete)
- [ ] Submitted mini-project (merge sort)

### Looking Ahead to Week 3

**Preview** (mention in Day 6):
- Week 3: Dependent types - types that depend on values!
- Example: Vectors with length in the type
- Example: Safe array indexing (no bounds checks at runtime!)
- Mini-project: Verified binary search with dependent pairs

---

## Troubleshooting Guide

### Termination Issues

**Issue 1: "Could not prove termination"**
- **Diagnosis**: F* can't infer decreasing metric
- **Solution**: Add explicit `decreases` clause
- **Example**:
```fsharp
// Before (fails):
let rec gcd a b = if b = 0 then a else gcd b (a % b)

// After (works):
let rec gcd a b decreases b =
  if b = 0 then a else gcd b (a % b)
```

**Issue 2: Lexicographic ordering errors**
- **Diagnosis**: Multiple arguments, unclear which decreases
- **Solution**: Use `decreases %[m; n]` for lexicographic ordering

### Proof Issues

**Issue 3: "Could not prove post-condition"**
- **Diagnosis**: F* can't prove lemma goal
- **Solution**: Add helper lemmas or intermediate `assert` statements
- **Debug strategy**:
```fsharp
let rec my_proof xs =
  match xs with
  | hd :: tl ->
      my_proof tl;
      admit();  // Temporarily admit to narrow down problem
      ()
```

**Issue 4: "Expected type X, got type Y" in lemma**
- **Diagnosis**: Type mismatch in proof
- **Solution**: Check that lemma statement matches what you're proving

---

## Additional Resources

**For Students**:
- F* tutorial: https://fstar-lang.org/tutorial/ (sections 4-6)
- EXAMPLES.md in this repository (list examples, lines 50-150)
- F* Zulip #beginner-questions

**For Instructors**:
- Software Foundations (Coq): Similar inductive proof pedagogy
- Solutions repository: `instructor_guide/solutions/week_02_all_solutions.fst`
- Week 2 rubric: `instructor_guide/rubrics/week_02_rubric.md`

---

**End of Week 2 Teaching Notes**

Next: `week_03_teaching_notes.md` (Dependent Types and Indexed Families)
