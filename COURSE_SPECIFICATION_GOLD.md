# F* Labs: Gold-Standard Course Specification
## From Novice to Master Formal Verification Engineer

**Version**: 2.0 (Complete Rebuild)
**Target**: Production-quality L1→L6 curriculum
**Timeline**: 24 weeks (2 semesters)
**Expected Effort**: Student 15-20 hours/week
**Status**: COMPLETE SPECIFICATION - Ready for implementation

---

## Executive Summary

This specification defines a **world-class formal verification course** that takes students from zero programming verification experience to industry-ready formal methods engineers capable of verifying real-world systems.

**What Makes This "Gold Standard":**
- ✅ **100+ exercises** with complete solutions
- ✅ **SMT solvers as first-class module** (Week 3, 9 hours of instruction)
- ✅ **Realistic timeline** (24 weeks to L6, not fantasy 12 weeks to L7)
- ✅ **Production systems** (verify real code: parser, allocator, crypto)
- ✅ **Multiple tracks** (academic, industry, research paths)
- ✅ **Field-tested approach** (pilot → iterate → scale)
- ✅ **Complete infrastructure** (auto-grading, CI/CD, video lectures)

**Learning Outcomes:**
- **Week 6**: Build verified data structures (L2 Apprentice)
- **Week 12**: Verify stateful systems with effects (L3 Journeyman)
- **Week 18**: Use proof tactics for complex proofs (L4 Expert)
- **Week 24**: Verify production crypto or parser (L5-L6 Master)

---

## Course Structure

### Semester 1: Foundations (Weeks 1-12, L1→L3)

**Week 1-2: Refinement Types and Type Safety**
- Refinement types, bounds checking, input validation
- 6 exercises, 1 mini-project (validated ETL pipeline)
- **Outcome**: L1 (Novice) - Can write simple refinement types

**Week 3: SMT Solver Foundations** ⭐ NEW DEDICATED MODULE
- How SMT solvers work (DPLL(T), theories)
- F* to SMT encoding, debugging with --log_queries
- Fuel, depth, timeouts, when to give up on automation
- 5 exercises, 1 mini-project (SMT performance profiling)
- **Outcome**: Can debug failing proofs, understand automation limits

**Week 4-5: Totality and Structural Induction**
- Termination proofs, decreases clauses, lexicographic ordering
- Structural induction on lists, trees
- Proof decomposition with helper lemmas
- 8 exercises, 1 mini-project (verified merge sort)
- **Outcome**: L2 start - Can write inductive proofs

**Week 6-7: Dependent Types and Type-Level Computation**
- Indexed families (vectors with length in type)
- GADTs, red-black trees balanced by construction
- Type-level computation and dependent pattern matching
- 10 exercises, 1 mini-project (verified balanced tree)
- **Outcome**: L2 complete - Build verified data structures

**Week 8-9: Effects and Stateful Verification**
- ST monad, heap reasoning, separation logic basics
- Verifying imperative algorithms
- 8 exercises, 1 mini-project (verified hash table)
- **Outcome**: L3 start - Verify stateful code

**Week 10-11: Low* and Memory Safety**
- C extraction, memory layout, bounds checking
- Constant-time verification basics
- 6 exercises, 1 mini-project (verified buffer library)
- **Outcome**: L3 progress - Verify low-level code

**Week 12: Semester 1 Capstone**
- Choose: Verified parser OR Verified allocator OR Verified crypto primitive
- Full specification → implementation → proof → extraction to C
- **Outcome**: L3 complete (Journeyman) - Integrate all techniques

### Semester 2: Advanced Topics (Weeks 13-24, L4→L6)

**Week 13-15: Proof Tactics and Metaprogramming**
- Meta-F* basics, tactic mode vs SMT mode
- Writing custom tactics for domain-specific proofs
- Proof automation strategies
- 10 exercises, 1 mini-project (domain tactic library)
- **Outcome**: L4 start - Automate proof patterns

**Week 16-17: Concurrency Verification**
- Monotonic state, invariants, ghost state
- Verifying concurrent algorithms (lock-free queue)
- 6 exercises, 1 mini-project (verified concurrent data structure)
- **Outcome**: L4 progress - Reason about concurrency

**Week 18-19: Information Flow and Security Properties**
- Noninterference, declassification
- Constant-time verification (crypto code)
- Side-channel resistance
- 6 exercises, 1 mini-project (constant-time comparison functions)
- **Outcome**: L4 complete - Prove security properties

**Week 20-21: Advanced Cryptography Verification**
- Functional correctness of crypto (HACL* case study)
- Memory safety + constant-time + functional spec
- 4 exercises, 1 mini-project (verify crypto primitive - ChaCha20 or Curve25519)
- **Outcome**: L5 start - Verify production crypto

**Week 22-23: Compiler Verification or Advanced Topics**
- **Track A**: Verify simple compiler (expression → assembly)
- **Track B**: Advanced separation logic (Iris-style reasoning)
- **Track C**: Research topic (student choice with advisor approval)
- **Outcome**: L5 progress - Specialized expertise

**Week 24: Final Capstone Project**
- Original verification project (500+ LOC verified)
- Options: Extend HACL*, verify new algorithm, contribute to F* stdlib
- Full documentation, proof engineering write-up
- **Outcome**: L6 (Master) - Production-ready verification engineer

---

## Detailed Module Specifications

### WEEK 3: SMT SOLVER FOUNDATIONS (NEW DEDICATED MODULE) ⭐

**Why This Week Exists:**
Students currently treat SMT as magic, can't debug proofs. This is the #1 cause of frustration in Weeks 2-6. By teaching SMT explicitly, we eliminate cargo-cult coding.

#### Day 7 (Monday): How SMT Solvers Work

**Duration**: 90 minutes
**Prerequisites**: Week 1-2 completed (seen refinement types work "automatically")

**[0-10 min] Motivation: What's Under the Hood**
- Week 1-2 recap: "It just worked! But WHY?"
- Show failing proof from Week 2: reverse_involution
- Question: "Why can't F* prove this automatically?"
- Preview: "Today we learn what F* sends to Z3"

**[10-35 min] SAT Solving and DPLL**
- Boolean satisfiability problem (SAT)
- Example: `(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z)` - is this satisfiable?
- DPLL algorithm (decision, propagation, backtracking)
- Live demo: MiniSat on simple formulas
- **Key insight**: SAT is decidable (guaranteed yes/no answer)

**[35-65 min] From SAT to SMT: Theories**
- Limitation: SAT only handles booleans
- SMT = SAT + Theories (integers, arrays, datatypes)
- **Theory of Linear Integer Arithmetic (LIA)**:
  - Formulas: `2x + 3y ≤ 10`, `x - y = 5`
  - Decidable! Simplex algorithm
  - Example: `type positive = x:int{x > 0}` → LIA formula
- **Theory of Nonlinear Integer Arithmetic (NIA)**:
  - Formulas: `x * y > 10`, `x² + y² = z²`
  - UNDECIDABLE! Z3 uses heuristics (may timeout)
  - Example: `let triple (x:positive) : positive = 3 * x` → NIA (multiplication by variable)
- **Theory of Arrays**:
  - `select(a, i)`, `store(a, i, v)`
  - Used for F* sequences
- **Theory of Datatypes**:
  - Lists, trees, option types
  - Constructor/destructor axioms

**[65-80 min] F* to SMT Translation**
- Show F* code: `type nat = x:int{x >= 0}`
- Show generated SMT-LIB: `(assert (>= x 0))`
- Refinement type → SMT assertion
- Function call → SMT function application
- Pattern matching → SMT ite (if-then-else)

**[80-90 min] Live Demo: --log_queries**
```fsharp
type even = x:int{x % 2 = 0}
let double (n:int) : even = 2 * n  // Might fail!
```
- Run: `fstar.exe --log_queries example.fst`
- Open: `query_*.smt2` file
- Read: What Z3 sees
- Analyze: Why it fails (modulo in NIA)

**Homework**:
- Exercise 3.1: Read SMT-LIB output (identify theories)
- Reading: Z3 guide (theory overview)

---

#### Day 8 (Wednesday): Debugging SMT Failures

**Duration**: 90 minutes
**Prerequisites**: Day 7 (understand theories)

**[0-15 min] Why Proofs Fail: The Three Causes**
1. **Undecidability**: Formula in undecidable theory (NIA, quantifiers)
2. **Timeout**: Decidable but Z3 runs out of time (complex formula)
3. **Fuel Exhaustion**: Recursive function not unfolded enough

**[15-40 min] Fuel and Depth: Controlling Unfolding**
- **Problem**:
  ```fsharp
  let rec factorial (n:nat) : nat =
    if n = 0 then 1 else n * factorial (n - 1)

  let test = assert (factorial 5 = 120)  // TIMEOUT!
  ```
- **Why**: Z3 must unfold `factorial` 5 times
- **Fuel**: How many times to unfold recursive calls
  - Default: fuel = 2 (unfolds twice)
  - `#set-options "--fuel 6"` fixes this
- **ifuel**: Fuel for inductive types (datatypes)
- **z3rlimit**: Timeout in "resource units"
- Live demo: Increase fuel until proof works
- **Warning**: High fuel = exponential blowup (fuel 10 = disaster)

**[40-70 min] The Debug Flags**
- `--debug SMT`: See SMT queries sent to Z3
- `--debug_level Low/Medium/High`: Verbosity
- `--log_queries`: Save SMT-LIB files
- `--log_failing_queries`: Only failed queries
- `--profile`: Time spent per function
- Live demo: Debug a failing proof step-by-step
  1. Run with --debug SMT
  2. Identify which assertion fails
  3. Add intermediate assert to help SMT
  4. Proof succeeds

**[70-85 min] When to Give Up on SMT**
- **SMT can handle**:
  - Linear arithmetic
  - Simple array reasoning
  - Datatype constructors/destructors
  - Boolean logic
- **SMT struggles with**:
  - Nonlinear arithmetic (multiplication by variables)
  - Deep recursion (fuel > 5)
  - Complex quantifiers
  - User-defined recursive functions on inductives
- **Decision tree**:
  1. Try higher fuel (up to 5)
  2. Try adding `assert` hints
  3. If still fails → Write manual proof with lemmas

**[85-90 min] Exercise 3.2 Introduction**
- Given: 5 failing proofs
- Task: Debug each using appropriate technique
- Homework: Complete Exercise 3.2

---

#### Day 9 (Friday): Advanced SMT and Performance

**Duration**: 90 minutes
**Prerequisites**: Day 8 (can debug with flags)

**[0-25 min] Quantifiers and Triggers**
- **Problem**: Lemmas introduce quantifiers
  ```fsharp
  val append_assoc: xs:list a -> ys:list a -> zs:list a ->
    Lemma (append (append xs ys) zs == append xs (append ys zs))
  ```
  SMT sees: `∀xs, ys, zs. append (append xs ys) zs = append xs (append ys zs)`
- **E-matching**: How Z3 instantiates quantifiers
- **Triggers**: Patterns that trigger instantiation
  - Good trigger: `{append (append xs ys) zs}`
  - Bad trigger: `{xs}` (too general, matching storm)
- **Matching loops**: Trigger fires infinitely
- F* picks triggers automatically (usually good)
- Manual override: `[@@ (smt_pat (append xs ys))]`

**[25-50 min] SMT Profiling**
- Run: `fstar.exe --profile file.fst`
- Output: Time per function verification
- Identify: Which function takes 10+ seconds?
- Techniques:
  - Split into smaller lemmas
  - Reduce fuel for fast functions
  - Use `assume` temporarily to isolate bottleneck
  - Consider manual proof (tactics)

**[50-75 min] SMT Patterns and Anti-Patterns**
- **Good Pattern**: Small, focused lemmas
  ```fsharp
  val length_append: xs -> ys -> Lemma (length (xs @ ys) = length xs + length ys)
  ```
- **Anti-Pattern**: Giant lemma with 5 quantifiers
- **Good Pattern**: Explicit type annotations help SMT
  ```fsharp
  let result : nat = compute_something x
  ```
- **Anti-Pattern**: Let SMT infer everything
- **Good Pattern**: `assert` intermediate steps
  ```fsharp
  assert (x > 0);
  assert (x + 1 > 1);  // Help SMT see the chain
  let result = x + 1
  ```

**[75-90 min] Case Study: Optimizing Slow Proof**
- Provided: Proof that takes 30 seconds
- Live debugging:
  1. `--profile` → Find slow function
  2. `--log_queries` → See massive SMT query
  3. Refactor: Split into 3 lemmas
  4. Result: 2 seconds total
- Takeaway: Proof engineering = SMT performance tuning

**Homework**:
- Exercise 3.3: Optimize slow verification
- Mini-project: SMT performance profiling report

---

### Week 3 Exercises

**Exercise 3.1: Reading SMT-LIB** (45 minutes)
```fsharp
module Exercise3_1
type even = x:int{x % 2 = 0}
type positive = x:int{x > 0}
type bounded = x:int{0 <= x && x < 100}

let test1 : even = 4
let test2 : positive = 10
let test3 : bounded = 50

// TASK: Run with --log_queries
// For each type, identify:
// 1. Which SMT theory is used?
// 2. What SMT formula represents the refinement?
// 3. Does Z3 use LIA or NIA?
```

**Exercise 3.2: Debugging Toolkit** (90 minutes)
```fsharp
// Given: 5 failing proofs
// Use appropriate debugging technique for each

// PROOF 1: Fuel issue
let rec sum (xs:list nat) : nat = match xs with
  | [] -> 0
  | hd::tl -> hd + sum tl
let test1 = assert (sum [1;2;3;4;5] = 15)  // TIMES OUT

// PROOF 2: NIA issue
type positive = x:int{x > 0}
let triple (x:positive) : positive = 3 * x  // FAILS

// PROOF 3: Needs assert hint
let complex_calc (x:nat) : y:nat{y >= x} =
  let a = x + 1 in
  let b = a + 2 in
  b  // FAILS to prove b >= x

// PROOF 4: Fundamentally needs lemma
let rec append (#a:Type) (xs ys:list a) : list a = match xs with
  | [] -> ys
  | hd::tl -> hd :: append tl ys
let test4 (xs ys zs:list int) =
  assert (append (append xs ys) zs == append xs (append ys zs))  // FAILS

// PROOF 5: Z3 timeout (complex formula)
// [Provided: Nested quantifiers example]

// TASK: Fix each with minimal changes, explain why it failed
```

**Exercise 3.3: LIA vs NIA Boundary** (60 minutes)
```fsharp
// Classify each formula: LIA (decidable) or NIA (undecidable)?
// Then verify your classification empirically

let ex1 (x y:int) : z:int{z > x + y} = x + y + 1  // ?
let ex2 (x:nat) : y:nat{y > 2*x} = 2*x + 1  // ?
let ex3 (x y:nat{y <> 0}) : z:nat{z*y >= x} = x / y  // ?
let ex4 (x:nat) : y:nat{y = x*x + 2*x + 1} = (x+1)*(x+1)  // ?

// TASK A: Predict LIA or NIA for each
// TASK B: Run F* and see which actually verify
// TASK C: For failures, fix with minimal assertions
```

**Exercise 3.4: Fuel Minimization** (60 minutes)
```fsharp
let rec fibonacci (n:nat) : nat =
  if n <= 1 then n else fibonacci (n-1) + fibonacci (n-2)

// These assertions need different fuel levels
let test1 = assert (fibonacci 3 = 2)   // Fuel needed: ?
let test2 = assert (fibonacci 5 = 5)   // Fuel needed: ?
let test3 = assert (fibonacci 7 = 13)  // Fuel needed: ?
let test4 = assert (fibonacci 10 = 55) // Fuel needed: ?

// TASK A: Find minimum fuel for each
// TASK B: Explain the pattern
// TASK C: At what N does fuel become impractical?
// TASK D: How would you verify fibonacci for arbitrary N?
```

**Exercise 3.5: SMT Pattern Engineering** (90 minutes)
```fsharp
// Given: Slow verification (10+ seconds)
let rec map (#a #b:Type) (f:a -> b) (xs:list a) : list b =
  match xs with | [] -> [] | hd::tl -> f hd :: map f tl

let rec filter (#a:Type) (p:a -> bool) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd::tl -> if p hd then hd :: filter p tl else filter p tl

// SLOW PROOF (times out):
val map_filter_fusion: #a:Type -> #b:Type -> f:(a -> b) -> p:(b -> bool) -> xs:list a ->
  Lemma (filter p (map f xs) == map f (filter (fun x -> p (f x)) xs))

let rec map_filter_fusion #a #b f p xs = match xs with
  | [] -> ()
  | hd::tl -> map_filter_fusion f p tl  // Takes 10+ seconds!

// TASK A: Profile with --profile
// TASK B: Add intermediate lemmas to speed up
// TASK C: Achieve <2 second verification
// TASK D: Explain what made it slow
```

**Mini-Project 3: SMT Performance Report** (3-4 hours)

**Scenario**: You've inherited a verified codebase with slow verification times (45 seconds for full project). Management wants <10 seconds for CI/CD integration.

**Provided**:
- Codebase: 500 LOC F* code (verified binary search tree with operations)
- Current verification: 45 seconds
- Problem areas marked with TODO comments

**Task**:
1. **Profile** (30 min):
   - Use `--profile` to identify slow functions
   - Use `--log_queries` to find large SMT queries
   - Create performance report table

2. **Optimize** (2 hours):
   - Apply techniques from Week 3
   - Reduce fuel where safe
   - Split large lemmas
   - Add strategic `assert` hints
   - Target: <10 seconds total

3. **Document** (1 hour):
   - Write report explaining:
     - What was slow and why
     - What optimizations were applied
     - Performance before/after (table)
     - Any trade-offs made
   - Include: SMT theory analysis (which parts LIA vs NIA)

4. **Validate**:
   - All proofs still verify
   - No additional `admit()` used
   - Verification time measured 3 times (average)

**Deliverable**: Git repo + PDF report + 5-min presentation

**Grading** (40 points):
- Achieves <10s (15 pts)
- Correct optimizations (10 pts)
- Clear report (10 pts)
- Presentation (5 pts)

---

### WEEK 4-5: TOTALITY AND STRUCTURAL INDUCTION (Enhanced)

**Changes from current Week 2:**
- **Add bridge exercises** between Week 3 (SMT) and induction
- **Gentler difficulty ramp** (no "graduate-level" spike)
- **SMT integration**: Students now understand why manual proofs needed

#### Week 4 Day 10: Termination Proofs

**[0-20 min] From SMT to Manual Proofs**
- Recap Week 3: SMT can't prove properties of recursive functions
- Today: Prove termination (totality)
- Why F* cares: Non-terminating functions break soundness

**[20-45 min] The decreases Clause**
```fsharp
let rec factorial (n:nat) : nat
  decreases n  // THIS IS NEW
= if n = 0 then 1 else n * factorial (n - 1)
```
- `decreases n`: Prove n gets smaller each call
- F* checks: `n - 1 < n` when we recurse
- Termination metric can be any well-founded order

**[45-70 min] Structural Recursion on Lists**
```fsharp
let rec length (#a:Type) (xs:list a) : nat
  decreases xs  // Structurally smaller
= match xs with
  | [] -> 0
  | hd::tl -> 1 + length tl  // tl is smaller than hd::tl
```
- F* knows `tl` is structurally smaller than `hd::tl`
- Datatypes have built-in well-founded order

**[70-90 min] Exercise 4.1: Basic Termination**
- Fibonacci with decreases
- Sum of list with decreases
- Multiple base cases

**Homework**: Complete Exercise 4.1, read on lexicographic ordering

---

#### Week 4 Day 11: Lexicographic Ordering

**[0-15 min] When One Metric Isn't Enough**
- Problem: Ackermann function recurses on (m-1, 1) and (m, n-1)
- Can't just use `m` (sometimes increases)
- Can't just use `n` (sometimes increases)
- Need: Combination of both

**[15-45 min] Lexicographic Tuples**
```fsharp
let rec ackermann (m:nat) (n:nat) : nat
  decreases %[m; n]  // Lexicographic ordering
= if m = 0 then n + 1
  else if n = 0 then ackermann (m-1) 1     // m decreases (primary)
  else ackermann (m-1) (ackermann m (n-1)) // n decreases (when m same)
```
- `%[m; n]`: Tuple ordered lexicographically
- Check: (m', n') < (m, n) if m' < m OR (m' = m AND n' < n)

**[45-75 min] Exercise 4.2: McCarthy 91**
- Prove termination with lexicographic metric
- Understand non-obvious termination

**[75-90 min] Advanced: Custom Metrics**
- Can use any well-founded order
- Example: Tree height for tree recursion
- Example: Difference metric for divide-and-conquer

---

#### Week 4 Day 12: Bridge to Induction

**NEW LECTURE** (bridges SMT week to induction week)

**[0-20 min] From SMT to Induction: Why the Gap?**
- Week 3: SMT proves `2 + 2 = 4` automatically
- Today: SMT can't prove `reverse (reverse xs) = xs`
- Why: Property over ALL lists (infinite)
- SMT is good at: Specific instances, arithmetic, boolean logic
- SMT struggles with: Properties over recursive types, induction

**[20-50 min] What IS Induction?**
- Mathematical induction recap
- Structural induction on datatypes
- The inductive hypothesis (IH)
- Base case + inductive case = proof for ALL values

**[50-75 min] Your First Inductive Proof**
```fsharp
// Prove: appending empty list does nothing
val append_nil: #a:Type -> xs:list a -> Lemma (append xs [] == xs)

let rec append_nil #a xs =
  match xs with
  | [] -> ()  // Base: append [] [] = [] ✓
  | hd::tl ->  // Inductive: append (hd::tl) [] = hd::tl
      append_nil tl;  // IH: append tl [] = tl
      // Now F* can prove: hd :: (append tl []) = hd :: tl
      ()
```
- Structure: match, base case, recursive call (apply IH)
- The `()` is the proof!

**[75-90 min] Exercise 4.3: Warmup Inductive Proofs**
- Prove `length (xs @ ys) = length xs + length ys`
- Prove `reverse [x] = [x]`
- Prove `sum (xs @ ys) = sum xs + sum ys`

**Homework**: Complete Exercise 4.3 (easier than Week 2's Exercise 2.3!)

---

#### Week 5 Day 13: Helper Lemmas

**[0-20 min] When Direct Proof Fails**
- Try to prove `reverse (reverse xs) = xs` directly
- F* error: "Could not prove post-condition"
- SMT doesn't know how `reverse` and `append` interact
- Solution: Helper lemmas

**[20-50 min] Proof Decomposition Strategy**
1. Try direct proof
2. Look at error: "Could not prove X"
3. Ask: "What would let me prove X?"
4. That's your helper lemma
5. Prove helper separately
6. Use helper in main proof

**[50-80 min] Example: Reverse Involution**
```fsharp
// Helper 1: How reverse distributes over append
val reverse_append: xs -> ys ->
  Lemma (reverse (xs @ ys) == reverse ys @ reverse xs)

let rec reverse_append xs ys = match xs with
  | [] -> ()
  | hd::tl -> reverse_append tl ys; ()

// Helper 2: Reverse of singleton
val reverse_singleton: x -> Lemma (reverse [x] == [x])
let reverse_singleton x = ()  // Trivial!

// Main proof NOW WORKS
val reverse_reverse: xs -> Lemma (reverse (reverse xs) == xs)
let rec reverse_reverse xs = match xs with
  | [] -> ()
  | hd::tl ->
      reverse_reverse tl;         // IH
      reverse_append (reverse tl) [hd];  // Helper 1
      reverse_singleton hd;       // Helper 2
      ()  // F* proves the goal!
```

**[80-90 min] Exercise 5.1: Guided Helper Lemmas**
- Prove `map f (xs @ ys) = map f xs @ map f ys`
- We provide skeleton of helper lemmas
- Student fills in proofs

---

#### Week 5 Day 14: Proof Engineering

**[0-30 min] Multiple Proof Strategies**
- Direct induction vs. mutual induction
- Strong induction vs. simple induction
- Induction on multiple variables
- When to generalize before proving

**[30-60 min] Case Study: Flatten Associativity**
```fsharp
let rec flatten (xss:list (list a)) : list a = match xss with
  | [] -> []
  | xs::xss' -> xs @ flatten xss'

// Prove: flatten (xss @ yss) = flatten xss @ flatten yss
// Strategy: Need helper about append associativity
```

**[60-80 min] Exercise 5.2: Self-Guided Proof**
- No skeleton provided
- Student must discover needed helpers
- Reflection: Explain proof strategy

**[80-90 min] Preview Week 6: Dependent Types**

---

### Week 4-5 Complete Exercise List (8 exercises + 1 mini-project)

1. **Exercise 4.1**: Basic termination (3 functions, 45 min)
2. **Exercise 4.2**: McCarthy 91 lexicographic (90 min)
3. **Exercise 4.3**: Warmup induction (3 easy proofs, 60 min)
4. **Exercise 4.4**: Map preserves length (45 min)
5. **Exercise 5.1**: Guided helper lemmas - map fusion (60 min)
6. **Exercise 5.2**: Self-guided proof - flatten append (90 min)
7. **Exercise 5.3**: Tree induction (60 min, NEW)
8. **Exercise 5.4**: Strong induction (90 min, NEW)
9. **Mini-Project**: Verified merge sort with full proof (no admits allowed, 4 hours)

**Difficulty progression**: Smooth ramp, no "graduate-level" spike

---

## WEEKS 6-24 SPECIFICATIONS

### Week 6-7: Dependent Types

**Day 15-17**: Vectors, indexed families, GADTs
**Day 18-20**: Red-black trees, type-level balancing
**Day 21**: Mini-project: Verified balanced search tree

**Exercises** (10 total):
- 6.1: Vector append preserves length (30 min)
- 6.2: Safe vector indexing (45 min)
- 6.3: Vector map with length proof (60 min)
- 6.4: Zip vectors of equal length (60 min)
- 7.1: Red node property (90 min)
- 7.2: Black height invariant (90 min)
- 7.3: Insert preserves RB properties (120 min)
- 7.4: Delete preserves balance (150 min, challenging)
- 7.5: RB tree theorem (120 min)
- Mini-project: Generic balanced tree (5 hours)

**Learning outcome**: L2 complete (Apprentice)

---

### Week 8-9: Effects and State

**Day 22-24**: ST monad, heap, references
**Day 25-27**: Verifying imperative algorithms
**Day 28**: Mini-project: Verified hash table

**Exercises** (8 total):
- 8.1: Stateful counter (45 min)
- 8.2: Swapping references (60 min)
- 8.3: Array operations (90 min)
- 8.4: In-place reverse (90 min)
- 9.1: Hash table insert (120 min)
- 9.2: Hash table lookup (90 min)
- 9.3: Hash table invariants (150 min)
- 9.4: Resizing with proof (180 min)
- Mini-project: Verified hash table (6 hours)

**Learning outcome**: L3 start (Journeyman)

---

### Week 10-11: Low* and Memory Safety

**Day 29-31**: C extraction, memory layout, buffers
**Day 32-33**: Constant-time verification basics
**Day 34**: Mini-project: Verified buffer library

**Exercises** (6 total):
- 10.1: Safe buffer indexing (90 min)
- 10.2: Buffer copy verification (120 min)
- 10.3: Constant-time comparison (90 min)
- 11.1: Memory-safe memcpy (150 min)
- 11.2: Bounds checking elimination (120 min)
- 11.3: Stack vs heap allocation (90 min)
- Mini-project: Verified bounded buffer (5 hours)

**Learning outcome**: L3 progress

---

### Week 12: Semester 1 Capstone

**Choose ONE**:
1. **Verified Parser**: JSON or CSV parser with full spec
2. **Verified Allocator**: Memory allocator with safety proofs
3. **Verified Crypto Primitive**: Simple cipher (e.g., XOR cipher, ROT13 → AES-CTR)

**Requirements**:
- Full specification (what it should do)
- Implementation (500+ LOC)
- Correctness proof (functional spec)
- Safety proof (memory safety, termination)
- Extraction to C
- Test suite
- Documentation

**Deliverable**: Git repo + 10-min presentation + written report

**Grading**: 100 points (20% of semester grade)

**Learning outcome**: L3 complete (Journeyman)

---

### Weeks 13-24: Semester 2 (L4→L6)

**Week 13-15**: Proof tactics, metaprogramming (L4 start)
**Week 16-17**: Concurrency verification (L4 progress)
**Week 18-19**: Security properties, information flow (L4 complete)
**Week 20-21**: Advanced cryptography (HACL*) (L5 start)
**Week 22-23**: Compiler verification OR advanced topics (L5 progress)
**Week 24**: Final capstone - production project (L6 Master)

**Total Semester 2**: 50+ exercises, 6 mini-projects, 1 final capstone

---

## Exercise Design Principles

Every exercise must:
1. ✅ **Build on prior knowledge** (progressive difficulty)
2. ✅ **Have clear learning objective** (stated explicitly)
3. ✅ **Include reflection questions** (graded, force conceptual understanding)
4. ✅ **Provide starter code** (clear TODOs, not blank file)
5. ✅ **Have complete solution** (with pedagogical notes)
6. ✅ **Include test cases** (students can check their work)
7. ✅ **Estimate time** (validated through pilots)
8. ✅ **Real-world relevance** (or clearly marked as "theoretical warmup")

**Anti-patterns to avoid**:
- ❌ No `admit()` crutches (forces completion)
- ❌ No "too hard, skip it" exercises (every exercise completable)
- ❌ No exercises requiring undocumented tricks
- ❌ No exercises that don't F*-typecheck

---

## Assessment Structure

### Grading Breakdown (Per Semester)

**Exercises** (40%):
- Weekly exercises (24 weeks × 1.5% = 36%)
- Completion + correctness + reflection

**Mini-Projects** (30%):
- 11 mini-projects × 2.5% = 27.5%
- Integration exercises

**Midterm Capstone** (15%):
- Week 12 capstone

**Final Capstone** (15%):
- Week 24 capstone

**Total**: 100%

### Grading Rubrics

**Exercise Grading** (per exercise):
- **Code Correctness** (60%): Typechecks, passes tests, no admits
- **Proof Quality** (20%): Clear structure, good lemma decomposition
- **Reflection Answers** (20%): Demonstrates understanding

**Mini-Project Grading**:
- **Specification** (10%): Clear, complete
- **Implementation** (30%): Correct, clean
- **Proofs** (40%): Complete, no admits, good engineering
- **Documentation** (10%): Clear explanations
- **Presentation** (10%): Effective communication

---

## Infrastructure Requirements

### Auto-Grading System

**Must support**:
- F* typecheck validation
- Test case execution
- Plagiarism detection (MOSS)
- Partial credit for incomplete proofs
- Reflection question grading (manual + rubric)

**Technology**: GitHub Classroom + GitHub Actions
- Student pushes to private repo
- CI runs F* verification
- Outputs: Passed/Failed + error messages
- TA reviews reflection questions

### Continuous Integration

**On every commit to course repo**:
```yaml
- Verify all solution files typecheck
- Run all test suites
- Check for broken links in docs
- Build course website
- Generate exercise PDFs
```

**Quality gate**: 100% solution verification before releasing week

### Video Lecture Production

**Format**:
- 3 lectures per week × 24 weeks = 72 lectures
- Each lecture: 90 min → Edit to 60-75 min video
- Include: Live coding, demos, student Q&A

**Production**:
- Record live lectures
- Professional editing
- Captions/subtitles
- Hosted on: YouTube (public) + university LMS

### Course Website

**Public site** (marketing + Week 1-3 free):
- Course overview
- Syllabus
- Sample lectures
- Exercise 1.1-1.2 (try before enrolling)

**Student portal** (LMS):
- All lectures
- All exercises
- Auto-grader submission
- Discussion forum
- Office hours schedule

---

## Piloting and Iteration

### Pilot 1: Weeks 1-3 (5 students)

**Timeline**: 3 weeks
**Focus**: SMT module validation

**Metrics**:
- Can students debug SMT failures by Week 3 end?
- Time estimates accurate?
- SMT module too hard/easy?

**Iteration**: Adjust SMT difficulty, add/remove exercises

### Pilot 2: Weeks 1-6 (10 students)

**Timeline**: 6 weeks
**Focus**: Validate L1→L2 progression

**Metrics**:
- Completion rate
- Student satisfaction (weekly surveys)
- Time spent per week (track actual vs estimated)
- Difficulty ratings per exercise

**Iteration**: Adjust difficulty curve, add bridge exercises

### Pilot 3: Full Semester 1 (30 students)

**Timeline**: 12 weeks
**Focus**: Scale testing, TA workload

**Metrics**:
- Capstone quality
- TA hours per week
- Auto-grader effectiveness
- Student outcomes (can they verify real code?)

**Iteration**: Optimize grading, refine capstone specs

### Full Release: Semester 1 + 2 (100+ students)

**Timeline**: 24 weeks
**With**: 3-5 TAs, professor, infrastructure team

---

## Success Metrics

### Student Outcomes

**By Week 12** (End Semester 1):
- ✅ 80%+ students reach L3 (Journeyman)
- ✅ Completion rate ≥70%
- ✅ Average satisfaction ≥4.0/5.0
- ✅ Capstone projects: 90%+ functional, 70%+ fully verified

**By Week 24** (End Semester 2):
- ✅ 70%+ students reach L5 (Master)
- ✅ 20%+ students reach L6 (Grandmaster)
- ✅ Completion rate ≥60%
- ✅ Final capstone: Production-quality code

### Industry Outcomes

**Within 6 months of graduation**:
- ✅ 50%+ employed in formal methods roles
- ✅ 80%+ feel prepared for verification work
- ✅ Employer satisfaction ≥4.5/5.0

**Companies hiring graduates**:
- Microsoft (HACL*, F* team)
- Amazon (Automated Reasoning Group)
- Galois
- Bedrock Systems
- Ethereum Foundation

---

## Implementation Timeline

### Phase 1: Core Curriculum (Months 1-6)

**Month 1-2**: Build Weeks 1-6
- Polish existing Weeks 1-2 (50 hours)
- Build Week 3: SMT module (60 hours)
- Build Weeks 4-5: Enhanced induction (80 hours)
- Build Weeks 6-7: Dependent types (100 hours)

**Month 3-4**: Build Weeks 7-12
- Weeks 8-9: Effects (100 hours)
- Weeks 10-11: Low* (80 hours)
- Week 12: Capstone specs (40 hours)

**Month 5**: Infrastructure
- Auto-grader (60 hours)
- CI/CD (40 hours)
- Course website (40 hours)

**Month 6**: Pilot 1-2
- Run pilots
- Iterate based on feedback

**Deliverable**: Production Semester 1 (Weeks 1-12)

### Phase 2: Advanced Content (Months 7-12)

**Month 7-8**: Build Weeks 13-18
- Tactics (100 hours)
- Concurrency (80 hours)
- Security (80 hours)

**Month 9-10**: Build Weeks 19-24
- Cryptography (100 hours)
- Compiler/advanced (100 hours)
- Final capstone (60 hours)

**Month 11**: Video production
- Record all lectures (80 hours)
- Edit videos (100 hours)

**Month 12**: Pilot 3 + polish

**Deliverable**: Complete 24-week course

### Phase 3: Scale and Sustain (Ongoing)

**Semester 1**: Teach Semester 1 (100 students)
**Semester 2**: Teach Semester 2 (80 students, some drop)
**Year 2+**: Iterate, update F* versions, add research topics

---

## Resource Requirements

### Personnel

**Core team**:
- 1 Lead instructor (PhD in formal methods) - 20 hours/week
- 1 Instructional designer - 10 hours/week (Months 1-6)
- 1 Infrastructure engineer - 15 hours/week (Months 1-3)
- 1 Video editor - 20 hours/week (Month 11)

**TAs** (during teaching):
- Semester 1: 3 TAs × 15 hours/week
- Semester 2: 2 TAs × 15 hours/week

### Budget

**Development** (Phases 1-2):
- Instructor: $50k (600 hours × $80/hr)
- Infrastructure: $15k (200 hours × $75/hr)
- Video production: $20k
- **Total**: $85k

**Per-semester operating**:
- Instructor: $15k (1 semester)
- TAs: $25k (3-5 TAs)
- Infrastructure: $2k (hosting, tools)
- **Total**: $42k/semester

### Technology Stack

**Required**:
- F* compiler + Z3 (free, open-source)
- GitHub (education plan, free)
- GitHub Classroom (free)
- Video hosting: YouTube (free) or Vimeo ($$)

**Optional**:
- Gradescope (auto-grading, $$$)
- Zoom (live lectures, $ if university doesn't provide)
- Slack/Discord (student forum, free)

---

## Risk Assessment

### High Risk

**Risk 1: F* compiler bugs break exercises**
- Probability: 40%
- Impact: High (students blocked)
- Mitigation: Pin F* version, have workarounds documented
- Contingency: Update exercises when F* updates

**Risk 2: Insufficient TA capacity**
- Probability: 60%
- Impact: High (grading delays)
- Mitigation: Heavy auto-grading, clear rubrics
- Contingency: Hire more TAs or reduce enrollment

**Risk 3: Students lack prerequisites**
- Probability: 50%
- Impact: Medium (high dropout)
- Mitigation: Diagnostic test, prerequisite enforcement
- Contingency: Offer "catch-up" boot camp (Week 0)

### Medium Risk

**Risk 4: SMT module too hard/boring**
- Probability: 30%
- Impact: Medium (students disengage)
- Mitigation: Pilot testing (5 students first)
- Contingency: Simplify or make optional

**Risk 5: Capstone projects too ambitious**
- Probability: 50%
- Impact: Medium (students struggle, use admits)
- Mitigation: Provide multiple difficulty tiers
- Contingency: Allow group projects (2 students max)

---

## Differentiation from Competitors

### vs. Software Foundations (Coq)

**Advantages**:
- ✅ More modern (SMT automation vs pure tactics)
- ✅ Security focus (crypto, constant-time)
- ✅ Production extraction (C, not just OCaml)
- ✅ Smaller learning curve (SMT helps beginners)

**Disadvantages**:
- ❌ Less mature (SF battle-tested for 15+ years)
- ❌ Smaller ecosystem (Coq has more libraries)
- ❌ Less PL theory (SF covers more foundations)

**Target audience**: Security engineers, crypto developers, systems programmers

### vs. CMU 15-414 (Bug Catching)

**Advantages**:
- ✅ Deeper on proof (15-414 surveys many tools)
- ✅ Full-semester dedicated to one tool (mastery)
- ✅ Production focus (extract real code)

**Disadvantages**:
- ❌ Narrower (no model checking, no symbolic execution)
- ❌ Less tool diversity

**Target audience**: Students wanting deep F* expertise, not tool survey

### vs. F* Official Tutorial

**Advantages**:
- ✅ Pedagogical structure (tutorial is reference)
- ✅ Exercises with solutions
- ✅ Classroom-tested
- ✅ Instructor support

**Disadvantages**:
- ❌ Duplicates effort (tutorial already exists)

**Mitigation**: Contribute exercises back to F* community

---

## Open Questions for Discussion

1. **Should we target universities or industry training?**
   - Universities: Semester pace, academic rigor
   - Industry: 2-week intensive, practical focus

2. **24 weeks too long?**
   - Alternative: 12 weeks to L4, then optional 12-week extension

3. **Should cryptography be required or elective?**
   - Not all students want crypto focus
   - But it's our unique strength

4. **Grading: Auto vs manual?**
   - Auto: Scales, fast feedback
   - Manual: Better learning, more expensive

5. **Open-source immediately or after pilot?**
   - Immediate: Community feedback
   - After pilot: Polish first

---

## Next Steps

### Immediate (This Week)

1. **Install F* toolchain** (8 hours)
2. **Verify existing Week 1-2 solutions** (16 hours)
3. **Draft Week 3 Day 7 teaching notes** (8 hours)

**Total**: 32 hours

### Short Term (Month 1)

1. **Complete Week 3 module** (60 hours)
   - 3 lecture notes
   - 5 exercises with solutions
   - Mini-project
2. **Revise Weeks 1-2** based on this spec (40 hours)
3. **Build auto-grader MVP** (40 hours)

**Total**: 140 hours

### Medium Term (Months 2-6)

1. **Build Weeks 4-12** (500 hours)
2. **Run pilots** (100 hours)
3. **Iterate based on feedback** (100 hours)

**Total**: 700 hours

### Long Term (Months 7-12)

1. **Build Weeks 13-24** (500 hours)
2. **Video production** (180 hours)
3. **Public launch** (100 hours)

**Total**: 780 hours

**GRAND TOTAL**: 1,652 hours (10-12 months at 30-40 hours/week)

---

## Approval and Sign-Off

This specification defines a **2,000+ hour, 12-month development project** to create a world-class formal verification course.

**Key decisions needed**:
- [ ] Approve 24-week timeline (vs 12-week)
- [ ] Approve SMT as dedicated module (Week 3)
- [ ] Approve budget ($85k development + $42k/semester)
- [ ] Approve piloting approach (3 phases)
- [ ] Approve L1→L6 scope (not L7)

**Signed**:
- Course Developer: ________________
- Department Chair: ________________
- Budget Approver: ________________

**Date**: ________________

---

**END OF SPECIFICATION**

**This is the GOLD STANDARD.**
**Now we build it.**
