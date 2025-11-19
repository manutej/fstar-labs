# Week 3 Teaching Notes: SMT Solver Foundations
## Understanding Automatic Proofs in F*

**Level**: L1 → L2 Transition (Novice to Apprentice)
**Duration**: 3 lectures × 90 minutes = 270 minutes
**Prerequisites**: Week 1-2 (Refinement types, basic F* syntax)

---

## Week Overview

**Big Idea**: Students must understand SMT solvers to effectively use F*. Week 1-2 made SMT look like "magic" - now we demystify it.

**Learning Objectives**:
By the end of Week 3, students will be able to:
1. **Explain** how SMT solvers decide formulas (DPLL(T) algorithm basics)
2. **Identify** which SMT theory a formula belongs to (LIA, NIA, arrays, datatypes)
3. **Use** `--log_queries` to inspect what F* sends to Z3
4. **Debug** failing proofs using fuel, depth, and --debug flags
5. **Decide** when to add assertions vs. write manual proofs vs. restructure code
6. **Profile** SMT performance and optimize slow verifications

**Why This Week Matters**:
- Week 2 students hit walls: "Why doesn't this prove automatically?"
- Without SMT knowledge, students cargo-cult patterns without understanding
- SMT debugging is a **core skill** for formal verification engineers
- Every major verification tool uses SMT (Dafny, Boogie, Why3, Prusti)

---

## Pre-Week Preparation (for Instructor)

### Essential Setup

1. **Install SMT-LIB tools** (optional but helpful):
   ```bash
   # MiniSat (for SAT demos)
   apt-get install minisat

   # Standalone Z3
   wget https://github.com/Z3Prover/z3/releases/...
   ```

2. **Prepare live demo files**:
   - `demos/sat_example.cnf` - Simple SAT formula
   - `demos/smt_lia_example.smt2` - LIA formula
   - `demos/smt_nia_example.smt2` - NIA formula (fails)

3. **Test all examples** from teaching notes:
   - Ensure they demonstrate the intended behavior
   - Have backup examples if live coding goes wrong

4. **Review Z3 documentation**:
   - https://microsoft.github.io/z3/doc/
   - SMT-LIB standard: http://smtlib.cs.uiowa.edu/

### Common Student Struggles (Be Prepared For)

**Struggle 1: "I don't care about theory, just show me how to fix my proof"**
- **Response**: Understanding WHY helps you fix it faster
- **Strategy**: Start with practical debugging (Day 8), circle back to theory

**Struggle 2: "This is too low-level, I thought F* was high-level"**
- **Response**: F* IS high-level, but understanding the engine makes you a better driver
- **Analogy**: You don't need to rebuild an engine, but knowing how it works helps when it breaks

**Struggle 3: "My proof still doesn't work after everything we learned"**
- **Response**: Some proofs fundamentally need manual work (Week 4-5 on induction)
- **Strategy**: Show that it's not failure - it's knowing when to switch strategies

### Materials to Bring

- Whiteboard markers (draw DPLL search tree)
- Laptop with projector (live coding)
- Backup slides (in case live demo fails)
- Printed SMT-LIB cheat sheet (handout)

---

## Day 7 (Monday): How SMT Solvers Work

**Duration**: 90 minutes
**Goal**: Demystify SMT - students understand what happens when F* "proves" something

### [0-10 min] Motivation: Pulling Back the Curtain

**Hook**: "Week 1-2, things either worked or didn't. Today we learn WHY."

**Show this code** (from Week 2, Exercise 2.3):
```fsharp
let rec reverse (#a:Type) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]

// This proof fails:
let rec reverse_reverse xs =
  match xs with
  | [] -> ()
  | hd :: tl -> reverse_reverse tl; ()
  // ERROR: "Could not prove post-condition"
```

**Ask**: "Why can't F* prove this? It's obviously true!"

**Poll** (show of hands):
- Who thinks F* is being dumb? (Many hands)
- Who thinks we're missing something? (Some hands)
- Who has no idea? (Honest hands)

**Preview**: "By Friday, you'll know exactly why this fails and how to fix it."

---

### [10-35 min] SAT Solving: The Foundation

**Transition**: "SMT is built on SAT. Let's start with pure boolean logic."

#### The Boolean Satisfiability Problem (SAT)

**Definition**: Given a boolean formula, is there an assignment of true/false to variables that makes it true?

**Example 1** (satisfiable):
```
(x OR y) AND (NOT x OR z)
```

**Live demo**: Find a satisfying assignment
- Try x=true, y=true, z=true → works!
- Formula is SAT (satisfiable)

**Example 2** (unsatisfiable):
```
(x OR y) AND (NOT x OR NOT y) AND (NOT x OR y) AND (x OR NOT y)
```

**Challenge students**: "Can you find values for x, y that satisfy this?"
- Give 2 minutes to try
- Reveal: It's UNSAT (unsatisfiable) - no assignment works

**Key insight**: SAT solvers answer "Is there a solution?" in finite time.

#### The DPLL Algorithm

**Whiteboard**: Draw a search tree

```
Initial: (x OR y) AND (NOT x OR z)

Try x = true:
  (true OR y) AND (NOT true OR z)
  = true AND (false OR z)
  = true AND z
  = z must be true
  → Solution: x=true, z=true (y can be anything)
```

**Steps**:
1. **Pick a variable** (e.g., x)
2. **Try x=true**, simplify formula
3. **Propagate** (unit clause rule)
4. **Repeat** or **backtrack** if contradiction
5. **Report** SAT (if found) or UNSAT (if all paths fail)

**Show with MiniSat** (if installed):
```bash
# Create file: example.cnf
echo "p cnf 3 2" > example.cnf
echo "1 2 0" >> example.cnf  # (x1 OR x2)
echo "-1 3 0" >> example.cnf # (NOT x1 OR x3)

minisat example.cnf
# Output: SATISFIABLE
#         x1=TRUE x2=TRUE x3=TRUE
```

**Key Takeaway**: SAT is decidable - guaranteed answer (but may take exponential time).

---

### [35-65 min] From SAT to SMT: Adding Theories

**Transition**: "SAT only handles true/false. What about numbers, lists, arrays?"

#### Limitation of SAT

**Problem**: Express "2x + 3y ≤ 10" in pure boolean logic?
- Could encode integers in binary (x = x₀ + 2x₁ + 4x₂ + ...)
- But: Exponential blowup, loses structure

**Solution**: SMT = SAT + Theories (Satisfiability Modulo Theories)

#### Theory of Linear Integer Arithmetic (LIA)

**Formulas**:
- Atoms: `2x + 3y ≤ 10`, `x - y = 5`, `x ≥ 0`
- Connectives: AND, OR, NOT
- Example: `(x ≥ 0) AND (y ≥ 0) AND (x + y ≤ 10)`

**Key Property**: LIA is **DECIDABLE**
- Z3 can always say SAT or UNSAT
- Uses Simplex algorithm (from linear programming)

**F* Example**:
```fsharp
type nat = x:int{x >= 0}  // LIA formula: x >= 0
type bounded = x:int{0 <= x && x < 100}  // LIA: two inequalities

let test : nat = 5  // Z3 proves: 5 >= 0 (easy in LIA)
```

**What Z3 sees** (simplified):
```smt2
(declare-const x Int)
(assert (>= x 0))    ; nat constraint
(assert (= x 5))     ; assignment
(check-sat)          ; Z3 answers: sat
```

#### Theory of Nonlinear Integer Arithmetic (NIA)

**Formulas**:
- Atoms: `x * y > 10`, `x² + y² = z²`, `x = y * z`
- Example: `x > 0 AND x * y > 0`

**Key Property**: NIA is **UNDECIDABLE**
- Z3 uses heuristics (may timeout or say "unknown")
- Multiplication by variables = nonlinear
- No guarantee of termination

**F* Example** (this often fails!):
```fsharp
type positive = x:int{x > 0}

let double (x:positive) : positive = 2 * x
// ERROR (often): Could not prove 2 * x > 0

let triple (x:positive) : positive = 3 * x
// ERROR: Multiplication by constant with variable → NIA!
```

**Why it fails**:
- F* generates: `x > 0 ==> 3 * x > 0`
- Z3 sees: Nonlinear (multiplication by variable)
- Z3 heuristics may not find the proof

**Fix** (hint to SMT):
```fsharp
let triple (x:positive) : positive =
  assert (x > 0);  // Remind Z3
  3 * x  // Now Z3 can often prove it
```

#### Theory of Arrays

**Operations**:
- `select(a, i)` - read array `a` at index `i`
- `store(a, i, v)` - write value `v` at index `i`

**Axioms**:
- `select(store(a, i, v), i) = v` (read after write)
- `i ≠ j ==> select(store(a, i, v), j) = select(a, j)` (no interference)

**F* Example**:
```fsharp
let a = Seq.create 10 0  // Array of 10 zeros
let a' = Seq.upd a 5 42  // a'[5] := 42
let x = Seq.index a' 5   // x := a'[5]
// Z3 proves: x = 42 (using array theory)
```

#### Theory of Datatypes

**Constructors/Destructors**:
- Lists: `Nil`, `Cons(hd, tl)`
- Options: `None`, `Some(v)`

**Axioms**:
- `hd(Cons(x, xs)) = x` (constructor/destructor)
- `Cons(hd(xs), tl(xs)) = xs` (if xs ≠ Nil)

**F* Example**:
```fsharp
type list a = | Nil | Cons of a * list a

let hd (xs:list a{xs ≠ Nil}) : a = match xs with
  | Cons (x, _) -> x

// Z3 uses datatype theory to reason about list structure
```

---

### [65-80 min] F* to SMT Translation

**Transition**: "Now we see what F* sends to Z3."

#### Live Demo: --log_queries

**Code**:
```fsharp
module Demo

type even = x:int{x % 2 = 0}

let test1 : even = 4  // Should work
let test2 : even = 2 * 3  // Should work
let test3 : even = 3  // Should fail
```

**Run**:
```bash
fstar.exe --log_queries demo.fst
```

**Output**: Creates `query_*.smt2` files

**Open query file** (simplified):
```smt2
(declare-const x Int)
(assert (= x 4))
(assert (= (mod x 2) 0))  ; even constraint
(check-sat)
; Z3 answers: sat
```

**Show for test3**:
```smt2
(declare-const x Int)
(assert (= x 3))
(assert (= (mod x 2) 0))  ; even constraint
(check-sat)
; Z3 answers: unsat (contradiction!)
```

**Key Insight**: F* doesn't "run" your code - it translates to logic and asks Z3 "Is this consistent?"

#### Translation Examples

**Refinement Type**:
```fsharp
type nat = x:int{x >= 0}
```
→ SMT: `(assert (>= x 0))`

**Function Call**:
```fsharp
let double (x:nat) : nat = x + x
```
→ SMT:
```smt2
(declare-fun double (Int) Int)
(assert (forall ((x Int)) (=> (>= x 0) (>= (double x) 0))))
(assert (forall ((x Int)) (= (double x) (+ x x))))
```

**Pattern Matching**:
```fsharp
match xs with | Nil -> 0 | Cons(_, tl) -> 1 + length tl
```
→ SMT: ite (if-then-else)
```smt2
(ite (= xs Nil) 0 (+ 1 (length (tl xs))))
```

---

### [80-90 min] Exercise 3.1 Introduction + Homework

**Exercise 3.1: Reading SMT-LIB** (homework, 45 minutes)

**Task**:
```fsharp
type even = x:int{x % 2 = 0}
type positive = x:int{x > 0}
type bounded = x:int{0 <= x && x < 100}

let test1 : even = 4
let test2 : positive = 10
let test3 : bounded = 50

// Run: fstar.exe --log_queries exercise_3_1.fst
// For each type, identify:
// 1. Which SMT theory is used? (LIA/NIA/arrays/datatypes)
// 2. What SMT formula represents the refinement?
// 3. Does Z3 use decidable reasoning?
```

**Deliverable**:
- Annotated SMT-LIB files (comments explaining each line)
- Table: Type | SMT Theory | Decidable? | Formula
- Reflection: "What surprised you about the translation?"

**Preview Day 8**: "Tomorrow: What to do when proofs fail"

**Homework**:
- Exercise 3.1 (above)
- Reading: Z3 guide - Theory overview (link in syllabus)
- Optional: Play with SMT-LIB online: https://rise4fun.com/z3

---

## After Class (Day 7)

**Self-Assessment**:
- Did students grasp SAT vs SMT distinction?
- Was DPLL too detailed or just right?
- Did live demo work smoothly?

**Common Student Confusions to Address Next Class**:
- "So F* is just calling Z3?" (Yes, but smart translation matters)
- "Why not always use NIA?" (Undecidable = may not terminate)
- "Can I write SMT-LIB directly?" (Technically yes, but F* does it better)

**Prepare for Day 8**:
- Have 3-5 failing proof examples ready
- Test all debug flags work
- Prepare fuel demo (fibonacci timeout)

---

## Day 8 (Wednesday): Debugging SMT Failures

**Duration**: 90 minutes
**Goal**: Students can systematically debug failing proofs

### [0-15 min] The Three Causes of Proof Failure

**Recap Day 7**: "We learned what SMT solvers CAN do. Today: what they CAN'T do."

**The Three Failure Modes**:

1. **Undecidability** (Theory Limitation)
   - Formula in undecidable theory (NIA, complex quantifiers)
   - Z3 may timeout or return "unknown"
   - Example: `let triple (x:positive) : positive = 3 * x` (NIA)

2. **Timeout** (Resource Exhaustion)
   - Formula is decidable but Z3 runs out of time
   - Complex formula, many quantifiers
   - Z3 has resource limit (default: ~10 million steps)
   - Example: Deep proof with many nested implications

3. **Fuel Exhaustion** (F* Specific)
   - Recursive function not unfolded enough times
   - F* limits how many times Z3 unfolds definitions
   - Default fuel = 2 (unfolds twice)
   - Example: `assert (factorial 5 = 120)` needs 5 unfolds

**Poll**: "Which have you encountered?"
- Raise hand if you've seen timeouts (expect many)
- Raise hand if you know what fuel is (expect few)

---

### [15-40 min] Fuel and Depth: Controlling Unfolding

**The Problem**: Recursive Function Timeouts

**Live Demo**:
```fsharp
let rec factorial (n:nat) : nat =
  if n = 0 then 1 else n * factorial (n - 1)

let test = assert (factorial 5 = 120)
// TIMEOUT or FAILS!
```

**Why**: Z3 must unfold `factorial` 5 times:
- `factorial 5 = 5 * factorial 4`
- `= 5 * 4 * factorial 3`
- `= 5 * 4 * 3 * factorial 2`
- `= 5 * 4 * 3 * 2 * factorial 1`
- `= 5 * 4 * 3 * 2 * 1 * factorial 0`
- `= 5 * 4 * 3 * 2 * 1 * 1 = 120`

But F* only unfolds twice by default!

#### Understanding Fuel

**Fuel**: Number of times F* unfolds recursive function definitions

**Syntax**:
```fsharp
#set-options "--fuel N"  // Set fuel to N for subsequent code
```

**Fix the factorial example**:
```fsharp
#set-options "--fuel 6"  // Need 5+1 for safety
let test = assert (factorial 5 = 120)  // NOW WORKS
```

**Live demo**: Show it working with different fuel levels
- Fuel 2 (default): FAILS
- Fuel 3: FAILS (still not enough)
- Fuel 5: FAILS (edge case)
- Fuel 6: WORKS!

**Warning**: High fuel = exponential blowup!
```fsharp
#set-options "--fuel 10"  // DANGER: May take forever
```

**Rule of thumb**: If you need fuel > 5, write a lemma instead.

#### IFuel (Fuel for Inductive Types)

**IFuel**: Like fuel, but for unfolding inductive type definitions

**Example**:
```fsharp
type tree = | Leaf | Node of int * tree * tree

let rec height (t:tree) : nat = match t with
  | Leaf -> 0
  | Node (_, l, r) -> 1 + max (height l) (height r)

#set-options "--ifuel 4"  // For deep trees
let test_tree = assert (height deep_tree = 3)
```

**Usually**: ifuel = fuel (they track together)

#### Z3 Resource Limit

**rlimit**: Total "steps" Z3 can take

```fsharp
#set-options "--z3rlimit 10"  // 10 million steps (default)
#set-options "--z3rlimit 100" // 100 million (for hard proofs)
```

**When to use**: Proofs that are decidable but slow

---

### [40-70 min] The Debug Flags Toolkit

**Transition**: "Fuel helps, but how do we diagnose the problem?"

#### Essential Debug Flags

**1. `--debug SMT`**: See SMT queries sent to Z3
```bash
fstar.exe --debug SMT file.fst
```
Output: Shows every query, Z3's response (sat/unsat/unknown)

**2. `--log_queries`**: Save SMT-LIB files
```bash
fstar.exe --log_queries file.fst
# Creates: query_*.smt2 files
```
Use: Inspect exact formula sent to Z3

**3. `--log_failing_queries`**: Only save failed queries
```bash
fstar.exe --log_failing_queries file.fst
```
Use: Focus on problematic queries

**4. `--debug_level Low|Medium|High`**: Verbosity
```bash
fstar.exe --debug SMT --debug_level High file.fst
```
- Low: Minimal output
- Medium: Moderate detail (default)
- High: Everything (overwhelming!)

**5. `--profile`**: Time spent verifying each function
```bash
fstar.exe --profile file.fst
```
Output:
```
function_a: 0.5s
function_b: 10.2s  <-- SLOW!
function_c: 0.3s
```

Use: Find performance bottlenecks

#### Debugging Workflow (Live Demo)

**Failing Proof**:
```fsharp
let rec append (#a:Type) (xs ys:list a) : list a =
  match xs with
  | [] -> ys
  | hd::tl -> hd :: append tl ys

let test (xs ys zs:list int) =
  assert (append (append xs ys) zs == append xs (append ys zs))
  // FAILS!
```

**Step 1**: Run with `--debug SMT`
```bash
fstar.exe --debug SMT demo.fst
```
Output shows: Z3 returns "unknown" (can't prove it)

**Step 2**: Try higher fuel
```fsharp
#set-options "--fuel 5"
let test (xs ys zs:list int) =
  assert (append (append xs ys) zs == append xs (append ys zs))
  // STILL FAILS!
```

**Step 3**: Realize this needs induction (fuel doesn't help)
- This is a property over ALL lists (infinite)
- SMT can't do induction automatically
- **Solution**: Write a lemma (next week!)

**Key Insight**: Debugging tells you WHEN to give up on SMT

---

### [70-85 min] When to Give Up on SMT

**Decision Tree**: What to do when proof fails?

```
Proof fails
  ├─> Try fuel 3-5
  │   ├─> Works! ✓ Done
  │   └─> Still fails
  │       ├─> Try adding assert hints
  │       │   ├─> Works! ✓ Done
  │       │   └─> Still fails
  │       │       └─> Write manual lemma (Week 4-5)
  │
  ├─> Check with --debug SMT
  │   ├─> Z3 says "unknown" → Undecidable (NIA or quantifiers)
  │   │   └─> Restructure code or write lemma
  │   └─> Z3 says "timeout" → Too complex
  │       └─> Simplify or break into smaller pieces
  │
  └─> Profile with --profile
      └─> Function takes >10s → Optimization needed (Day 9)
```

**SMT CAN Handle**:
- Linear arithmetic (`x + y > 10`, `2*x ≤ 5`)
- Simple array reasoning (`a[i]`, `a[i] := v`)
- Datatype constructors/destructors (`hd(Cons(x,xs)) = x`)
- Boolean logic (AND, OR, NOT)
- Small proofs (< 10 steps)

**SMT STRUGGLES With**:
- Nonlinear arithmetic (`x * y > 10`, `x² + y²`)
- Deep recursion (fuel > 5)
- Complex quantifiers (∀x,y,z with many interactions)
- Induction (properties over ALL values)
- User-defined recursive functions on inductives

**Rule of Thumb**:
- Fuel 1-3: SMT can handle
- Fuel 4-5: Try it, but be ready to write lemma
- Fuel 6+: Write a lemma instead

---

### [85-90 min] Exercise 3.2 Introduction

**Exercise 3.2: Debugging Toolkit** (homework, 90 minutes)

**Task**: Fix 5 failing proofs using appropriate techniques

**Deliverable**:
- Fixed proofs (with minimal changes)
- Explanation of why each failed
- Which technique you used (fuel/assert/lemma/restructure)

**Preview Day 9**: "Friday: Advanced SMT patterns and performance"

---

## After Class (Day 8)

**Self-Assessment**:
- Do students understand fuel conceptually?
- Can they use --debug flags?
- Do they know when to give up?

**Prepare for Day 9**:
- Have slow proof example (10+ seconds)
- Test profiling workflow
- Prepare quantifier examples

---

## Day 9 (Friday): Advanced SMT Patterns and Performance

**Duration**: 90 minutes
**Goal**: Students can optimize slow verifications and understand advanced SMT features

### [0-25 min] Quantifiers and Triggers

**Transition**: "Some of you asked: How do lemmas work in SMT?"

#### The Quantifier Problem

**Lemma in F***:
```fsharp
val append_nil: #a:Type -> xs:list a -> Lemma (append xs [] == xs)
let rec append_nil #a xs = match xs with
  | [] -> ()
  | hd::tl -> append_nil tl; ()
```

**What Z3 sees**:
```smt2
(assert (forall ((a Type) (xs (List a)))
  (= (append xs nil) xs)))
```

**Problem**: When should Z3 USE this fact?
- Could instantiate for any xs (infinite possibilities!)
- Z3 needs hints about WHEN to apply the quantifier

#### E-Matching and Triggers

**Trigger**: A pattern that tells Z3 when to instantiate a quantifier

**Example**:
```smt2
(assert (forall ((xs (List Int)))
  (!  ; ! means "pattern follows"
    (= (append xs nil) xs)
    :pattern ((append xs nil))  ; Trigger: append xs nil
  )))
```

**How it works**:
- Z3 sees term `append [1;2;3] []` in proof
- Trigger matches: instantiate quantifier with xs=[1;2;3]
- Z3 learns: `append [1;2;3] [] = [1;2;3]`

**F* picks triggers automatically** (usually good!)
- Trigger: Largest sub-term containing all quantified variables
- Example: `append xs ys` (contains both xs and ys)

**Manual override** (rarely needed):
```fsharp
val lemma_with_pattern: xs:list a -> ys:list a ->
  Lemma (ensures append xs ys == ...)
        [SMTPat (append xs ys)]  // Force this trigger
```

---

### [25-50 min] SMT Performance Profiling

**Transition**: "Some proofs are slow. Let's find out why."

#### Using --profile

**Slow Code** (takes 30 seconds):
```fsharp
// Binary search tree with verification
type bst = | Leaf | Node of int * bst * bst

val insert: bst -> int -> bst
val insert_preserves_bst: t:bst -> x:int -> Lemma (is_bst (insert t x))
// ... implementations ...

// SLOW PROOF (30+ seconds):
let test_many_inserts () =
  let t0 = Leaf in
  let t1 = insert t0 1 in
  insert_preserves_bst t0 1;
  let t2 = insert t1 2 in
  insert_preserves_bst t1 2;
  // ... 20 more insertions ...
  assert (is_bst t20)
```

**Step 1: Profile**
```bash
fstar.exe --profile bst.fst
```

Output:
```
Verifying function: insert (0.3s)
Verifying function: insert_preserves_bst (12.5s)  <-- SLOW!
Verifying function: test_many_inserts (15.2s)  <-- ALSO SLOW!
```

**Step 2: Optimize with SMTPat**

**After** (fast):
```fsharp
// Lemma: Inserting preserves BST (auto-applied)
val insert_always_bst: t:bst -> x:int -> Lemma
  (requires is_bst t)
  (ensures is_bst (insert t x))
  [SMTPat (insert t x)]  // Auto-apply when insert is called

// Now test is fast:
let test_many_inserts () =
  let t0 = Leaf in
  let t1 = insert t0 1 in  // Lemma auto-applies
  let t2 = insert t1 2 in  // Lemma auto-applies
  // ... no manual calls needed
  assert (is_bst t20)  // Verification: 2 seconds!
```

**Result**: 30s → 2s (15x speedup!)

---

### [50-75 min] SMT Patterns and Anti-Patterns

**Good Pattern 1**: Small, Focused Lemmas
```fsharp
// GOOD
val length_append: xs -> ys -> Lemma (length (xs @ ys) = length xs + length ys)
val append_assoc: xs -> ys -> zs -> Lemma (xs @ (ys @ zs) = (xs @ ys) @ zs)

// BAD (too big)
val everything_about_lists: xs -> ys -> zs ->
  Lemma (
    length (xs @ ys) = length xs + length ys /\
    xs @ (ys @ zs) = (xs @ ys) @ zs /\
    reverse (xs @ ys) = reverse ys @ reverse xs /\
    // ... 10 more properties
  )
```

**Good Pattern 2**: Explicit Type Annotations
```fsharp
// GOOD
let result : nat = compute_something x

// BAD (SMT must infer type, may fail)
let result = compute_something x
```

**Good Pattern 3**: Assert Intermediate Steps
```fsharp
// GOOD
let f (x:nat) : y:nat{y > x} =
  assert (x >= 0);         // Remind SMT
  let tmp = x + 1 in
  assert (tmp > x);        // Chain of reasoning
  tmp

// BAD (SMT must figure out whole chain at once)
let f (x:nat) : y:nat{y > x} = x + 1
```

---

### [75-85 min] Week 3 Wrap-up

**What We Learned This Week**:
- ✅ How SMT solvers work (DPLL(T), theories)
- ✅ What F* sends to Z3 (--log_queries)
- ✅ How to debug failing proofs (fuel, --debug flags)
- ✅ When to give up on SMT (write lemmas instead)
- ✅ How to optimize slow proofs (profiling, refactoring)

**Skills Acquired**:
- Use `--log_queries` to inspect SMT formulas
- Identify theory (LIA vs NIA)
- Adjust fuel for recursive functions
- Add strategic assertions
- Profile and optimize slow verifications
- Know when manual proof is needed

**Next Week** (Week 4-5):
- Manual proofs with induction
- Writing lemmas
- Proof decomposition strategies

**Mini-Project 3** (assigned):
- **Due**: Next Friday
- **Task**: Optimize slow verification (45s → <10s)
- **Skills**: All of Week 3
- **Start early!**

---

### [85-90 min] Course Transition

**Looking Back** (Weeks 1-3):
- Week 1-2: "It just works!" (SMT automatic)
- Week 3: "Now I know WHY it works (or doesn't)"

**Looking Ahead** (Weeks 4-12):
- Week 4-5: Manual proofs with induction (when SMT can't help)
- Week 6-7: Dependent types (vectors, balanced trees)
- Week 8-9: Effects and state (stateful verification)
- Week 10-11: Low* and C extraction
- Week 12: Capstone project

**You are now at L2 (Apprentice) level!**
- Can write refinement types
- Understand SMT automation
- Can debug proofs systematically
- Ready for manual proof engineering

---

## After Class (Day 9)

**Final Week 3 Assessment**:
- Can students debug a failing proof?
- Do they understand when SMT can't help?
- Can they profile and optimize?

**Feedback to Collect**:
- Was Week 3 too hard/easy?
- Was SMT theory useful or too abstract?
- Should we spend more time on practical debugging?

**Prepare for Week 4**:
- Transition to manual proofs (induction)
- Students now understand SMT limitations
- Ready for "why we need lemmas"

---

**END OF WEEK 3 TEACHING NOTES**

Total Lecture Time: 270 minutes (3 × 90min)
Total Exercises: 5 exercises + 1 mini-project
Learning Outcome: L1→L2 transition (SMT mastery)
Next: Week 4-5 Totality and Induction

