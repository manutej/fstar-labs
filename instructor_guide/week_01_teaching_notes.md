# Week 1 Teaching Notes: Introduction to F* and Type Safety
## Level 1 (Novice) - Refinement Types and SMT Solving

**Week Theme**: Build confidence with first formal proofs using refinement types
**Learning Goal**: By end of Week 1, every student should have at least one proof typecheck successfully
**Assessment**: Mini-project (safe calculator) due Friday

---

## Overview

### Week 1 Learning Objectives

By the end of Week 1, students will be able to:
1. **Install and configure** F* toolchain and editor integration
2. **Define refinement types** using `{x:t | predicate}` syntax
3. **Leverage SMT solver** (Z3) for automatic proof search
4. **Compose verified functions** while maintaining type safety
5. **Use option types** for error handling in pipelines
6. **Debug type errors** and understand F* error messages
7. **Complete mini-project**: Build safe calculator with division-by-zero safety

**Note**: Totality and termination proofs (`decreases` clauses) are introduced in Week 2, Day 4.

### Pre-Week Preparation (for Instructor)

**Before Week 1 starts:**
- [ ] Test all exercises yourself (2-3 hours)
- [ ] Verify F* installation on target platforms (Linux, Mac, Windows)
- [ ] Prepare backup: Docker container with F* pre-installed
- [ ] Set up auto-grader for Exercise 1.1-1.3 (see `solutions/autograder/`)
- [ ] Review SKILL.md sections 1-3 (refresher on refinement types)
- [ ] Prepare "installation party" session (optional, recommended for Sunday before Week 1)

**Teaching Materials Needed:**
- Lecture slides: `slides/week_01_day_01.md` through `week_01_day_03.md`
- Exercise starters: `exercises/week_01/`
- Solutions (instructor only): `instructor_guide/solutions/week_01_all_solutions.fst`
- Auto-grader: `instructor_guide/rubrics/autograder/week_01_tests.py`

---

## Day 1 (Monday): What is Formal Verification?

### Learning Objectives
1. Explain the difference between testing and verification
2. Identify when formal methods are cost-effective
3. Install F* toolchain and verify first program
4. Understand the Curry-Howard correspondence (informal introduction)

### Lecture Structure (90 minutes)

#### [0-15 min] Course Overview and Motivation

**Opening** (5 min):
```
"Welcome to Formal Verification with F*! Show of hands:
 - Who has written a test that passed but the code still had bugs? (most hands)
 - Who has spent hours debugging a problem testing missed? (many hands)
 - Who wants to mathematically *prove* their code is correct? (fewer hands - good!)

This course teaches you to write code with mathematical proofs of correctness.
By Week 12, you'll verify cryptographic implementations used in production systems."
```

**Set Expectations** (5 min):
- This course is **hard** - proofs are like learning a foreign language
- Struggle is **normal** and **expected** - we celebrate productive failures
- You will get stuck - that's the point! Office hours = "proof workshop"
- Collaboration encouraged, but copying is academic dishonesty

**Course Structure** (5 min):
- Show 7-level progression (L1 → L7)
- Week 1-2: Refinement types (L1)
- Week 3-4: Inductive proofs (L2)
- [Brief overview of Weeks 5-12]
- Assessment: exercises, mini-projects, midterm, capstone

#### [15-30 min] The Verification Spectrum

**Slide: Testing vs. Verification** (10 min)

| Approach | Coverage | Confidence | Cost |
|----------|----------|------------|------|
| Manual Testing | Example inputs | Low | Low |
| Unit Tests | More examples | Medium | Medium |
| Property Testing | Random inputs | Higher | Medium |
| **Formal Verification** | **ALL inputs** | **Proof** | **High** |

**Live Demo** (5 min):
```fsharp
// Show buggy code that passes tests
let divide (a:int) (b:int) : int = a / b

// Test passes!
assert (divide 10 2 = 5)
assert (divide 100 10 = 10)

// But runtime crash:
divide 10 0  // Exception! Tests didn't catch this.
```

**Discussion Prompt** (5 min):
- "When is verification worth the cost?"
- Expected answers: safety-critical systems, cryptography, compilers
- Mention: HACL* (crypto lib in Firefox), CompCert (verified compiler)

#### [30-60 min] F* Installation and "Hello, Verification!"

**Installation Walkthrough** (20 min):

**NOTE**: This is the most frustrating part for students. Be patient and have backup plans ready.

**Live demonstration** (instructor shares screen):
1. Check F* is installed: `fstar.exe --version` (or `fstar` on Unix)
2. Open VS Code with F* extension
3. Create `hello.fst` file
4. Write first F* code:

```fsharp
module Hello

// Our first verified function!
let add (x:int) (y:int) : int = x + y

// Natural numbers (refinement type)
type nat = x:int{x >= 0}

// Safe function: only accepts non-negative inputs
let add_nat (x:nat) (y:nat) : nat = x + y
```

5. Press F8 (or verify command) - watch it typecheck!
6. Show error: `add_nat 5 (-3)` - type error at compile time!

**Common Installation Issues** (10 min):
- **Windows**: Path issues with Z3
  - Solution: Use WSL or Docker container
- **Mac**: OCaml dependency conflicts
  - Solution: Use opam switch for isolated environment
- **Linux**: Usually smoothest, but may need `sudo apt install z3`

**Backup Plan**: If students can't install:
- Provide Docker container: `docker run -it fstar-course`
- Cloud IDE (if available)
- Pair with student who has working install

#### [60-75 min] First Refinement Type: `nat`

**Concept Introduction** (10 min):

"Refinement types = base type + logical predicate"

```fsharp
type nat = x:int{x >= 0}
//         │  │   └─ predicate (must be true)
//         │  └───── base type
//         └──────── variable name
```

**Live Coding** (5 min):
```fsharp
// This type checks!
let five : nat = 5

// This doesn't - type error!
let negative : nat = -3
// Error: "Expected type nat, got type int"

// Functions can require refined inputs
let sqrt_approx (n:nat) : nat =
  // Implementation... (simplified for demo)
  n
```

**Key Point**: "Errors at compile time, not runtime!"

#### [75-90 min] Exercise 1.1: Safe Division Function

**Exercise Introduction** (5 min):

"Your first formal proof! You'll write a division function that can't crash."

**Exercise 1.1 Specification:**
```fsharp
// TODO: Define nonzero type (note: F* convention is lowercase)
type nonzero = (* YOUR CODE HERE *)

// TODO: Implement safe_divide
let safe_divide (a:int) (b:nonzero) : int =
  (* YOUR CODE HERE *)

// Test cases (should typecheck):
let test1 = safe_divide 10 2  // ✓ Should work
let test2 = safe_divide 10 0  // ✗ Should be type error!
```

**Instructions** (5 min):
- Work in pairs (assign pairs)
- 10 minutes to attempt
- Use `{ x:int | ... }` syntax
- Think: what property must `b` satisfy?

**Debrief** (5 min):
- Walk around, help students
- Common mistake: Forgetting the refinement syntax
- After 10 min, show solution (next section)

---

### After Class

**Homework Assignment:**
- Complete Exercise 1.1 (if not finished in class)
- Start Exercise 1.2 (Positive type)
- **Read**: SKILL.md sections 1-2 (refinement types basics)
- **Install**: Ensure F* works on your machine (use office hours if stuck!)

**Office Hours Preparation:**
- Expect installation help questions
- Have Docker container ready
- Keep track of common errors (update troubleshooting guide)

---

## Day 2 (Tuesday): Refinement Types Deep Dive

### Learning Objectives
1. Define custom refinement types using `{x:t | p}`
2. Leverage SMT solver for automatic proof search
3. Understand when SMT fails and manual proofs needed
4. Debug SMT failures using `--debug` flags

### Lecture Structure (90 minutes)

#### [0-20 min] Review Day 1 + Common Installation Issues

**Quick Poll** (5 min):
- "Who got F* installed and working?" (track percentage)
- "Who completed Exercise 1.1?" (track completion)
- "What was most confusing yesterday?"

**Installation Troubleshooting** (10 min):
- Address top 3 issues from students
- Pair students who have working setups with those who don't
- "By end of today, EVERYONE should have working F*"

**Exercise 1.1 Solution Review** (5 min):
```fsharp
// Solution: nonzero refinement type
type nonzero = x:int{x <> 0}

let safe_divide (a:int) (b:nonzero) : int = a / b

// Type checks!
let test1 = safe_divide 10 2

// Type error (as expected):
// let test2 = safe_divide 10 0
// Error: "Expected type nonzero, got type int"
```

**Key Insight**: "The type system prevents runtime errors at compile time!"

#### [20-40 min] Refinement Type Syntax and Semantics

**Formal Syntax** (10 min):

```fsharp
// General form:
type alias = x:basetype{predicate_on_x}

// Examples:
type nat = x:int{x >= 0}
type pos = x:int{x > 0}
type even = x:int{x % 2 = 0}
type bounded = x:int{x >= 0 && x < 100}

// Can use in function types directly:
let abs (n:int) : nat = if n < 0 then -n else n
//                └─── return type is refined!
```

**Semantics** (10 min):

"When you write `x:nat`, you're making a **proof obligation**:"

```fsharp
let five : nat = 5
// F* must prove: 5 >= 0  ✓ SMT solver checks this automatically!

let negative : nat = -3
// F* must prove: -3 >= 0  ✗ Fails! Type error.
```

**Under the Hood**: Z3 SMT solver
- SMT = Satisfiability Modulo Theories
- Decides formulas in theories (integers, arrays, etc.)
- F* translates refinement types to SMT queries
- Z3 either proves it OR gives counterexample

**Live Demo: SMT in Action** (5 min):
```bash
# Show F* with debug flag
fstar.exe --debug SMT hello.fst

# Shows SMT queries sent to Z3 (lots of output!)
# Point out: F* is doing the proving for you
```

#### [40-65 min] Live Coding: Array Bounds Checking

**Motivating Example** (5 min):

"Most common bug class: array out-of-bounds. Let's prove it can't happen!"

**Live Coding** (15 min):

```fsharp
module SafeArray
open FStar.List.Tot

// Array type (simplified using lists)
type array (a:Type) (len:nat) = l:list a{length l = len}

// Index type: must be in bounds!
type index (len:nat) = i:nat{i < len}

// Custom safe nth function (standard nth returns option)
val nth_safe: #a:Type -> l:list a -> i:nat{i < length l} -> Tot a
let rec nth_safe #a l i =
  match l with
  | hd :: tl -> if i = 0 then hd else nth_safe tl (i - 1)

// Safe array access - can't fail!
let get (#a:Type) (#len:nat) (arr:array a len) (i:index len) : a =
  nth_safe arr i  // F* proves i < length arr!

// Example usage:
let my_array : array int 3 = [1; 2; 3]

let first = get my_array 0  // ✓ Typechecks (0 < 3)
let second = get my_array 1  // ✓ Typechecks (1 < 3)
// let bad = get my_array 5  // ✗ Type error! (5 < 3 fails)
```

**Pause for Questions** (3 min)

**Deliberate Error** (2 min):
```fsharp
// Show what happens when we try to break it:
let oob = get my_array 10
// Error: "Expected type index 3, got type int"
// F* says: "Prove that 10 < 3" - can't, so type error!
```

#### [65-80 min] SMT Solver Internals (Z3 Primer)

**What is Z3?** (5 min):
- Theorem prover from Microsoft Research
- Decides formulas in first-order logic + theories
- Theories: integers, reals, arrays, bit-vectors, etc.
- Used by F*, Dafny, and many other verifiers

**When SMT Succeeds** (5 min):
```fsharp
let example1 (x:nat) : nat = x + 1
// SMT proves: if (x >= 0) then (x + 1 >= 0)  ✓

let example2 (x:pos) (y:pos) : pos = x * y
// SMT proves: if (x > 0 && y > 0) then (x * y > 0)  ✓
```

**When SMT Fails** (5 min):
- Nonlinear arithmetic (sometimes)
- Quantifiers (often needs help)
- Complex recursive functions
- Solution: Write explicit lemmas (Week 2!)

**Demo: SMT Timeout** (intentional failure):
```fsharp
// This might time out (nonlinear arithmetic):
let hard_for_smt (x:pos) : pos =
  x * x * x + x * x + x + 1
// May need --z3rlimit flag or manual proof
```

#### [80-90 min] Exercise 1.2: Validated Input Parsing

**Exercise Introduction** (3 min):

"Real-world scenario: parse user input with validation"

**Exercise 1.2 Specification:**
```fsharp
// User age: must be between 0 and 150
type age = x:int{x >= 0 && x <= 150}

// Parse string to age (returns option type)
let parse_age (s:string) : option age =
  (* YOUR CODE HERE *)
  // Hint: use int_of_string and check bounds

// Clamp function: force value into range
let clamp (min:int) (max:int{max >= min}) (x:int)
  : y:int{y >= min && y <= max} =
  (* YOUR CODE HERE *)
  // If x < min, return min
  // If x > max, return max
  // Otherwise, return x
```

**Instructions** (2 min):
- 15 minutes to work (rest of class + start at home)
- `clamp` is the interesting one - requires proof thinking
- Hint: use `if-then-else`, F* will check each branch

**Homework** (5 min):
- Complete Exercise 1.2
- Start Exercise 1.3 (preview next class)
- Read SKILL.md section 3 (totality and termination)

---

### After Class

**Grading Notes:**
- Exercise 1.1: Auto-grade (should all pass)
- Exercise 1.2: Check manually for creativity
- Look for: Did they understand refinement type syntax?

**Common Errors to Watch For:**
- Forgetting `{}` vs `()` (refinement vs function call)
- Wrong predicate logic (e.g., `x > 0 && x > 100` instead of `&&`)
- Not returning refined type (return `int` instead of refined)

---

## Day 3 (Wednesday): Composing Verified Functions

### Learning Objectives
1. Chain refinement types through function composition
2. Understand subtyping in refinement hierarchies
3. Use `assert` and `assume` strategically
4. Read and interpret F* error messages

### Lecture Structure (90 minutes)

#### [0-15 min] Debrief Homework Struggles

**Open Discussion** (10 min):
- "What was hardest about Exercise 1.2?"
- Expected: `clamp` function proofs
- Common issue: "How do I prove the return type?"

**Solution Walkthrough** (5 min):
```fsharp
let clamp (min:int) (max:int{max >= min}) (x:int)
  : y:int{y >= min && y <= max} =
  if x < min then min
  else if x > max then max
  else x

// Why this works:
// Branch 1: if x < min, return min
//   F* proves: min >= min && min <= max  ✓ (from precondition)
// Branch 2: if x > max, return max
//   F* proves: max >= min && max <= max  ✓
// Branch 3: else (min <= x <= max)
//   F* proves: x >= min && x <= max  ✓ (from control flow!)
```

**Key Insight**: "F* tracks control flow information in types!"

#### [15-35 min] Function Composition with Refined Types

**Concept: Composition** (10 min):

"In functional programming, we build complex functions from simple ones."

```fsharp
// Simple functions:
let parse (s:string) : option int = (* ... *)
let validate (x:int) : option nat = (* ... *)
let process (x:nat) : string = (* ... *)

// Composition (manual):
let pipeline (s:string) : option string =
  match parse s with
  | None -> None
  | Some x ->
    match validate x with
    | None -> None
    | Some n -> Some (process n)
```

"Refinement types ensure each step's output matches next step's input!"

**Type-Driven Composition** (10 min):

```fsharp
// Better: use bind (monadic composition)
let (>>=) (m:option 'a) (f:'a -> option 'b) : option 'b =
  match m with
  | None -> None
  | Some x -> f x

// Now pipeline is clean:
let pipeline (s:string) : option string =
  parse s >>= validate >>= (fun n -> Some (process n))
```

**ETL Example** (like DisCoPy lesson):
```fsharp
module ETLPipeline

type RawData = string
type ParsedData = list (string * int)
type ValidData = list (string * nat)  // All ints are positive!
type Output = string

let parse (raw:RawData) : option ParsedData = (* ... *)
let validate (data:ParsedData) : option ValidData = (* ... *)
let transform (data:ValidData) : Output = (* ... *)

// Composed pipeline:
let etl_pipeline (raw:RawData) : option Output =
  parse raw >>= validate >>= (fun v -> Some (transform v))
```

#### [35-60 min] Subtyping: When `{x >= 0}` Implies `{x > -1}`

**Subtyping Hierarchy** (15 min):

"Some refinements are 'stronger' than others:"

```fsharp
type int = int  // Base type (weakest)
type nat = x:int{x >= 0}  // Natural numbers
type pos = x:int{x > 0}  // Positive (stronger than nat!)
type small_pos = x:int{x > 0 && x < 10}  // Even stronger!

// Subtyping relationships:
// small_pos <: pos <: nat <: int

// This means:
let a : pos = 5
let b : nat = a  // ✓ Works! pos is subtype of nat

let c : nat = 3
// let d : pos = c  // ✗ Doesn't work! nat is not subtype of pos
```

**Live Demo: Subtyping in Action** (10 min):

```fsharp
// Function expects nat:
let double (x:nat) : nat = x * 2

// Can pass pos (stronger type):
let test1 = double (5 : pos)  // ✓ Works

// Can't pass int (weaker type):
// let test2 = double ((-3) : int)  // ✗ Type error

// Explicit refinement ascription:
let test3 : nat = 5  // ✓ F* checks 5 >= 0
let test4 = double test3  // ✓ Works
```

**Practical Example**: "Why subtyping matters"

```fsharp
// Library function (you can't change):
val process_natural : nat -> string

// Your function returns pos:
let my_function () : pos = 42

// Composition works because pos <: nat:
let result = process_natural (my_function ())  // ✓
```

#### [60-80 min] Exercise 1.3: ETL Pipeline (F* Version)

**Exercise Introduction** (5 min):

"Build a data processing pipeline with verified transformations!"

**Exercise 1.3 Specification:**
```fsharp
module Exercise13

// Types representing pipeline stages:
type RawCSV = string
type ParsedRows = list (string * string)  // (key, value) pairs
type ValidatedData = list (string * nat)  // Values must be natural numbers!
type JSONOutput = string

// TODO: Implement these functions:
val parse_csv : RawCSV -> option ParsedRows
val validate_rows : ParsedRows -> option ValidatedData
  // Hint: Convert string values to nat, reject if invalid
val rows_to_json : ValidatedData -> JSONOutput

// TODO: Compose the pipeline:
val etl_pipeline : RawCSV -> option JSONOutput
  // Should compose the three functions above

// Test case (instructor provides):
let test_input = "temperature,25\nhumidity,60\nage,30"
let test_output = etl_pipeline test_input
// Should produce: Some "{\"temperature\": 25, \"humidity\": 60, \"age\": 30}"

let test_invalid = "temperature,25\nhumidity,-10"
let test_fail = etl_pipeline test_invalid
// Should produce: None (because -10 is not a nat)
```

**Instructions** (5 min):
- Work in pairs (same pairs as Monday)
- You have rest of class (15 min) + tonight to complete
- Key challenge: `validate_rows` must convert strings to nat
- Use `int_of_string : string -> int` (built-in)
- Then check if result is >= 0

**Work Time** (10 min):
- Students work, instructor circulates
- Help with type errors
- Common question: "How do I check if int is nat?"
  - Answer: Use refinement type ascription + match

#### [80-90 min] Mini-Project Kickoff: Safe Calculator

**Mini-Project Announcement** (10 min):

"Your first major assignment! Build a calculator that can't crash."

**Project Specification:**
```fsharp
module SafeCalculator

// Operations:
type op = Add | Sub | Mul | Div

// Safe evaluate: no division by zero!
val eval : int -> op -> int -> option int
// Should return None if division by zero attempted

// REPL interface:
val calculator_repl : unit -> unit
// Read-Eval-Print Loop for calculator
// Example session:
// > 10 + 5
// 15
// > 20 / 0
// Error: Division by zero
// > 15 * 3
// 45
```

**Requirements**:
1. Implement `eval` with division safety using refinement types
2. Build REPL that reads user input and calls `eval`
3. Handle all error cases gracefully (parse errors, div-by-zero)
4. **Extra credit**: Support parentheses and operator precedence

**Due**: Friday 11:59 PM
**Submission**: Git repository link
**Grading rubric**: See `rubrics/week_01_mini_project_rubric.md`

**Hints**:
- Use Exercise 1.1 (`NonZero` type) for division safety
- Parse user input into `(int, op, int)` tuple
- Use `match` on `op` to dispatch to operations

---

### After Class

**Homework**:
- Complete Exercise 1.3 (due Thursday morning)
- Start Mini-Project (due Friday)
- Read: SKILL.md section 4 (options and error handling)

**For Instructor**:
- Grade Exercise 1.1 and 1.2 (use auto-grader + manual review)
- Prepare solution for Exercise 1.3 (show on Thursday briefly)
- Office hours: Expect mini-project questions (have design guidance ready)

---

## Week 1 Wrap-Up

### Key Concepts Covered
- ✅ Refinement types: `{x:t | predicate}`
- ✅ SMT-based automatic proofs
- ✅ Function composition with type safety
- ✅ Subtyping hierarchies
- ✅ Error handling with `option` types

### Common Misconceptions to Address

**Misconception 1**: "Refinement types are runtime checks"
- **Reality**: They're compile-time proofs! No runtime overhead after extraction.
- **Correction**: Show extracted OCaml code - refinements erased

**Misconception 2**: "SMT solver always works"
- **Reality**: SMT can fail or timeout on complex proofs
- **Correction**: Week 2 teaches manual proofs with lemmas

**Misconception 3**: "I need to prove everything manually"
- **Reality**: SMT handles most simple arithmetic automatically
- **Correction**: Show examples where F* "just works"

**Misconception 4**: "Types are just documentation"
- **Reality**: Types are mathematical theorems enforced by compiler
- **Correction**: Show rejected code that testing would miss

### Assessment Checklist

By end of Week 1, students should:
- [ ] Have working F* installation
- [ ] Completed Exercises 1.1, 1.2, 1.3
- [ ] Submitted Mini-Project (safe calculator)
- [ ] Understand refinement type syntax
- [ ] Can read F* error messages (basic level)

### Looking Ahead to Week 2

**Preview** (mention in Day 3):
- Week 2: Lists, options, and total functions
- Termination proofs with `decreases` clauses
- First lemmas and inductive proofs
- Mini-project: Verified merge sort

---

## Troubleshooting Guide

### Installation Issues

**Issue 1: F* command not found**
- **Diagnosis**: PATH not set correctly
- **Solution (Windows)**: Add F*/bin to PATH environment variable
- **Solution (Unix)**: Add to `.bashrc` or `.zshrc`

**Issue 2: Z3 not found**
- **Diagnosis**: Z3 not installed or not in PATH
- **Solution**: Install Z3 via package manager or download binary
- **Check**: `z3 --version` should work

**Issue 3: VS Code extension not working**
- **Diagnosis**: Extension can't find F* binary
- **Solution**: Configure extension settings with full path to fstar.exe
- **Alternative**: Use Emacs mode instead

### Type Error Debugging

**Error: "Expected type X, got type Y"**
- **Meaning**: Type mismatch - function expects X, you gave Y
- **Solution**: Check function signature and what you're passing
- **Example**: Expected `nat`, got `int` → add refinement proof

**Error: "Could not prove refinement"**
- **Meaning**: SMT couldn't verify the predicate
- **Solution 1**: Add intermediate `assert` to help SMT
- **Solution 2**: May need explicit lemma (Week 2)
- **Example**: `let x : nat = complicated_expr` → add `assert (complicated_expr >= 0)`

**Error: "SMT timeout"**
- **Meaning**: Z3 ran out of time trying to prove
- **Solution 1**: Increase timeout with `--z3rlimit N`
- **Solution 2**: Simplify proof by breaking into steps
- **Solution 3**: Write manual proof (Week 2 skill)

---

## Additional Resources

**For Students**:
- F* tutorial: https://fstar-lang.org/tutorial/ (sections 1-3)
- F* Zulip #beginner-questions: https://fstar-lang.zulipchat.com/
- SKILL.md in this repository (comprehensive reference)

**For Instructors**:
- F* Zulip #teaching channel (instructor-only)
- Solutions repository: `instructor_guide/solutions/week_01_all_solutions.fst`
- Auto-grader setup: `instructor_guide/rubrics/autograder/README.md`

---

**End of Week 1 Teaching Notes**

Next: `week_02_teaching_notes.md` (Lists, Options, and Total Functions)
