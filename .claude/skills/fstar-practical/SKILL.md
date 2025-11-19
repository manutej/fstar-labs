# F* Practical Development & Debugging

**Skill Type:** Technical - Formal Verification
**Expertise Level:** L2-L6 (Apprentice to Grandmaster)
**Activation:** Automatic when working with F* code, debugging, or performance optimization
**Complements:** `/skill/SKILL.md` (F* theoretical foundations)

---

## Purpose

This skill provides **practical F* development and debugging expertise** for productive verification engineering. While `/skill/SKILL.md` covers theoretical foundations (dependent types, refinement types, effect system), this skill focuses on:

- **Debugging workflows** - Systematic problem-solving with F* tools
- **Performance optimization** - Making verification fast and CI-friendly
- **Real-world patterns** - Production verification techniques
- **Tooling mastery** - IDE integration, flags, automation
- **Common pitfalls** - Avoiding frustration with known issues

**Use this skill when:**
- Debugging verification failures
- Optimizing slow proofs
- Setting up F* development environment
- Building verified systems for production
- Teaching practical F* skills

---

## Core Competencies

### 1. Verification Debugging Workflow

#### The Three Failure Modes

**TIMEOUT** - Z3 takes too long (>2 seconds default)
```fsharp
// Symptom:
// Error: Query timeout

// Diagnosis:
fstar.exe --query_stats file.fst  // Find slow queries
fstar.exe --log_queries file.fst  // Inspect SMT-LIB

// Solutions:
// 1. Increase z3rlimit (last resort)
#push-options "--z3rlimit 20"
...
#pop-options

// 2. Add fuel for recursive functions
#push-options "--fuel 3"
...
#pop-options

// 3. Help Z3 with assertions
assert (key_fact);
...

// 4. Break into smaller lemmas
val helper_lemma: ...
let helper_lemma x = ...
let main_lemma x =
  helper_lemma x;
  ...
```

**UNKNOWN** - Z3 can't decide (usually NIA)
```fsharp
// Symptom:
// Error: Unknown (could not decide)

// Common cause: Nonlinear Arithmetic (variable * variable)
type positive = x:int{x > 0}

let multiply (x:positive) (y:positive) : positive =
  x * y  // FAILS with "unknown"

// Solution: Add hints for Z3
let multiply_fixed (x:positive) (y:positive) : positive =
  assert (x > 0 && y > 0);  // Remind Z3
  assert (x * y >= x);       // Hint about result
  x * y  // Now works!

// Or: Prove lemma separately
val multiply_positive: x:positive -> y:positive -> Lemma (x * y > 0)
let multiply_positive x y =
  assert (x > 0);
  assert (y > 0);
  ()

let multiply_with_lemma (x:positive) (y:positive) : positive =
  multiply_positive x y;
  x * y
```

**UNSAT (Proof Failed)** - Z3 proved the negation
```fsharp
// Symptom:
// Error: Could not prove post-condition

// This means your spec is WRONG, not Z3
let broken_max (x:int) (y:int) : z:int{z >= x && z >= y} =
  if x > y then x else x  // BUG! Should be y in else

// Debug workflow:
// 1. Read error carefully - what exactly failed?
// 2. Check your logic - is the code actually correct?
// 3. Test with concrete values mentally
// 4. Add intermediate assertions to isolate issue
let debug_max (x:int) (y:int) : z:int{z >= x && z >= y} =
  let result = if x > y then x else y in
  assert (result >= x);  // Check each property
  assert (result >= y);
  result
```

#### Systematic Debugging Steps

```
1. READ ERROR CAREFULLY
   - What file/line?
   - What kind of failure? (timeout, unknown, unsat)
   - What was F* trying to prove?

2. ISOLATE THE ISSUE
   - Comment out code to find minimal failing case
   - Add assert statements to narrow down
   - Test with simpler inputs

3. GATHER INFORMATION
   - Run with --query_stats (find slow queries)
   - Run with --log_queries (inspect SMT-LIB)
   - Run with --debug SMT (verbose Z3 output)

4. APPLY TARGETED FIX
   - Timeout? → Add fuel or split lemma
   - Unknown? → Add assertions (especially for NIA)
   - Unsat? → Fix the code logic

5. VERIFY FIX
   - Re-run F*
   - Check verification time didn't explode
   - Remove debug flags/assertions if not needed

6. DOCUMENT
   - Comment why fix was needed
   - Update TESTING.md if systematic issue
   - Share pattern with team
```

---

### 2. Performance Optimization

#### Profiling Workflow

```bash
# Step 1: Measure baseline
fstar.exe --query_stats file.fst | tee baseline.txt

# Step 2: Identify bottlenecks
grep "Query" baseline.txt | sort -k3 -n  # Sort by time

# Step 3: Focus on slowest queries (Pareto principle: 20% cause 80% of time)

# Step 4: Apply optimizations (see below)

# Step 5: Measure improvement
fstar.exe --query_stats file.fst | tee optimized.txt
diff baseline.txt optimized.txt
```

#### Fuel Optimization

**Fuel = How many times F* unrolls recursive definitions**

```fsharp
let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n - 1)

// ❌ BAD: Global high fuel (slow for everything)
#set-options "--fuel 20"

// ✅ GOOD: Localized minimal fuel
let some_proof () =
  #push-options "--fuel 3"  // Only for this proof
  assert (factorial 2 = 2);
  #pop-options
  ()

// ✅ BETTER: Replace fuel with explicit proof
let rec factorial_correct (n:nat)
  : Lemma (factorial n > 0) =
  match n with
  | 0 -> ()
  | _ -> factorial_correct (n - 1)  // Guides Z3 with recursion
```

**Finding Minimum Fuel:**
1. Start with fuel = 0
2. Increment until it verifies
3. That's your minimum
4. Use EXACTLY that much (not more!)

#### SMTPat Patterns (Automation)

**Without SMTPat** - Manual lemma calls everywhere
```fsharp
val append_length: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) = length xs + length ys)

let my_proof xs ys zs =
  append_length xs ys;           // Manual call 1
  append_length (append xs ys) zs  // Manual call 2
```

**With SMTPat** - Automatic application
```fsharp
val append_length_auto: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) = length xs + length ys)
        [SMTPat (length (append xs ys))]  // TRIGGER PATTERN

let my_proof xs ys zs =
  ()  // Z3 applies lemma automatically!
```

**Pattern Design Rules:**
- ✅ **Specific enough** - Doesn't trigger on every use
- ✅ **General enough** - Triggers when actually needed
- ❌ **Too general** - `[SMTPat (length xs)]` triggers on EVERY list length (slow!)
- ❌ **Too specific** - Never triggers, lemma useless

**Good patterns:**
```fsharp
[SMTPat (length (append xs ys))]        // Triggers on length of append
[SMTPat (is_sorted (insert t x))]       // Triggers on sorted after insert
[SMTPat (mem x (insert t y))]           // Triggers on membership after insert
```

---

### 3. Common Pitfalls & Solutions

#### Pitfall 1: NIA (Nonlinear Arithmetic)

**Problem:** Variable * variable is undecidable
```fsharp
type even = x:int{x % 2 = 0}

let multiply_evens (x:even) (y:even) : even =
  x * y  // FAILS with "unknown"
```

**Solution:** Help Z3 with assertions
```fsharp
let multiply_evens_fixed (x:even) (y:even) : even =
  // Remind Z3 of key facts
  assert (x % 2 = 0);
  assert (y % 2 = 0);
  // Hint: if x = 2k and y = 2m, then xy = 4km
  x * y
```

#### Pitfall 2: Too Much Fuel

**Problem:** Setting fuel = 20 "just to be safe"
```fsharp
#set-options "--fuel 20"  // TERRIBLE for performance!
```

**Impact:**
- Verification time explodes (minutes instead of seconds)
- SMT-LIB queries become huge
- CI/CD pipelines timeout

**Solution:** Find minimum fuel per proof
```fsharp
// Localized, minimal fuel
#push-options "--fuel 3"
let specific_proof = ...
#pop-options

// Back to default fuel = 1 for rest of file
```

#### Pitfall 3: Missing Decreases Clauses

**Problem:** F* can't prove termination
```fsharp
let rec ackermann (m:nat) (n:nat) : nat =
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))
// ERROR: Could not prove termination
```

**Solution:** Lexicographic ordering
```fsharp
let rec ackermann (m:nat) (n:nat)
  : Tot nat (decreases %[m; n]) =  // m decreases first, then n
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))
```

#### Pitfall 4: Forgetting `Tot` Effect

**Problem:** Partial functions when you need totality
```fsharp
let rec length (xs:list 'a) : nat =  // Defaults to Dv (divergence allowed)
  match xs with
  | [] -> 0
  | _ :: tl -> 1 + length tl
```

**Solution:** Explicit `Tot` for total functions
```fsharp
let rec length (xs:list 'a) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | _ :: tl -> 1 + length tl
```

#### Pitfall 5: Module Not Found

**Problem:** Missing `open` statements
```fsharp
let xs = [1;2;3]  // ERROR: Constructor Cons not found
```

**Solution:** Open required modules
```fsharp
open FStar.List.Tot  // Or FStar.List

let xs = [1;2;3]  // Now works
```

---

### 4. Development Environment Setup

#### Essential F* Flags

```bash
# PROFILING
--query_stats          # Show time per query (ESSENTIAL for optimization)
--log_queries          # Dump SMT-LIB to queries-*.smt2
--debug SMT            # Verbose Z3 interaction
--debug <Module>       # Debug specific module

# PERFORMANCE
--z3rlimit N           # Resource limit (replaces time limit)
--fuel N               # Recursive unfolding depth
--ifuel N              # Inductive fuel (for datatypes)
--z3refresh            # Restart Z3 between queries

# VERIFICATION
--admit_smt_queries true  # Accept all SMT queries (for testing structure)
--warn_error @247      # Turn deprecation warnings into errors

# OUTPUT
--print_implicits      # Show implicit arguments
--print_universes      # Show universe levels
--print_effect_args    # Show effect arguments
```

#### VS Code Integration

**Extensions:**
- `FStarLang.fstar-vscode-assistant` - Official F* extension
- Provides: syntax highlighting, error checking, hover info

**Settings (`.vscode/settings.json`):**
```json
{
  "fstar.executable": "fstar.exe",
  "fstar.flyCheck": "lax",  // Fast checking while typing
  "fstar.verifyOnOpen": false,  // Don't verify immediately
  "fstar.debug": false
}
```

**Keybindings:**
- `Ctrl+Shift+.` - Verify to cursor
- `Ctrl+Shift+Enter` - Verify full file
- `Ctrl+.` - Show hints

#### Emacs Integration

```elisp
;; .emacs configuration
(require 'fstar-mode)

(setq fstar-executable "fstar.exe")
(setq fstar-smt-executable "z3")

;; Keybindings
;; C-c C-n - Next proof
;; C-c C-p - Previous proof
;; C-c RET - Verify to point
```

---

### 5. CI/CD Integration

#### GitHub Actions Example

```yaml
name: F* Verification

on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2

      - name: Install F*
        run: |
          wget https://github.com/FStarLang/FStar/releases/download/v2025.10.06/fstar-v2025.10.06-Linux-x86_64.tar.gz
          tar -xzf fstar-*.tar.gz
          echo "${PWD}/fstar-*/bin" >> $GITHUB_PATH

      - name: Verify all files
        run: |
          ./scripts/verify_all.sh

      - name: Upload verification log
        if: failure()
        uses: actions/upload-artifact@v2
        with:
          name: verification-log
          path: verification.log
```

#### Performance Targets for CI

- **Individual file:** <10 seconds
- **Total suite:** <5 minutes (for merge queue)
- **Nightly verification:** <30 minutes (for full regression)

**If exceeding targets:**
1. Profile with `--query_stats`
2. Find slowest 20% of queries
3. Optimize those specifically
4. Consider parallelizing verification

---

### 6. Real-World Verification Patterns

#### Pattern 1: Stateful Verification (ST Monad)

```fsharp
module StatefulExample

open FStar.ST

// Mutable reference with invariant
let create_counter (init:nat{init < 100})
  : ST (ref nat)
       (requires (fun h -> True))
       (ensures (fun h0 r h1 ->
         modifies !{} h0 h1 /\
         sel h1 r = init))
  = alloc init

// Increment with overflow check
let increment (r:ref nat)
  : ST unit
       (requires (fun h -> sel h r < 100))
       (ensures (fun h0 _ h1 ->
         modifies !{r} h0 h1 /\
         sel h1 r = sel h0 r + 1))
  = r := !r + 1
```

#### Pattern 2: Ghost Code (Proof-Only)

```fsharp
// Ghost parameters don't appear in compiled code
let rec fold_right (#a:Type) (#b:Type) (f:a -> b -> b) (xs:list a) (init:b)
  : Tot b (decreases xs)
  = match xs with
    | [] -> init
    | hd :: tl -> f hd (fold_right f tl init)

// Ghost proof that fold is correct
let rec fold_length_correct (#a:Type) (xs:list a)
  : Lemma (fold_right (fun _ acc -> acc + 1) xs 0 = length xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> fold_length_correct tl
```

#### Pattern 3: Refinement Subtyping

```fsharp
type nat = x:int{x >= 0}
type pos = x:int{x > 0}
type even = x:int{x % 2 = 0}
type even_pos = x:int{x > 0 && x % 2 = 0}

// Subtyping relationships (automatic)
let example (x:even_pos) : pos = x  // Works: even_pos <: pos
let example2 (x:even_pos) : even = x  // Works: even_pos <: even
let example3 (x:even_pos) : nat = x   // Works: even_pos <: nat

// Use this for flexible APIs
val process_positive: pos -> int
val process_even: even -> int

let process_both (x:even_pos) =
  process_positive x,  // No conversion needed
  process_even x       // Subtyping handles it
```

---

### 7. Testing Strategy

#### Unit Tests (Assertions)

```fsharp
// Test individual functions with assertions
let test_factorial () : unit =
  assert (factorial 0 = 1);
  assert (factorial 1 = 1);
  assert (factorial 5 = 120);
  ()

// Test properties
let test_append_length () : unit =
  let xs = [1;2;3] in
  let ys = [4;5] in
  assert (length (append xs ys) = length xs + length ys);
  ()
```

#### Property-Based Tests (QuickCheck-style)

```fsharp
// Prove properties hold for ALL inputs
val append_nil_left: #a:Type -> xs:list a ->
  Lemma (append [] xs = xs)

val append_nil_right: #a:Type -> xs:list a ->
  Lemma (append xs [] = xs)

val append_assoc: #a:Type -> xs:list a -> ys:list a -> zs:list a ->
  Lemma (append (append xs ys) zs = append xs (append ys zs))
```

#### Regression Tests

```bash
# Save known-good verification times
fstar.exe --query_stats file.fst > baseline.txt

# On each change, compare
fstar.exe --query_stats file.fst > current.txt
diff baseline.txt current.txt

# Alert if verification slowed >2x
```

---

### 8. Migration & Upgrade Strategies

#### Upgrading F* Versions

```bash
# 1. Create branch
git checkout -b upgrade-fstar-2025.10.06

# 2. Install new version alongside old
# Keep old: ~/.fstar/old-version/
# Install new: ~/.fstar/new-version/

# 3. Try verification
export PATH=~/.fstar/new-version/bin:$PATH
./scripts/verify_all.sh 2>&1 | tee upgrade.log

# 4. Fix deprecations and breaking changes
# Common issues:
# - Syntax changes (rare)
# - Performance regressions (check with --query_stats)
# - New warnings (turn into errors with --warn_error)

# 5. Update CI/CD to new version

# 6. Merge when all passes
```

#### Handling Breaking Changes

```fsharp
// Old F* version might accept:
let old_style = ...

// New version requires:
#push-options "--warn_error -271"  // Suppress specific warning
let migrated_style = ...
#pop-options

// Eventually fix properly:
let proper_style = ...
```

---

### 9. Advanced Debugging Techniques

#### Reading SMT-LIB Queries

```bash
fstar.exe --log_queries file.fst
# Produces: queries-file.smt2

# Inspect SMT-LIB:
cat queries-file.smt2
```

```smt2
; Example SMT-LIB output
(declare-fun x () Int)
(assert (> x 0))            ; From: type positive = x:int{x > 0}
(declare-fun result () Int)
(assert (= result (* 2 x))) ; From: let result = 2 * x
(assert (not (> result 0))) ; Negated postcondition (proof by contradiction)
(check-sat)                 ; Z3 should return "unsat" (proof succeeds)
```

**When to use:**
- Understanding why Z3 fails
- Debugging SMTPat patterns (do they trigger?)
- Finding performance issues (huge queries = slow)

#### Manual Z3 Testing

```bash
# Extract query from --log_queries
cat queries-file.smt2

# Run Z3 manually with profiling
z3 -v:2 -st queries-file.smt2

# Try different Z3 tactics
z3 -smt2 -in < queries-file.smt2
```

#### Interactive Debugging with F* REPL

```fsharp
// In fstar.exe --in (REPL mode)
#push-options "--admit_smt_queries true"  // Temporarily ignore SMT
let test x = x + 1  // Check if syntax is right
#pop-options

// Now verify properly
let test (x:nat) : nat = x + 1
```

---

### 10. Performance Benchmarking

#### Baseline Metrics

**Good performance targets:**
- Simple refinement (x > 0): <50ms
- List length proof: <100ms
- Inductive proof (append): <200ms
- Complex proof (merge sort): <1-2 seconds
- Full file (100-500 lines): <5 seconds

**If exceeding:**
1. Profile with `--query_stats`
2. Check for accidental NIA (variable * variable)
3. Minimize fuel usage
4. Add SMTPat patterns for automation
5. Break into smaller lemmas

#### Comparing Approaches

```bash
# Approach A: High fuel
time fstar.exe --fuel 10 approach-a.fst

# Approach B: Explicit proof
time fstar.exe --fuel 2 approach-b.fst

# Compare:
# Approach A: 15 seconds (slow!)
# Approach B: 2 seconds (fast!)
# Winner: Explicit proof
```

---

## When to Use This Skill

### ✅ Activate When:
- Writing F* code and encountering errors
- Optimizing slow verification (<5 sec target)
- Setting up F* in new environment
- Debugging specific proof failures
- Teaching practical F* development
- Building production verified systems
- Integrating F* into CI/CD
- Migrating between F* versions

### ⏸️ Defer to `/skill/SKILL.md` When:
- Learning dependent type theory
- Understanding refinement type semantics
- Studying effect system foundations
- Exploring theoretical aspects
- Proving complex mathematical properties
- Designing new type system features

---

## Quick Reference Card

### Most Useful F* Flags
```bash
--query_stats          # Profile verification performance
--log_queries          # Inspect SMT-LIB queries
--fuel N               # Control recursive unfolding
--z3rlimit N           # Set Z3 resource limit
--debug SMT            # Verbose Z3 debugging
```

### Debugging Workflow
```
1. Error → Read carefully
2. Isolate → Minimal failing case
3. Profile → --query_stats
4. Inspect → --log_queries
5. Fix → Targeted solution
6. Verify → Re-run
```

### Performance Optimization
```
1. Profile first (--query_stats)
2. Find bottleneck (slowest 20%)
3. Minimize fuel (find minimum needed)
4. Add SMTPat (automate lemmas)
5. Help Z3 (assertions for NIA)
6. Measure improvement
```

### Common Fixes
- **Timeout** → Add fuel or split lemma
- **Unknown** → Add assertions (especially NIA)
- **Unsat** → Fix code logic
- **Module not found** → Add `open` statement
- **Can't prove termination** → Add `decreases` clause

---

## Integration with Course Materials

This skill complements:
- **Week 1-2:** Basic F* syntax and refinement types (`/skill/SKILL.md`)
- **Week 3:** SMT solver debugging (this skill's focus)
- **Week 4-6:** Advanced patterns and libraries
- **Installation:** `INSTALLATION_GUIDE.md`, `scripts/install_fstar.sh`
- **Testing:** `TESTING.md`, `scripts/verify_all.sh`

---

## Expertise Levels

- **L2 (Apprentice):** Can debug basic failures, use --query_stats
- **L3 (Competent):** Optimize fuel, understand NIA, use SMTPat
- **L4 (Proficient):** Read SMT-LIB, design patterns, fast verification
- **L5 (Expert):** Build production systems, CI/CD, advanced optimization
- **L6 (Master):** F* internals, custom tactics, Z3 theory solvers

---

## Resources

### Official Documentation
- F* Tutorial: https://fstar-lang.org/tutorial
- F* Wiki: https://github.com/FStarLang/FStar/wiki
- Z3 Guide: https://microsoft.github.io/z3/

### Community
- F* Zulip: https://fstar.zulipchat.com/
- GitHub Issues: https://github.com/FStarLang/FStar/issues
- Paper: "Dependent Types and Multi-Monadic Effects in F*" (POPL 2016)

### Course Materials
- `instructor_guide/week_03_teaching_notes.md` - SMT debugging guide
- `TESTING.md` - Verification quality gates
- `SMT_COVERAGE_ANALYSIS.md` - Deep SMT analysis

---

**Status:** Production-ready practical F* development expertise
**Activation:** Automatic when debugging or optimizing F* code
**Complements:** `/skill/SKILL.md` (theoretical foundations)
**Coverage:** L2-L6 practical skills for productive verification engineering
