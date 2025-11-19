module Exercise3_4

(**
 * Exercise 3.4: Fuel Minimization for Performance
 *
 * Learning Objectives:
 * - Understand fuel as a performance optimization tool
 * - Find minimum fuel needed for verification
 * - Trade off between fuel and explicit proofs
 * - Measure and optimize verification performance
 *
 * Key Insight:
 * MORE fuel ≠ BETTER verification
 * - Too little: verification fails
 * - Too much: verification is SLOW
 * - Just right: fast and correct!
 *
 * Time Estimate: 45-60 minutes
 * Difficulty: L3 (Advanced - requires performance analysis)
 *)

(**
 * PART 1: What Is Fuel? (10 minutes)
 *
 * Fuel controls how many times F* "unfolds" recursive definitions
 * when translating to SMT-LIB for Z3.
 *)

let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n - 1)

(**
 * With fuel = 0:
 *   factorial(5) stays as "factorial(5)" in SMT-LIB
 *   Z3 sees it as an opaque function
 *
 * With fuel = 1:
 *   factorial(5) → 5 * factorial(4)
 *   Still not fully expanded
 *
 * With fuel = 6:
 *   factorial(5) → 5 * 4 * 3 * 2 * 1 * 1
 *   Fully expanded!
 *)

(**
 * TODO 1: Understanding fuel unrolling
 *
 * Q1: Why do we need fuel = 6 to prove factorial(5) = 120?
 * A1: (* YOUR ANSWER *)
 *
 * Q2: How much fuel would we need for factorial(10)?
 * A2: (* YOUR ANSWER *)
 *
 * Q3: What happens if we set fuel = 100 for factorial(5)?
 *    (Will it be faster or slower than fuel = 6?)
 * A3: (* YOUR ANSWER *)
 *)

(**
 * PART 2: Finding Minimum Fuel (15 minutes)
 *
 * Your mission: Find the MINIMUM fuel for each assertion.
 *)

let rec length (#a:Type) (xs:list a) : nat =
  match xs with
  | [] -> 0
  | _ :: tl -> 1 + length tl

let rec append (#a:Type) (xs:list a) (ys:list a) : list a =
  match xs with
  | [] -> ys
  | hd :: tl -> hd :: append tl ys

(**
 * TODO 2: Fuel experiments
 *
 * For each assertion below:
 * 1. Try fuel = 0, 1, 2, 3, ... until it verifies
 * 2. Record the MINIMUM fuel needed
 * 3. Measure verification time with --query_stats
 *
 * Run: fstar.exe --fuel N --query_stats exercise_3_4.fst
 *)

// Experiment 1: Length of explicit list
// #push-options "--fuel N"
// let test1 = assert (length [1;2;3] = 3)
// #pop-options

(**
 * | Fuel | Verifies? | Time (ms) |
 * |------|-----------|-----------|
 * |  0   |           |           |
 * |  1   |           |           |
 * |  2   |           |           |
 * |  3   |           |           |
 * |  4   |           |           |
 *
 * Minimum fuel: ___
 *)

// Experiment 2: Length of empty list
// #push-options "--fuel N"
// let test2 = assert (length ([]<:list int>) = 0)
// #pop-options

(**
 * Minimum fuel: ___
 * Why is this different from test1? ___
 *)

// Experiment 3: Append with explicit lists
// #push-options "--fuel N"
// let test3 = assert (append [1;2] [3;4] = [1;2;3;4])
// #pop-options

(**
 * Minimum fuel: ___
 *)

(**
 * TODO 3: Analyze the pattern
 *
 * Q4: What's the relationship between list length and minimum fuel?
 * A4: (* YOUR ANSWER *)
 *
 * Q5: Why does increasing fuel make verification SLOWER?
 * A5: (* YOUR ANSWER *)
 *)

(**
 * PART 3: Fuel vs Explicit Proofs (15 minutes)
 *
 * Sometimes you can AVOID needing fuel by writing an explicit proof.
 *)

// Approach 1: HIGH FUEL (brute force)
#push-options "--fuel 10"
let append_nil_right (#a:Type) (xs:list a)
  : Lemma (append xs [] = xs) =
  ()  // Z3 figures it out with enough fuel
#pop-options

// Approach 2: LOW FUEL + INDUCTION (elegant)
let rec append_nil_right_proof (#a:Type) (xs:list a)
  : Lemma (append xs [] = xs) =
  match xs with
  | [] -> ()
  | _ :: tl -> append_nil_right_proof tl  // Inductive case

(**
 * The second approach uses recursion to guide the proof,
 * requiring MUCH less fuel (usually fuel = 1 or 2).
 *)

(**
 * TODO 4: Compare approaches
 *
 * Measure verification time for both:
 *
 * | Approach              | Fuel | Time (ms) |
 * |-----------------------|------|-----------|
 * | append_nil_right      | 10   |           |
 * | append_nil_right_proof| 2    |           |
 *
 * Q6: Which is faster? By how much?
 * A6: (* YOUR ANSWER *)
 *
 * Q7: Which is more maintainable for large proofs?
 * A7: (* YOUR ANSWER *)
 *)

(**
 * TODO 5: Write your own fuel-efficient proof
 *
 * Prove that length is preserved by append:
 *)

// High-fuel version (fill in the fuel needed)
#push-options "--fuel ___"  // What fuel do you need?
let append_length_bruteforce (#a:Type) (xs:list a) (ys:list a)
  : Lemma (length (append xs ys) = length xs + length ys) =
  ()
#pop-options

// Low-fuel version with explicit recursion
let rec append_length_efficient (#a:Type) (xs:list a) (ys:list a)
  : Lemma (length (append xs ys) = length xs + length ys) =
  admit() // YOUR PROOF HERE (use pattern matching and recursion)

(**
 * PART 4: Performance Profiling (10 minutes)
 *
 * Let's verify some larger structures and measure performance.
 *)

let rec sum_up_to (n:nat) : nat =
  if n = 0 then 0
  else n + sum_up_to (n - 1)

(**
 * TODO 6: Performance experiment
 *
 * Try to verify: assert (sum_up_to 10 = 55)
 *
 * Test with different fuel values and measure:
 *
 * | Fuel | Verifies? | Time (ms) | SMT-LIB size |
 * |------|-----------|-----------|--------------|
 * |  5   |           |           |              |
 * | 10   |           |           |              |
 * | 11   |           |           |              |
 * | 15   |           |           |              |
 * | 20   |           |           |              |
 *
 * Q8: What's the minimum fuel needed?
 * A8: ___
 *
 * Q9: What happens to verification time as fuel increases beyond the minimum?
 * A9: (* YOUR ANSWER *)
 *
 * Q10: Use --log_queries to check SMT-LIB size. Does it grow with fuel?
 * A10: (* YOUR ANSWER *)
 *)

(**
 * PART 5: Fuel Optimization Strategies (10 minutes)
 *
 * When verification is slow, here's your decision tree:
 *)

(**
 * STRATEGY 1: Start with minimal fuel
 * - Use fuel = 1 by default
 * - Increase only when needed
 * - Never use fuel > 10 without profiling
 *)

(**
 * STRATEGY 2: Localize fuel increases
 * - Use #push-options / #pop-options around specific definitions
 * - Don't set global high fuel
 *)

// BAD: Global high fuel
// #set-options "--fuel 20"
// let everything_is_slow = ...

// GOOD: Localized fuel
let rec fast_function = ...  // Uses default fuel = 1

#push-options "--fuel 5"
let this_one_needs_fuel = ...
#pop-options

let back_to_fast = ...  // Back to fuel = 1

(**
 * STRATEGY 3: Replace fuel with proofs
 * - Write explicit recursive lemmas
 * - Use calc proofs to guide Z3
 * - Add assert statements as hints
 *)

(**
 * TODO 7: Apply optimization strategies
 *
 * This code is SLOW (>5 seconds). Optimize it!
 *)

let rec slow_reverse (#a:Type) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd :: tl -> append (slow_reverse tl) [hd]

#push-options "--fuel 15"  // YIKES! Way too much fuel
let test_reverse = assert (slow_reverse [1;2;3;4;5] = [5;4;3;2;1])
#pop-options

(**
 * Step 1: Measure current performance
 * Time with fuel = 15: ___ ms
 *
 * Step 2: Find minimum fuel
 * Minimum fuel needed: ___
 *
 * Step 3: Try adding assertions to reduce fuel
 *)

#push-options "--fuel ___"  // Your optimized fuel
let test_reverse_optimized =
  // Add helpful assertions here
  assert (slow_reverse [1;2;3;4;5] = [5;4;3;2;1])
#pop-options

(**
 * Q11: What's your optimized fuel value?
 * A11: ___
 *
 * Q12: What assertions did you add to help Z3?
 * A12: (* YOUR ANSWER *)
 *
 * Q13: What's the new verification time?
 * A13: ___ ms (speedup: ___x)
 *)

(**
 * BONUS CHALLENGE: Zero-Fuel Verification
 *
 * Can you prove append_nil_right with fuel = 0?
 * You'll need to write a VERY explicit proof.
 *)

#push-options "--fuel 0"
let rec append_nil_right_zero_fuel (#a:Type) (xs:list a)
  : Lemma (append xs [] = xs) =
  admit() // CHALLENGE: Make this work with fuel = 0!
#pop-options

(**
 * REFLECTION QUESTIONS
 *
 * Q14: What's your fuel optimization workflow? (List 3-5 steps)
 * A14: (* YOUR ANSWER *)
 *
 * Q15: When would you choose high fuel over writing an explicit proof?
 * A15: (* YOUR ANSWER *)
 *
 * Q16: How does fuel relate to the SMT-LIB queries sent to Z3?
 * A16: (* YOUR ANSWER *)
 *)

(**
 * ASSESSMENT RUBRIC (15 points total)
 *
 * Part 1: Understanding (3 points)
 * - Q1-Q3: Correct fuel reasoning (3 pts)
 *
 * Part 2: Experiments (4 points)
 * - Fuel experiments: Complete tables (2 pts)
 * - Q4-Q5: Pattern analysis (2 pts)
 *
 * Part 3: Explicit Proofs (4 points)
 * - TODO 4: Performance comparison (2 pts)
 * - append_length_efficient: Working proof (2 pts)
 *
 * Part 4: Profiling (2 points)
 * - TODO 6: Complete performance table (2 pts)
 *
 * Part 5: Optimization (2 points)
 * - TODO 7: Successful optimization (2 pts)
 *
 * Bonus (+3 points):
 * - append_nil_right_zero_fuel: Works with fuel = 0 (2 pts)
 * - Q14-Q16: Insightful reflections (1 pt)
 *)

(**
 * LEARNING OUTCOMES
 *
 * After this exercise, you should be able to:
 * ✓ Understand fuel as a performance knob, not a magic fix
 * ✓ Find minimum fuel needed for verification
 * ✓ Measure verification performance with --query_stats
 * ✓ Trade off between fuel and explicit proofs
 * ✓ Optimize slow verifications systematically
 * ✓ Use #push-options / #pop-options to localize fuel
 *
 * Next: Exercise 3.5 will teach SMT pattern engineering (SMTPat)
 *)

(**
 * INSTRUCTOR NOTES
 *
 * This exercise is HANDS-ON and requires actual F* installation.
 * Students need to run experiments and collect data.
 *
 * Common student mistakes:
 * 1. Setting fuel = 100 "just to be safe" (terrible for performance)
 * 2. Not using #push-options / #pop-options (global fuel pollution)
 * 3. Not profiling before optimizing (guessing instead of measuring)
 * 4. Thinking more fuel always helps (it can make things worse!)
 *
 * Teaching tips:
 * - Show live demo of verification time with different fuel
 * - Use --query_stats to visualize performance
 * - Emphasize MEASUREMENT over intuition
 * - Connect fuel to SMT-LIB query size (--log_queries)
 *
 * Time distribution:
 * - Part 1: 10 min (reading + questions)
 * - Part 2: 15 min (experiments take time)
 * - Part 3: 15 min (writing proofs)
 * - Part 4: 10 min (profiling)
 * - Part 5: 10 min (optimization)
 * Total: 60 min (can reduce by making some experiments optional)
 *
 * F* VERSION NOTE: Requires F* 2024.01.13+
 * --query_stats flag might not exist in older versions.
 *
 * Performance baselines (on reference machine):
 * - factorial(5) with fuel=6: ~50ms
 * - factorial(5) with fuel=20: ~200ms (4x slower!)
 * - append_nil_right with fuel=10: ~100ms
 * - append_nil_right_proof with fuel=2: ~30ms (3x faster!)
 *)

(**
 * FURTHER READING
 *
 * F* documentation on fuel:
 * - https://fstar-lang.org/tutorial (Chapter on SMT encoding)
 * - https://github.com/FStarLang/FStar/wiki/Fuel
 *
 * Performance optimization:
 * - "Optimizing F* Verification" (FStar wiki)
 * - Z3 resource limits: https://microsoft.github.io/z3/
 *
 * Alternative approaches:
 * - SMTPat patterns (Exercise 3.5)
 * - calc proofs (Week 4)
 * - Proof automation with tactics (Week 6)
 *)
