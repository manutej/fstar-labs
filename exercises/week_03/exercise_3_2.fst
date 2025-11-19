module Exercise3_2

(**
 * Exercise 3.2: SMT Debugging Toolkit
 *
 * Learning Objectives:
 * - Diagnose three types of verification failures (timeout, unknown, unsat)
 * - Use fuel and depth controls to fix recursive function verification
 * - Apply debug flags effectively: --debug, --z3rlimit, --query_stats
 *
 * Skills:
 * - Identify failure modes from F* error messages
 * - Select appropriate debugging flags for each problem
 * - Optimize verification performance
 *
 * Time Estimate: 45-60 minutes
 * Difficulty: L2-L3 (Intermediate to Advanced)
 *)

(**
 * PART 1: Three Failure Modes (15 minutes)
 *
 * F* verification can fail in three ways. Let's learn to recognize each.
 *)

// Scenario A: TIMEOUT
// This verification takes too long (>2 seconds default)
let rec fibonacci (n:nat) : nat =
  if n <= 1 then n
  else fibonacci (n - 1) + fibonacci (n - 2)

// Attempting to prove a property about fibonacci might TIMEOUT
// because the solver explores exponential paths
let fib_positive (n:nat) : Lemma (fibonacci n >= 0) =
  admit() // Would timeout without fuel

(**
 * TODO 1: Understanding TIMEOUT failures
 *
 * Q1: What does a "timeout" mean in Z3?
 * A1: (* YOUR ANSWER HERE *)
 *
 * Q2: Which debug flag increases the timeout limit?
 * A2: (* YOUR ANSWER HERE *)
 *
 * Q3: Is increasing timeout always the right solution? Why or why not?
 * A3: (* YOUR ANSWER HERE *)
 *)

// Scenario B: UNKNOWN
// Z3 can't decide if the query is satisfiable
type my_type = x:int{x * x >= 0 && x * x * x < 100}

// This involves NONLINEAR ARITHMETIC (x * x * x)
// Z3 might return "unknown" because NIA is undecidable
let test_unknown : my_type = 4  // Might fail with "unknown"

(**
 * TODO 2: Understanding UNKNOWN failures
 *
 * Q4: What does "unknown" mean in Z3's response?
 * A4: (* YOUR ANSWER HERE *)
 *
 * Q5: Why does nonlinear arithmetic (x * x * x) cause "unknown" results?
 * A5: (* YOUR ANSWER HERE *)
 *
 * Q6: How can you FIX "unknown" failures? (Hint: assertions)
 * A6: (* YOUR ANSWER HERE *)
 *)

// Scenario C: UNSAT (but we expected SAT)
// This means Z3 proved the NEGATION of what we wanted
let broken_max (x:int) (y:int) : z:int{z >= x && z >= y && (z = x || z = y)} =
  if x > y then x else x  // BUG! Should be "y" in else branch

(**
 * Z3 will report: "Could not prove post-condition"
 * This is actually an UNSAT result (no model satisfies our spec)
 *)

(**
 * TODO 3: Fix the broken_max function
 *)
let fixed_max (x:int) (y:int) : z:int{z >= x && z >= y && (z = x || z = y)} =
  admit() // YOUR FIX HERE

(**
 * PART 2: Fuel and Depth Controls (20 minutes)
 *
 * Fuel controls how many times F* "unrolls" recursive function definitions
 * when sending queries to Z3.
 *)

let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n - 1)

// Without enough fuel, F* can't prove this
// let test_factorial = assert (factorial 5 = 120)  // FAILS with default fuel

(**
 * TODO 4: Understanding fuel
 *
 * Q7: What is "fuel" in F* verification?
 * A7: (* YOUR ANSWER HERE *)
 *
 * Q8: Why does `assert (factorial 5 = 120)` need fuel >= 6?
 * A8: (* YOUR ANSWER HERE *)
 *
 * Q9: Run this with different fuel values and observe:
 *     fstar.exe --fuel 1 exercise_3_2.fst   (what happens?)
 *     fstar.exe --fuel 6 exercise_3_2.fst   (what happens?)
 * A9: (* YOUR OBSERVATIONS HERE *)
 *)

// Setting fuel locally
#push-options "--fuel 6 --ifuel 6"
let test_factorial_with_fuel = assert (factorial 5 = 120)
#pop-options

(**
 * TODO 5: Minimal fuel experiment
 *
 * What's the MINIMUM fuel needed to prove each assertion?
 * Try different values and fill in the table:
 *
 * | Assertion                  | Minimum Fuel | Why? |
 * |----------------------------|--------------|------|
 * | factorial 0 = 1            |              |      |
 * | factorial 1 = 1            |              |      |
 * | factorial 2 = 2            |              |      |
 * | factorial 5 = 120          |              |      |
 * | factorial 10 = 3628800     |              |      |
 *)

(**
 * PART 3: Debug Flags Toolkit (15 minutes)
 *
 * F* provides many debug flags. Here are the most useful:
 *
 * --log_queries           Show SMT-LIB queries sent to Z3
 * --query_stats           Show timing for each query
 * --debug SMT             Verbose SMT debugging output
 * --debug Yes             Maximum verbosity (very noisy!)
 * --z3rlimit N            Set Z3 resource limit (replaces time limit)
 * --z3refresh             Force Z3 restart between queries
 *)

(**
 * TODO 6: Debug flags practice
 *
 * Q10: When would you use --log_queries?
 * A10: (* YOUR ANSWER HERE *)
 *
 * Q11: What information does --query_stats provide?
 * A11: (* YOUR ANSWER HERE *)
 *
 * Q12: What's the difference between --z3rlimit and fuel?
 * A12: (* YOUR ANSWER HERE *)
 *)

(**
 * PART 4: Hands-On Debugging Challenge (15 minutes)
 *
 * The function below has verification issues. Your job:
 * 1. Identify the failure mode (timeout, unknown, or wrong spec)
 * 2. Use debug flags to diagnose the problem
 * 3. Fix it with the minimal set of changes
 *)

let rec sum_up_to (n:nat) : nat =
  if n = 0 then 0
  else n + sum_up_to (n - 1)

// This SHOULD verify but might fail
let gauss_formula (n:nat) : Lemma (sum_up_to n = n * (n + 1) / 2) =
  admit() // TODO: Make this verify

(**
 * TODO 7: Debug the lemma
 *
 * Step 1: Try to verify without admit(). What error do you get?
 * A: (* YOUR ANSWER *)
 *
 * Step 2: What debug flags did you use to diagnose it?
 * A: (* YOUR ANSWER *)
 *
 * Step 3: What fix did you apply?
 * A: (* YOUR ANSWER *)
 *
 * Step 4: Implement the fix below
 *)

// Your fixed version:
#push-options (* YOUR OPTIONS HERE *)
let gauss_formula_fixed (n:nat) : Lemma (sum_up_to n = n * (n + 1) / 2) =
  admit() // Replace with real proof (may need induction)
#pop-options

(**
 * PART 5: Performance Optimization (10 minutes)
 *
 * Sometimes verification is SLOW not because it's wrong, but because
 * it's inefficient. Let's measure and optimize.
 *)

let rec slow_append (#a:Type) (xs:list a) (ys:list a) : list a =
  match xs with
  | [] -> ys
  | hd :: tl -> hd :: slow_append tl ys

(**
 * TODO 8: Performance measurement
 *
 * Run with query stats:
 *   fstar.exe --query_stats exercise_3_2.fst
 *
 * Q13: How long does slow_append take to verify? (in milliseconds)
 * A13: (* YOUR MEASUREMENT *)
 *
 * Q14: Now add a termination measure:
 *)

let rec fast_append (#a:Type) (xs:list a) (ys:list a)
  : Tot (list a) (decreases xs) =  // Explicit decreases
  match xs with
  | [] -> ys
  | hd :: tl -> hd :: fast_append tl ys

(**
 * Q15: Does the termination measure improve verification time? By how much?
 * A15: (* YOUR MEASUREMENT *)
 *
 * Q16: Why does helping F* with termination speed things up?
 * A16: (* YOUR ANSWER *)
 *)

(**
 * REFLECTION QUESTIONS
 *
 * Q17: What's your debugging workflow when a proof fails?
 *      (List 3-5 steps in order)
 * A17: (* YOUR WORKFLOW *)
 *
 * Q18: When would you use fuel vs z3rlimit?
 * A18: (* YOUR ANSWER *)
 *
 * Q19: What's the most useful debug flag you learned today? Why?
 * A19: (* YOUR ANSWER *)
 *)

(**
 * ASSESSMENT RUBRIC (15 points total)
 *
 * Part 1: Failure Modes (4 points)
 * - Q1-Q3: Understands timeout (1 pt)
 * - Q4-Q6: Understands unknown (1 pt)
 * - fixed_max: Correct implementation (2 pts)
 *
 * Part 2: Fuel (4 points)
 * - Q7-Q9: Understands fuel concept (2 pts)
 * - TODO 5: Correct minimum fuel table (2 pts)
 *
 * Part 3: Debug Flags (3 points)
 * - Q10-Q12: Correct flag usage (3 pts)
 *
 * Part 4: Debugging Challenge (3 points)
 * - TODO 7: Systematic debugging process (1 pt)
 * - gauss_formula_fixed: Working proof (2 pts)
 *
 * Part 5: Performance (1 point)
 * - Q13-Q16: Measurements and analysis (1 pt)
 *
 * Bonus (+2 points):
 * - Q17-Q19: Insightful reflections (1 pt)
 * - Complete all measurements with actual data (1 pt)
 *)

(**
 * LEARNING OUTCOMES
 *
 * After this exercise, you should be able to:
 * ✓ Recognize timeout, unknown, and unsat failure modes
 * ✓ Use fuel and ifuel to control recursive unfolding
 * ✓ Apply debug flags systematically (--log_queries, --query_stats, etc.)
 * ✓ Measure verification performance
 * ✓ Optimize slow proofs with termination measures
 * ✓ Build a systematic debugging workflow
 *
 * Next: Exercise 3.3 will deep-dive into LIA vs NIA (decidability)
 *)

(**
 * INSTRUCTOR NOTES
 *
 * Common student mistakes:
 * 1. Confusing fuel with z3rlimit (fuel = unrolling, rlimit = solver time)
 * 2. Using --debug Yes instead of specific debug flags (too noisy)
 * 3. Not starting with --query_stats to find slow queries
 * 4. Increasing fuel without understanding WHY it's needed
 *
 * Time estimate validation:
 * - Part 1: 15 min (reading + fixing broken_max)
 * - Part 2: 20 min (fuel experiments take time)
 * - Part 3: 15 min (reading documentation)
 * - Part 4: 15 min (debugging challenge is hard)
 * - Part 5: 10 min (measurement)
 * Total: 75 min (adjust to 45-60 by making some parts optional)
 *
 * F* VERSION NOTE: This exercise requires F* 2024.01.13 or later
 * for --query_stats flag.
 *)
