module MiniProjectSMTPerformance

(**
 * Week 3 Mini-Project: SMT Performance Optimization
 *
 * Estimated Time: 4-6 hours
 * Difficulty: Advanced (L3 Competent)
 * Due: End of Week 3 (Friday 11:59 PM)
 *
 * Learning Objectives:
 * - Diagnose and fix verification performance problems
 * - Apply the complete SMT debugging toolkit
 * - Optimize fuel usage for large proofs
 * - Use SMTPat patterns to automate lemma application
 * - Understand the interaction between F* and Z3
 *
 * Project Overview:
 * You are given SLOW, poorly-optimized verification code. Your mission:
 * 1. Profile to find bottlenecks (using --query_stats)
 * 2. Diagnose failure modes (timeout, unknown, unsat)
 * 3. Apply optimizations systematically
 * 4. Achieve target verification time (<5 seconds total)
 *
 * Grading Breakdown:
 * - Part 1 (10 points): Profiling and diagnosis
 * - Part 2 (15 points): Optimization implementation
 * - Part 3 (10 points): SMTPat pattern design
 * - Part 4 (5 points): Documentation and analysis
 * - Part 5 (Extra Credit): +5 points for advanced optimizations
 * Total: 40 points (45 with extra credit)
 *
 * Performance Targets:
 * - Baseline (provided code): ~30-60 seconds
 * - Your optimized code: <5 seconds
 * - Exceptional: <2 seconds
 *
 * Tips for Success:
 * - Profile BEFORE optimizing (measure, don't guess!)
 * - Fix the slowest queries first (biggest impact)
 * - Use --query_stats to track progress
 * - Document WHY each optimization works
 * - Test incrementally (optimize, verify, repeat)
 *)

open FStar.List.Tot

(**
 * =============================================================================
 * SCENARIO: Binary Search Tree Verification
 * =============================================================================
 *
 * You work at a verification engineering firm. A client provided this
 * BST verification code, but it's PAINFULLY slow (60+ seconds to verify).
 * They need it under 5 seconds for CI/CD pipeline integration.
 *
 * Your task: Optimize without changing correctness guarantees.
 *)

(**
 * =============================================================================
 * PART 1: Profiling and Diagnosis (10 points)
 * =============================================================================
 *
 * First, understand WHERE the performance problems are.
 *)

// Binary Search Tree definition
type tree =
  | Leaf : tree
  | Node : left:tree -> value:int -> right:tree -> tree

// BST invariant: all left values < root < all right values
let rec is_bst (t:tree) : bool =
  match t with
  | Leaf -> true
  | Node l v r ->
      (forall x. mem x l ==> x < v) &&
      (forall x. mem x r ==> x > v) &&
      is_bst l && is_bst r

and mem (x:int) (t:tree) : bool =
  match t with
  | Leaf -> false
  | Node l v r -> x = v || mem x l || mem x r

// Type alias for trees satisfying BST property
type bst = t:tree{is_bst t}

(**
 * TODO 1.1: Profile the baseline (3 points)
 *
 * Run: fstar.exe --query_stats exercise_3_miniproject.fst
 *
 * Fill in this table for the ORIGINAL CODE (before optimizations):
 *
 * | Function/Lemma           | Verification Time (ms) | Fuel | z3rlimit |
 * |--------------------------|------------------------|------|----------|
 * | is_bst                   |                        |      |          |
 * | mem                      |                        |      |          |
 * | insert (below)           |                        |      |          |
 * | insert_preserves_bst     |                        |      |          |
 * | search_correct           |                        |      |          |
 * | TOTAL                    |                        |      |          |
 *)

(**
 * TODO 1.2: Identify bottlenecks (3 points)
 *
 * Q1: Which function/lemma is the SLOWEST?
 * A1: (* YOUR ANSWER *)
 *
 * Q2: What failure mode do you observe (timeout, unknown, or slow-but-works)?
 * A2: (* YOUR ANSWER *)
 *
 * Q3: Use --log_queries. How large are the SMT-LIB queries (in lines)?
 * A3: (* YOUR ANSWER *)
 *)

(**
 * TODO 1.3: Root cause analysis (4 points)
 *
 * Q4: Why is the slow function slow? (Check: fuel, NIA, quantifiers, etc.)
 * A4: (* YOUR ANSWER *)
 *
 * Q5: What debug flags did you use to diagnose this?
 * A5: (* YOUR ANSWER *)
 *
 * Q6: Propose 2-3 optimization strategies for the bottleneck.
 * A6: (* YOUR ANSWER *)
 *)

(**
 * =============================================================================
 * PART 2: Optimization Implementation (15 points)
 * =============================================================================
 *
 * Now apply your optimizations. The code below is INTENTIONALLY SLOW.
 *)

// SLOW INSERT (baseline - DO NOT MODIFY THIS, use for profiling)
let rec insert_slow (t:tree) (x:int) : tree =
  match t with
  | Leaf -> Node Leaf x Leaf
  | Node l v r ->
      if x < v then Node (insert_slow l x) v r
      else if x > v then Node l v (insert_slow r x)
      else t

// SLOW PROOF: Insert preserves BST property
#push-options "--fuel 10 --z3rlimit 50"  // YIKES! Way too much
let rec insert_preserves_bst_slow (t:bst) (x:int)
  : Lemma (is_bst (insert_slow t x)) =
  match t with
  | Leaf -> ()
  | Node l v r ->
      insert_preserves_bst_slow l x;
      insert_preserves_bst_slow r x;
      // No additional help for Z3
      ()
#pop-options

(**
 * TODO 2.1: Optimize insert (5 points)
 *
 * Create an optimized version with:
 * - Minimal fuel (find the minimum needed)
 * - Helpful assertions for Z3
 * - Better termination measures if needed
 *)

let rec insert_fast (t:tree) (x:int) : tree =
  admit() // YOUR OPTIMIZED IMPLEMENTATION

(**
 * TODO 2.2: Optimize the BST preservation proof (10 points)
 *
 * Strategies to try:
 * - Reduce fuel to minimum
 * - Add strategic assertions
 * - Use SMTPat patterns (see Part 3)
 * - Break into helper lemmas
 *
 * Target: <500ms verification time (down from 20+ seconds)
 *)

// Your optimized proof:
#push-options "--fuel ___ --z3rlimit ___"  // Find minimal values
let rec insert_preserves_bst_fast (t:bst) (x:int)
  : Lemma (is_bst (insert_fast t x)) =
  admit() // YOUR OPTIMIZED PROOF
#pop-options

(**
 * Documentation (required):
 *
 * Q7: What fuel did you use in the optimized version?
 * A7: (* YOUR ANSWER *)
 *
 * Q8: How much did you reduce verification time? (Original → Optimized)
 * A8: (* YOUR ANSWER *)
 *
 * Q9: What was the KEY optimization that had the biggest impact?
 * A9: (* YOUR ANSWER *)
 *)

(**
 * =============================================================================
 * PART 3: SMTPat Pattern Engineering (10 points)
 * =============================================================================
 *
 * Add automatic lemma application using SMTPat patterns.
 *)

(**
 * TODO 3.1: Design a lemma with SMTPat (5 points)
 *
 * Write a lemma that Z3 can auto-apply when checking BST operations.
 * Choose ONE of these (or design your own):
 *
 * Option A: mem_insert (x is in tree after inserting x)
 * Option B: mem_preserves (if y was in tree, still in after inserting x)
 * Option C: insert_increases_size (tree size after insert)
 *)

// TODO: Implement your chosen lemma with SMTPat
val your_lemma: (* YOUR SIGNATURE *)
  Lemma (* YOUR POST CONDITION *)
        [(* YOUR SMTPAT PATTERN *)]

let rec your_lemma (* YOUR PARAMS *) =
  admit() // YOUR IMPLEMENTATION

(**
 * Q10: What lemma did you choose and why?
 * A10: (* YOUR ANSWER *)
 *
 * Q11: What pattern did you use in SMTPat?
 * A11: (* YOUR ANSWER *)
 *
 * Q12: How did you verify the pattern triggers correctly?
 * A12: (* YOUR ANSWER *)
 *)

(**
 * TODO 3.2: Test automatic application (5 points)
 *
 * Write a proof that USES your lemma WITHOUT explicitly calling it.
 * The SMTPat should make Z3 apply it automatically.
 *)

let test_automatic_lemma (t:bst) (x:int) (y:int)
  : Lemma (* YOUR POSTCONDITION USING THE LEMMA *) =
  ()  // Should work with no manual lemma calls!

(**
 * Q13: Does your test verify without manual lemma calls?
 * A13: (* YOUR ANSWER *)
 *
 * Q14: If not, debug: What went wrong with your pattern?
 * A14: (* YOUR ANSWER *)
 *)

(**
 * =============================================================================
 * PART 4: Documentation and Analysis (5 points)
 * =============================================================================
 *
 * Professional verification engineering requires clear documentation.
 *)

(**
 * TODO 4.1: Performance summary table (2 points)
 *
 * | Metric                    | Baseline | Optimized | Improvement |
 * |---------------------------|----------|-----------|-------------|
 * | Total verification time   |          |           |             |
 * | Max fuel used             |          |           |             |
 * | Slowest query             |          |           |             |
 * | Number of Z3 queries      |          |           |             |
 * | Average query time        |          |           |             |
 *)

(**
 * TODO 4.2: Optimization report (3 points)
 *
 * Write a brief report (10-15 sentences) for your client explaining:
 * 1. What performance problems you found
 * 2. What optimizations you applied
 * 3. Why each optimization worked
 * 4. Final performance numbers
 * 5. Recommendations for maintaining performance
 *
 * REPORT:
 * (* YOUR REPORT HERE *)
 *)

(**
 * =============================================================================
 * PART 5: Extra Credit (5 points)
 * =============================================================================
 *
 * Choose ONE advanced optimization:
 *)

(**
 * OPTION A: Implement calc proof (2 points)
 *
 * Rewrite one of your proofs using F*'s calc syntax for clarity.
 *)

// Example structure:
// let lemma_with_calc ... =
//   calc (==) {
//     expression1;
//     == { reason1 }
//     expression2;
//     == { reason2 }
//     expression3;
//   }

(**
 * OPTION B: Multiple SMTPat patterns (2 points)
 *
 * Write a lemma with MULTIPLE SMTPat patterns (OR relationship).
 * Test that EITHER pattern triggers the lemma.
 *)

(**
 * OPTION C: Performance profiling tool (3 points)
 *
 * Write a script that:
 * 1. Parses --query_stats output
 * 2. Identifies queries >100ms
 * 3. Suggests optimizations (fuel, patterns, etc.)
 *
 * Submit as: profile_tool.sh or profile_tool.py
 *)

(**
 * OPTION D: Compare F* versions (2 points)
 *
 * Test your code on 2+ F* versions (e.g., 2023.09.03 vs 2024.01.13).
 * Document performance differences. Has Z3 improved? Regressed?
 *)

(**
 * Document your extra credit work:
 *
 * Q15: Which option did you choose?
 * A15: (* YOUR ANSWER *)
 *
 * Q16: What did you learn from this advanced optimization?
 * A16: (* YOUR ANSWER *)
 *)

(**
 * =============================================================================
 * TESTING AND VALIDATION
 * =============================================================================
 *)

// Test cases for your optimized code
let test1 = assert (is_bst (insert_fast Leaf 5))
let test2 = assert (is_bst (insert_fast (insert_fast Leaf 5) 3))
let test3 = assert (is_bst (insert_fast (insert_fast (insert_fast Leaf 5) 3) 7))

// These should verify quickly (<100ms each)
#push-options "--query_stats"
let _ = insert_preserves_bst_fast Leaf 5
let _ = insert_preserves_bst_fast (insert_fast Leaf 5) 3
#pop-options

(**
 * =============================================================================
 * SUBMISSION CHECKLIST
 * =============================================================================
 *
 * Before submitting, verify:
 * [ ] All TODO sections completed
 * [ ] All questions answered (Q1-Q14 minimum, Q15-Q16 for extra credit)
 * [ ] Code verifies with F* (no admits in final submission)
 * [ ] Performance target met (<5 seconds total verification)
 * [ ] Profiling tables filled with actual measurements
 * [ ] Optimization report written
 * [ ] Test cases pass
 * [ ] (Optional) Extra credit completed and documented
 *
 * Submit:
 * - This .fst file (completed)
 * - performance_report.txt (your measurements)
 * - (Optional) Extra credit artifacts
 *)

(**
 * =============================================================================
 * ASSESSMENT RUBRIC
 * =============================================================================
 *
 * PART 1: Profiling (10 points)
 * - TODO 1.1: Complete baseline table (3 pts)
 * - TODO 1.2: Correct bottleneck identification (3 pts)
 * - TODO 1.3: Accurate root cause analysis (4 pts)
 *
 * PART 2: Optimization (15 points)
 * - TODO 2.1: insert_fast implementation (5 pts)
 *   - Correct implementation (3 pts)
 *   - Performance improvement (2 pts)
 * - TODO 2.2: insert_preserves_bst_fast (10 pts)
 *   - Correct proof (5 pts)
 *   - Meets performance target <500ms (3 pts)
 *   - Minimal fuel usage (2 pts)
 *
 * PART 3: SMTPat (10 points)
 * - TODO 3.1: Lemma design and implementation (5 pts)
 *   - Correct lemma (2 pts)
 *   - Good pattern choice (2 pts)
 *   - Working SMTPat (1 pt)
 * - TODO 3.2: Automatic application test (5 pts)
 *   - Test verifies without manual calls (3 pts)
 *   - Debugging analysis (2 pts)
 *
 * PART 4: Documentation (5 points)
 * - TODO 4.1: Performance summary (2 pts)
 * - TODO 4.2: Optimization report (3 pts)
 *   - Clear explanation (1 pt)
 *   - Technical accuracy (1 pt)
 * - Professional presentation (1 pt)
 *
 * EXTRA CREDIT (5 points)
 * - Choose one option, implement thoroughly
 * - Maximum bonus: +5 points
 *
 * TOTAL: 40 points (45 with extra credit)
 *
 * PERFORMANCE BONUSES:
 * - <5 seconds: Standard expectation (0 bonus)
 * - <2 seconds: +2 points (exceptional optimization)
 * - <1 second: +3 points (outstanding work!)
 *
 * DEDUCTIONS:
 * - Code doesn't verify: -20 points (must fix!)
 * - Uses admits in final submission: -5 points each
 * - Missing profiling data: -5 points
 * - Incomplete documentation: -3 points
 *)

(**
 * =============================================================================
 * INSTRUCTOR NOTES
 * =============================================================================
 *
 * Learning Goals:
 * This mini-project integrates ALL Week 3 concepts:
 * - Reading SMT-LIB queries (Exercise 3.1)
 * - Using debug toolkit (Exercise 3.2)
 * - Understanding LIA vs NIA (Exercise 3.3)
 * - Minimizing fuel (Exercise 3.4)
 * - SMTPat patterns (Exercise 3.5)
 *
 * Expected Student Approach:
 * 1. Profile baseline (30-60 min)
 * 2. Optimize insert_preserves_bst (2-3 hours)
 * 3. Add SMTPat patterns (1-2 hours)
 * 4. Write documentation (30-60 min)
 * 5. (Optional) Extra credit (1-2 hours)
 *
 * Common Struggles:
 * - Not profiling first (guessing optimizations)
 * - Using fuel=20 instead of finding minimum
 * - SMTPat patterns that never trigger
 * - Incomplete documentation
 *
 * Success Indicators:
 * - Systematic profiling workflow
 * - Evidence-based optimization choices
 * - Understanding WHY optimizations work
 * - Professional documentation
 *
 * Grading Guidelines:
 * - Focus on PROCESS over final numbers
 * - Reward systematic debugging
 * - Partial credit for attempted optimizations
 * - Bonus for exceptional performance
 *
 * F* VERSION NOTE: Requires F* 2024.01.13+
 * Performance numbers will vary by machine and F* version.
 *
 * Reference Implementation Performance (instructor machine):
 * - Baseline: 45 seconds
 * - Optimized: 2.3 seconds
 * - Best student: 0.8 seconds (exceptional!)
 *)
