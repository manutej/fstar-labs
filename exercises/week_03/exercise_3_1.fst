module Exercise3_1

(**
 * Exercise 3.1: Reading SMT-LIB Queries
 *
 * Learning Objectives:
 * - Understand how F* translates refinement types to SMT-LIB
 * - Read Z3 query output to debug verification failures
 * - Connect F* syntax to underlying solver constraints
 *
 * Skills:
 * - Use --log_queries to inspect SMT-LIB
 * - Identify translated refinement predicates
 * - Understand quantifier instantiation
 *
 * Time Estimate: 30-40 minutes
 * Difficulty: L2 (Intermediate)
 *)

(**
 * PART 1: Basic Translation (10 minutes)
 *
 * Consider this F* code:
 *)

type positive = x:int{x > 0}

let double (n:positive) : positive =
  2 * n

(**
 * When F* verifies this, it sends a query to Z3. Here's the SMT-LIB output
 * (simplified for readability):
 *
 * ```smt2
 * (declare-fun n () Int)
 * (assert (> n 0))               ; Precondition: n is positive
 * (declare-fun result () Int)
 * (assert (= result (* 2 n)))     ; Definition: result = 2 * n
 * (assert (not (> result 0)))     ; Negated postcondition (proof by contradiction)
 * (check-sat)
 * ```
 *
 * If Z3 returns "unsat", F* knows the postcondition MUST hold.
 * If Z3 returns "sat", F* found a counterexample.
 *)

(**
 * TODO 1: Answer these questions by analyzing the SMT-LIB above
 *
 * Q1: What does the assertion `(assert (> n 0))` represent in F* terms?
 * A1: (* YOUR ANSWER HERE *)
 *
 * Q2: Why is the postcondition NEGATED (`(assert (not (> result 0)))`)?
 * A2: (* YOUR ANSWER HERE *)
 *
 * Q3: If Z3 returns "sat", what does that mean for our proof?
 * A3: (* YOUR ANSWER HERE *)
 *)

(**
 * PART 2: Verification Failure Analysis (15 minutes)
 *
 * Now consider this BUGGY code:
 *)

let add_positive (x:positive) (y:positive) : positive =
  x + y - 1  // OOPS! This can be 0 when x=y=1

(**
 * The SMT-LIB query looks like:
 *
 * ```smt2
 * (declare-fun x () Int)
 * (declare-fun y () Int)
 * (assert (> x 0))
 * (assert (> y 0))
 * (declare-fun result () Int)
 * (assert (= result (- (+ x y) 1)))
 * (assert (not (> result 0)))      ; Is result always positive?
 * (check-sat)
 * (get-model)
 * ```
 *
 * Z3 returns:
 * ```
 * sat
 * (model
 *   (define-fun x () Int 1)
 *   (define-fun y () Int 1)
 *   (define-fun result () Int 0))
 * ```
 *)

(**
 * TODO 2: Interpret the counterexample
 *
 * Q4: What values did Z3 find that break our proof?
 * A4: (* YOUR ANSWER HERE *)
 *
 * Q5: Why is result = 0 a problem for our postcondition?
 * A5: (* YOUR ANSWER HERE *)
 *
 * Q6: How would you FIX the function to make it verify?
 * A6: (* YOUR ANSWER HERE *)
 *)

// TODO 3: Implement the FIXED version
let add_positive_fixed (x:positive) (y:positive) : positive =
  admit() // Replace with correct implementation

(**
 * PART 3: Quantifier Translation (10 minutes)
 *
 * Consider this lemma about list length:
 *)

val length: list 'a -> nat
let rec length xs =
  match xs with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val append_length_lemma: xs:list 'a -> ys:list 'a ->
  Lemma (length (xs @ ys) = length xs + length ys)

(**
 * F* translates this to SMT-LIB with QUANTIFIERS:
 *
 * ```smt2
 * (assert (forall ((xs (Seq Int)) (ys (Seq Int)))
 *   (= (length (seq.++ xs ys))
 *      (+ (length xs) (length ys)))))
 * ```
 *
 * This is a UNIVERSALLY QUANTIFIED formula - it must hold for ALL lists.
 *)

(**
 * TODO 4: Understanding quantifiers
 *
 * Q7: What does "forall" mean in the SMT-LIB formula?
 * A7: (* YOUR ANSWER HERE *)
 *
 * Q8: Why can't Z3 just "try all possible lists" to verify this?
 * A8: (* YOUR ANSWER HERE *)
 *
 * Q9: What might go wrong if Z3 doesn't instantiate this quantifier correctly?
 * A9: (* YOUR ANSWER HERE *)
 *)

(**
 * PART 4: Hands-On Debugging (5 minutes)
 *
 * TODO 5: Generate SMT-LIB for your own code
 *
 * Instructions:
 * 1. Write a simple function with a refinement type (below)
 * 2. Run: fstar.exe --log_queries exercise_3_1.fst
 * 3. Look in queries-*.smt2 files
 * 4. Paste a snippet of the SMT-LIB output in the comments below
 *)

// TODO: Write your function here
type even = x:int{x % 2 = 0}

let add_evens (x:even) (y:even) : even =
  admit() // Implement this

(**
 * TODO: Paste SMT-LIB snippet here (5-10 lines)
 *
 * SMT-LIB OUTPUT:
 * ```smt2
 * (* PASTE HERE *)
 * ```
 *)

(**
 * REFLECTION (Answer after completing the exercise)
 *
 * Q10: How does seeing the SMT-LIB help you debug verification failures?
 * A10: (* YOUR ANSWER HERE *)
 *
 * Q11: When would you use --log_queries in your own work?
 * A11: (* YOUR ANSWER HERE *)
 *
 * Q12: What's the relationship between F* refinement types and SMT assertions?
 * A12: (* YOUR ANSWER HERE *)
 *)

(**
 * ASSESSMENT RUBRIC (10 points total)
 *
 * Part 1 (3 points):
 * - Q1: Correct identification of precondition (1 pt)
 * - Q2: Understands proof by contradiction (1 pt)
 * - Q3: Interprets "sat" correctly (1 pt)
 *
 * Part 2 (3 points):
 * - Q4-Q5: Correct counterexample interpretation (1 pt)
 * - Q6: Valid fix suggested (1 pt)
 * - add_positive_fixed: Working implementation (1 pt)
 *
 * Part 3 (2 points):
 * - Q7-Q9: Understands quantifiers (2 pts)
 *
 * Part 4 (2 points):
 * - add_evens: Correct implementation (1 pt)
 * - SMT-LIB snippet: Demonstrates --log_queries usage (1 pt)
 *
 * Bonus (+1 point):
 * - Q10-Q12: Insightful reflections connecting concepts
 *)

(**
 * LEARNING OUTCOMES
 *
 * After this exercise, you should be able to:
 * ✓ Run F* with --log_queries to inspect SMT-LIB
 * ✓ Read basic SMT-LIB assertions and declarations
 * ✓ Interpret Z3 counterexamples to fix verification failures
 * ✓ Understand the connection between F* types and solver constraints
 * ✓ Recognize quantified formulas in SMT-LIB output
 *
 * Next: Exercise 3.2 will teach you the DEBUGGING TOOLKIT for common failures.
 *)
