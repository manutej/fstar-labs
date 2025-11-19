module Exercise3_3

(**
 * Exercise 3.3: LIA vs NIA - Understanding Decidability
 *
 * Learning Objectives:
 * - Distinguish Linear Integer Arithmetic (LIA) from Nonlinear (NIA)
 * - Understand why NIA causes "unknown" solver results
 * - Learn techniques to help Z3 with nonlinear constraints
 * - Recognize when multiplication is linear vs nonlinear
 *
 * Key Concept:
 * LIA (Linear Integer Arithmetic) is DECIDABLE - Z3 always terminates
 * NIA (Nonlinear Integer Arithmetic) is UNDECIDABLE - Z3 may fail
 *
 * Time Estimate: 40-50 minutes
 * Difficulty: L3 (Advanced - requires mathematical reasoning)
 *)

(**
 * PART 1: What Makes Arithmetic "Linear"? (15 minutes)
 *
 * LINEAR means: coefficients are CONSTANTS, not variables
 *)

// EXAMPLE 1: This is LINEAR (LIA)
type positive = x:int{x > 0}

let double (n:positive) : positive =
  2 * n  // CONSTANT * variable is LINEAR

(**
 * Why is `2 * n` linear?
 * - The coefficient 2 is a CONSTANT
 * - SMT formula: (= result (* 2 n))
 * - This is in the LIA theory (decidable)
 *)

// EXAMPLE 2: This is NONLINEAR (NIA)
let square (n:positive) : nat =
  n * n  // variable * variable is NONLINEAR

(**
 * Why is `n * n` nonlinear?
 * - Both factors are VARIABLES
 * - SMT formula: (= result (* n n))
 * - This is in the NIA theory (undecidable)
 *)

(**
 * TODO 1: Classify these expressions
 *
 * For each expression, mark it as LIA (linear) or NIA (nonlinear):
 *
 * | Expression      | LIA or NIA? | Why? |
 * |-----------------|-------------|------|
 * | 3 * x + 5       |             |      |
 * | x * y           |             |      |
 * | x + y + z       |             |      |
 * | x * x           |             |      |
 * | 10 * x - 20 * y |             |      |
 * | x * (y + 1)     |             |      |
 * | x / 2           |             |      |
 * | x * 2 * 3       |             |      |
 *)

(**
 * PART 2: When NIA Causes Failures (15 minutes)
 *
 * Let's see NIA in action and why it fails.
 *)

// This function LOOKS simple but involves NIA
type even = x:int{x % 2 = 0}

let multiply_evens (x:even) (y:even) : even =
  x * y  // This might FAIL! (x * y involves NIA reasoning)

(**
 * Why does this fail?
 * - Z3 needs to prove: (x * y) % 2 = 0
 * - Given: x % 2 = 0 and y % 2 = 0
 * - This requires reasoning about PRODUCTS of variables (NIA)
 * - Z3 might return "unknown"
 *)

(**
 * TODO 2: Fix multiply_evens with an assertion
 *
 * Hint: Help Z3 by explicitly asserting useful facts
 *)
let multiply_evens_fixed (x:even) (y:even) : even =
  // Add assertion here to help Z3
  admit() // Replace with real implementation

(**
 * Q1: What assertion did you add? Why does it help?
 * A1: (* YOUR ANSWER *)
 *)

// Another NIA example: proving positivity
type positive = x:int{x > 0}

let multiply_positive (x:positive) (y:positive) : positive =
  x * y  // This SHOULD work but might timeout

(**
 * TODO 3: Understanding the difficulty
 *
 * Q2: Why is proving x * y > 0 harder than proving 2 * x > 0?
 * A2: (* YOUR ANSWER *)
 *
 * Q3: What mathematical fact would help Z3 prove this?
 *     (Hint: "positive * positive = ?")
 * A3: (* YOUR ANSWER *)
 *)

(**
 * PART 3: Techniques for Helping Z3 with NIA (15 minutes)
 *
 * Technique 1: ASSERTIONS (manual hints)
 *)

let square_positive (x:positive) : positive =
  assert (x > 0);  // Remind Z3 of the precondition
  x * x

(**
 * Why does this help?
 * - Z3 might "forget" x > 0 during NIA reasoning
 * - The assertion brings it back into focus
 * - Acts as a HINT for the solver
 *)

// Technique 2: LEMMAS (reusable facts)
val multiply_positive_lemma: x:positive -> y:positive ->
  Lemma (x * y > 0)

let multiply_positive_lemma x y =
  // Z3 can usually prove this with a little help
  assert (x > 0 && y > 0);
  assert (x * y >= x);  // Hint: x * y at least as big as x
  ()

// Now use the lemma
let safe_multiply (x:positive) (y:positive) : positive =
  multiply_positive_lemma x y;  // Apply the lemma
  x * y  // Now Z3 knows the result is positive!

(**
 * TODO 4: Write your own lemma
 *
 * Prove that squaring preserves positivity:
 *)
val square_preserves_positive: x:positive -> Lemma (x * x > 0)

let square_preserves_positive x =
  admit() // YOUR PROOF HERE

(**
 * TODO 5: Use your lemma
 *)
let safe_square (x:positive) : positive =
  admit() // Use square_preserves_positive, then return x * x

(**
 * PART 4: LIA vs NIA in the Wild (10 minutes)
 *
 * Real-world example: array indexing
 *)

val get: #a:Type -> xs:list a -> i:nat{i < List.length xs} -> a

(**
 * Suppose we have this buggy code:
 *)
let get_double_index (#a:Type) (xs:list a) (i:nat{2 * i + 1 < List.length xs})
  : a =
  get xs (2 * i)  // This is FINE (LIA)

let get_product_index (#a:Type) (xs:list a) (i:nat) (j:nat{i * j < List.length xs})
  : a =
  get xs (i * j)  // This might FAIL (NIA in the bound check)

(**
 * TODO 6: Analysis
 *
 * Q4: Why does get_double_index verify easily?
 * A4: (* YOUR ANSWER *)
 *
 * Q5: Why might get_product_index have trouble?
 * A5: (* YOUR ANSWER *)
 *
 * Q6: How would you fix get_product_index?
 * A6: (* YOUR ANSWER *)
 *)

(**
 * PART 5: Practical Decision Tree (5 minutes)
 *
 * When you encounter verification failures involving multiplication:
 *
 * STEP 1: Is it CONSTANT * variable?
 *   → YES: It's LIA, problem is elsewhere
 *   → NO: Go to STEP 2
 *
 * STEP 2: Is it variable * variable?
 *   → YES: It's NIA, go to STEP 3
 *
 * STEP 3: Can you help Z3?
 *   → Add assertions (assert x > 0)
 *   → Write lemmas (prove mathematical facts)
 *   → Use SMTPat patterns (advanced, Week 4)
 *   → Restructure code to avoid NIA
 *)

(**
 * TODO 7: Apply the decision tree
 *
 * This function fails to verify. Debug it using the decision tree.
 *)

let mystery (x:nat{x < 100}) (y:nat{y < 100}) : nat =
  x * y  // Fails: "Could not prove post-condition"

(**
 * Q7: What's the verification goal?
 * A7: (* YOUR ANSWER *)
 *
 * Q8: Is this LIA or NIA?
 * A8: (* YOUR ANSWER *)
 *
 * Q9: What assertion would help? (Don't just guess - explain WHY)
 * A9: (* YOUR ANSWER *)
 *)

// TODO: Fix mystery
let mystery_fixed (x:nat{x < 100}) (y:nat{y < 100}) : nat =
  admit() // YOUR FIX HERE

(**
 * BONUS CHALLENGE: Avoiding NIA Entirely
 *
 * Sometimes you can RESTRUCTURE code to eliminate NIA.
 *)

// BEFORE (NIA):
let area_rectangle (width:positive) (height:positive) : positive =
  width * height  // NIA reasoning required

// AFTER (recursive, LIA only):
let rec area_rectangle_lia (width:positive) (height:positive)
  : Tot positive (decreases width) =
  if width = 1 then height
  else height + area_rectangle_lia (width - 1) height

(**
 * TODO 8 (BONUS): Explain the transformation
 *
 * Q10: Why is area_rectangle_lia easier for Z3?
 * A10: (* YOUR ANSWER *)
 *
 * Q11: What's the trade-off of this approach?
 * A11: (* YOUR ANSWER *)
 *)

(**
 * REFLECTION QUESTIONS
 *
 * Q12: In your own words, what's the difference between LIA and NIA?
 * A12: (* YOUR ANSWER *)
 *
 * Q13: When would you choose to help Z3 with assertions vs writing a lemma?
 * A13: (* YOUR ANSWER *)
 *
 * Q14: Have you encountered NIA failures in previous exercises? Where?
 * A14: (* YOUR ANSWER *)
 *)

(**
 * ASSESSMENT RUBRIC (15 points total)
 *
 * Part 1: Classification (3 points)
 * - TODO 1: Correct LIA/NIA classification for 8 expressions (3 pts)
 *
 * Part 2: Failures (3 points)
 * - multiply_evens_fixed: Correct fix (1 pt)
 * - Q2-Q3: Understanding difficulty (2 pts)
 *
 * Part 3: Techniques (4 points)
 * - square_preserves_positive: Working proof (2 pts)
 * - safe_square: Correct usage (2 pts)
 *
 * Part 4: Real-world (3 points)
 * - Q4-Q6: Array indexing analysis (3 pts)
 *
 * Part 5: Decision Tree (2 points)
 * - Q7-Q9: Systematic debugging (1 pt)
 * - mystery_fixed: Correct fix (1 pt)
 *
 * Bonus (+3 points):
 * - Q10-Q11: area_rectangle_lia explanation (2 pts)
 * - Q12-Q14: Deep reflections (1 pt)
 *)

(**
 * LEARNING OUTCOMES
 *
 * After this exercise, you should be able to:
 * ✓ Distinguish LIA from NIA by analyzing expressions
 * ✓ Predict when Z3 might struggle with nonlinear arithmetic
 * ✓ Help Z3 with assertions and lemmas
 * ✓ Apply the LIA/NIA decision tree to debug failures
 * ✓ Recognize NIA in real-world verification scenarios
 * ✓ Trade off between NIA reasoning and code restructuring
 *
 * Next: Exercise 3.4 will optimize fuel usage for performance
 *)

(**
 * INSTRUCTOR NOTES
 *
 * This exercise is MATHEMATICALLY challenging for students without
 * formal logic background. Key teaching points:
 *
 * 1. Decidability is about GUARANTEES, not speed
 *    - LIA: Z3 WILL terminate (but might be slow)
 *    - NIA: Z3 MIGHT not terminate or return "unknown"
 *
 * 2. "Linear" means linear in VARIABLES, not constants
 *    - Students often confuse "2 * x * 3" (still linear!) with "x * y" (nonlinear)
 *
 * 3. Assertions are HINTS, not proofs
 *    - `assert (x > 0)` doesn't prove anything
 *    - It just reminds Z3 of facts it might have forgotten
 *
 * 4. NIA is not "broken" - it's fundamentally harder
 *    - Analogy: solving x² = 4 (easy) vs x² + y² = z² (Fermat, hard!)
 *
 * Common student mistakes:
 * - Thinking LIA means "simple" (it can still be complex)
 * - Adding random assertions hoping something works
 * - Not understanding WHY an assertion helps
 *
 * Extension ideas:
 * - Show SMT-LIB for LIA vs NIA queries
 * - Profile verification time: LIA vs NIA
 * - Introduce integer division (also nonlinear!)
 *
 * F* VERSION NOTE: Requires F* 2024.01.13+
 * Earlier versions might behave differently with NIA.
 *)

(**
 * MATHEMATICAL BACKGROUND (Optional Reading for Students)
 *
 * Why is NIA undecidable?
 *
 * Gödel's Incompleteness Theorem (1931) shows that arithmetic with
 * multiplication is fundamentally incomplete - there's no algorithm
 * that can decide ALL true statements about integers.
 *
 * LIA avoids this by restricting to ADDITION only (with constant multipliers).
 * This restriction makes it decidable (Presburger Arithmetic, 1929).
 *
 * NIA allows full multiplication, hitting Gödel's limits.
 *
 * Further reading:
 * - Presburger Arithmetic: https://en.wikipedia.org/wiki/Presburger_arithmetic
 * - Decidability in SMT: "Satisfiability Modulo Theories" (Barrett et al, 2009)
 * - Z3 Theory Solvers: https://microsoft.github.io/z3/
 *)
