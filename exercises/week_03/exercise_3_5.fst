module Exercise3_5

(**
 * Exercise 3.5: SMT Pattern Engineering (Advanced)
 *
 * Learning Objectives:
 * - Understand quantifier instantiation in Z3
 * - Use SMTPat to trigger automatic lemma application
 * - Design effective patterns that avoid performance issues
 * - Debug pattern matching with --log_queries
 *
 * Key Concept:
 * SMTPat = "SMT Pattern" - tells Z3 WHEN to apply a lemma automatically
 * Without patterns, you must call lemmas manually everywhere.
 * With patterns, Z3 applies them automatically when needed!
 *
 * Time Estimate: 60-75 minutes
 * Difficulty: L4 (Expert - requires deep understanding of SMT)
 *)

(**
 * PART 1: The Quantifier Problem (15 minutes)
 *
 * First, let's see WHY we need patterns.
 *)

let rec length (#a:Type) (xs:list a) : nat =
  match xs with
  | [] -> 0
  | _ :: tl -> 1 + length tl

let rec append (#a:Type) (xs:list a) (ys:list a) : list a =
  match xs with
  | [] -> ys
  | hd :: tl -> hd :: append tl ys

// This lemma is TRUE and useful:
val append_length_lemma: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) = length xs + length ys)

let rec append_length_lemma #a xs ys =
  match xs with
  | [] -> ()
  | _ :: tl -> append_length_lemma tl ys

(**
 * Without SMTPat, you must call the lemma MANUALLY:
 *)
let test_manual (xs:list int) (ys:list int) (zs:list int)
  : Lemma (length (append (append xs ys) zs) =
           length xs + length ys + length zs) =
  append_length_lemma xs ys;       // Manual call 1
  append_length_lemma (append xs ys) zs  // Manual call 2

(**
 * This is tedious! Can Z3 do it automatically?
 *)

(**
 * TODO 1: Understanding the problem
 *
 * Q1: Why doesn't Z3 automatically apply append_length_lemma?
 * A1: (* YOUR ANSWER *)
 *
 * Q2: What would happen if Z3 tried ALL possible instantiations of the lemma?
 * A2: (* YOUR ANSWER *)
 *
 * Q3: How many times did we manually call the lemma in test_manual?
 * A3: (* YOUR ANSWER *)
 *)

(**
 * PART 2: SMTPat to the Rescue (15 minutes)
 *
 * SMTPat tells Z3: "Apply this lemma whenever you see PATTERN"
 *)

// Same lemma, but with SMTPat annotation:
val append_length_auto: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) = length xs + length ys)
        [SMTPat (length (append xs ys))]  // PATTERN

let rec append_length_auto #a xs ys =
  match xs with
  | [] -> ()
  | _ :: tl -> append_length_auto tl ys

(**
 * Now Z3 applies it AUTOMATICALLY when it sees "length (append xs ys)"
 *)

let test_auto (xs:list int) (ys:list int) (zs:list int)
  : Lemma (length (append (append xs ys) zs) =
           length xs + length ys + length zs) =
  ()  // No manual calls needed! Z3 figures it out!

(**
 * TODO 2: Understanding SMTPat
 *
 * Q4: What pattern triggers append_length_auto?
 * A4: (* YOUR ANSWER *)
 *
 * Q5: When Z3 sees "length (append [1;2] [3;4])", what happens?
 * A5: (* YOUR ANSWER *)
 *
 * Q6: Compare test_manual and test_auto. Which is easier to maintain?
 * A6: (* YOUR ANSWER *)
 *)

(**
 * PART 3: Designing Good Patterns (20 minutes)
 *
 * Not all patterns are created equal. Let's learn pattern design.
 *)

// EXAMPLE 1: Too general (BAD)
val bad_pattern_1: #a:Type -> xs:list a ->
  Lemma (length xs >= 0)
        [SMTPat (length xs)]  // Triggers on EVERY length call!

(**
 * Why is this bad?
 * - Triggers on EVERY list length
 * - Creates huge proof search space
 * - Verification becomes VERY slow
 *)

// EXAMPLE 2: Too specific (BAD)
val bad_pattern_2: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) = length xs + length ys)
        [SMTPat (append xs ys); SMTPat (length (append xs ys))]
        // Two patterns = triggers less often than needed

(**
 * Why is this bad?
 * - Requires BOTH patterns to match
 * - Might not trigger when needed
 *)

// EXAMPLE 3: Just right (GOOD)
val good_pattern: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) = length xs + length ys)
        [SMTPat (length (append xs ys))]  // Specific but not too specific

(**
 * Why is this good?
 * - Triggers when we care about length of appended lists
 * - Doesn't trigger on every length
 * - Natural and predictable
 *)

(**
 * TODO 3: Pattern design practice
 *
 * For each lemma, choose the BEST SMTPat pattern:
 *)

// Lemma A: Append is associative
val append_assoc: #a:Type -> xs:list a -> ys:list a -> zs:list a ->
  Lemma (append (append xs ys) zs = append xs (append ys zs))

(**
 * Which pattern is best?
 * Option 1: [SMTPat (append xs ys)]
 * Option 2: [SMTPat (append (append xs ys) zs)]
 * Option 3: [SMTPat (append xs (append ys zs))]
 *
 * Q7: Which option is best and why?
 * A7: (* YOUR ANSWER *)
 *)

// Lemma B: Reverse of reverse is identity
let rec reverse (#a:Type) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]

val reverse_reverse: #a:Type -> xs:list a ->
  Lemma (reverse (reverse xs) = xs)

(**
 * Which pattern is best?
 * Option 1: [SMTPat (reverse xs)]
 * Option 2: [SMTPat (reverse (reverse xs))]
 * Option 3: No pattern (call manually)
 *
 * Q8: Which option is best and why?
 * A8: (* YOUR ANSWER *)
 *)

(**
 * PART 4: Implementing Your Own Patterns (20 minutes)
 *
 * Now you design and implement SMTPat-annotated lemmas.
 *)

// TODO 4: Add SMTPat to this lemma
let rec append_nil_right (#a:Type) (xs:list a)
  : Lemma (append xs [] = xs)
          [(* YOUR SMTPAT HERE *)] =
  match xs with
  | [] -> ()
  | _ :: tl -> append_nil_right tl

(**
 * Q9: What pattern did you choose?
 * A9: (* YOUR ANSWER *)
 *
 * Q10: Test it - does this verify without manual lemma calls?
 *)
let test_append_nil (xs:list int) (ys:list int)
  : Lemma (append (append xs ys) [] = append xs ys) =
  ()  // Should work if your pattern is correct!

(**
 * TODO 5: Write a lemma with SMTPat for list reversal
 *
 * Prove that length is preserved by reverse:
 *)
val reverse_length: #a:Type -> xs:list a ->
  Lemma (length (reverse xs) = length xs)
        [(* YOUR SMTPAT HERE *)]

let rec reverse_length #a xs =
  admit() // YOUR PROOF HERE

(**
 * Test it:
 *)
let test_reverse_length (xs:list int)
  : Lemma (length (reverse (reverse xs)) = length xs) =
  ()  // Should auto-apply reverse_length twice!

(**
 * PART 5: Debugging Patterns (10 minutes)
 *
 * Sometimes patterns don't trigger when you expect. How to debug?
 *)

// TECHNIQUE 1: Use --log_queries to see instantiations
// In the SMT-LIB output, look for:
// (assert (forall ...))  <- Your lemma as quantifier
// And check when Z3 instantiates it

// TECHNIQUE 2: Use --debug SMT for verbose output
// Shows every pattern match and instantiation

// TECHNIQUE 3: Add assert to force instantiation
let test_force_pattern (xs:list int) (ys:list int) =
  assert (length (append xs ys) >= 0);  // Forces pattern match
  admit()

(**
 * TODO 6: Debug this failing proof
 *)

val mystery_lemma: #a:Type -> xs:list a ->
  Lemma (length (append xs xs) = 2 * length xs)
        [SMTPat (append xs xs)]  // Is this pattern right?

let rec mystery_lemma #a xs =
  match xs with
  | [] -> ()
  | _ :: tl -> mystery_lemma tl

// This SHOULD verify but might not:
let test_mystery (xs:list int)
  : Lemma (length (append xs xs) = 2 * length xs) =
  ()  // Does your pattern trigger?

(**
 * Q11: Does test_mystery verify with the current pattern?
 * A11: (* YOUR ANSWER *)
 *
 * Q12: If not, what's wrong with the pattern?
 * A12: (* YOUR ANSWER *)
 *
 * Q13: Fix the pattern below:
 *)
val mystery_lemma_fixed: #a:Type -> xs:list a ->
  Lemma (length (append xs xs) = 2 * length xs)
        [(* YOUR FIXED PATTERN *)]

let rec mystery_lemma_fixed #a xs =
  match xs with
  | [] -> ()
  | _ :: tl -> mystery_lemma_fixed tl

(**
 * BONUS CHALLENGE: Multiple Patterns (Advanced)
 *
 * Sometimes you need MULTIPLE patterns (OR relationship, not AND).
 *)

// This lemma should trigger on EITHER pattern:
val append_comm_length: #a:Type -> xs:list a -> ys:list a ->
  Lemma (length (append xs ys) = length (append ys xs))
        [SMTPat (append xs ys); SMTPat (append ys xs)]

(**
 * Q14 (BONUS): Does [SMTPat P; SMTPat Q] mean "P AND Q" or "P OR Q"?
 * A14: (* YOUR ANSWER *)
 *
 * Q15 (BONUS): How would you test this empirically?
 * A15: (* YOUR ANSWER *)
 *)

(**
 * REFLECTION QUESTIONS
 *
 * Q16: What's the trade-off between manual lemma calls and SMTPat?
 * A16: (* YOUR ANSWER *)
 *
 * Q17: When would you avoid using SMTPat?
 * A17: (* YOUR ANSWER *)
 *
 * Q18: How do patterns relate to trigger terms in quantifier instantiation?
 * A18: (* YOUR ANSWER *)
 *)

(**
 * ASSESSMENT RUBRIC (20 points total)
 *
 * Part 1: Understanding (3 points)
 * - Q1-Q3: Quantifier problem (3 pts)
 *
 * Part 2: SMTPat Basics (3 points)
 * - Q4-Q6: Pattern mechanics (3 pts)
 *
 * Part 3: Pattern Design (6 points)
 * - Q7-Q8: Design analysis (2 pts each)
 *
 * Part 4: Implementation (5 points)
 * - append_nil_right: Correct pattern (2 pts)
 * - reverse_length: Correct pattern + proof (3 pts)
 *
 * Part 5: Debugging (3 points)
 * - Q11-Q13: Systematic debugging (3 pts)
 *
 * Bonus (+5 points):
 * - Q14-Q15: Multiple patterns (2 pts)
 * - All lemmas verify with correct patterns (3 pts)
 *)

(**
 * LEARNING OUTCOMES
 *
 * After this exercise, you should be able to:
 * ✓ Understand quantifier instantiation in Z3
 * ✓ Use SMTPat to automate lemma application
 * ✓ Design effective patterns (not too general, not too specific)
 * ✓ Debug pattern matching failures
 * ✓ Trade off between automation and explicit proofs
 * ✓ Read SMT-LIB to verify pattern triggers
 *
 * Next: Mini-Project will integrate all SMT concepts in a performance challenge
 *)

(**
 * INSTRUCTOR NOTES
 *
 * This is the MOST ADVANCED exercise in Week 3. Students need:
 * - Solid understanding of quantifiers (from logic courses)
 * - Experience with SMT-LIB (Exercise 3.1)
 * - Debugging skills (Exercise 3.2)
 *
 * Common student mistakes:
 * 1. Too general patterns (triggers everywhere, kills performance)
 * 2. Too specific patterns (never trigger, lemma unused)
 * 3. Confusing multiple [SMTPat ...] (it's OR, not AND)
 * 4. Not testing patterns empirically
 * 5. Using patterns when manual calls are clearer
 *
 * Teaching tips:
 * - Show --log_queries output to visualize triggers
 * - Compare verification time: with/without patterns
 * - Emphasize: patterns are OPTIMIZATION, not magic
 * - Connect to E-matching in Z3 internals
 *
 * Time distribution:
 * - Part 1: 15 min (understanding problem)
 * - Part 2: 15 min (seeing solution)
 * - Part 3: 20 min (design principles)
 * - Part 4: 20 min (hands-on implementation)
 * - Part 5: 10 min (debugging)
 * Total: 80 min (can reduce by making bonus optional)
 *
 * Prerequisites:
 * - Exercises 3.1-3.4 completed
 * - Formal logic background (or Week 2 material)
 * - Comfort with F* lemmas and proofs
 *
 * F* VERSION NOTE: Requires F* 2024.01.13+
 * SMTPat syntax has changed in older versions.
 *
 * Further reading:
 * - "Trigger Selection Strategies in SMT" (Moskal, 2009)
 * - Z3 E-matching: https://microsoft.github.io/z3/
 * - F* SMTPat guide: https://fstar-lang.org/tutorial
 *)

(**
 * MATHEMATICAL BACKGROUND (For Curious Students)
 *
 * Quantifier Instantiation Problem:
 *
 * Given: ∀x,y. P(x,y)  (a universally quantified formula)
 * Goal: Prove some specific fact using this formula
 *
 * Z3 must decide: Which values of x,y should I try?
 * - Trying ALL values = infinite search (impossible)
 * - Trying NONE = useless lemma (lemma never applied)
 * - Trying SOME = pattern-based instantiation (SMTPat)
 *
 * E-matching (Simplify, Z3):
 * - Scan the proof state for terms matching PATTERN
 * - Instantiate quantifier with matched terms
 * - Add resulting fact to solver knowledge
 *
 * Trade-offs:
 * - More patterns = more instantiations = slower but more complete
 * - Fewer patterns = faster but might miss proofs
 *
 * This is an active research area! Z3 developers constantly tune this.
 *
 * Further reading:
 * - "Efficient E-Matching for SMT Solvers" (de Moura & Bjørner, 2007)
 * - "Quantifier Instantiation in SMT" (Reynolds et al, 2013)
 *)
