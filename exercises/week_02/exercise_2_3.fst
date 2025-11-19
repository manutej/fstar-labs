module Exercise2_3

(**
 * Exercise 2.3: Reverse Involution
 *
 * Learning Objectives:
 * - Write inductive proofs using recursive lemmas
 * - Understand when helper lemmas are needed
 * - Practice reasoning about list operations
 *
 * Background:
 * An involution is a function that is its own inverse.
 * The reverse function is an involution: reverse (reverse xs) = xs
 *
 * This exercise is INTENTIONALLY CHALLENGING - you will need to
 * discover and prove helper lemmas!
 *)

open FStar.List.Tot

(**
 * We provide the naive reverse function for you.
 * This matches the version discussed in lecture (Day 5).
 *)
let rec reverse (#a:Type) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]

(**
 * Test that reverse works as expected
 *)
let test_reverse_123 = assert (reverse [1;2;3] = [3;2;1])
let test_reverse_empty = assert (reverse ([] <: list int) = [])
let test_reverse_single = assert (reverse [42] = [42])

(**
 * PART A: Warmup - Prove a helper lemma
 *
 * Before proving the main theorem, you'll need to understand how
 * reverse interacts with append. This lemma is crucial!
 *)

// TODO: Prove that reverse distributes over append
// Hint: This needs induction on xs
// Hint: The relationship is: reverse (xs @ ys) = reverse ys @ reverse xs
val reverse_append: #a:Type -> xs:list a -> ys:list a ->
  Lemma (reverse (append xs ys) == append (reverse ys) (reverse xs))

let rec reverse_append #a xs ys =
  (* YOUR PROOF HERE *)
  (*
   * Hints:
   * - Use structural induction on xs
   * - Base case: xs = []
   * - Inductive case: xs = hd :: tl
   * - You may need append_assoc from FStar.List.Tot.Properties
   *)
  admit() // Remove this when you implement the proof

(**
 * PART B: Another helper - reverse of a singleton
 *)

// TODO: Prove that reversing a single-element list gives the same list
// Hint: This one is trivial - F* can prove it automatically!
val reverse_singleton: #a:Type -> x:a ->
  Lemma (reverse [x] == [x])

let reverse_singleton #a x =
  (* YOUR PROOF HERE *)
  admit() // Remove this when you implement the proof

(**
 * PART C: Main Theorem - Reverse Involution
 *)

// TODO: Prove that reverse is an involution
// Hint: You'll need to use your helper lemmas!
// Hint: Induction on xs
// Hint: You may need additional helper lemmas about append
let rec reverse_involution (#a:Type) (xs:list a)
  : Lemma (ensures reverse (reverse xs) = xs)
          (decreases xs)
  =
  (* YOUR PROOF HERE *)
  admit() // Remove this when you implement the proof

(**
 * Test cases for the main theorem
 *)
let test_involution_1 = reverse_involution [1;2;3]
let test_involution_2 = reverse_involution ([] <: list int)
let test_involution_3 = reverse_involution [5;4;3;2;1]

(**
 * Reflection Questions:
 *
 * Q1: Why do we need the helper lemma reverse_aux_append?
 *     What goes wrong if we try to prove reverse_involution directly?
 * A1: YOUR ANSWER HERE
 *
 * Q2: Explain the induction hypothesis in your proof of reverse_involution.
 *     What can you assume about reverse (reverse tl)?
 * A2: YOUR ANSWER HERE
 *
 * Q3: How does F*'s SMT solver help with these proofs? What parts
 *     can it figure out automatically vs. what needs explicit proof?
 * A3: YOUR ANSWER HERE
 *
 * Q4: (Challenge) The teaching notes mention an accumulator-based reverse
 *     that's more efficient. Why might proving properties about accumulator-based
 *     functions be harder than proving properties about naive implementations?
 * A4: YOUR ANSWER HERE
 *)

(**
 * CHALLENGE (Optional):
 * Prove that reverse preserves the length of a list.
 *)

// let rec reverse_length (#a:Type) (xs:list a)
//   : Lemma (ensures length (reverse xs) = length xs)
//   =
//   (* YOUR PROOF HERE *)
