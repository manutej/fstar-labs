module Exercise2_2

(**
 * Exercise 2.2: McCarthy 91 Function
 *
 * Learning Objectives:
 * - Handle non-structural recursion with lexicographic decreases
 * - Understand nested recursive calls
 * - Practice proving termination for complex recursive patterns
 *
 * Background:
 * The McCarthy 91 function is a famous example of non-trivial recursion:
 *   M(n) = n - 10           if n > 100
 *   M(n) = M(M(n + 11))     if n ≤ 100
 *
 * Despite its strange definition, M(n) = 91 for all n ≤ 100!
 *
 * This is CHALLENGING because:
 * - The recursive call M(n+11) increases the argument
 * - The nested structure M(M(...)) is complex
 * - We need a lexicographic measure to prove termination
 *)

// TODO: Implement McCarthy 91 function
// Hint: You need a lexicographic decreases clause
// Hint: Consider the measure (101 - n, recursive_depth)
// Hint: When n > 100, we're done; when n ≤ 100, we add 11 but decrease "distance to 101"

let rec mccarthy91 (n:int) : int
  (* TODO: Add lexicographic decreases clause here *)
  (* Hint: Use %[...] syntax for lexicographic ordering *)
  (* Hint: What decreases is (101 - n) when n ≤ 100 *)
  =
  (* YOUR CODE HERE *)

(**
 * Test Cases
 *
 * The amazing property: M(n) = 91 for all n ≤ 100
 *)
let test_m91_0 = assert (mccarthy91 0 = 91)
let test_m91_50 = assert (mccarthy91 50 = 91)
let test_m91_100 = assert (mccarthy91 100 = 91)

// For n > 100, M(n) = n - 10
let test_m91_101 = assert (mccarthy91 101 = 91)
let test_m91_105 = assert (mccarthy91 105 = 95)
let test_m91_200 = assert (mccarthy91 200 = 190)

(**
 * Reflection Questions:
 *
 * Q1: Why can't F* prove termination automatically for this function?
 * A1: YOUR ANSWER HERE
 *
 * Q2: Explain the lexicographic ordering you used. What quantities
 *     decrease on each recursive call?
 * A2: YOUR ANSWER HERE
 *
 * Q3: Trace through mccarthy91 5 by hand. How many recursive calls
 *     are made before reaching a base case?
 * A3: YOUR ANSWER HERE
 *
 * Q4: Why does M(n) = 91 for all n ≤ 100? (This is not obvious!
 *     Don't worry if you can't prove it - this is research-level.)
 * A4: YOUR ANSWER HERE
 *)

(**
 * ADVANCED CHALLENGE (Very Hard):
 * Prove that mccarthy91 n = 91 for all n ≤ 100.
 * This requires induction and lemmas about the function's behavior.
 *)

// let rec mccarthy91_theorem (n:int{n <= 100})
//   : Lemma (mccarthy91 n = 91)
//   =
//   (* YOUR PROOF HERE - this is research-level difficulty! *)
