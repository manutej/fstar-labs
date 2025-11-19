module Exercise1_1

(**
 * Exercise 1.1: Safe Division Function
 *
 * Learning Objectives:
 * - Define refinement types using {x:t | predicate} syntax
 * - Use refinement types to prevent runtime errors at compile time
 * - Understand how F* enforces type safety
 *
 * Instructions:
 * 1. Define a NonZero refinement type for non-zero integers
 * 2. Implement safe_divide that takes a NonZero divisor
 * 3. Test that the type system rejects division by zero
 *)

// TODO: Define NonZero type
// Hint: NonZero should be integers where x <> 0
type nonzero = (* YOUR CODE HERE *)

// TODO: Implement safe_divide
// This function should take any integer a and a non-zero integer b
// and return their quotient
let safe_divide (a:int) (b:nonzero) : int =
  (* YOUR CODE HERE *)

(**
 * Test Cases
 *
 * These should typecheck successfully:
 *)
let test1 = safe_divide 10 2
let test2 = safe_divide 100 (-5)
let test3 = safe_divide 7 1

(**
 * These should be TYPE ERRORS (uncomment to verify):
 *)
// let test_fail1 = safe_divide 10 0
// let test_fail2 : nonzero = 0

(**
 * Reflection Questions (answer in comments):
 *
 * Q1: Why does F* reject `safe_divide 10 0` at compile time?
 * A1: YOUR ANSWER HERE
 *
 * Q2: How is this different from a runtime check like `if b == 0 then error`?
 * A2: YOUR ANSWER HERE
 *
 * Q3: What happens to the refinement type after code extraction to OCaml?
 * A3: YOUR ANSWER HERE (Hint: read SKILL.md section on extraction)
 *)
