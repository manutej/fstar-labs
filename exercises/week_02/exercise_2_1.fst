module Exercise2_1

(**
 * Exercise 2.1: Verified Fibonacci
 *
 * Learning Objectives:
 * - Understand and use explicit `decreases` clauses for termination
 * - Prove termination for recursive functions on natural numbers
 * - Recognize when F* needs help proving termination
 *
 * Background:
 * The Fibonacci sequence is defined as:
 *   fib(0) = 0
 *   fib(1) = 1
 *   fib(n) = fib(n-1) + fib(n-2) for n > 1
 *
 * While this is structurally recursive, it makes TWO recursive calls,
 * so we need to be explicit about what decreases.
 *)

// TODO: Implement fibonacci with explicit decreases clause
// Hint: The argument n decreases on each recursive call
// Hint: Use pattern matching or conditionals to handle base cases
let rec fibonacci (n:nat) : nat
  (* TODO: Add decreases clause here *)
  =
  (* YOUR CODE HERE *)

(**
 * Test Cases
 *
 * These should all typecheck and verify:
 *)
let test_fib_0 = assert (fibonacci 0 = 0)
let test_fib_1 = assert (fibonacci 1 = 1)
let test_fib_5 = assert (fibonacci 5 = 5)
let test_fib_10 = assert (fibonacci 10 = 55)

// Additional test for reference
let test_fib_6 = fibonacci 6  // Should be 8
let test_fib_7 = fibonacci 7  // Should be 13

(**
 * Reflection Questions (answer in comments):
 *
 * Q1: Why do we need an explicit `decreases` clause for fibonacci?
 *     Hint: Compare to a simple recursive function like factorial.
 * A1: YOUR ANSWER HERE
 *
 * Q2: What would happen if we removed the `decreases` clause?
 *     (Try it and observe the error!)
 * A2: YOUR ANSWER HERE
 *
 * Q3: The fibonacci function has type nat -> nat. Why is it important
 *     that the input is nat (non-negative) rather than just int?
 * A3: YOUR ANSWER HERE
 *
 * Q4: This implementation is inefficient (exponential time). Can you think
 *     of why? (We'll learn how to verify more efficient versions later!)
 * A4: YOUR ANSWER HERE
 *)

(**
 * CHALLENGE (Optional):
 * Implement an iterative fibonacci using a helper function that
 * tracks two values (previous two fibonacci numbers). You'll need
 * to prove it terminates by showing the counter decreases.
 *)

// let rec fib_iter (n:nat) (a:nat) (b:nat) (count:nat) : nat
//   decreases count
//   =
//   (* YOUR CODE HERE *)
//
// let fibonacci_fast (n:nat) : nat =
//   fib_iter n 0 1 n
