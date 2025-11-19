module Exercise1_2

(**
 * Exercise 1.2: Validated Input Parsing
 *
 * Learning Objectives:
 * - Create refinement types with compound predicates
 * - Return refined types from functions
 * - Use control flow to help SMT prove refinements
 *
 * Real-world scenario: Parse and validate user input
 *)

(** Part A: Age validation *)

// TODO: Define age type
// Age must be between 0 and 150 (inclusive)
type age = (* YOUR CODE HERE *)

// TODO: Implement clamp function
// Clamp x to the range [min, max]
// This is the tricky one - think about each branch!
let clamp (min:int) (max:int{max >= min}) (x:int)
  : y:int{y >= min && y <= max} =
  (* YOUR CODE HERE *)

// Test cases for clamp:
let clamp_test1 = clamp 0 100 50   // Should return 50
let clamp_test2 = clamp 0 100 (-10) // Should return 0
let clamp_test3 = clamp 0 100 200  // Should return 100

(** Part B: Positive refinement *)

// TODO: Define positive type
type positive = (* YOUR CODE HERE *)

// TODO: Implement safe_sqrt that only accepts positive numbers
// For this exercise, just return the input (we'll implement real sqrt later)
let safe_sqrt (n:positive) : positive =
  (* YOUR CODE HERE *)

(** Part C: Bounded integers *)

// TODO: Define bounded100 type (integers from 0 to 99)
type bounded100 = (* YOUR CODE HERE *)

// TODO: Implement increment with wraparound
// If x is 99, wrap to 0; otherwise increment
let increment_wrap (x:bounded100) : bounded100 =
  (* YOUR CODE HERE *)

(**
 * Reflection Questions:
 *
 * Q1: In the clamp function, how does F* know that each branch
 *     returns a value satisfying `y >= min && y <= max`?
 * A1: YOUR ANSWER HERE
 *
 * Q2: Why do we need the precondition `max >= min` on clamp?
 * A2: YOUR ANSWER HERE
 *
 * Q3: What would happen if we removed the precondition?
 *     (Try it and observe the error!)
 * A3: YOUR ANSWER HERE
 *)
