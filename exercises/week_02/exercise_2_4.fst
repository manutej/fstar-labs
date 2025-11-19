module Exercise2_4

(**
 * Exercise 2.4: Map Preserves Length
 *
 * Learning Objectives:
 * - Practice structural induction on lists
 * - Write simple inductive proofs
 * - Understand how map works
 *
 * Background:
 * The map function applies a function to every element of a list.
 * An important property: mapping doesn't change the list's length!
 *
 * This exercise is more straightforward than the reverse involution.
 * You should be able to complete it without helper lemmas.
 *)

open FStar.List.Tot

(**
 * We provide the map function for reference.
 * (It's also available from FStar.List.Tot, but we show it here)
 *)
let rec map (#a #b:Type) (f:a -> b) (xs:list a) : list b =
  match xs with
  | [] -> []
  | hd :: tl -> f hd :: map f tl

(**
 * Test that map works as expected
 *)
let double (x:int) : int = x * 2
let is_even (x:int) : bool = x % 2 = 0

let test_map_double = assert (map double [1;2;3] = [2;4;6])
let test_map_empty = assert (map double [] = [])
let test_map_bool = assert (map is_even [1;2;3;4] = [false;true;false;true])

(**
 * PART A: Main Theorem - Map Preserves Length
 *)

// TODO: Prove that map preserves the length of a list
// Hint: Use structural induction on xs
// Hint: Base case: empty list
// Hint: Inductive case: what can you assume about map f tl?
let rec map_length (#a #b:Type) (f:a -> b) (xs:list a)
  : Lemma (ensures length (map f xs) = length xs)
          (decreases xs)
  =
  (* YOUR PROOF HERE *)
  admit() // Remove this when you implement the proof

(**
 * Test cases for the theorem
 *)
let test_map_length_1 = map_length double [1;2;3;4;5]
let test_map_length_2 = map_length is_even []
let test_map_length_3 = map_length (fun x -> x + 1) [10;20;30]

(**
 * PART B: Map Composition
 *
 * Another nice property: mapping with f, then g, is the same as
 * mapping with their composition.
 *)

// TODO: Prove that map distributes over function composition
// Hint: Similar structure to map_length
let rec map_compose (#a #b #c:Type) (f:a -> b) (g:b -> c) (xs:list a)
  : Lemma (ensures map g (map f xs) = map (fun x -> g (f x)) xs)
          (decreases xs)
  =
  (* YOUR PROOF HERE *)
  admit() // Remove this when you implement the proof

(**
 * Test the composition property
 *)
let increment (x:int) : int = x + 1
let square (x:int) : int = x * x

let test_composition = map_compose increment square [1;2;3]
// map square (map increment [1;2;3]) = map (fun x -> square (increment x)) [1;2;3]
// map square [2;3;4] = map (fun x -> (x+1)*(x+1)) [1;2;3]
// [4;9;16] = [4;9;16]

(**
 * PART C: Map Identity
 *
 * Mapping the identity function does nothing.
 *)

// TODO: Prove that mapping the identity function returns the original list
let rec map_id (#a:Type) (xs:list a)
  : Lemma (ensures map (fun x -> x) xs = xs)
          (decreases xs)
  =
  (* YOUR PROOF HERE *)
  admit() // Remove this when you implement the proof

(**
 * Reflection Questions:
 *
 * Q1: Compare the proof of map_length to reverse_involution (Exercise 2.3).
 *     Which one is easier? Why?
 * A1: YOUR ANSWER HERE
 *
 * Q2: In the inductive case of map_length, what is the induction hypothesis?
 *     How do you use it?
 * A2: YOUR ANSWER HERE
 *
 * Q3: Why don't we need helper lemmas for these map proofs?
 * A3: YOUR ANSWER HERE
 *
 * Q4: The map_compose theorem shows that map is a functor. What does this
 *     mean in category theory? (Optional - research this if interested!)
 * A4: YOUR ANSWER HERE
 *)

(**
 * CHALLENGE (Optional):
 * Prove that two maps in sequence equal a single map with composed functions.
 *)

// let rec map_map (#a #b #c:Type) (f:a -> b) (g:b -> c) (xs:list a)
//   : Lemma (ensures map g (map f xs) = map (fun x -> g (f x)) xs)
//   =
//   (* YOUR PROOF HERE - note this is the same as map_compose! *)
