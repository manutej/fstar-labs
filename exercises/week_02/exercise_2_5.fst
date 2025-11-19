module Exercise2_5

(**
 * Exercise 2.5: Flatten Associativity
 *
 * Learning Objectives:
 * - Use helper lemmas in proofs
 * - Understand how flatten (concat) works on lists of lists
 * - Practice combining multiple lemmas to prove a theorem
 *
 * Background:
 * The flatten function (also called concat or join) takes a list of lists
 * and concatenates them into a single list.
 *
 * We want to prove: flatten (xs @ ys) = flatten xs @ flatten ys
 * This shows that flatten distributes over append.
 *)

open FStar.List.Tot

(**
 * We provide the flatten function for you.
 * It recursively appends each inner list.
 *)
let rec flatten (#a:Type) (xss:list (list a)) : list a =
  match xss with
  | [] -> []
  | xs :: xss' -> xs @ flatten xss'

(**
 * Test that flatten works as expected
 *)
let test_flatten_1 = assert (flatten [[1;2];[3;4];[5]] = [1;2;3;4;5])
let test_flatten_2 = assert (flatten ([] <: list (list int)) = [])
let test_flatten_3 = assert (flatten [[1];[];[2;3];[]] = [1;2;3])

(**
 * PART A: Helper Lemma - Append Associativity
 *
 * We provide this crucial helper lemma for you.
 * Append is associative: (xs @ ys) @ zs = xs @ (ys @ zs)
 *)
let rec append_assoc (#a:Type) (xs ys zs:list a)
  : Lemma (ensures (xs @ ys) @ zs = xs @ (ys @ zs))
          (decreases xs)
  =
  match xs with
  | [] -> ()
  | hd :: tl -> append_assoc tl ys zs

(**
 * Test the helper lemma
 *)
let test_assoc = append_assoc [1;2] [3;4] [5;6]
// ([1;2] @ [3;4]) @ [5;6] = [1;2] @ ([3;4] @ [5;6])
// [1;2;3;4;5;6] = [1;2;3;4;5;6]

(**
 * PART B: Main Theorem - Flatten Distributes Over Append
 *)

// TODO: Prove that flatten distributes over append
// Hint: Use induction on xss
// Hint: You'll need to use append_assoc in the inductive case
// Hint: The proof structure follows the structure of flatten
let rec flatten_append (#a:Type) (xss yss:list (list a))
  : Lemma (ensures flatten (xss @ yss) = flatten xss @ flatten yss)
          (decreases xss)
  =
  (* YOUR PROOF HERE *)
  (* Hint: Pattern match on xss *)
  (* Hint: In the cons case, use append_assoc to rearrange the appends *)
  admit() // Remove this when you implement the proof

(**
 * Test cases for the theorem
 *)
let test_flatten_append_1 =
  flatten_append [[1;2];[3]] [[4;5];[6]]
// flatten ([[1;2];[3]] @ [[4;5];[6]]) = flatten [[1;2];[3]] @ flatten [[4;5];[6]]
// flatten [[1;2];[3];[4;5];[6]] = [1;2;3] @ [4;5;6]
// [1;2;3;4;5;6] = [1;2;3;4;5;6]

let test_flatten_append_2 =
  flatten_append ([] <: list (list int)) [[1;2];[3]]

let test_flatten_append_3 =
  flatten_append [[1];[];[2]] [[3;4]]

(**
 * PART C: Flatten of Map
 *
 * Another interesting property involves map.
 *)

// TODO: Prove this property about flatten and map
// Hint: Induction on xss
// Hint: You may need to use properties of map and append
let rec flatten_map_singleton (#a:Type) (xs:list a)
  : Lemma (ensures flatten (map (fun x -> [x]) xs) = xs)
          (decreases xs)
  =
  (* YOUR PROOF HERE *)
  admit() // Remove this when you implement the proof

(**
 * Test flatten_map_singleton
 *)
let test_map_singleton = flatten_map_singleton [1;2;3;4;5]
// flatten (map (fun x -> [x]) [1;2;3;4;5]) = [1;2;3;4;5]
// flatten [[1];[2];[3];[4];[5]] = [1;2;3;4;5]

(**
 * Reflection Questions:
 *
 * Q1: In the proof of flatten_append, where exactly do you use append_assoc?
 *     Why is it necessary?
 * A1: YOUR ANSWER HERE
 *
 * Q2: What is the induction hypothesis when proving flatten_append?
 *     Write it out explicitly.
 * A2: YOUR ANSWER HERE
 *
 * Q3: Compare this exercise to Exercise 2.4 (map_length). Both use
 *     structural induction, but this one needs a helper lemma. Why?
 * A3: YOUR ANSWER HERE
 *
 * Q4: The property flatten (xss @ yss) = flatten xss @ flatten yss
 *     is sometimes called "homomorphism". What does this mean?
 * A4: YOUR ANSWER HERE
 *)

(**
 * CHALLENGE (Optional):
 * Prove that flatten is idempotent when applied to lists of lists of lists.
 *)

// let rec flatten_flatten (#a:Type) (xsss:list (list (list a)))
//   : Lemma (ensures flatten (flatten xsss) = flatten (map flatten xsss))
//   =
//   (* YOUR PROOF HERE *)
//   admit()

(**
 * ADVANCED CHALLENGE (Very Hard):
 * Prove the flatten-map fusion law:
 *   flatten (map f xss) = map f (flatten xss)
 * when f : a -> b (i.e., f doesn't change the list structure)
 *
 * Note: This requires thinking carefully about types and what f does.
 *)
