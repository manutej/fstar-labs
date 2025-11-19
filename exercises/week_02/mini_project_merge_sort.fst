module MiniProjectMergeSort

(**
 * Week 2 Mini-Project: Verified Merge Sort
 *
 * Estimated Time: 3-5 hours
 * Difficulty: Challenging (L2 Apprentice)
 * Due: End of Week 2 (Friday 11:59 PM)
 *
 * Learning Objectives:
 * - Implement a divide-and-conquer sorting algorithm
 * - Use decreases clauses for termination proofs on non-structural recursion
 * - Prove functional correctness (sorted output)
 * - Understand the relationship between implementation and specification
 * - (Extra Credit) Prove permutation preservation
 *
 * Project Overview:
 * You will implement merge sort and prove it always produces sorted output.
 * This combines everything from Week 2: totality, structural recursion,
 * lemmas, and inductive proofs.
 *
 * Grading Breakdown:
 * - Part 1 (Provided): Helper predicates - 0 points (study these!)
 * - Part 2 (20 points): merge (10) and merge_sort (10) implementation
 * - Part 3 (15 points): Correctness proof (merge_sort_sorted)
 * - Part 4 (5 points): Code quality (structure, comments, helper lemmas)
 * - Part 5 (Extra Credit): +5 points for permutation proof
 * Total: 40 points (45 with extra credit)
 *
 * Tips for Success:
 * - Start early! This is more complex than it looks.
 * - Get the implementation working BEFORE attempting proofs.
 * - Use admit() as a placeholder while developing proofs.
 * - Break down proofs into smaller helper lemmas.
 * - Test your functions with the provided test cases.
 * - Ask for help in office hours if stuck!
 *)

open FStar.List.Tot

(**
 * =============================================================================
 * PART 1: Helper Predicates (PROVIDED - Study These!)
 * =============================================================================
 *
 * These predicates define what it means for a list to be sorted and for
 * two lists to be permutations of each other. You will use these in your
 * proofs, so make sure you understand how they work!
 *)

(**
 * Sorted Predicate
 *
 * A list is sorted if every element is less than or equal to all elements
 * that come after it. We define this inductively:
 * - Empty list: sorted
 * - Single element: sorted
 * - Two or more elements: first <= second AND rest is sorted
 *)
let rec sorted (xs:list int) : bool =
  match xs with
  | [] -> true
  | [x] -> true
  | x :: y :: rest -> x <= y && sorted (y :: rest)

(**
 * Permutation Predicate
 *
 * Two lists are permutations if they contain the same elements with the
 * same frequencies, possibly in different orders.
 *
 * We define this using a count-based approach: for every element e,
 * the number of times e appears in xs equals the number of times it
 * appears in ys.
 *)

// Helper: Count occurrences of an element in a list
let rec count (e:int) (xs:list int) : nat =
  match xs with
  | [] -> 0
  | hd :: tl -> (if hd = e then 1 else 0) + count e tl

// Two lists are permutations if every element has the same count in both
let rec permutation (xs ys:list int) : bool =
  match xs with
  | [] -> (match ys with | [] -> true | _ -> false)
  | hd :: tl -> count hd xs = count hd ys && permutation tl ys

(**
 * Study Questions (think about these, don't need to answer in code):
 *
 * Q1: Why is sorted defined recursively on pairs (x::y::rest) instead of
 *     checking all pairs at once?
 *
 * Q2: The permutation check seems inefficient (quadratic time). Why is this
 *     okay for a specification? (Hint: specs vs. implementation)
 *
 * Q3: Could we define permutation differently? What are other approaches?
 *)

(**
 * =============================================================================
 * PART 2: Implementation (20 POINTS - YOU IMPLEMENT THIS)
 * =============================================================================
 *
 * Implement merge sort using the standard divide-and-conquer approach:
 * 1. Split the list into two halves
 * 2. Recursively sort each half
 * 3. Merge the sorted halves
 *
 * Key Challenge: Proving termination for merge_sort!
 * The recursion is NOT structural (we don't just recurse on tl).
 * You'll need a decreases clause based on list length.
 *)

(**
 * Helper: Split a list into two roughly equal parts
 *
 * This is provided to help you implement merge_sort.
 * Example: split [1;2;3;4;5] = ([1;3;5], [2;4])
 *)
let rec split (#a:Type) (xs:list a) : (list a * list a) =
  match xs with
  | [] -> ([], [])
  | [x] -> ([x], [])
  | x :: y :: rest ->
      let (left, right) = split rest in
      (x :: left, y :: right)

(**
 * TODO 1: Implement merge (10 points)
 *
 * Merge two sorted lists into a single sorted list.
 *
 * Requirements:
 * - Must produce a sorted list (you'll prove this in Part 3)
 * - Must include all elements from both input lists
 * - Must maintain relative order of equal elements (stable sort)
 *
 * Examples:
 *   merge [1;3;5] [2;4;6] = [1;2;3;4;5;6]
 *   merge [1;1;2] [1;3]   = [1;1;1;2;3]
 *   merge [] [1;2;3]      = [1;2;3]
 *
 * Hints:
 * - Use structural recursion (match on both lists)
 * - F* should infer termination automatically
 * - Think about all cases: both empty, one empty, both non-empty
 * - When both non-empty, compare heads and take smaller
 *)
val merge: xs:list int -> ys:list int -> list int

let rec merge xs ys =
  (* TODO: YOUR CODE HERE *)
  admit() // Remove this and implement merge

(**
 * TODO 2: Implement merge_sort (15 points)
 *
 * Sort a list using the merge sort algorithm.
 *
 * Requirements:
 * - Must use divide-and-conquer approach (split, recurse, merge)
 * - Must terminate (use decreases clause!)
 * - Must produce a sorted list (you'll prove this in Part 3)
 *
 * Algorithm:
 * 1. Base case: lists of length 0 or 1 are already sorted
 * 2. Recursive case:
 *    a. Split list into two halves
 *    b. Recursively sort each half
 *    c. Merge the sorted halves
 *
 * CRITICAL: Termination
 * This recursion is NOT structural! You recurse on sublists that are
 * NOT just 'tl' of the input. F* will reject this without a decreases clause.
 *
 * Hints for decreases clause:
 * - What metric decreases with each recursive call?
 * - Answer: length of the list!
 * - Use: decreases (length xs)
 * - F* will verify that split produces shorter sublists
 *
 * Example:
 *   merge_sort [3;1;4;1;5;9;2;6] = [1;1;2;3;4;5;6;9]
 *)
val merge_sort: xs:list int -> list int

let rec merge_sort xs =
  (* TODO: Add decreases clause here! *)
  (* TODO: YOUR CODE HERE *)
  admit() // Remove this and implement merge_sort

(**
 * Test Cases for Part 2
 *
 * Uncomment these once you've implemented merge and merge_sort.
 * They should all evaluate to true.
 *)

// Basic merge tests
// let test_merge_1 = merge [] [] = []
// let test_merge_2 = merge [1] [] = [1]
// let test_merge_3 = merge [] [2] = [2]
// let test_merge_4 = merge [1;3;5] [2;4;6] = [1;2;3;4;5;6]
// let test_merge_5 = merge [1;1;2] [1;3] = [1;1;1;2;3]

// Basic merge_sort tests
// let test_sort_1 = merge_sort [] = []
// let test_sort_2 = merge_sort [1] = [1]
// let test_sort_3 = merge_sort [2;1] = [1;2]
// let test_sort_4 = merge_sort [3;1;4;1;5;9;2;6] = [1;1;2;3;4;5;6;9]
// let test_sort_5 = merge_sort [5;4;3;2;1] = [1;2;3;4;5]

// Verify sorted predicate works
// let test_sorted_1 = sorted [] = true
// let test_sorted_2 = sorted [1] = true
// let test_sorted_3 = sorted [1;2;3] = true
// let test_sorted_4 = sorted [1;3;2] = false
// let test_sorted_5 = sorted (merge_sort [3;1;4;1;5;9;2;6]) = true

(**
 * =============================================================================
 * PART 3: Correctness Proof (15 POINTS - YOU PROVE THIS)
 * =============================================================================
 *
 * Prove that merge_sort always produces a sorted list.
 *
 * This is the heart of the mini-project! You'll use structural induction,
 * helper lemmas, and proof decomposition strategies from Week 2.
 *)

(**
 * TODO 3a: Prove merge preserves sortedness (20 points)
 *
 * Lemma: If xs and ys are both sorted, then merge xs ys is sorted.
 *
 * This is a helper lemma for the main theorem. You'll use induction on xs and ys.
 *
 * Proof Strategy:
 * 1. Match on xs (base case: xs = [])
 * 2. Match on ys (base case: ys = [])
 * 3. Inductive case: xs = x::xs', ys = y::ys'
 *    - Case x <= y: Show that x :: merge xs' ys is sorted
 *    - Case x > y: Show that y :: merge xs ys' is sorted
 *    - Use induction hypothesis (recursive call)
 *
 * Hints:
 * - You'll likely need helper lemmas about sorted lists
 * - Think about: what does it mean to cons an element onto a sorted list?
 * - Suggested helper: sorted_cons (prove separately)
 * - Don't be afraid to use admit() initially to structure the proof
 *
 * This is HARD! It's okay to struggle. The learning is in the process.
 *)
val merge_sorted:
  xs:list int -> ys:list int ->
  Lemma (requires sorted xs /\ sorted ys)
        (ensures sorted (merge xs ys))

let rec merge_sorted xs ys =
  (* TODO: YOUR PROOF HERE *)
  admit()

(**
 * TODO 3b: Prove merge_sort produces sorted output (40 points)
 *
 * Main Theorem: For any list xs, merge_sort xs is sorted.
 *
 * This is what you've been building toward! Use everything you've learned.
 *
 * Proof Strategy:
 * 1. Induction on length of xs (use the decreases metric!)
 * 2. Base cases: [] and [x] are already sorted
 * 3. Inductive case:
 *    - Split xs into left and right
 *    - By IH: merge_sort left is sorted
 *    - By IH: merge_sort right is sorted
 *    - By merge_sorted lemma: merge (merge_sort left) (merge_sort right) is sorted
 *    - Therefore: merge_sort xs is sorted
 *
 * Key Challenges:
 * - F* needs to know that split produces shorter lists (for termination)
 * - You may need helper lemmas about split and length
 * - Proof structure mirrors the implementation structure
 *
 * Suggested Helper Lemmas (you may need these):
 * - split_shorter: split always produces sublists shorter than original
 * - sorted_single: single-element lists are sorted
 * - sorted_empty: empty list is sorted
 *
 * Time Management:
 * If you get stuck on this proof after 2 hours, use admit() and move on.
 * Come to office hours for help! This is graduate-level material.
 *)
val merge_sort_sorted: xs:list int ->
  Lemma (sorted (merge_sort xs))

let rec merge_sort_sorted xs =
  (* TODO: YOUR PROOF HERE *)
  (* Hint: Match on xs to handle base cases explicitly *)
  (* Hint: Use merge_sorted lemma in the inductive case *)
  admit()

(**
 * Reflection Questions for Part 3 (answer in comments):
 *
 * Q1: Why did you need the merge_sorted helper lemma? Could you prove
 *     merge_sort_sorted without it?
 * A1: YOUR ANSWER HERE
 *
 * Q2: How does the structure of the proof relate to the structure of the
 *     merge_sort implementation?
 * A2: YOUR ANSWER HERE
 *
 * Q3: Where did F* need your help vs. where did SMT solve things automatically?
 * A3: YOUR ANSWER HERE
 *)

(**
 * =============================================================================
 * PART 4: Code Quality (5 POINTS - Assessed During Grading)
 * =============================================================================
 *
 * This part is assessed based on:
 * - Clean code structure and formatting
 * - Helpful comments explaining your approach
 * - Well-organized helper lemmas with clear purposes
 * - Meaningful variable names
 *
 * No explicit deliverable - just write clean, well-documented code!
 *)

(**
 * =============================================================================
 * PART 5: Permutation Proof (+5 POINTS EXTRA CREDIT)
 * =============================================================================
 *
 * Prove that merge_sort produces a permutation of the input.
 * This shows that merge_sort doesn't lose or duplicate elements!
 *
 * This is SIGNIFICANTLY harder than Part 3. Only attempt after completing Part 3.
 *)

(**
 * TODO 4a: Prove merge preserves all elements (7 points EC)
 *
 * Lemma: merge xs ys is a permutation of (append xs ys).
 *
 * This shows that merge doesn't lose or duplicate elements.
 *
 * Hints:
 * - You'll need properties about count and append
 * - Think about: how does merge distribute elements?
 * - Suggested helpers: count_append, count_cons
 * - This requires careful reasoning about counts
 *)
val merge_permutation:
  xs:list int -> ys:list int ->
  Lemma (permutation (merge xs ys) (append xs ys))

let rec merge_permutation xs ys =
  (* TODO: YOUR PROOF HERE (Extra Credit) *)
  admit()

(**
 * TODO 4b: Prove merge_sort is a permutation (8 points EC)
 *
 * Main Theorem: merge_sort xs is a permutation of xs.
 *
 * This combines with merge_sort_sorted to give full correctness:
 * - merge_sort_sorted: output is sorted
 * - merge_sort_perm: output contains exactly the input elements
 *
 * Together: merge_sort correctly sorts!
 *
 * Hints:
 * - Use merge_permutation in the inductive case
 * - You'll need properties about split and permutation
 * - Suggested helper: split_permutation (split doesn't lose elements)
 * - This is research-level proof complexity!
 *)
val merge_sort_perm: xs:list int ->
  Lemma (permutation xs (merge_sort xs))

let rec merge_sort_perm xs =
  (* TODO: YOUR PROOF HERE (Extra Credit) *)
  admit()

(**
 * =============================================================================
 * SUBMISSION CHECKLIST
 * =============================================================================
 *
 * Before submitting, verify:
 * - [ ] merge implementation compiles and passes test cases
 * - [ ] merge_sort implementation compiles and passes test cases
 * - [ ] merge_sort has a decreases clause and F* accepts it
 * - [ ] merge_sorted proof compiles (no admit() unless stuck)
 * - [ ] merge_sort_sorted proof compiles (no admit() unless stuck)
 * - [ ] All test cases uncommented and passing
 * - [ ] Reflection questions answered
 * - [ ] (EC) merge_permutation attempted
 * - [ ] (EC) merge_sort_perm attempted
 * - [ ] File typechecks with: fstar.exe mini_project_merge_sort.fst
 *
 * Partial Credit:
 * If you can't complete a proof, document your attempt:
 * - Show your proof structure (match cases, etc.)
 * - Explain where you got stuck
 * - Use admit() for the parts you couldn't prove
 * - Write comments explaining your approach
 *
 * This shows understanding even if you couldn't finish!
 *
 * =============================================================================
 * GETTING HELP
 * =============================================================================
 *
 * This is a challenging project! Resources available:
 *
 * - Office Hours: Monday/Wednesday 3-5pm, Friday 1-3pm
 * - Piazza: Post questions (NO complete solutions please)
 * - Study Groups: Encouraged! Discuss approaches, not code.
 * - F* Zulip: #beginner-questions channel
 * - Teaching Notes: instructor_guide/week_02_teaching_notes.md (if available)
 * - Examples: EXAMPLES.md sections on sorting and induction
 *
 * Academic Integrity:
 * - Discussing approaches and strategies: Allowed
 * - Sharing helper lemma ideas: Allowed
 * - Looking at merge sort pseudocode: Allowed
 * - Copying code or proofs from others: NOT allowed
 * - Sharing your solution code: NOT allowed
 *
 * When in doubt, ask!
 *
 * =============================================================================
 * GOOD LUCK!
 * =============================================================================
 *
 * This is one of the hardest projects in the course. Take pride in attempting it!
 * Even partial completion demonstrates significant learning.
 *
 * Remember: The goal is not just a working proof, but understanding WHY it works.
 *
 * You've got this!
 *)
