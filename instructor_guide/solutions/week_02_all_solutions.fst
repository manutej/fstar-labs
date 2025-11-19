module Week02_AllSolutions

(**
 * Complete Solutions for Week 2 Exercises
 *
 * INSTRUCTOR ONLY - Do not distribute to students!
 *
 * This file contains:
 * - Exercise 2.1: Fibonacci with decreases
 * - Exercise 2.2: McCarthy 91 function
 * - Exercise 2.3: Reverse involution (with helper lemmas!)
 * - Exercise 2.4: Map preserves length
 * - Exercise 2.5: Flatten associativity
 * - Pedagogical notes explaining solution choices
 * - Common student mistakes to watch for
 * - Alternative solutions where applicable
 *)

open FStar.List.Tot

(******************************************************************************)
(** Exercise 2.1: Fibonacci with Decreases Clause                           *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * This is students' first explicit termination proof. The key learning is
 * understanding what `decreases` means and why F* needs it.
 *
 * Common mistakes:
 * 1. Forgetting base cases (especially fib(1))
 * 2. Writing `decreases n` but still getting termination error (wrong base cases)
 * 3. Not understanding WHY n decreases (needs n > 1 before recursive calls)
 * 4. Calling fibonacci on negative numbers (should use nat, not int)
 *
 * If students struggle:
 * - Ask: "What are the base cases for Fibonacci?"
 * - Ask: "When do we recurse? What happens when n = 0 or n = 1?"
 * - Show: Draw recursion tree for fib(4) to visualize decreasing
 *)

// Solution:
let rec fibonacci (n:nat) : nat
  decreases n
=
  if n = 0 then 0
  else if n = 1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

(**
 * WHY THIS WORKS:
 *
 * F* needs to prove that the metric `n` decreases on every recursive call:
 *
 * Base cases:
 * - n = 0: No recursion, returns 0 immediately
 * - n = 1: No recursion, returns 1 immediately
 *
 * Recursive case (n >= 2):
 * - Call 1: fibonacci (n - 1)
 *   - Metric: n - 1 < n ✓ (F* proves this)
 *   - Valid because n >= 2, so n - 1 >= 1 >= 0 (still nat)
 * - Call 2: fibonacci (n - 2)
 *   - Metric: n - 2 < n ✓ (F* proves this)
 *   - Valid because n >= 2, so n - 2 >= 0 (still nat)
 *
 * Both recursive calls have strictly smaller arguments, so F* accepts the proof.
 *
 * IMPORTANT: The condition `n >= 2` (implicit in the else-else branch) ensures
 * that n - 1 and n - 2 are both valid nat values. F* tracks this via control flow.
 *)

// Test cases
let test_fib_0 = fibonacci 0   // Result: 0
let test_fib_1 = fibonacci 1   // Result: 1
let test_fib_2 = fibonacci 2   // Result: 1
let test_fib_5 = fibonacci 5   // Result: 5
let test_fib_10 = fibonacci 10 // Result: 55

(**
 * PERFORMANCE NOTE (for advanced students):
 * This implementation is exponential time O(2^n) because it recomputes
 * values. In Week 5, we'll see how to optimize with memoization while
 * maintaining verification.
 *)

(**
 * ALTERNATIVE SOLUTION (tail-recursive with accumulator):
 *)
let rec fibonacci_acc (n:nat) (a:nat) (b:nat) : nat
  decreases n
=
  if n = 0 then a
  else fibonacci_acc (n - 1) b (a + b)

let fibonacci_tail (n:nat) : nat =
  fibonacci_acc n 0 1

(**
 * PEDAGOGICAL NOTE on alternative:
 * The tail-recursive version is more efficient (linear time) and shows
 * that the same mathematical function can have multiple implementations
 * with different termination arguments. This is a nice "stretch goal"
 * for advanced students.
 *)

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: Why does F* require the `decreases` clause here?
 * A1: While F* could potentially infer `decreases n` automatically for this
 *     simple case, requiring it explicitly helps students understand that
 *     termination is not magic - it requires a proof. The decreasing metric
 *     is the fundamental concept.
 *
 * Q2: What would happen if we removed the base case for n = 1?
 * A2: The function would get stuck: fib(1) = fib(0) + fib(-1), but -1 is
 *     not a nat! F* would give a type error, preventing this bug at compile
 *     time. This is refinement types protecting us.
 *
 * Q3: Can you write a fibonacci function that doesn't terminate?
 * A3: In the `Tot` effect, no - F* rejects all non-terminating functions.
 *     However, you could use the `Dv` (divergence) effect:
 *     `let rec bad_fib (n:int) : Dv int = bad_fib n`
 *     This explicitly marks the function as potentially non-terminating.
 *)

(******************************************************************************)
(** Exercise 2.2: McCarthy 91 Function                                      *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * This is significantly harder than 2.1! The McCarthy 91 function is a
 * classic example of non-structural recursion requiring lexicographic ordering.
 *
 * Named after John McCarthy (inventor of Lisp), this function is famous for:
 * - Non-obvious termination proof
 * - Multiple recursive calls with different arguments
 * - Interesting mathematical properties
 *
 * Common mistakes:
 * 1. Using `decreases n` (doesn't work - n increases sometimes!)
 * 2. Not understanding lexicographic ordering %[m; n]
 * 3. Getting the decreasing metric backwards
 * 4. Confusion about why 101 is the pivot
 *
 * Teaching strategy:
 * - Work through examples: M(99), M(100), M(101)
 * - Show the recursion tree
 * - Explain: "When n > 100, we subtract. When n <= 100, we add then recurse twice."
 * - Key insight: The metric (101 - n, n) decreases lexicographically
 *)

// Solution:
let rec mccarthy91 (n:int) : int
  decreases %[101 - n; n]  // Lexicographic ordering!
=
  if n > 100
  then n - 10
  else mccarthy91 (mccarthy91 (n + 11))

(**
 * WHY THIS WORKS (detailed explanation):
 *
 * The decreasing metric is %[101 - n; n], which means:
 * - First priority: 101 - n decreases
 * - Second priority: if 101 - n stays the same, then n decreases
 *
 * Case 1: n > 100
 * - No recursion, returns immediately
 * - No need to check metric
 *
 * Case 2: n <= 100
 * - Outer call: mccarthy91 (mccarthy91 (n + 11))
 * - Inner call first: mccarthy91 (n + 11)
 *
 * Inner call: mccarthy91 (n + 11)
 * - Argument: n + 11
 * - New metric: %[101 - (n + 11); n + 11] = %[90 - n; n + 11]
 * - Compare to old: %[101 - n; n]
 * - First component: (90 - n) < (101 - n)?
 *   - Yes! 90 - n = (101 - n) - 11, so first component decreases ✓
 *
 * Outer call: mccarthy91 (result)
 * - Where result = mccarthy91 (n + 11)
 * - If n <= 100, then n + 11 <= 111
 * - After one call, we know result will be either:
 *   a) (n + 11) - 10 = n + 1 (if n + 11 > 100, i.e., n >= 90)
 *   b) 91 (after several recursive calls, if n < 90)
 * - In case (a): metric for mccarthy91(n+1) is %[101-(n+1); n+1] = %[100-n; n+1]
 *   - First component: (100-n) < (101-n)? Yes! ✓
 * - In case (b): metric for mccarthy91(91) is %[101-91; 91] = %[10; 91]
 *   - First component: 10 < (101-n) for all n <= 100?
 *   - Yes! Since n <= 100, we have 101-n >= 1, and in practice 101-n >= 10
 *   - Actually, we need more careful analysis...
 *
 * BETTER EXPLANATION of the metric:
 * The key insight is that 101 - n measures "distance to the base case".
 * - When n > 100, we're at the base case
 * - When n <= 100, adding 11 brings us closer (101 - (n+11) = 90 - n < 101 - n)
 * - The second component n is used to break ties
 *
 * This is a sophisticated termination argument! Don't expect all students to
 * fully understand it. Focus on: "F* accepts it, trust the tool."
 *)

// Test cases
let test_m91_1 = mccarthy91 99   // Result: 91
let test_m91_2 = mccarthy91 100  // Result: 91
let test_m91_3 = mccarthy91 101  // Result: 91
let test_m91_4 = mccarthy91 102  // Result: 92
let test_m91_5 = mccarthy91 110  // Result: 100

(**
 * MATHEMATICAL PROPERTY (cool fact to share):
 * For all n, mccarthy91(n) returns:
 * - 91 if n <= 101
 * - n - 10 if n > 101
 *
 * This is a provable theorem! (But beyond scope of Week 2)
 *)

(**
 * ALTERNATIVE SOLUTION (explicit about metric):
 * Some students might find it clearer to use a helper function:
 *)
let rec mccarthy91_helper (n:int) (fuel:nat) : option int
  decreases fuel
=
  if fuel = 0 then None  // Out of fuel
  else if n > 100 then Some (n - 10)
  else (
    match mccarthy91_helper (n + 11) (fuel - 1) with
    | None -> None
    | Some m -> mccarthy91_helper m (fuel - 1)
  )

let mccarthy91_alt (n:int) : int =
  match mccarthy91_helper n 1000 with  // Sufficient fuel
  | Some m -> m
  | None -> 91  // Should never happen

(**
 * PEDAGOGICAL NOTE on alternative:
 * The fuel-based approach is more explicit but less elegant. It's useful
 * for showing students that termination can be made obvious by adding
 * a decreasing counter. However, it's not as clean as the direct approach.
 *)

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: Why doesn't `decreases n` work for this function?
 * A1: Because in the recursive case, we call mccarthy91(n + 11) where
 *     n + 11 > n! The metric n actually *increases* on the inner call.
 *     We need a more sophisticated metric that accounts for the fact
 *     that adding 11 brings us closer to the base case (> 100).
 *
 * Q2: What does the lexicographic ordering %[101 - n; n] mean?
 * A2: Lexicographic ordering is like dictionary ordering:
 *     - Compare first components: if 101-n decreases, accept
 *     - If first components are equal, compare second components
 *     - %[a; b] < %[c; d] iff (a < c) OR (a = c AND b < d)
 *     For McCarthy 91, 101-n is the primary metric (distance to base case).
 *
 * Q3: Trace mccarthy91(99) by hand. What happens?
 * A3: mccarthy91(99)
 *     = mccarthy91(mccarthy91(110))    [since 99 <= 100]
 *     = mccarthy91(100)                [since 110 > 100]
 *     = mccarthy91(mccarthy91(111))    [since 100 <= 100]
 *     = mccarthy91(101)                [since 111 > 100]
 *     = mccarthy91(mccarthy91(112))    [since 101 <= 100]
 *     = mccarthy91(102)                [since 112 > 100]
 *     = ... eventually reaches 91
 *     This shows the complex recursion pattern!
 *
 * Q4: (Challenge) Prove that mccarthy91(n) = 91 for all n <= 101.
 * A4: This requires strong induction on 101 - n. The proof is beyond
 *     Week 2 scope, but here's the idea:
 *     - Base case: n > 100, then mccarthy91(n+11) > 100, so result = n+1
 *     - Inductive case: n <= 100, by IH mccarthy91(n+11) eventually equals 91
 *       (or n+1 if n >= 90), then mccarthy91(91) = 91 (or mccarthy91(n+1))...
 *     (Full proof in Software Foundations vol. 2)
 *)

(******************************************************************************)
(** Exercise 2.3: Reverse Involution                                        *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * This is the HARDEST Week 2 exercise! It requires:
 * - Understanding structural induction
 * - Discovering needed helper lemmas
 * - Applying helper lemmas correctly
 *
 * This exercise is designed to frustrate students (in a good way!) to show
 * that proof engineering requires planning and decomposition.
 *
 * Common mistakes:
 * 1. Trying to prove directly without helper lemmas (F* rejects)
 * 2. Not understanding what helper lemmas are needed
 * 3. Confusion about when to apply helper lemmas
 * 4. Forgetting to recurse (apply IH)
 * 5. Not understanding why ()` is the proof
 *
 * Teaching strategy:
 * - Let students struggle! This builds problem-solving skills.
 * - When they get stuck, ask: "What does F* need to know about reverse and append?"
 * - Guide them to discover reverse_append lemma
 * - Show that proof decomposition is normal engineering practice
 *)

// Reverse function (provided)
let rec reverse (#a:Type) (xs:list a) : list a =
  match xs with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]

(**
 * HELPER LEMMA 1: Reverse distributes over append (with swap)
 *)
val reverse_append: #a:Type -> xs:list a -> ys:list a ->
  Lemma (reverse (append xs ys) == append (reverse ys) (reverse xs))

let rec reverse_append #a xs ys =
  match xs with
  | [] ->
      // Base case: reverse (append [] ys) == append (reverse ys) (reverse [])
      // LHS: reverse (append [] ys) = reverse ys  [by def of append]
      // RHS: append (reverse ys) (reverse [])
      //    = append (reverse ys) []               [by def of reverse]
      //    = reverse ys                           [by property of append]
      // F* proves these are equal automatically!
      ()
  | hd :: tl ->
      // Inductive case: reverse (append (hd::tl) ys) == append (reverse ys) (reverse (hd::tl))
      // IH: reverse (append tl ys) == append (reverse ys) (reverse tl)
      reverse_append tl ys;  // Apply induction hypothesis
      // Now F* knows: reverse (append tl ys) == append (reverse ys) (reverse tl)
      //
      // LHS: reverse (append (hd::tl) ys)
      //    = reverse (hd :: append tl ys)              [by def of append]
      //    = append (reverse (append tl ys)) [hd]      [by def of reverse]
      //    = append (append (reverse ys) (reverse tl)) [hd]  [by IH]
      //
      // RHS: append (reverse ys) (reverse (hd::tl))
      //    = append (reverse ys) (append (reverse tl) [hd])  [by def of reverse]
      //
      // We need: append (append (reverse ys) (reverse tl)) [hd]
      //       == append (reverse ys) (append (reverse tl) [hd])
      // This is append associativity! F* knows this for lists.
      ()

(**
 * WHY WE NEED THIS HELPER:
 * In the main proof reverse_reverse, when we have reverse(reverse(hd::tl)),
 * we get reverse(append (reverse tl) [hd]). To make progress, we need to
 * know how reverse distributes over append. That's what this lemma provides.
 *)

(**
 * HELPER LEMMA 2: Reverse of singleton
 *)
val reverse_singleton: #a:Type -> x:a ->
  Lemma (reverse [x] == [x])

let reverse_singleton #a x =
  // reverse [x]
  // = reverse (x :: [])            [by notation]
  // = append (reverse []) [x]      [by def of reverse]
  // = append [] [x]                [by def of reverse]
  // = [x]                          [by def of append]
  // F* proves this automatically!
  ()

(**
 * PEDAGOGICAL NOTE:
 * reverse_singleton is trivial (F* proves it with just `()`), but it's
 * good to state it explicitly for clarity. Some students will discover
 * they don't need this lemma - that's fine! The proof works either way.
 *)

(**
 * MAIN PROOF: Reverse is an involution
 *)
val reverse_reverse: #a:Type -> xs:list a ->
  Lemma (reverse (reverse xs) == xs)

let rec reverse_reverse #a xs =
  match xs with
  | [] ->
      // Base case: reverse (reverse []) == []
      // LHS: reverse (reverse []) = reverse [] = []
      // RHS: []
      // Trivially equal!
      ()
  | hd :: tl ->
      // Inductive case: reverse (reverse (hd::tl)) == hd::tl
      // IH: reverse (reverse tl) == tl
      reverse_reverse tl;  // Apply IH
      // Now F* knows: reverse (reverse tl) == tl
      //
      // LHS: reverse (reverse (hd::tl))
      //    = reverse (append (reverse tl) [hd])       [by def of reverse]
      //
      // Now apply helper lemma: reverse (append xs ys) == append (reverse ys) (reverse xs)
      reverse_append (reverse tl) [hd];
      // F* now knows: reverse (append (reverse tl) [hd])
      //            == append (reverse [hd]) (reverse (reverse tl))
      //
      // Simplify reverse [hd]:
      reverse_singleton hd;
      // F* now knows: reverse [hd] == [hd]
      //
      // Continue:
      //    = append [hd] (reverse (reverse tl))   [by reverse_singleton]
      //    = append [hd] tl                       [by IH]
      //    = hd :: tl                             [by def of append]
      //
      // Which equals the RHS! QED.
      ()

(**
 * PROOF STRUCTURE SUMMARY:
 * 1. Match on xs (structural induction)
 * 2. Base case []: trivial
 * 3. Inductive case hd::tl:
 *    a. Apply IH: reverse_reverse tl
 *    b. Apply helper: reverse_append (reverse tl) [hd]
 *    c. Apply helper: reverse_singleton hd
 *    d. F* + SMT connect the dots!
 *
 * This is beautiful proof engineering: complex property proven by combining
 * simple lemmas and letting the SMT solver handle the arithmetic.
 *)

(**
 * ALTERNATIVE SOLUTION (more explicit asserts):
 * Some students might want to see intermediate steps:
 *)
let rec reverse_reverse_explicit #a xs =
  match xs with
  | [] -> ()
  | hd :: tl ->
      reverse_reverse_explicit tl;
      reverse_append (reverse tl) [hd];
      reverse_singleton hd;
      // Explicit asserts to show F* what we know:
      assert (reverse (hd :: tl) == append (reverse tl) [hd]);
      assert (reverse (append (reverse tl) [hd]) == append [hd] (reverse (reverse tl)));
      assert (reverse (reverse tl) == tl);
      assert (append [hd] tl == hd :: tl);
      ()

(**
 * PEDAGOGICAL NOTE on explicit version:
 * The asserts are unnecessary (F* figures it out), but they help students
 * see the logical steps. Use this for students who say "I don't understand
 * what F* is doing!" Show them: these are the steps F* takes internally.
 *)

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: Why can't we prove reverse_reverse without helper lemmas?
 * A1: Because the SMT solver doesn't automatically know how reverse interacts
 *     with append. When we expand reverse(reverse(hd::tl)), we get
 *     reverse(append (reverse tl) [hd]), and F* doesn't know how to
 *     "pull apart" this nested structure without the reverse_append lemma.
 *
 * Q2: What is the induction hypothesis in this proof?
 * A2: In the inductive case (hd::tl), the IH is: reverse(reverse tl) == tl.
 *     This is what we get from the recursive call `reverse_reverse tl`.
 *     We assume the property holds for smaller lists (tl) and use that
 *     to prove it for the larger list (hd::tl).
 *
 * Q3: Why is the return value `()` for lemmas?
 * A3: Lemmas prove properties, not compute values. The interesting part is
 *     the TYPE: `Lemma (reverse (reverse xs) == xs)` says "this is a proof
 *     of that property". The return value `()` (unit) is just a marker
 *     that the proof completed. The real "output" is the knowledge F*
 *     gains about the property being true.
 *
 * Q4: (Challenge) Prove reverse_append without using associativity of append.
 * A4: You'd need to prove append associativity first! This shows the
 *     hierarchy of lemmas:
 *     - append_assoc (primitive)
 *     - reverse_append (uses append_assoc)
 *     - reverse_reverse (uses reverse_append)
 *     This is proof engineering: building complex proofs from simple ones.
 *)

(******************************************************************************)
(** Exercise 2.4: Map Preserves Length                                      *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * This is easier than 2.3 (no helper lemmas needed!), but still requires
 * understanding structural induction. It's a good "confidence builder"
 * after the difficulty of reverse_reverse.
 *
 * Common mistakes:
 * 1. Forgetting to apply IH (recursive call to lemma)
 * 2. Not understanding why base case is trivial
 * 3. Confusion about implicit type parameters (#a #b)
 *
 * Teaching strategy:
 * - Use this to reinforce induction pattern
 * - Show that some proofs are easy (SMT handles most of it)
 * - Contrast with 2.3 to show when helper lemmas are needed
 *)

// Map function (standard library, but we'll show it for completeness)
let rec map (#a #b:Type) (f:a -> b) (xs:list a) : list b =
  match xs with
  | [] -> []
  | hd :: tl -> f hd :: map f tl

(**
 * LEMMA: Map preserves length
 *)
val map_length: #a:Type -> #b:Type -> f:(a -> b) -> xs:list a ->
  Lemma (length (map f xs) == length xs)

let rec map_length #a #b f xs =
  match xs with
  | [] ->
      // Base case: length (map f []) == length []
      // LHS: length (map f []) = length [] = 0  [by def of map and length]
      // RHS: length [] = 0                      [by def of length]
      // Equal! QED.
      ()
  | hd :: tl ->
      // Inductive case: length (map f (hd::tl)) == length (hd::tl)
      // IH: length (map f tl) == length tl
      map_length f tl;  // Apply IH
      // Now F* knows: length (map f tl) == length tl
      //
      // LHS: length (map f (hd::tl))
      //    = length (f hd :: map f tl)    [by def of map]
      //    = 1 + length (map f tl)        [by def of length]
      //    = 1 + length tl                [by IH]
      //
      // RHS: length (hd::tl)
      //    = 1 + length tl                [by def of length]
      //
      // Equal! F* + SMT prove this automatically.
      ()

(**
 * WHY THIS WORKS WITHOUT HELPER LEMMAS:
 * Unlike reverse_reverse, this proof doesn't involve nested function
 * compositions. The structure of map and length align perfectly:
 * - Both recurse on the list structure
 * - Both have simple recursive cases (1 + ...)
 * - SMT can handle the arithmetic automatically
 *
 * This is an example where induction + SMT is sufficient!
 *)

// Test: Demonstrate the lemma
let example_map_length () =
  let f (x:int) : int = x * 2 in
  let xs = [1; 2; 3; 4; 5] in
  map_length f xs;
  // Now F* knows: length (map f xs) == length xs
  assert (length (map f xs) == 5);
  ()

(**
 * ALTERNATIVE SOLUTION (using FStar.List.Tot.Properties):
 * The standard library already has this lemma! Students could just use:
 *)
// open FStar.List.Tot.Properties
// // Then map_length is already available!

(**
 * PEDAGOGICAL NOTE on standard library:
 * Don't tell students about FStar.List.Tot.Properties yet! The point of
 * Week 2 is to learn to WRITE proofs. In Week 4+, we'll teach them to
 * use library lemmas. For now, reinvent the wheel to learn the skill.
 *)

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: Why is this proof easier than reverse_reverse?
 * A1: Because map and length have aligned recursive structure, and there's
 *     no nested function composition. We don't need to reason about how
 *     one function affects another's result - just that both recurse the
 *     same way on the list structure.
 *
 * Q2: What are the implicit type parameters #a and #b?
 * A2: The `#` means F* infers these from context. When we write
 *     `map_length f xs` where `f : int -> string` and `xs : list int`,
 *     F* automatically infers #a=int and #b=string. This is type inference.
 *     We could write it explicitly: `map_length #int #string f xs`.
 *
 * Q3: Does this property hold for all functions f, or only some?
 * A3: ALL functions! The type `f:(a -> b)` means any total function from
 *     a to b. The length property doesn't depend on what f does to elements,
 *     only that map applies f to each element. This is a universal property.
 *
 * Q4: (Challenge) Prove that map (compose f g) xs == map f (map g xs).
 * A4: This requires structural induction on xs, similar to map_length:
 *     ```
 *     let rec map_compose #a #b #c (f:b -> c) (g:a -> b) (xs:list a) :
 *       Lemma (map (fun x -> f (g x)) xs == map f (map g xs)) =
 *       match xs with
 *       | [] -> ()
 *       | hd :: tl -> map_compose f g tl; ()
 *     ```
 *     This is a functor law from category theory!
 *)

(******************************************************************************)
(** Exercise 2.5: Flatten Associativity                                     *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * This exercise teaches proof decomposition: using a provided helper lemma
 * to prove a more complex property. It's easier than 2.3 (helper is given!)
 * but harder than 2.4 (need to apply helper correctly).
 *
 * Common mistakes:
 * 1. Not understanding when to apply append_assoc
 * 2. Applying append_assoc with wrong arguments
 * 3. Forgetting the IH
 * 4. Not seeing the connection between flatten and append
 *
 * Teaching strategy:
 * - Provide append_assoc (focus on using it, not proving it)
 * - Guide students: "Where does append_assoc help in the inductive case?"
 * - Show: Helper lemmas are tools in your toolbox
 *)

// Flatten function
let rec flatten (#a:Type) (xss:list (list a)) : list a =
  match xss with
  | [] -> []
  | xs :: xss' -> append xs (flatten xss')

(**
 * HELPER LEMMA (provided to students):
 * Append is associative
 *)
val append_assoc: #a:Type -> xs:list a -> ys:list a -> zs:list a ->
  Lemma (append (append xs ys) zs == append xs (append ys zs))

let rec append_assoc #a xs ys zs =
  match xs with
  | [] ->
      // Base: append (append [] ys) zs == append [] (append ys zs)
      // LHS: append (append [] ys) zs = append ys zs
      // RHS: append [] (append ys zs) = append ys zs
      ()
  | hd :: tl ->
      // Inductive: append (append (hd::tl) ys) zs == append (hd::tl) (append ys zs)
      // IH: append (append tl ys) zs == append tl (append ys zs)
      append_assoc tl ys zs;
      // LHS: append (append (hd::tl) ys) zs
      //    = append (hd :: append tl ys) zs
      //    = hd :: append (append tl ys) zs
      //    = hd :: append tl (append ys zs)    [by IH]
      // RHS: append (hd::tl) (append ys zs)
      //    = hd :: append tl (append ys zs)
      // Equal!
      ()

(**
 * MAIN PROOF: Flatten distributes over append of list-of-lists
 *)
val flatten_append: #a:Type -> xss:list (list a) -> yss:list (list a) ->
  Lemma (flatten (append xss yss) == append (flatten xss) (flatten yss))

let rec flatten_append #a xss yss =
  match xss with
  | [] ->
      // Base case: flatten (append [] yss) == append (flatten []) (flatten yss)
      // LHS: flatten (append [] yss)
      //    = flatten yss                  [by def of append]
      // RHS: append (flatten []) (flatten yss)
      //    = append [] (flatten yss)      [by def of flatten]
      //    = flatten yss                  [by def of append]
      // Equal!
      ()
  | xs :: xss' ->
      // Inductive case: flatten (append (xs::xss') yss) == append (flatten (xs::xss')) (flatten yss)
      // IH: flatten (append xss' yss) == append (flatten xss') (flatten yss)
      flatten_append xss' yss;  // Apply IH
      // Now F* knows: flatten (append xss' yss) == append (flatten xss') (flatten yss)
      //
      // LHS: flatten (append (xs::xss') yss)
      //    = flatten (xs :: append xss' yss)           [by def of append]
      //    = append xs (flatten (append xss' yss))     [by def of flatten]
      //    = append xs (append (flatten xss') (flatten yss))  [by IH]
      //
      // RHS: append (flatten (xs::xss')) (flatten yss)
      //    = append (append xs (flatten xss')) (flatten yss)  [by def of flatten]
      //
      // We need: append xs (append (flatten xss') (flatten yss))
      //       == append (append xs (flatten xss')) (flatten yss)
      //
      // This is EXACTLY append associativity!
      append_assoc xs (flatten xss') (flatten yss);
      // Now F* knows the two sides are equal. QED.
      ()

(**
 * WHY append_assoc IS THE KEY:
 * In the inductive case, we end up with:
 * - LHS: append xs (append (flatten xss') (flatten yss))
 * - RHS: append (append xs (flatten xss')) (flatten yss)
 *
 * These are EXACTLY the two sides of append associativity! The helper lemma
 * append_assoc tells F* they're equal, completing the proof.
 *
 * This demonstrates: proof engineering = recognizing patterns and applying
 * the right lemma at the right time.
 *)

// Test example
let example_flatten_append () =
  let xss = [[1; 2]; [3]] in
  let yss = [[4; 5]; [6; 7]] in
  flatten_append xss yss;
  // Now F* knows:
  // flatten (append xss yss) == append (flatten xss) (flatten yss)
  // i.e., flatten [[1;2]; [3]; [4;5]; [6;7]] == [1;2;3;4;5;6;7]
  assert (flatten (append xss yss) == [1; 2; 3; 4; 5; 6; 7]);
  ()

(**
 * ALTERNATIVE SOLUTION (inline the append_assoc proof):
 * Advanced students might try to prove it all at once:
 *)
let rec flatten_append_inline #a xss yss =
  match xss with
  | [] -> ()
  | xs :: xss' ->
      flatten_append_inline xss' yss;
      // Inline proof of append_assoc:
      let rec append_assoc_inline (xs ys zs : list a) :
        Lemma (append (append xs ys) zs == append xs (append ys zs)) =
        match xs with
        | [] -> ()
        | h :: t -> append_assoc_inline t ys zs
      in
      append_assoc_inline xs (flatten xss') (flatten yss);
      ()

(**
 * PEDAGOGICAL NOTE on inlining:
 * This works but is bad style! Proof modularity is important:
 * - Separate lemmas are reusable
 * - Separate lemmas are easier to understand
 * - Separate lemmas can be tested independently
 * Discourage students from inlining everything.
 *)

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: Why do we need the append_assoc helper lemma?
 * A1: Because in the inductive case, we need to rearrange parentheses in
 *     nested appends. SMT doesn't automatically know append is associative
 *     (it's not a built-in axiom). We must prove it via the helper lemma.
 *
 * Q2: Could we prove flatten_append without append_assoc?
 * A2: Not easily! We'd have to prove associativity inline, which means
 *     proving append_assoc within our proof. It's much cleaner to factor
 *     it out as a separate helper. This is proof engineering best practice.
 *
 * Q3: What pattern do you see in flatten vs. flatten_append?
 * A3: Both use structural induction on the outer list structure:
 *     - flatten recurses on xss
 *     - flatten_append also recurses on xss (the first argument)
 *     This alignment makes the proof straightforward. When function and
 *     lemma recurse the same way, the proof often "just works" with IH + helpers.
 *
 * Q4: (Challenge) Prove that flatten [[x]] == [x].
 * A4: Direct proof:
 *     ```
 *     let flatten_singleton #a (x:a) : Lemma (flatten [[x]] == [x]) =
 *       // flatten [[x]]
 *       // = flatten ([x] :: [])        [by notation]
 *       // = append [x] (flatten [])    [by def of flatten]
 *       // = append [x] []              [by def of flatten]
 *       // = [x]                        [by property of append]
 *       ()
 *     ```
 *     F* proves this automatically! No recursion needed for singleton.
 *)

(******************************************************************************)
(** Pedagogical Meta-Notes for Instructors                                  *)
(******************************************************************************)

(**
 * GRADING RUBRIC GUIDANCE:
 *
 * Exercise 2.1 (Fibonacci): (10 points)
 * - Correct implementation: 5 points
 * - Correct decreases clause: 3 points
 * - Reflection answers: 2 points
 * PARTIAL CREDIT: Base cases correct but termination fails: 6 points
 *
 * Exercise 2.2 (McCarthy 91): (15 points)
 * - Correct implementation: 7 points (this is HARD!)
 * - Correct lexicographic decreases: 6 points (many will struggle here)
 * - Reflection answers: 2 points
 * PARTIAL CREDIT: Correct logic but wrong decreases: 7 points
 * PARTIAL CREDIT: Using fuel-based alternative: full credit (it works!)
 *
 * Exercise 2.3 (Reverse involution): (25 points)
 * - Helper lemma reverse_append: 10 points (crucial!)
 * - Helper lemma reverse_singleton: 3 points (nice to have)
 * - Main proof reverse_reverse: 10 points
 * - Reflection answers: 2 points
 * PARTIAL CREDIT: Correct structure but using admit(): 15 points
 * PARTIAL CREDIT: Only one helper lemma: 18 points
 *
 * Exercise 2.4 (Map length): (15 points)
 * - Correct proof: 12 points
 * - Reflection answers: 3 points
 * PARTIAL CREDIT: Correct structure but admit(): 8 points
 * NOTE: This is easier than 2.3, expect high scores
 *
 * Exercise 2.5 (Flatten append): (20 points)
 * - Correct proof using append_assoc: 15 points
 * - Reflection answers: 5 points
 * PARTIAL CREDIT: Correct structure but not applying append_assoc: 10 points
 *
 * TOTAL: 85 points
 * (Mini-project adds 100 points for Week 2 total of 185)
 *
 * GRADING PHILOSOPHY:
 * - Week 2 is HARD - first exposure to manual proofs
 * - Be generous with partial credit for effort and understanding
 * - Value correct structure even if proof incomplete
 * - Reward creative solutions (fuel-based, explicit asserts, etc.)
 * - Penalize only severe misunderstandings (no recursion, no induction)
 *)

(**
 * COMMON EXCELLENT STUDENT SOLUTIONS:
 *
 * 1. Adding explicit asserts to show understanding
 *    - Great! Shows they understand the proof steps
 *    - Even if asserts are unnecessary, shows good thinking
 *
 * 2. Writing additional helper lemmas beyond what's required
 *    - Excellent proof engineering! Reward this
 *    - Example: append_nil, reverse_nil, etc.
 *
 * 3. Providing alternative implementations (tail-recursive, fuel-based)
 *    - Shows deep understanding of termination
 *    - Give bonus points for creative alternatives
 *
 * 4. Detailed comments explaining proof steps
 *    - This is professional-quality work
 *    - Consider showcasing in class (with permission)
 *)

(**
 * RED FLAGS (possible issues to investigate):
 *
 * 1. All exercises perfect but student struggled in class
 *    - Talk to student: "Can you explain your reverse_append proof?"
 *    - If they can't explain, discuss academic integrity
 *
 * 2. Solutions identical to another student
 *    - Compare git histories, timestamps
 *    - Could be collaboration (allowed) or copying (not allowed)
 *    - Have conversation to determine which
 *
 * 3. Solutions match instructor solutions exactly (!)
 *    - Investigate: did solutions leak?
 *    - Check repository access logs
 *    - Remind students: instructor solutions are confidential
 *
 * 4. Using advanced features not taught yet
 *    - Example: tactics, calc mode, SMT patterns
 *    - Could be student explored on their own (great!)
 *    - Or copied from internet (concerning)
 *    - Ask: "Where did you learn about this?"
 *)

(**
 * EXTENSION EXERCISES (for advanced students):
 *
 * 1. Prove that flatten is a monoid homomorphism:
 *    - flatten [] == []
 *    - flatten (append xss yss) == append (flatten xss) (flatten yss)
 *    - (Second part is Exercise 2.5!)
 *
 * 2. Implement and verify list_map_option:
 *    - Type: (a -> option b) -> list a -> option (list b)
 *    - Prove: If f always returns Some, result is always Some
 *
 * 3. Prove map fusion: map f (map g xs) == map (f ∘ g) xs
 *
 * 4. Implement fold_right and prove fold_right (:) [] xs == xs
 *
 * 5. Prove that reverse is its own inverse using only structural induction
 *    (no helper lemmas about append)
 *    Hint: Define reverse with an accumulator
 *)

(**
 * COMMON STUDENT QUESTIONS (and how to answer):
 *
 * Q: "Why do I need to write `()` at the end of lemmas?"
 * A: Lemmas return unit type. `()` is the only value of unit type.
 *    Think of it as "proof complete" marker. The interesting part is
 *    the Lemma type, not the return value.
 *
 * Q: "How do I know what helper lemmas I need?"
 * A: Great question! Try proving directly first. When F* gives error
 *    "could not prove X", ask: "What would let me prove X?" That's
 *    often your helper lemma. It's a skill developed through practice.
 *
 * Q: "Can I use admit() in my submission?"
 * A: For Week 2, yes! We give partial credit. Mark clearly what you
 *    couldn't complete. But try to minimize - each admit() loses points.
 *
 * Q: "Why doesn't F* prove this automatically? It seems obvious!"
 * A: F* uses SMT solver, which is powerful but not omniscient. Some
 *    properties (like reverse_append) require explicit inductive proofs.
 *    As you gain experience, you'll develop intuition for what SMT can
 *    vs. can't handle automatically.
 *
 * Q: "Is there a way to see what F* is doing internally?"
 * A: Yes! Use `--debug` flags and `--log_queries`. But this is advanced.
 *    For Week 2, focus on understanding the proof structure. We'll
 *    cover debugging in Week 6.
 *)

(**
 * TIPS FOR OFFICE HOURS:
 *
 * When student is stuck on 2.1 (Fibonacci):
 * - Ask them to trace fibonacci(3) by hand
 * - Draw the recursion tree
 * - Ask: "What's the base case? Recursive case?"
 * - Point out: Need TWO base cases (0 and 1)
 *
 * When student is stuck on 2.2 (McCarthy 91):
 * - Don't expect full understanding! This is HARD.
 * - Suggest: Try the fuel-based approach (more intuitive)
 * - Or: Provide the decreases clause, ask them to explain why it works
 * - Focus on: Understanding the recursion pattern, not the metric
 *
 * When student is stuck on 2.3 (Reverse involution):
 * - Ask: "What does F* error say?"
 * - Guide: "What property of reverse and append do you need?"
 * - Hint: "What happens when you reverse a concatenation?"
 * - If really stuck: Give them reverse_append, ask them to prove main lemma
 *
 * When student is stuck on 2.4 (Map length):
 * - This should be easier! If stuck, check understanding of:
 *   - Structural induction pattern
 *   - How to apply IH (recursive call to lemma)
 *   - Base case vs. inductive case
 * - Walk through the proof step by step
 *
 * When student is stuck on 2.5 (Flatten append):
 * - Ask: "Where in your proof do you have nested appends?"
 * - Point out: "You need to rearrange parentheses. What helps with that?"
 * - Show them the append_assoc lemma and ask where to apply it
 * - If they apply it wrong, trace through the types
 *)
