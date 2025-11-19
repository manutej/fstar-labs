module Week01_AllSolutions

(**
 * Complete Solutions for Week 1 Exercises
 *
 * INSTRUCTOR ONLY - Do not distribute to students!
 *
 * This file contains:
 * - Exercise 1.1: Safe Division
 * - Exercise 1.2: Validated Input Parsing
 * - Exercise 1.3: ETL Pipeline
 * - Pedagogical notes explaining solution choices
 *)

open FStar.List.Tot

(******************************************************************************)
(** Exercise 1.1: Safe Division Function                                     *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * This is students' first refinement type definition. Keep it simple!
 *
 * Common mistakes:
 * 1. Using `=` instead of `<>` (wrong inequality)
 * 2. Forgetting the curly braces {}
 * 3. Writing `type nonzero = int{x <> 0}` (missing variable binding)
 *
 * If students struggle, ask:
 * - "What property must b have to make division safe?"
 * - "How do you write 'not equal' in F*?" (answer: <>)
 *)

// Solution:
type nonzero = x:int{x <> 0}

let safe_divide (a:int) (b:nonzero) : int = a / b

// Test cases
let test1_1 = safe_divide 10 2     // Result: 5
let test1_2 = safe_divide 100 (-5) // Result: -20
let test1_3 = safe_divide 7 1      // Result: 7

// These should be TYPE ERRORS:
// let test_fail1 = safe_divide 10 0
// Error: "Expected type nonzero, got type int"
//
// let test_fail2 : nonzero = 0
// Error: "Could not prove refinement: 0 <> 0"

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: Why does F* reject `safe_divide 10 0` at compile time?
 * A1: F* checks that 0 has type `nonzero`. This requires proving `0 <> 0`,
 *     which is false. Therefore, type checking fails at compile time.
 *
 * Q2: How is this different from a runtime check?
 * A2: Runtime checks (like `if b == 0 then error else a/b`) happen during
 *     execution and can fail. F*'s refinement types are checked at compile
 *     time, so invalid code never runs. This is provable safety.
 *
 * Q3: What happens to refinement types during extraction?
 * A3: Refinement types are erased during extraction to OCaml/F#/C.
 *     The extracted code is just `let safe_divide a b = a / b` with no
 *     runtime checks, because F* already proved it's safe at compile time.
 *)

(******************************************************************************)
(** Exercise 1.2: Validated Input Parsing                                    *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * The clamp function is the key challenge. Students must understand
 * that F* tracks control flow information.
 *
 * Common mistakes:
 * 1. Forgetting the precondition `max >= min`
 * 2. Not understanding why each branch typechecks
 * 3. Trying to add explicit asserts (unnecessary here!)
 *
 * Teaching strategy:
 * - Show students the error when precondition is removed
 * - Ask them to explain why each branch satisfies the postcondition
 * - Emphasize: F* is tracking what's true in each branch!
 *)

// Solution:
type age = x:int{x >= 0 && x <= 150}

let clamp (min:int) (max:int{max >= min}) (x:int)
  : y:int{y >= min && y <= max} =
  if x < min then min
  else if x > max then max
  else x

(**
 * WHY THIS WORKS (detailed proof for instructors to explain):
 *
 * Branch 1: `if x < min then min`
 *   - Context: x < min
 *   - Return: min
 *   - Prove: min >= min && min <= max
 *   - F* proves: min >= min (trivial) && min <= max (from precondition)
 *
 * Branch 2: `else if x > max then max`
 *   - Context: x >= min && x > max
 *   - Return: max
 *   - Prove: max >= min && max <= max
 *   - F* proves: max >= min (from precondition) && max <= max (trivial)
 *
 * Branch 3: `else x`
 *   - Context: x >= min && x <= max (negation of previous conditions)
 *   - Return: x
 *   - Prove: x >= min && x <= max
 *   - F* proves: directly from control flow context!
 *
 * This is a beautiful example of F* tracking control flow information.
 *)

// Test cases:
let clamp_test1 = clamp 0 100 50    // Result: 50
let clamp_test2 = clamp 0 100 (-10) // Result: 0
let clamp_test3 = clamp 0 100 200   // Result: 100

// Part B: Positive refinement
type positive = x:int{x > 0}

let safe_sqrt (n:positive) : positive = n
// Note: Real sqrt would return float, this is simplified for exercise

// Part C: Bounded integers
type bounded100 = x:int{x >= 0 && x < 100}

let increment_wrap (x:bounded100) : bounded100 =
  if x = 99 then 0 else x + 1

(**
 * ALTERNATIVE SOLUTION for increment_wrap (using mod):
 *)
let increment_wrap_alt (x:bounded100) : bounded100 =
  (x + 1) % 100

(**
 * PEDAGOGICAL NOTE on alternatives:
 * The modulo version is more concise but requires SMT to prove
 * `(x + 1) % 100 < 100` for all x in [0, 99]. The if-then-else
 * version is more explicit. Show both to students!
 *)

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: In clamp, how does F* know each branch satisfies the postcondition?
 * A1: F* performs control flow analysis. In each branch, it knows what
 *     conditions are true (e.g., "x < min" in branch 1) and uses this
 *     to prove the returned value satisfies the postcondition.
 *
 * Q2: Why do we need the precondition `max >= min`?
 * A2: Without it, branch 1 `return min` couldn't prove `min <= max`.
 *     The precondition establishes that the range [min, max] is valid.
 *
 * Q3: What happens if we remove the precondition?
 * A3: F* gives error: "Could not prove postcondition: min <= max"
 *     in branch 1. The SMT solver can't prove this without the assumption.
 *)

(******************************************************************************)
(** Exercise 1.3: ETL Pipeline with Verified Transformations                 *)
(******************************************************************************)

(**
 * PEDAGOGICAL NOTE:
 * This is the most complex Week 1 exercise, combining multiple concepts:
 * - Option types for error handling
 * - List processing with map/filter
 * - Refinement types (nat) in composed pipeline
 * - Monadic composition with >>=
 *
 * Many students will struggle with this. Encourage them to:
 * 1. Implement each function independently first
 * 2. Test each function before composing
 * 3. Use helper functions to break down complexity
 *
 * Common issues:
 * - Forgetting to handle None cases in option processing
 * - Not understanding how >>= chains computations
 * - Confusion about when to use admit() vs implementing
 *)

(** Helper functions *)

// Simplified string split (normally would use FStar.String)
assume val split_string : char -> string -> list string

// Convert string to int
assume val string_to_int : string -> option int

// String trim
assume val string_trim : string -> string

// Parse single CSV line
let parse_line (line:string) : option (string * string) =
  match split_string ',' line with
  | [k; v] -> Some (string_trim k, string_trim v)
  | _ -> None

(** Solution: Part A - Parse CSV *)

// Helper: Parse all lines, collecting successes
let rec parse_all_lines (lines:list string) : option parsed_rows =
  match lines with
  | [] -> Some []
  | hd :: tl ->
    match parse_line hd with
    | None -> None  // One failure aborts the whole parse
    | Some row ->
      match parse_all_lines tl with
      | None -> None
      | Some rest -> Some (row :: rest)

let parse_csv (csv:raw_csv) : option parsed_rows =
  let lines = split_string '\n' csv in
  parse_all_lines lines

(**
 * ALTERNATIVE SOLUTION using List.fold_right:
 *)
let parse_csv_alt (csv:raw_csv) : option parsed_rows =
  let lines = split_string '\n' csv in
  FStar.List.Tot.fold_right
    (fun line acc ->
      match parse_line line, acc with
      | Some row, Some rows -> Some (row :: rows)
      | _, _ -> None)
    lines
    (Some [])

(** Solution: Part B - Validate rows *)

// Helper: Validate single row
let validate_row (key:string) (value_str:string) : option (string * nat) =
  match string_to_int value_str with
  | None -> None
  | Some n ->
    if n >= 0
    then Some (key, n)  // n has type nat because we checked n >= 0
    else None

// Validate all rows
let rec validate_all_rows (rows:parsed_rows) : option validated_data =
  match rows with
  | [] -> Some []
  | (key, value_str) :: tl ->
    match validate_row key value_str with
    | None -> None
    | Some validated_row ->
      match validate_all_rows tl with
      | None -> None
      | Some rest -> Some (validated_row :: rest)

let validate_rows (rows:parsed_rows) : option validated_data =
  validate_all_rows rows

(**
 * PEDAGOGICAL NOTE on validate_row:
 * The key insight is that F* infers `n : nat` in the then-branch
 * because we checked `n >= 0`. This is refinement type inference!
 *
 * Students might try:
 *   Some (key, (n <: nat))  // Explicit type ascription
 * This works but is unnecessary. F* infers it from control flow.
 *)

(** Solution: Part C - Convert to JSON *)

// Helper: Convert single row to JSON entry
let row_to_json_entry (key:string, value:nat) : string =
  "\"" ^ key ^ "\": " ^ (string_of_int value)

// Assume string functions (normally FStar.String)
assume val string_of_int : int -> string
assume val string_concat : string -> list string -> string

let rows_to_json (data:validated_data) : json_output =
  let entries = FStar.List.Tot.map row_to_json_entry data in
  "{" ^ (string_concat ", " entries) ^ "}"

(**
 * Example output:
 * [("temp", 25), ("humidity", 60)]
 * =>
 * "{\"temp\": 25, \"humidity\": 60}"
 *)

(** Solution: Part D - Compose pipeline *)

// Monadic bind (provided)
let (>>=) (m:option 'a) (f:'a -> option 'b) : option 'b =
  match m with
  | None -> None
  | Some x -> f x

// Full pipeline composition
let etl_pipeline (csv:raw_csv) : option json_output =
  parse_csv csv >>=
  validate_rows >>=
  (fun validated -> Some (rows_to_json validated))

(**
 * ALTERNATIVE (more explicit):
 *)
let etl_pipeline_explicit (csv:raw_csv) : option json_output =
  match parse_csv csv with
  | None -> None
  | Some parsed ->
    match validate_rows parsed with
    | None -> None
    | Some validated ->
      Some (rows_to_json validated)

(**
 * PEDAGOGICAL NOTE on composition styles:
 * - The >>= version is concise and functional
 * - The explicit version shows exactly what's happening
 * - Show both! Students coming from imperative backgrounds prefer explicit
 * - Students with Haskell background prefer >>=
 * - Both are correct; it's a matter of style
 *)

(** Test cases *)

let test_valid = "temperature,25\nhumidity,60\nage,30"
let result_valid = etl_pipeline test_valid
// Expected: Some "{\"temperature\": 25, \"humidity\": 60, \"age\": 30}"

let test_invalid = "temperature,25\nhumidity,-10"
let result_invalid = etl_pipeline test_invalid
// Expected: None (validation fails on -10)

(**
 * ANSWER KEY for reflection questions:
 *
 * Q1: Why is validate_rows return type `option validated_data`?
 * A1: Because validation can fail (e.g., non-numeric string, negative value).
 *     The option type represents this possibility: None = failure, Some = success.
 *
 * Q2: How does the type system ensure rows_to_json only receives validated data?
 * A2: The type signature `rows_to_json : validated_data -> json_output` requires
 *     the input to be `validated_data`, which is `list (string * nat)`. The
 *     refinement type `nat` guarantees all values are >= 0. The pipeline
 *     composition with >>= ensures rows_to_json is only called if validate_rows
 *     succeeds (returns Some).
 *
 * Q3: What happens if parse_csv succeeds but validate_rows fails?
 * A3: Trace:
 *     1. parse_csv csv returns Some parsed_rows
 *     2. >>= unwraps and calls validate_rows parsed_rows
 *     3. validate_rows returns None (validation failure)
 *     4. >>= sees None and short-circuits, returning None
 *     5. Final None never reaches rows_to_json
 *     This is the power of monadic composition - automatic error propagation!
 *
 * Q4: (Challenge) Multiple data types while maintaining type safety?
 * A4: Use variant types (discriminated unions):
 *
 *     type value =
 *       | VNat of nat
 *       | VString of string
 *       | VFloat of float
 *
 *     type validated_data = list (string * value)
 *
 *     Then validate_rows would parse value strings and infer the appropriate
 *     variant constructor. F* would track which variant each value is!
 *)

(******************************************************************************)
(** Pedagogical Meta-Notes for Instructors                                   *)
(******************************************************************************)

(**
 * GRADING RUBRIC GUIDANCE:
 *
 * Exercise 1.1: (10 points)
 * - Correct nonzero definition: 5 points
 * - Correct safe_divide implementation: 3 points
 * - Thoughtful reflection answers: 2 points
 *
 * Exercise 1.2: (20 points)
 * - clamp function: 8 points (this is the hard one!)
 *   - Correct signature: 2 points
 *   - Correct implementation: 5 points
 *   - Understanding why it works (reflection): 1 point
 * - positive type: 3 points
 * - bounded100 and increment_wrap: 5 points
 * - Reflection answers: 4 points
 *
 * Exercise 1.3: (30 points)
 * - parse_csv: 7 points
 * - validate_rows: 10 points (most complex)
 * - rows_to_json: 5 points
 * - etl_pipeline composition: 5 points
 * - Reflection answers: 3 points
 *
 * PARTIAL CREDIT:
 * - Give credit for correct approach even if implementation incomplete
 * - admit() with good comment explaining approach: 50% credit
 * - Type errors but correct logic: 70% credit
 * - Reward creative solutions even if not identical to this key
 *
 * COMMON EXCELLENT STUDENT SOLUTIONS:
 * - Using assert to help SMT in clamp (unnecessary but shows understanding)
 * - Writing extensive helper functions in 1.3 (good decomposition!)
 * - Alternative implementations using fold, recursion, etc.
 *
 * RED FLAGS (possible plagiarism or misunderstanding):
 * - Solution appears suddenly without git history
 * - Student can't explain their code in office hours
 * - Identical to another student's solution (investigate)
 *)

(**
 * EXTENSION EXERCISES (for advanced students who finish early):
 *
 * 1. Extend safe_divide to return option int instead of requiring nonzero,
 *    but still use refinement types internally
 *
 * 2. Implement a version of clamp that returns a proof that the result
 *    is in bounds (dependent pair)
 *
 * 3. Extend ETL pipeline to support CSV with headers
 *
 * 4. Add a sanitization step that removes rows with suspicious values
 *
 * 5. Implement JSON parsing in the reverse direction (JSON -> validated_data)
 *)
