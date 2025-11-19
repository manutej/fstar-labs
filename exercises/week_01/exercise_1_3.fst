module Exercise1_3

open FStar.List.Tot

(**
 * Exercise 1.3: ETL Pipeline with Verified Transformations
 *
 * Learning Objectives:
 * - Compose verified functions into pipelines
 * - Use option types for error handling
 * - Apply refinement types in realistic data processing scenario
 *
 * Scenario: Build an Extract-Transform-Load (ETL) pipeline
 * that processes CSV data with validation
 *)

(** Type definitions for pipeline stages *)

type raw_csv = string
type parsed_rows = list (string * string)  // Key-value pairs
type validated_data = list (string * nat)  // Values must be natural numbers!
type json_output = string

(** Helper functions (assumed for this exercise) *)

// String operations (not in F* standard library)
assume val split_char : char -> string -> list string
assume val string_trim : string -> string

// Parse a single line "key,value" into (key, value)
let parse_line (line:string) : option (string * string) =
  // Simplified implementation
  match split_char ',' line with
  | [k; v] -> Some (string_trim k, string_trim v)
  | _ -> None

// Convert string to int (built-in would be int_of_string)
assume val string_to_int : string -> option int

(** TODO: Implement these functions *)

// Part A: Parse CSV into rows
// Split by newlines and parse each line
let parse_csv (csv:raw_csv) : option parsed_rows =
  (* YOUR CODE HERE *)
  (*
   * Hints:
   * - Use String.split ['\n'] csv to get lines
   * - Use List.map with parse_line
   * - Handle None cases appropriately
   *
   * You can use helper functions:
   * - List.map : ('a -> 'b) -> list 'a -> list 'b
   * - List.filter : ('a -> bool) -> list 'a -> list 'a
   *)
  admit() // Remove this and implement!

// Part B: Validate rows
// Convert string values to nat, reject invalid data
let validate_rows (rows:parsed_rows) : option validated_data =
  (* YOUR CODE HERE *)
  (*
   * Hints:
   * - For each (key, value_str), convert value_str to int
   * - Check if int >= 0 (i.e., it's a nat)
   * - If any conversion fails or value is negative, return None
   * - Otherwise, return Some of the validated list
   *
   * Consider using a helper function:
   * let validate_row (key, value_str) : option (string * nat) = ...
   *)
  admit() // Remove this and implement!

// Part C: Convert to JSON (simplified)
// Convert list of (key, nat) pairs to JSON string
let rows_to_json (data:validated_data) : json_output =
  (* YOUR CODE HERE *)
  (*
   * Simplified JSON format:
   * [("temp", 25), ("humidity", 60)] =>
   * "{\"temp\": 25, \"humidity\": 60}"
   *
   * Hint: Use String.concat and List.map
   *)
  admit() // Remove this and implement!

(** Part D: Compose the pipeline *)

// Monadic bind for option (provided)
let (>>=) (m:option 'a) (f:'a -> option 'b) : option 'b =
  match m with
  | None -> None
  | Some x -> f x

// TODO: Implement full pipeline using composition
let etl_pipeline (csv:raw_csv) : option json_output =
  (* YOUR CODE HERE *)
  (*
   * Hint: Use >>= to chain:
   * parse_csv csv >>= validate_rows >>= ...
   *)
  admit() // Remove this and implement!

(** Test cases *)

let test_valid_input =
  "temperature,25\nhumidity,60\nage,30"

let test_result = etl_pipeline test_valid_input
// Expected: Some "{\"temperature\": 25, \"humidity\": 60, \"age\": 30}"

let test_invalid_input =
  "temperature,25\nhumidity,-10"  // Negative value!

let test_fail = etl_pipeline test_invalid_input
// Expected: None (validation should fail)

(**
 * Reflection Questions:
 *
 * Q1: Why is the return type of validate_rows `option validated_data`
 *     instead of just `validated_data`?
 * A1: YOUR ANSWER HERE
 *
 * Q2: How does the type system ensure that rows_to_json only receives
 *     validated data (i.e., all values are natural numbers)?
 * A2: YOUR ANSWER HERE
 *
 * Q3: What happens if parse_csv succeeds but validate_rows fails?
 *     Trace through the execution of etl_pipeline.
 * A3: YOUR ANSWER HERE
 *
 * Q4: (Challenge) How would you extend this to support multiple data types
 *     (strings, ints, floats) while maintaining type safety?
 * A4: YOUR ANSWER HERE
 *)
