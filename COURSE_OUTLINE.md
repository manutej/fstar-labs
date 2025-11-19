# Formal Verification with F*: Complete Course Outline
## From Novice to Expert in Proof-Oriented Programming

**Course Duration**: 12 weeks (36 lectures × 90 minutes)
**Target Audience**: Programmers with basic functional programming knowledge
**Prerequisites**: Python/OCaml/F# experience, basic logic, willingness to learn
**Course Philosophy**: Progressive mastery through categorical levels (L1→L7)

---

## Course Architecture

### Level Mapping (Aligned with F* Labs Framework)

| Week | Level | Theme | Core Concepts |
|------|-------|-------|---------------|
| 1-2 | **L1: Novice** | Type Safety Foundations | Refinement types, SMT solving, bounds checking |
| 3-4 | **L2: Apprentice** | Inductive Reasoning | Lemmas, structural induction, recursive proofs |
| 5-6 | **L3: Journeyman** | Dependent Types | Indexed families, type-level computation, GADTs |
| 7-8 | **L4: Expert** | Effect Systems | Stateful verification, heap reasoning, monadic effects |
| 9-10 | **L5: Master** | Metaprogramming | Tactics, proof automation, custom decision procedures |
| 11 | **L6: Grandmaster** | Security Properties | Non-interference, information flow, constant-time |
| 12 | **L7: Genius** | Research Frontiers | Novel architectures, publication-quality proofs |

---

## Weekly Breakdown

### **Week 1: Introduction to F* and Type Safety (L1 Start)**

#### Day 1 (Monday): What is Formal Verification?
- **Learning Objectives**:
  1. Explain the difference between testing and verification
  2. Identify when formal methods are cost-effective
  3. Install F* toolchain and verify first program
  4. Understand the Curry-Howard correspondence basics

- **Lecture Topics** (90 min):
  - [0-15 min] Course overview and motivation
  - [15-30 min] The verification spectrum (types → tests → proofs)
  - [30-60 min] F* installation and "Hello, Verification!"
  - [60-75 min] First refinement type: `nat` (natural numbers)
  - [75-90 min] Exercise 1.1: Safe division function

- **Exercises**:
  - Ex 1.1: Implement `safe_divide: int -> x:int{x <> 0} -> int`
  - Ex 1.2: Create `positive` refinement type
  - Homework: Read SKILL.md sections 1-2

#### Day 2 (Tuesday): Refinement Types Deep Dive
- **Learning Objectives**:
  1. Define custom refinement types using `{x:t | p}`
  2. Leverage SMT solver for automatic proof search
  3. Understand when SMT fails and manual proofs needed
  4. Debug SMT failures using `--debug` flags

- **Lecture Topics** (90 min):
  - [0-20 min] Review Day 1, common installation issues
  - [20-40 min] Refinement type syntax and semantics
  - [40-65 min] Live coding: Array bounds checking
  - [65-80 min] SMT solver internals (Z3 primer)
  - [80-90 min] Exercise 1.2: Validated input parsing

- **Exercises**:
  - Ex 1.2: Parse user input with range validation
  - Ex 1.3: Implement `clamp` function with refinement proof
  - Homework: Mini-project planning (safe calculator)

#### Day 3 (Wednesday): Composing Verified Functions
- **Learning Objectives**:
  1. Chain refinement types through function composition
  2. Understand subtyping in refinement hierarchies
  3. Use `assert` and `assume` strategically
  4. Read and interpret F* error messages

- **Lecture Topics** (90 min):
  - [0-15 min] Debrief homework struggles
  - [15-35 min] Function composition with refined types
  - [35-60 min] Subtyping: when `{x >= 0}` implies `{x > -1}`
  - [60-80 min] Exercise 1.3: ETL pipeline (F* version)
  - [80-90 min] Mini-project kickoff: Safe calculator

- **Exercises**:
  - Ex 1.3: Build `parse >> validate >> compute >> format` pipeline
  - Mini-Project: Calculator with division-by-zero safety
  - Homework: Complete calculator (due Friday)

---

### **Week 2: Lists, Options, and Total Functions (L1 Complete)**

#### Day 4 (Monday): Total Functions and Termination
- **Learning Objectives**:
  1. Explain why F* requires proofs of termination
  2. Use `decreases` clauses for recursive functions
  3. Identify non-structural recursion patterns
  4. Convert partial functions to total functions

- **Lecture Topics** (90 min):
  - [0-15 min] Review Week 1 mini-projects (show & tell)
  - [15-40 min] The halting problem and totality
  - [40-65 min] Decreasing metrics for recursion
  - [65-85 min] Exercise 2.1: Verified `fibonacci`
  - [85-90 min] Preview: Why totality matters for security

- **Exercises**:
  - Ex 2.1: Fibonacci with decreases proof
  - Ex 2.2: McCarthy 91 function verification
  - Homework: Read about Ackermann function

#### Day 5 (Tuesday): Lists and Structural Induction (L2 Start)
- **Learning Objectives**:
  1. Define inductive data types (lists, trees)
  2. Write structurally recursive functions
  3. State and prove simple lemmas about lists
  4. Use `Tot` effect for pure computations

- **Lecture Topics** (90 min):
  - [0-10 min] Termination quiz (5 questions)
  - [10-35 min] List type definition and recursion patterns
  - [35-60 min] Live coding: `append`, `reverse`, `length`
  - [60-80 min] First lemma: `length (append xs ys) == length xs + length ys`
  - [80-90 min] Exercise 2.3: Prove `reverse (reverse xs) == xs`

- **Exercises**:
  - Ex 2.3: Reverse involution proof
  - Ex 2.4: `map` preserves length
  - Homework: Study EXAMPLES.md list examples

#### Day 6 (Wednesday): Lemmas and Proof Engineering
- **Learning Objectives**:
  1. Structure proofs using helper lemmas
  2. Apply induction hypotheses correctly
  3. Debug proof failures with `admit()`
  4. Understand SMT vs. manual proof trade-offs

- **Lecture Topics** (90 min):
  - [0-20 min] Common proof mistakes from homework
  - [20-45 min] Proof decomposition strategies
  - [45-70 min] Case analysis and pattern matching in proofs
  - [70-85 min] Exercise 2.5: `flatten` associativity
  - [85-90 min] Week 2 mini-project: Verified merge sort

- **Exercises**:
  - Ex 2.5: Prove `flatten (append xss yss) == append (flatten xss) (flatten yss)`
  - Mini-Project: Merge sort with correctness proof (due next Monday)
  - Homework: Sketch merge sort proof strategy

---

### **Week 3: Dependent Types Introduction (L3 Start)**

#### Day 7 (Monday): Indexed Types and Length-Indexed Vectors
- **Learning Objectives**:
  1. Distinguish refinement types from dependent types
  2. Define vector type `vec (n:nat)` with length index
  3. Write dependently-typed `head` and `tail` functions
  4. Understand type-level computation

- **Lecture Topics** (90 min):
  - [0-15 min] Merge sort project showcase (3 students present)
  - [15-35 min] Refinement vs. Dependent: What's the difference?
  - [35-65 min] Vector implementation and safe indexing
  - [65-85 min] Exercise 3.1: `zip` for equal-length vectors
  - [85-90 min] Discussion: When to use dependent types?

#### Day 8 (Tuesday): Type-Level Arithmetic
- **Learning Objectives**:
  1. Perform computation at the type level
  2. Prove type equality with lemmas
  3. Use `append` to combine vectors with length tracking
  4. Debug type unification failures

- **Lecture Topics** (90 min):
  - [0-15 min] Vector quiz and common errors
  - [15-40 min] Type arithmetic: `n + m`, `n * m` in types
  - [40-70 min] Live coding: Matrix type `matrix n m`
  - [70-85 min] Exercise 3.2: Matrix transpose
  - [85-90 min] Preview: Dependent pairs (Σ-types)

#### Day 9 (Wednesday): Dependent Pairs and Existentials
- **Learning Objectives**:
  1. Use `dtuple2` for Σ-types (dependent pairs)
  2. Encode existential types with dependent pairs
  3. Extract witnesses from proofs
  4. Apply to real-world parsing problems

- **Lecture Topics** (90 min):
  - [0-15 min] Review: Universal (Π) vs. Existential (Σ)
  - [15-40 min] Dependent pair syntax and examples
  - [40-70 min] Exercise 3.3: Find + prove element in list
  - [70-85 min] Mini-project: Verified binary search
  - [85-90 min] Project guidelines and rubric

---

### **Week 4: Advanced Induction (L2 Complete, L3 Continue)**

#### Day 10 (Monday): Well-Founded Recursion
- **Learning Objectives**:
  1. Define custom well-founded relations
  2. Prove recursion terminates via accessibility predicates
  3. Implement division using subtraction (Euclidean algorithm)
  4. Handle complex decreases clauses

- **Lecture Topics** (90 min):
  - [0-20 min] Binary search projects: common issues
  - [20-45 min] When structural recursion isn't enough
  - [45-75 min] Well-founded induction theory
  - [75-85 min] Exercise 4.1: GCD implementation
  - [85-90 min] Homework: Collatz conjecture (open problem!)

#### Day 11 (Tuesday): Mutual Recursion and Nested Induction
- **Learning Objectives**:
  1. Define mutually recursive functions with `and`
  2. Handle nested data structures (trees of lists)
  3. Write mutually recursive proofs
  4. Understand F*'s positivity checker

- **Lecture Topics** (90 min):
  - [0-15 min] Review well-founded recursion struggles
  - [15-40 min] Mutual recursion syntax and semantics
  - [40-65 min] Live coding: Expression evaluator (AST)
  - [65-85 min] Exercise 4.2: Prove evaluator deterministic
  - [85-90 min] Discussion: Compilers and interpreters

#### Day 12 (Wednesday): Midterm Review and Practice Exam
- **Learning Objectives**:
  1. Synthesize L1-L2 concepts (refinement + induction)
  2. Prepare for midterm exam (Friday)
  3. Practice time management for proofs
  4. Review common mistakes

- **Lecture Topics** (90 min):
  - [0-30 min] Midterm format and expectations
  - [30-60 min] Practice problems (timed, 30 min)
  - [60-80 min] Solutions walkthrough
  - [80-90 min] Q&A and office hours signup

- **Midterm Coverage**: Weeks 1-4 (L1-L2 complete, L3 intro)

---

### **Week 5: Effect Systems Introduction (L4 Start)**

#### Day 13 (Monday): Pure vs. Stateful Computation
- **Learning Objectives**:
  1. Distinguish `Tot`, `GTot`, `Lemma` effects
  2. Understand why effects matter for verification
  3. Introduce `ST` (state) effect for mutation
  4. Read effect signatures in F* code

- **Lecture Topics** (90 min):
  - [0-15 min] Midterm debrief (anonymized stats)
  - [15-40 min] Effect system motivation: controlling side effects
  - [40-65 min] The effect ladder: Tot < ST < All
  - [65-85 min] Exercise 5.1: Implement stateful counter
  - [85-90 min] Preview: Heap reasoning next week

#### Day 14 (Tuesday): Mutable References and Heap
- **Learning Objectives**:
  1. Allocate references with `alloc`
  2. Read/write with `!` and `:=` operators
  3. Understand heap frames and separation
  4. Reason about aliasing

- **Lecture Topics** (90 min):
  - [0-15 min] Effect quiz (quick check)
  - [15-45 min] Reference types: `ref t` and heap model
  - [45-70 min] Live coding: Swap two references
  - [70-85 min] Exercise 5.2: Implement stack (push/pop)
  - [85-90 min] Common bug: Aliasing errors

#### Day 15 (Wednesday): Preconditions and Postconditions
- **Learning Objectives**:
  1. Write function specs with `requires` and `ensures`
  2. Use `modifies` clauses for frame conditions
  3. Prove stateful code correct
  4. Debug SMT timeouts in heap reasoning

- **Lecture Topics** (90 min):
  - [0-20 min] Stack implementation review
  - [20-50 min] Hoare logic basics (informal)
  - [50-75 min] Exercise 5.3: Verified in-place array reversal
  - [75-85 min] Mini-project: Verified hash table
  - [85-90 min] Project specification and rubric

---

### **Week 6: Advanced Effects (L4 Continue)**

#### Day 16 (Monday): Monadic Effects and Bind
- **Learning Objectives**:
  1. Understand effect monads (return, bind)
  2. Chain stateful computations with `let*`
  3. Prove monad laws for custom effects
  4. Compare F* effects to Haskell monads

- **Lecture Topics** (90 min):
  - [0-15 min] Hash table progress check-in
  - [15-40 min] Monads crash course (for non-Haskellers)
  - [40-70 min] F* effect encoding via `repr`
  - [70-85 min] Exercise 6.1: Define `Maybe` monad
  - [85-90 min] Discussion: Algebraic effects

#### Day 17 (Tuesday): Ghost Code and Specifications
- **Learning Objectives**:
  1. Use `Ghost` effect for proof-only code
  2. Write specifications without runtime cost
  3. Erase ghost code during extraction
  4. Understand computational irrelevance

- **Lecture Topics** (90 min):
  - [0-15 min] Monad quiz
  - [15-40 min] Ghost vs. concrete: The two-stage world
  - [40-65 min] Live coding: List with cached length (ghost field)
  - [65-85 min] Exercise 6.2: Verified quicksort with ghost pivot
  - [85-90 min] Extraction demo: Ghost code disappears

#### Day 18 (Wednesday): Exceptions and Divergence
- **Learning Objectives**:
  1. Handle `Exn` effect for exceptions
  2. Reason about divergence with `Dv` effect
  3. Use `All` for maximum expressiveness
  4. Trade-offs: Precision vs. convenience

- **Lecture Topics** (90 min):
  - [0-20 min] Review ghost code misconceptions
  - [20-45 min] Exception semantics in F*
  - [45-70 min] Exercise 6.3: Parser with error handling
  - [70-85 min] Divergence: When we can't prove termination
  - [85-90 min] Week 6 wrap-up: Effect hierarchy complete

---

### **Week 7: Tactics and Metaprogramming (L5 Start)**

#### Day 19 (Monday): Introduction to F* Tactics
- **Learning Objectives**:
  1. Invoke tactics with `by (tactic)`
  2. Use built-in tactics: `trivial`, `split`, `rewrite`
  3. Understand proof goal view
  4. Debug tactic failures

- **Lecture Topics** (90 min):
  - [0-15 min] Motivation: When SMT isn't enough
  - [15-40 min] Tactic mode vs. SMT mode
  - [40-70 min] Live coding: Manual proof with tactics
  - [70-85 min] Exercise 7.1: Prove commutativity with tactics
  - [85-90 min] Tactic reference sheet (cheat sheet)

#### Day 20 (Tuesday): Writing Custom Tactics
- **Learning Objectives**:
  1. Define tactics using `T` monad
  2. Inspect proof state with `cur_goal()`
  3. Apply transformations programmatically
  4. Build reusable proof automation

- **Lecture Topics** (90 min):
  - [0-15 min] Review built-in tactics
  - [15-45 min] The `T` monad and proof state API
  - [45-70 min] Exercise 7.2: Write `auto_arith` tactic
  - [70-85 min] Case study: Ring solver tactic
  - [85-90 min] Mini-project: Custom decision procedure

#### Day 21 (Wednesday): Metaprogramming with Reflection
- **Learning Objectives**:
  1. Reflect F* terms to syntax trees
  2. Analyze and transform code programmatically
  3. Generate boilerplate with meta-programs
  4. Understand staging: compile-time vs. runtime

- **Lecture Topics** (90 min):
  - [0-15 min] Metaprogramming quiz
  - [15-45 min] Reflection API: `pack_term`, `inspect`
  - [45-70 min] Exercise 7.3: Generate equality boilerplate
  - [70-85 min] Live demo: Deriving `show` instances
  - [85-90 min] Discussion: Metaprogramming ethics (maintainability)

---

### **Week 8: Cryptography and Constant-Time (L6 Start)**

#### Day 22 (Monday): Introduction to Verified Cryptography
- **Learning Objectives**:
  1. Understand security properties (correctness, secrecy, authenticity)
  2. Model attackers formally
  3. Use F* for cryptographic implementations
  4. Study HACL* case study

- **Lecture Topics** (90 min):
  - [0-20 min] Why cryptography needs formal methods
  - [20-45 min] Threat models: Dolev-Yao, timing attacks
  - [45-70 min] HACL* tour: Poly1305, ChaCha20
  - [70-85 min] Exercise 8.1: Implement XOR cipher (toy)
  - [85-90 min] Preview: Constant-time programming

#### Day 23 (Tuesday): Constant-Time Programming
- **Learning Objectives**:
  1. Explain timing side-channels
  2. Write constant-time code with `secret` modality
  3. Prove absence of timing leaks
  4. Use `Low*` subset for C extraction

- **Lecture Topics** (90 min):
  - [0-15 min] Side-channel attack videos (real exploits)
  - [15-40 min] Constant-time invariants
  - [40-65 min] Live coding: Constant-time compare
  - [65-85 min] Exercise 8.2: Constant-time max function
  - [85-90 min] Common pitfalls: Branching on secrets

#### Day 24 (Wednesday): Information Flow and Non-Interference
- **Learning Objectives**:
  1. Define non-interference formally
  2. Use labels (Low/High) for information flow
  3. Prove programs don't leak secrets
  4. Apply to real-world: password checking

- **Lecture Topics** (90 min):
  - [0-20 min] Constant-time code review
  - [20-50 min] Information flow type systems
  - [50-75 min] Exercise 8.3: Prove password checker non-interference
  - [75-85 min] Mini-project: Verified AES (simplified)
  - [85-90 min] Project spec: Correctness + constant-time

---

### **Week 9: Concurrency and State Machines (L5-L6 Continue)**

#### Day 25 (Monday): Concurrent Separation Logic
- **Learning Objectives**:
  1. Reason about concurrent programs
  2. Use separation logic (`*` connective)
  3. Prove race-freedom with disjoint footprints
  4. Introduce atomic references

- **Lecture Topics** (90 min):
  - [0-15 min] AES project progress check
  - [15-40 min] Concurrency bugs: data races, deadlocks
  - [40-70 min] Separation logic primer
  - [70-85 min] Exercise 9.1: Parallel map with disjoint regions
  - [85-90 min] Reading: Steel tutorial

#### Day 26 (Tuesday): State Machines and Protocols
- **Learning Objectives**:
  1. Model protocols as state machines
  2. Verify state transitions preserve invariants
  3. Use F* for protocol verification
  4. Case study: Two-phase commit

- **Lecture Topics** (90 min):
  - [0-15 min] Separation logic quiz
  - [15-45 min] State machine formalism
  - [45-70 min] Live coding: Mutex state machine
  - [70-85 min] Exercise 9.2: Verify read-write lock
  - [85-90 min] Protocol verification in the wild

#### Day 27 (Wednesday): Advanced Concurrency (Optional Depth)
- **Learning Objectives**:
  1. Explore Steel framework for concurrent verification
  2. Understand pulse (linear types)
  3. Compare F* to other verifiers (Iris, VST)
  4. Guest lecture or recorded talk

- **Lecture Topics** (90 min):
  - [0-30 min] Guest speaker: F* team member (or recorded talk)
  - [30-60 min] Q&A and discussion
  - [60-85 min] Exercise 9.3: Explore Steel examples
  - [85-90 min] Optional reading: Advanced concurrency papers

---

### **Week 10: Verified Compilers and Interpreters (L6 Continue)**

#### Day 28 (Monday): Language Semantics
- **Learning Objectives**:
  1. Define abstract syntax trees (ASTs)
  2. Write small-step operational semantics
  3. Prove semantic properties (determinism, progress)
  4. Introduction to compiler verification

- **Lecture Topics** (90 min):
  - [0-15 min] Motivation: CompCert case study
  - [15-40 min] Defining a toy imperative language
  - [40-70 min] Big-step vs. small-step semantics
  - [70-85 min] Exercise 10.1: Prove `eval` deterministic
  - [85-90 min] Preview: Type soundness theorem

#### Day 29 (Tuesday): Type Soundness Proofs
- **Learning Objectives**:
  1. State progress and preservation theorems
  2. Prove type soundness ("well-typed programs don't go wrong")
  3. Handle typing contexts and substitution lemmas
  4. Understand mechanized metatheory

- **Lecture Topics** (90 min):
  - [0-15 min] Semantics quiz
  - [15-45 min] The soundness proof roadmap
  - [45-70 min] Live coding: Simply-typed lambda calculus
  - [70-85 min] Exercise 10.2: Prove progress for STLC
  - [85-90 min] Challenges: Dependent types soundness

#### Day 30 (Wednesday): Compiler Correctness
- **Learning Objectives**:
  1. Define compilation as a transformation
  2. State correctness: behavior preservation
  3. Prove a simple compiler correct
  4. Understand verified extraction

- **Lecture Topics** (90 min):
  - [0-20 min] Type soundness review
  - [20-50 min] Compiler correctness formalization
  - [50-75 min] Exercise 10.3: Expression compiler to stack machine
  - [75-85 min] Mini-project: Verified calculator compiler
  - [85-90 min] Project: Compiler from arithmetic to assembly

---

### **Week 11: Advanced Topics and Specialization (L7 Start)**

#### Day 31 (Monday): Choose Your Adventure
Students pick ONE track for deep dive:

**Track A: Advanced Cryptography**
- Zero-knowledge proofs in F*
- Verified key exchange protocols
- Post-quantum cryptography

**Track B: Systems Verification**
- Verified operating system components
- File system verification
- Network stack verification

**Track C: Programming Languages**
- Advanced type systems (linear, session)
- Compiler optimizations
- Verified program synthesis

**Track D: Formal Methods Research**
- Read cutting-edge papers
- Reproduce proofs from literature
- Propose mini-research project

- **Lecture Topics** (90 min):
  - [0-30 min] Track presentations (15 min each × 2 tracks)
  - [30-45 min] Track selection and team formation
  - [45-90 min] Track-specific kickoff (split into rooms)

#### Day 32 (Tuesday): Track-Specific Deep Dive
- Per-track content (see instructor guide for details)
- Advanced exercises specific to chosen track
- Capstone project planning begins

#### Day 33 (Wednesday): Research Frontiers Panel
- **Learning Objectives**:
  1. Understand current research in formal verification
  2. Identify open problems
  3. Evaluate career paths in formal methods
  4. Network with researchers

- **Format** (90 min):
  - [0-60 min] Panel: 3-4 researchers/practitioners
  - [60-85 min] Q&A
  - [85-90 min] Capstone project proposal guidelines

---

### **Week 12: Capstone Projects and Presentations (L7 Demonstration)**

#### Day 34 (Monday): Capstone Work Time
- In-class work time with instructor available
- Peer review sessions
- Technical writing workshop (proof presentation)

#### Day 35 (Tuesday): Capstone Presentations (Day 1)
- 15 minutes per student/team
- 10 min presentation + 5 min Q&A
- Rubric: Correctness, novelty, presentation quality

#### Day 36 (Wednesday): Capstone Presentations (Day 2) + Course Wrap-Up
- Remaining presentations
- Course retrospective
- Where to go next: resources, communities, conferences
- Final exam preview (optional, if required by institution)

---

## Assessment Summary

### Formative Assessments (Ongoing)
- **Daily Quizzes**: 5-10 min, 3-5 questions (Weeks 1-10)
- **Exercises**: 3-5 per week, auto-graded where possible
- **Code Reviews**: Peer review every Week 3, 6, 9

### Summative Assessments
- **Mini-Projects**: End of Weeks 1, 3, 6, 8, 10 (5 total)
- **Midterm Exam**: End of Week 4 (covers L1-L2)
- **Final Exam**: Week 12 (optional, comprehensive)
- **Capstone Project**: Weeks 11-12 (major assessment)

### Diagnostic Assessments (Week 0, Pre-Course)
- Python/OCaml proficiency check
- Logic and proof basics
- Installation troubleshooting survey

### Grading Weights (Suggested)
- Exercises: 20%
- Mini-Projects: 25%
- Midterm: 15%
- Capstone: 30%
- Participation/Quizzes: 10%

---

## Learning Outcomes

By the end of this course, students will be able to:

### L1 (Novice) - Achieved by Week 2
✅ Define refinement types for input validation
✅ Leverage SMT solvers for automatic proofs
✅ Write total functions with termination proofs

### L2 (Apprentice) - Achieved by Week 4
✅ Prove properties of recursive data structures
✅ Apply structural induction to list and tree algorithms
✅ Debug proof failures and repair lemmas

### L3 (Journeyman) - Achieved by Week 6
✅ Use dependent types for rich specifications
✅ Implement length-indexed vectors and matrices
✅ Reason about type-level computation

### L4 (Expert) - Achieved by Week 8
✅ Verify stateful programs with heap reasoning
✅ Use effect systems to control side effects
✅ Prove correctness of imperative algorithms

### L5 (Master) - Achieved by Week 10
✅ Write custom tactics for proof automation
✅ Use metaprogramming to generate verified code
✅ Build domain-specific verification tools

### L6 (Grandmaster) - Achieved by Week 11
✅ Verify cryptographic implementations
✅ Prove information flow security properties
✅ Reason about concurrent programs

### L7 (Genius) - Demonstrated in Week 12
✅ Design novel verification architectures
✅ Contribute to formal methods research
✅ Communicate proofs to technical audiences

---

## Instructor Resources

See `instructor_guide/` for:
- Weekly teaching notes with timing breakdowns
- Solutions to all exercises (with pedagogical comments)
- Grading rubrics for all assessments
- Lecture slides (Reveal.js format)
- Auto-grading scripts (pytest-based)
- Troubleshooting guide for common issues
- Assessment calibration guidelines

---

## Prerequisites and Preparation

### Required Background
- **Programming**: Proficient in at least one functional language (OCaml, Haskell, F#, or ML)
- **Logic**: Basic propositional and predicate logic
- **Mathematics**: Comfortable with mathematical notation and proofs
- **Tools**: Command-line proficiency, text editor/IDE setup

### Recommended (Not Required)
- Exposure to type theory or category theory
- Prior verification experience (Coq, Isabelle, Dafny)
- Cryptography or security background

### Pre-Course Setup (Week 0)
1. Install F* toolchain (see installation guide)
2. Set up editor (VS Code with F* extension recommended)
3. Complete diagnostic assessment
4. Join course forum/Slack

---

## Course Materials

### Required Textbook
- **F* Tutorial**: https://fstar-lang.org/tutorial/ (free, online)

### Supplementary Resources
- This repository: `/skill/SKILL.md`, `EXAMPLES.md`
- HACL* case studies: https://github.com/hacl-star/hacl-star
- Academic papers (provided weekly)

### Software Requirements
- F* compiler (latest stable release)
- Z3 SMT solver (version 4.8.5+)
- OCaml toolchain (for extraction)
- Git (for assignments submission)

---

## Pedagogical Philosophy

This course follows these principles:

1. **Progressive Mastery**: Build from concrete (refinement types) to abstract (metaprogramming)
2. **Example-Driven**: Every concept introduced with runnable code
3. **Fail Early, Fail Often**: Deliberate error introduction to build debugging skills
4. **Real-World Relevance**: Case studies from industry (HACL*, EverParse)
5. **Active Learning**: 60% of class time spent coding/proving
6. **Peer Learning**: Regular code reviews and pair programming
7. **Growth Mindset**: Proofs are hard; struggle is expected and valued

---

## Adaptations for Different Contexts

### Semester (15 weeks)
- Add Week 0 for deeper prerequisites review
- Add Week 13 for buffer/review
- More time for capstone projects

### Quarter (10 weeks)
- Compress Weeks 1-2 into one week
- Skip Week 9 (concurrency) or make optional
- Shorter capstone (10 hours instead of 20)

### Self-Paced / MOOC
- Add video lectures for each section
- Auto-grading for all exercises
- Optional peer review via forums
- Capstone as optional certification project

### Workshop (2-3 days)
- Focus on L1-L2 only (Weeks 1-2 content)
- Hands-on emphasis, minimal theory
- Take-home reading for deeper concepts

---

## Next Steps

This outline is the foundation. Next, we build:

1. **Detailed lesson plans** for each day (see `instructor_guide/week_XX_teaching_notes.md`)
2. **All exercises and solutions** (see `exercises/` and `instructor_guide/solutions/`)
3. **Assessment materials** (quizzes, exams, rubrics)
4. **Lecture slides** (markdown format)
5. **Auto-grading infrastructure** (pytest + F* testing)

**Ready to dive into Week 1 detailed content? Let's build!** 🚀
