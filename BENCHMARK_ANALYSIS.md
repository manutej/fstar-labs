# F* Labs Benchmark Analysis vs. Industry-Standard Formal Verification Courses

**Analysis Date**: 2025-11-19
**F* Labs Status**: Weeks 1-2 implemented (of 12-week curriculum)
**Comparison Scope**: Pedagogical effectiveness, topic coverage, difficulty, outcomes

---

## Executive Summary

**BRUTAL HONESTY VERDICT**: F* Labs is **ambitious but currently incomplete**. Compared to established courses, we show promise in practical application and modern tooling, but lack the battle-tested pedagogical refinement and comprehensive exercise libraries of Software Foundations. We're competitive in scope but untested in execution.

### Quick Comparison Table

| Aspect | Software Foundations | CMU 15-414 | MIT 6.820 | F* Official Tutorial | F* Labs | Gap Analysis |
|--------|---------------------|------------|-----------|---------------------|---------|--------------|
| **Duration** | 14-16 weeks | 15 weeks | 13 weeks | Self-paced | 12 weeks | ✓ Competitive |
| **Lecture Hours/Week** | ~3 hours | ~3 hours | ~3 hours | N/A | **4.5 hours** | ⚠️ Too much? |
| **Student Hours/Week** | 10-15 hours | 8-12 hours | 12-15 hours | Variable | **Unknown** | ❌ Not specified |
| **Total Exercises** | 100+ across vols | ~30-40 | 6 problem sets | 50+ | **~40 planned** | ⚠️ Lower quantity |
| **Tool** | Coq | Why3, SAT/SMT | Coq | F* | F* | ✓ Modern choice |
| **Proof Assistant** | Interactive | Automated | Both | Both | Both | ✓ Balanced |
| **Target Level** | Advanced UG-PhD | Advanced UG | Graduate | Practitioners | Advanced UG | ✓ Appropriate |
| **Industry Adoption** | Very High | Medium | Medium | Growing | Unknown | ❌ Unproven |
| **Material Quality** | Battle-tested | Established | Established | Official | **Untested** | ❌ Major risk |

---

## 1. Topic Coverage Comparison

### Software Foundations (Volumes 1-3)

**Volume 1: Logical Foundations (~8 weeks)**
- Basics: Functional programming in Coq
- Induction: Proof by induction
- Lists: Working with structured data
- Poly: Polymorphism and higher-order functions
- Tactics: More basic tactics
- Logic: Logic in Coq
- IndProp: Inductively defined propositions
- Maps: Total and partial maps
- ProofObjects: The Curry-Howard correspondence
- IndPrinciples: Induction principles

**Volume 2: Programming Language Foundations (~6 weeks)**
- IMP: Simple imperative programs
- Operational semantics
- Hoare logic
- Type systems
- Type soundness (progress + preservation)

**Volume 3: Verified Functional Algorithms**
- Extraction and runtime analysis
- Verified data structures
- Red-black trees
- ADTs with proofs

**TOTAL DEPTH**: 3 volumes, ~30 chapters, covering foundations → PLT → algorithms

### CMU 15-414 Bug Catching (15 weeks)

**Core Topics**:
1. Propositional logic and SAT solving (~2 weeks)
2. SAT solvers: DPLL algorithm implementation (~2 weeks)
3. Binary Decision Diagrams (BDDs) (~1 week)
4. Model checking: CTL, LTL (~2 weeks)
5. SMT (Satisfiability Modulo Theories) (~2 weeks)
6. Program verification with Why3 (~3 weeks)
7. Symbolic execution (~1 week)
8. Abstract interpretation (~2 weeks)

**Major Projects**:
- Implement SAT solver (verified)
- Fault-tolerant protocol verification
- Mini-project 1: Verification with Why3
- Mini-project 2: Advanced verification

**TOTAL DEPTH**: Tool-focused, 8 major topics, 2 substantial projects

### MIT 6.820 Fundamentals of Program Analysis (13 weeks)

**Units**:
1. Functional programming & operational semantics (~2 weeks)
2. Type theory (~3 weeks)
3. Types for imperative programs (~2 weeks)
4. Axiomatic semantics (Hoare logic) (~2 weeks)
5. Abstract interpretation (~2 weeks)
6. Model checking and synthesis (~2 weeks)

**Assignments**: 6 problem sets (mix of theory + Coq implementation)

**TOTAL DEPTH**: Broad survey, heavy on theory, Coq for proofs

### F* Official Tutorial (Self-Paced)

**Part 1**: Total functions, refinement types, SMT
**Part 2**: Inductive types, pattern matching
**Part 3**: Modularity, interfaces, typeclasses
**Part 4+**: Case studies (HACL*, parsers, protocols)

**TOTAL DEPTH**: ~20 chapters, focused on F* specifics, excellent for practitioners

### F* Labs (12 Weeks - Planned)

**Weeks 1-2 (L1)**: Refinement types, totality, SMT
**Weeks 3-4 (L2-L3)**: Induction, dependent types
**Weeks 5-6 (L3-L4)**: Effects, stateful verification
**Weeks 7 (L5)**: Tactics and metaprogramming
**Week 8 (L6)**: Cryptography, constant-time
**Weeks 9-10 (L6)**: Concurrency, compilers
**Week 11 (L7)**: Advanced tracks (choose one)
**Week 12**: Capstone presentations

**TOTAL DEPTH**: 7 levels, ~35 exercises planned, 5 mini-projects, 1 capstone

---

## Coverage Gap Analysis

### What They Cover That We Don't

#### Software Foundations Strengths:
1. **Deep logical foundations**: Curry-Howard, proof objects, induction principles
2. **Operational semantics**: Small-step, big-step, equivalences
3. **Type soundness proofs**: Progress + preservation for STLC
4. **Extraction theory**: From Coq to OCaml with correctness guarantees
5. **Battle-tested exercises**: 100+ exercises refined over 15+ years
6. **ProofObjects chapter**: Makes connection between proofs and programs explicit

#### CMU 15-414 Strengths:
1. **SAT solver implementation**: Students build core tool from scratch
2. **BDDs**: Important data structure we skip entirely
3. **Symbolic execution**: Critical bug-finding technique (we only touch in Week 11)
4. **Abstract interpretation**: Entire theory missing from F* Labs
5. **Why3 platform**: Students learn industrial verification tool
6. **Real-world bug catching**: Focus on finding bugs, not just proving correctness

#### MIT 6.820 Strengths:
1. **Abstract interpretation theory**: Lattices, fixpoints, Galois connections
2. **Model checking depth**: CTL, LTL model checking algorithms
3. **Graduate-level rigor**: More mathematical depth in soundness proofs
4. **Synthesis**: Program synthesis from specifications (we lack this)

#### F* Tutorial Strengths:
1. **Official examples**: Vetted by F* developers
2. **HACL* integration**: Real-world cryptography case study
3. **Low* and extraction**: Deep dive into C extraction
4. **Meta-F***: Advanced metaprogramming (we touch briefly)

### What We Cover That They Don't

#### F* Labs Unique Strengths:
1. **Modern effect systems**: F* effect system is more advanced than Coq's
2. **SMT integration**: Deep coverage of SMT-based automation (vs. purely interactive)
3. **Constant-time programming**: Security properties (timing side-channels)
4. **Information flow**: Non-interference proofs (Week 8)
5. **Concurrent separation logic**: Steel framework (Week 9)
6. **Categorical meta-prompting**: L1-L7 framework (pedagogical innovation)
7. **Practical extraction**: Multiple targets (C, OCaml, F#, WASM)
8. **Real-world security**: HACL* case studies, production crypto

---

## 2. Exercise Difficulty Comparison

### Software Foundations Exercises

**Example: Reverse Involution (Lists.v)**
```coq
Theorem rev_involutive : forall l : list nat,
  rev (rev l) = l.
Proof.
  (* Students must discover helper lemma: rev_app_distr *)
  (* Requires understanding induction + lemma composition *)
  (* Estimated time: 30-60 minutes for beginners *)
```

**Difficulty Levels**:
- ⭐ (1 star): Simple, direct application (1-10 minutes)
- ⭐⭐ (2 stars): Requires thought, maybe helper lemma (10-30 minutes)
- ⭐⭐⭐ (3 stars): Challenging, multiple lemmas (30-90 minutes)
- ⭐⭐⭐⭐ (4 stars): Advanced, significant proof engineering (1-3 hours)
- ⭐⭐⭐⭐⭐ (5 stars): Research-level (3+ hours)

**Distribution**: ~40% 1-star, 30% 2-star, 20% 3-star, 10% 4-5 star

### F* Labs Exercises (Week 2)

**Example: Reverse Involution (Exercise 2.3)**
```fstar
let rec reverse_involution (#a:Type) (xs:list a)
  : Lemma (ensures reverse (reverse xs) = xs)
          (decreases xs)
  =
  (* Students must discover: reverse_append helper *)
  (* Must understand: append_assoc from library *)
  (* Must apply: structural induction correctly *)
  (* Estimated time: 45-90 minutes *)
```

**Our Grading** (from mini-project merge sort):
- Part 2 (Implementation): 20 points
- Part 3 (Correctness proof): 15 points
- Part 4 (Code quality): 5 points
- Part 5 (Permutation - Extra Credit): 5 points

**Comparison**:
- **Equivalent difficulty**: Our Exercise 2.3 ≈ SF 3-star exercise
- **Our mini-project**: Equivalent to SF 4-star (merge_sort_sorted is hard!)
- **Time estimates**: We're realistic (3-5 hours for mini-project)
- **Extra credit**: Good idea - encourages depth without punishing struggling students

### CMU 15-414 Assignments

**Example: SAT Solver with Unit Propagation**
- Implement DPLL algorithm in Why3
- Prove termination and correctness
- Verify unit propagation optimization
- Estimated time: 8-12 hours

**Comparison**:
- **Much larger scope**: Single assignment = our entire mini-project
- **Tool complexity**: Learning Why3 + proving = steep learning curve
- **Implementation focus**: More code, less proof engineering
- **Estimated time: 8-12 hours per assignment**

### MIT 6.820 Problem Sets

**Example: Problem Set 4 (Axiomatic Semantics)**
- Prove Hoare logic rules sound with respect to operational semantics
- Formalize in Coq
- Mix of theory problems + Coq proofs
- Estimated time: 10-15 hours

**Comparison**:
- **More theoretical**: Heavy on pen-and-paper proofs
- **Graduate level**: Assumes strong mathematical maturity
- **Coq implementation**: Similar to our approach but more proof-heavy

### Difficulty Verdict

| Course | Hardest Exercise | Typical Exercise | Progression |
|--------|-----------------|------------------|-------------|
| **Software Foundations** | 4-5 star exercises (research-level) | 2-3 stars | Gentle → Steep |
| **CMU 15-414** | Final SAT solver competition | Moderate Why3 proofs | Steady |
| **MIT 6.820** | Soundness proofs in Coq | Mixed theory/practice | Graduate-level throughout |
| **F* Labs** | Merge sort correctness | Reverse involution | **Potentially too steep?** |

**CRITICAL FINDING**: Our Week 2 mini-project (merge_sort_sorted) is **extremely hard** for students with only 1 week of induction experience. Software Foundations builds to similar difficulty over 4-5 chapters.

---

## 3. Prerequisites Comparison

### Software Foundations
**Assumed**:
- No specific background in logic or PLT
- "Degree of mathematical maturity helpful"
- Programming experience (any language)
- Ability to read proofs

**Provides**:
- Complete introduction to Coq from scratch
- Functional programming tutorial built-in
- Logic refresher (propositional, predicate)

### CMU 15-414
**Assumed**:
- Undergraduate CS background
- Discrete math, logic
- Programming proficiency
- Algorithms knowledge

**Provides**:
- Quick refresher on logic
- Why3 tutorial
- SAT/SMT background

### MIT 6.820
**Assumed**:
- Graduate-level CS maturity
- Strong math background
- Programming languages knowledge
- Comfort with formal notation

**Provides**:
- Coq crash course (1 lecture)
- Operational semantics review

### F* Labs (Our Course)
**Assumed** (from COURSE_OUTLINE.md):
- "Python/OCaml/F# experience"
- "Basic logic"
- "Willingness to learn"

**Provides**:
- F* installation and toolchain setup
- Refinement types from scratch
- SMT solver primer
- Progressive L1→L7 framework

**REALITY CHECK**:
- **Understated prerequisites**: "Basic logic" is not enough for Week 2 exercises
- **Functional programming**: We assume more FP knowledge than stated
- **Proof experience**: We jump into induction proofs very quickly
- **SMT understanding**: Students need to debug SMT failures without deep background

### Prerequisites Gap Analysis

**Where We're Too Lax**:
1. "Basic logic" should be "Propositional + predicate logic with proof experience"
2. Should require: "Experience with at least one functional language (OCaml, Haskell, F#)"
3. Should recommend: "Prior exposure to types (TAPL or similar)"

**Where We're Good**:
1. Progressive disclosure (L1→L7)
2. Explicit skill levels help students self-assess
3. Installation guide in Week 1

---

## 4. Learning Outcomes Comparison

### Software Foundations Graduates Can:

**After Volume 1 (Logical Foundations)**:
✅ Write and prove theorems in Coq
✅ Define inductive data types and predicates
✅ Apply induction (structural, strong, well-founded)
✅ Use standard proof tactics (induction, destruct, rewrite, auto)
✅ Understand Curry-Howard correspondence
✅ Extract Coq code to OCaml

**After Volume 2 (Programming Language Foundations)**:
✅ Define operational semantics for languages
✅ Prove type soundness (progress + preservation)
✅ Formalize Hoare logic
✅ Verify imperative programs with pre/postconditions
✅ Understand subtyping and polymorphism

**After Volume 3 (Verified Functional Algorithms)**:
✅ Implement and verify complex data structures (RB-trees)
✅ Reason about algorithmic complexity
✅ Prove correctness of algorithms (sorting, searching)

**Career Impact**: Prepared for research in PLT, formal methods, or verification engineering roles

### CMU 15-414 Graduates Can:

✅ Implement SAT solvers from scratch
✅ Use SMT solvers for program verification
✅ Apply model checking to finite-state systems
✅ Use Why3 for deductive verification
✅ Apply symbolic execution for bug finding
✅ Understand abstract interpretation basics
✅ Verify non-trivial programs (fault-tolerant protocols)

**Career Impact**: Prepared for verification engineering, security analysis, tool development

### MIT 6.820 Graduates Can:

✅ Formalize programming languages in Coq
✅ Prove soundness of type systems
✅ Understand abstract interpretation theory
✅ Apply axiomatic semantics (Hoare logic, separation logic)
✅ Use model checking for finite-state verification
✅ Understand program synthesis basics

**Career Impact**: Prepared for graduate research, PL theory, advanced verification

### F* Tutorial Completers Can:

✅ Write F* programs with refinement types
✅ Prove properties using SMT automation
✅ Define and use inductive types
✅ Work with F* effect system
✅ Extract F* to OCaml/F#/C
✅ Understand HACL* case studies

**Career Impact**: Can contribute to F* projects, apply F* in security contexts

### F* Labs Graduates Can (Projected):

**L1-L2 (Weeks 1-4)**:
✅ Write verified functions with refinement types
✅ Leverage SMT for automatic proofs
✅ Prove properties using structural induction
✅ Debug proof failures and write lemmas

**L3-L4 (Weeks 5-8)**:
✅ Use dependent types for rich specifications
✅ Verify stateful programs with effects
✅ Reason about heaps and aliasing
✅ Prove constant-time properties
✅ Implement verified cryptographic primitives

**L5-L6 (Weeks 9-11)**:
✅ Write custom tactics for proof automation
✅ Use metaprogramming for code generation
✅ Verify concurrent programs with separation logic
✅ Prove compiler correctness
✅ Model security protocols

**L7 (Week 12)**:
✅ Design novel verification architectures
✅ Integrate multiple verification techniques
✅ Communicate formal proofs effectively

**Career Impact (Projected)**: Security engineering, cryptography, verified systems

---

## Learning Outcomes Gap Analysis

| Capability | SF | CMU 15-414 | MIT 6.820 | F* Labs | Assessment |
|-----------|----|-----------|-----------|---------| -----------|
| **Proof engineering** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | Competitive |
| **Tool usage (practical)** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | Strong |
| **Type theory depth** | ⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | Moderate |
| **Security properties** | ⭐⭐ | ⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐⭐ | **Unique strength** |
| **Cryptography** | ⭐ | ⭐⭐ | ⭐ | ⭐⭐⭐⭐⭐ | **Unique strength** |
| **Bug finding** | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐ | **Weakness** |
| **Model checking** | ⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐ | **Major gap** |
| **Abstract interpretation** | ⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐ | **Major gap** |
| **PL foundations** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | Moderate |
| **Production readiness** | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ | Strong |

**Key Gaps**:
1. **No model checking**: CMU 15-414 and MIT 6.820 cover this extensively
2. **No abstract interpretation**: Critical verification technique completely missing
3. **Weak on bug finding**: We focus on proving correct, not finding bugs
4. **Less PL theory**: Type soundness proofs not as deep as SF or MIT 6.820

**Key Strengths**:
1. **Security focus**: Information flow, constant-time, cryptography
2. **Modern effects**: F* effect system more advanced than Coq
3. **Practical extraction**: Multiple targets, production-ready
4. **Real-world case studies**: HACL*, not toy examples

---

## 5. Time Investment Analysis

### Software Foundations

**Lecture Time**: ~3 hours/week (typical university course)
**Student Work**:
- Reading chapters: 2-4 hours/week
- Exercises: 6-12 hours/week
- **Total: 8-16 hours/week**

**Completion Time**:
- Fast students: 1 volume in 8 weeks (~10 hours/week)
- Typical students: 1 volume in 12 weeks (~12 hours/week)
- Struggling students: 1 volume in 16 weeks (~15 hours/week)

**Source**: Student self-reports on GitHub, course forums

### CMU 15-414

**Lecture Time**: ~3 hours/week (2 × 1.5 hour lectures)
**Student Work**:
- Assignments (written + programming): 8-12 hours/week
- Mini-projects: 15-20 hours each (2 total)
- **Total: 8-12 hours/week average**

**Late Policy**: 5 late days total (max 2 per assignment)

### MIT 6.820

**Lecture Time**: ~3 hours/week
**Student Work**:
- Problem sets: 10-15 hours each (6 total)
- Reading: 2-3 hours/week
- **Total: 12-15 hours/week**

**Graduate Course**: Expectation is high workload

### F* Official Tutorial

**Self-paced**: Variable
**Estimated**:
- Fast learners: 40-60 hours total
- Typical learners: 80-120 hours total
- With all case studies: 150+ hours

### F* Labs (Our Course)

**Lecture Time**:
- 3 lectures × 90 min = **4.5 hours/week** ⚠️
- This is **50% more than standard courses**

**Student Work (Estimated)**:
- Week 1-2: 3 exercises + mini-project = 5-8 hours
- Week 3-4: 3 exercises + mini-project + midterm = 10-15 hours (peak)
- Week 5-6: 3 exercises + mini-project = 8-12 hours
- Week 7: Tactics (steep learning curve) = 6-10 hours
- Week 8: Crypto mini-project = 8-12 hours
- Week 9-10: Concurrency + compiler project = 10-15 hours
- Week 11-12: Capstone = 20-30 hours

**Total Per Week**:
- **Minimum**: 6 hours (lecture 4.5 + homework 1.5)
- **Typical**: 10-12 hours (lecture 4.5 + homework 5.5-7.5)
- **Peak weeks**: 15-20 hours (midterm, capstone)

---

## Time Investment Verdict

| Course | Lecture Hours/Week | Student Hours/Week | Total Hours/Week | Sustainable? |
|--------|-------------------|-------------------|-----------------|-------------|
| **Software Foundations** | 3 | 8-16 | 11-19 | ✓ Yes (standard) |
| **CMU 15-414** | 3 | 8-12 | 11-15 | ✓ Yes |
| **MIT 6.820** | 3 | 12-15 | 15-18 | ⚠️ High but grad-level |
| **F* Labs** | **4.5** | **~10-15** | **14.5-19.5** | ⚠️ **Very high** |

### CRITICAL FINDINGS:

1. **Lecture time too high**: 4.5 hours/week is excessive
   - Standard is 3 hours (2 × 1.5 hour lectures)
   - We have 3 × 1.5 hour lectures (unusual)
   - **RECOMMENDATION**: Cut to 2 lectures/week or shorten to 75 min each

2. **Peak weeks unsustainable**: Week 4 (midterm) and Week 11-12 (capstone) may burn out students
   - **RECOMMENDATION**: Spread capstone over 2 weeks, lighter Week 11

3. **No buffer time**: 12 weeks is tight
   - SF uses 14-16 weeks
   - CMU uses 15 weeks
   - We have no slack for makeup lectures, extensions
   - **RECOMMENDATION**: Add Week 13 for overflow/review

4. **Time estimates missing from outline**
   - Students can't plan their schedule
   - **RECOMMENDATION**: Add estimated hours to each exercise

---

## 6. Capstone Project Complexity

### Software Foundations
**No single capstone** - Instead:
- Volume 3 final chapters: Verified red-black trees (~20 hours)
- Self-directed exploration encouraged
- Some universities add custom capstone projects

### CMU 15-414
**Two mini-projects** (not single capstone):
1. Mid-semester: Deductive verification with Why3 (~20 hours)
2. Final: SAT solver competition (~25 hours)

**Characteristics**:
- Clear specifications
- Auto-grading where possible
- Competitive element (SAT solver performance)

### MIT 6.820
**No capstone mentioned** - Focus on problem sets

### F* Labs Capstone (Week 12)

**From COURSE_OUTLINE.md**:
- Week 11: Choose one of 4 tracks (Crypto, Systems, PL, Research)
- Week 12: Presentations (15 min + 5 min Q&A)

**Grading**: 30% of final grade

**Current Guidance**:
> "Design novel verification architectures"
> "Contribute to formal methods research"
> "Publication-quality proofs"

**PROBLEM**: This is **vague and potentially overwhelming**

---

## Capstone Comparison

| Aspect | SF (Implicit) | CMU Mini-Projects | F* Labs Capstone | Assessment |
|--------|--------------|-------------------|------------------|------------|
| **Scope** | 1 complex project | 2 medium projects | 1 research project | ⚠️ Unclear |
| **Time** | ~20 hours | 20 + 25 = 45 hours | 20-30 hours (est.) | ✓ Reasonable |
| **Specification** | Clear (RB-trees) | Very clear | **Vague** | ❌ Major issue |
| **Deliverables** | Code + proof | Code + proof | Presentation + ??? | ⚠️ Underspecified |
| **Grading Rubric** | Provided | Detailed | **Missing** | ❌ Critical gap |
| **Examples** | Provided | Multiple provided | **None yet** | ❌ Critical gap |

### CRITICAL FINDINGS:

1. **L7 "Genius" is unrealistic**: Expecting undergrads to produce "publication-quality proofs" in 2 weeks is absurd

2. **No example projects**: Students need concrete examples
   - SF shows red-black trees
   - CMU shows SAT solver specs
   - We show: "novel architectures" (terrifying!)

3. **Track selection too late**: Week 11 is too late to choose specialization
   - Should be decided by Week 8
   - Need track-specific preparation

4. **Missing scaffolding**:
   - No intermediate milestones
   - No proposal review
   - No checkpoint presentations
   - All-or-nothing Week 12 demo

### RECOMMENDATIONS:

1. **Realistic capstone examples**:
   - Track A (Crypto): Verify ChaCha20 or Poly1305 (spec provided)
   - Track B (Systems): Verify file system operation (simplified model)
   - Track C (PL): Type soundness proof for lambda calculus extension
   - Track D (Research): Replicate proof from paper (curated list provided)

2. **Add structure**:
   - Week 9: Capstone proposal (1 page)
   - Week 10: Checkpoint presentation (5 min)
   - Week 11: Peer review draft
   - Week 12: Final presentation

3. **Grading rubric** (30% total):
   - Correctness (40%): Does it verify?
   - Specification quality (20%): Clear, appropriate scope
   - Proof engineering (20%): Well-structured, reusable lemmas
   - Presentation (20%): Clear communication

---

## 7. What We Should ADD

### High Priority (Required for Competitiveness)

1. **Model Checking Basics** (Week 9 or 10)
   - CTL/LTL basics
   - Finite-state verification
   - Integration with F* (via F* model checker)
   - **Why**: Major gap vs. CMU 15-414 and MIT 6.820

2. **Abstract Interpretation Primer** (Week 10)
   - Lattices and fixpoints
   - Interval analysis example
   - Connection to refinement types
   - **Why**: Fundamental verification technique we completely miss

3. **Detailed Time Estimates** (All exercises)
   - Add to every exercise: "Estimated time: 30-60 minutes"
   - Track actuals in instructor notes
   - **Why**: Students can't manage time without this

4. **Grading Rubrics** (All assessments)
   - Detailed rubrics for every mini-project
   - Partial credit guidelines
   - **Why**: Students need to know expectations

5. **Example Solutions** (Instructor-only)
   - Multiple solution approaches
   - Common mistakes documented
   - **Why**: Instructors need this for consistent grading

6. **Prerequisite Diagnostic** (Week 0)
   - Test: Propositional logic, proofs by induction, FP basics
   - Self-assessment before course starts
   - **Why**: Current prereqs understated

### Medium Priority (Improve Quality)

7. **More Warmup Exercises** (Week 2)
   - Add 2-3 easier induction proofs before reverse
   - Scaffold to helper lemmas
   - **Why**: Difficulty spike too steep

8. **Proof Strategy Templates** (Weeks 2-4)
   - Template: "Proof by induction on X"
   - Step-by-step guide for common patterns
   - **Why**: Students struggle with proof structure

9. **Common Mistakes Guide** (All weeks)
   - Anticipated errors with explanations
   - How to debug SMT failures
   - **Why**: Reduces instructor support burden

10. **Office Hours Guidelines** (Instructor guide)
    - What help is appropriate
    - How to give hints without giving answers
    - **Why**: Maintain academic integrity

### Low Priority (Nice to Have)

11. **Video Lectures** (All topics)
    - Record live lectures
    - Short concept explainers (5-10 min)
    - **Why**: Accessibility, async learning

12. **Auto-grading Infrastructure** (Weeks 1-6)
    - Pytest-based F* testing
    - Immediate feedback on exercises
    - **Why**: Faster iteration for students

13. **Peer Review Process** (Weeks 3, 6, 9)
    - Structured peer code review
    - Rubric for constructive feedback
    - **Why**: Learn from others, reduce grading load

---

## 8. What We Should CUT

### High Priority (Cut to Stay Focused)

1. **Week 9 Concurrency Track** (Make Optional)
   - Current: Mandatory concurrent separation logic
   - **CUT**: Steel framework (too advanced for L6)
   - **KEEP**: Basic race-freedom reasoning
   - **Why**: Steel is research-level, overwhelming for 12-week course

2. **Week 7 Metaprogramming** (Reduce Scope)
   - Current: Custom tactics, reflection API, meta-programs
   - **CUT**: Meta-programs and code generation
   - **KEEP**: Basic tactic usage, built-in tactics
   - **Why**: Too much for one week, low ROI for most students

3. **L7 "Genius" Framing** (Rebrand)
   - Current: "Novel architectures, publication-quality"
   - **CUT**: Research expectations
   - **NEW**: "Advanced Integration: Apply L1-L6 to substantial project"
   - **Why**: Unrealistic and demotivating

4. **Week 11 Four-Track Split** (Simplify)
   - Current: 4 specialized tracks with custom content
   - **CUT**: Track D (Research) - too vague
   - **MERGE**: Track A+B (Security & Systems)
   - **NEW**: 2 tracks only (Security/Systems vs. PL Theory)
   - **Why**: Too much instructor prep, splits small classes too much

### Medium Priority (Streamline)

5. **Week 8 AES Mini-Project** (Replace)
   - Current: "Verified AES (simplified)"
   - **PROBLEM**: AES is complex, hard to "simplify" meaningfully
   - **REPLACE WITH**: ChaCha20 (simpler stream cipher, HACL* example)
   - **Why**: ChaCha20 more teachable, real HACL* case study

6. **Week 10 Compiler Correctness** (Reduce)
   - Current: Full compiler verification
   - **CUT**: Multi-pass compiler
   - **KEEP**: Single-pass expression compiler to stack machine
   - **Why**: Compiler verification is entire courses; keep manageable

7. **Daily Quizzes** (Weeks 1-10)
   - Current: 5-10 min quiz every lecture
   - **CUT**: Reduce to weekly quizzes (Friday)
   - **Why**: Too much overhead, disrupts flow

### Low Priority (Polish)

8. **Some Example Complexity** (SKILL.md, EXAMPLES.md)
   - Current: 20+ examples in EXAMPLES.md
   - **CUT**: Reduce to 12-15 essential examples
   - **Why**: Information overload, maintain quality

9. **Optional Reading** (Most weeks)
   - Current: Academic papers listed
   - **CUT**: Most optional readings (keep 1-2 seminal papers)
   - **Why**: Students won't read them anyway

---

## 9. Critical Weaknesses (Brutal Honesty)

### Where We're Weaker (Specific)

#### 1. **Unproven Pedagogy** ⚠️⚠️⚠️
- **Issue**: No field testing with real students
- **Evidence**: Software Foundations refined over 15+ years, 1000+ students
- **Impact**: Exercises may be too hard, too easy, or miss learning objectives
- **Risk**: High failure rate, student frustration
- **Mitigation**: Need pilot run with 5-10 students before full deployment

#### 2. **Difficulty Calibration** ⚠️⚠️⚠️
- **Issue**: Week 2 merge sort proof is brutally hard
- **Evidence**: Equivalent to SF 4-star exercise (research-level)
- **Impact**: Students hit wall, lose confidence
- **Comparison**: SF builds to this over 4-5 chapters
- **Fix**: Add 3 intermediate induction exercises in Week 2

#### 3. **Missing Model Checking** ⚠️⚠️
- **Issue**: No model checking coverage
- **Evidence**: CMU 15-414 spends 3 weeks on this; MIT 6.820 covers extensively
- **Impact**: Students miss major verification technique
- **Gap**: Finite-state verification completely absent
- **Fix**: Add Week 9 model checking basics (replace concurrency depth)

#### 4. **Missing Abstract Interpretation** ⚠️⚠️
- **Issue**: No abstract interpretation coverage
- **Evidence**: MIT 6.820 dedicates 2 weeks; CMU touches on it
- **Impact**: Students don't understand lattice-based analysis
- **Gap**: Foundational technique missing
- **Fix**: Add Week 10 abstract interpretation primer

#### 5. **Vague Capstone Specification** ⚠️⚠️
- **Issue**: "Novel architectures" is terrifying and unclear
- **Evidence**: CMU provides exact specs; SF provides worked examples
- **Impact**: Students panic, scope creep, poor outcomes
- **Fix**: Provide 6-8 concrete project options with detailed specs

#### 6. **No Exercise Solutions** ⚠️⚠️
- **Issue**: No reference solutions for instructors
- **Evidence**: SF provides full solutions with pedagogical notes
- **Impact**: Inconsistent grading, instructors struggle
- **Fix**: Write solutions for all exercises + common mistakes

#### 7. **Understated Prerequisites** ⚠️
- **Issue**: "Basic logic" is insufficient
- **Evidence**: Week 2 requires induction proof experience
- **Impact**: Unprepared students fall behind immediately
- **Fix**: Explicit prereq test, recommended preparation materials

#### 8. **No Formative Assessment** ⚠️
- **Issue**: Midterm Week 4, but no earlier feedback
- **Evidence**: SF has progressive exercises with self-check
- **Impact**: Students don't know if they're on track
- **Fix**: Weekly auto-graded check-ins (simple proofs)

#### 9. **Excessive Lecture Time** ⚠️
- **Issue**: 4.5 hours/week lectures vs. 3 hours standard
- **Evidence**: All comparison courses use 3 hours
- **Impact**: Student burnout, less time for homework
- **Fix**: Reduce to 2 × 90 min or 3 × 60 min

#### 10. **Weak on Bug Finding** ⚠️
- **Issue**: Focus on proving correct, not finding bugs
- **Evidence**: CMU 15-414 entire focus is bug catching
- **Impact**: Students think verification = proofs only
- **Fix**: Add Week 5 symbolic execution + testing integration

---

### Where We're Stronger (Honest Assessment)

#### 1. **Security Focus** ✓✓✓
- **Advantage**: Constant-time, information flow, crypto primitives
- **Evidence**: None of the comparison courses cover this depth
- **Value**: Highly relevant to industry (HACL*, miTLS)
- **Unique**: F* specifically designed for this

#### 2. **Modern Effect System** ✓✓
- **Advantage**: F* effects more advanced than Coq
- **Evidence**: Monadic effects, effect polymorphism built-in
- **Value**: Teaches modern PL concepts
- **Unique**: Software Foundations doesn't cover effects deeply

#### 3. **SMT Integration** ✓✓
- **Advantage**: Deep coverage of SMT-based automation
- **Evidence**: More than Coq courses, complementary to Why3
- **Value**: Practical verification skill
- **Unique**: Balance of automation + interactive proving

#### 4. **Practical Extraction** ✓✓
- **Advantage**: Multiple targets (C, OCaml, F#, WASM)
- **Evidence**: HACL* extracts to production C code
- **Value**: Verified code can actually ship
- **Unique**: Low* for C extraction uncommon in courses

#### 5. **Categorical Framework** ✓
- **Advantage**: L1-L7 progressive disclosure
- **Evidence**: Clear skill progression
- **Value**: Students understand where they are
- **Limitation**: Untested pedagogically

#### 6. **Real-World Case Studies** ✓
- **Advantage**: HACL*, miTLS, not toy examples
- **Evidence**: Production code at Microsoft
- **Value**: Motivation, career relevance
- **Limitation**: May be too complex for students

---

## 10. Final Verdict: Is F* Labs Competitive?

### Overall Assessment: **POTENTIALLY COMPETITIVE, BUT HIGH RISK**

#### Strengths (Sell F* Labs on These)
1. ✅ **Modern tooling**: F* is cutting-edge (2016-present)
2. ✅ **Security focus**: Unique strength (constant-time, crypto)
3. ✅ **Practical outcomes**: Extraction to production languages
4. ✅ **Real-world relevance**: HACL*, miTLS case studies
5. ✅ **Balanced approach**: SMT automation + interactive proving
6. ✅ **Effect system**: Modern PL concepts (monads, effects)

#### Weaknesses (Must Fix Before Launch)
1. ❌ **Unproven pedagogy**: Zero field testing
2. ❌ **Difficulty spikes**: Week 2 too hard
3. ❌ **Missing topics**: Model checking, abstract interpretation
4. ❌ **Vague assessments**: Capstone underspecified
5. ❌ **No solutions**: Instructors lack reference materials
6. ❌ **Time unrealistic**: 4.5 hours lecture + heavy homework

#### Comparison Verdict

**vs. Software Foundations**:
- ⚠️ **Less mature**: SF has 15+ years of refinement
- ⚠️ **Fewer exercises**: 40 vs. 100+
- ⚠️ **Less proven**: No track record
- ✅ **More modern**: F* vs. Coq (2010s tech)
- ✅ **More practical**: Extraction to C/WASM
- ✅ **Better security**: Info flow, constant-time

**Verdict**: *Not yet competitive with SF for general formal methods education. Could be competitive for security-focused programs.*

**vs. CMU 15-414**:
- ❌ **Missing core topics**: No model checking, weak on SAT/SMT
- ❌ **Less tool diversity**: Only F*, vs. Why3 + SAT + SMT
- ✅ **Deeper proofs**: More interactive theorem proving
- ✅ **Better security**: Constant-time verification
- ⚠️ **Different focus**: Bug catching vs. proving correct

**Verdict**: *Complementary, not competitive. 15-414 focuses on automated tools; we focus on interactive proving.*

**vs. MIT 6.820**:
- ❌ **Less theory**: Graduate-level PL theory missing
- ❌ **Missing AI**: No abstract interpretation
- ✅ **More practical**: Production code extraction
- ✅ **More security**: Crypto + info flow
- ⚠️ **Different audience**: Advanced UG vs. Graduate

**Verdict**: *Not competitive for PL theory. Competitive for applied verification.*

**vs. F* Official Tutorial**:
- ✅ **More structured**: 12-week progression vs. self-paced
- ✅ **More assessment**: Graded exercises, exams, capstone
- ✅ **Pedagogical framework**: L1-L7 levels
- ⚠️ **Untested**: Tutorial battle-tested by community
- ⚠️ **Reinventing wheel**: Could just assign tutorial

**Verdict**: *Adds structure to official tutorial. Unclear if worth the overhead.*

---

## 11. Recommendations Summary

### MUST FIX (Before Any Pilot)

1. **Write instructor solutions** for all exercises (40 exercises × 2 hours = 80 hours work)
2. **Add detailed rubrics** for all assessments (5 mini-projects + midterm + capstone)
3. **Specify capstone projects** with concrete examples (6-8 projects with full specs)
4. **Add time estimates** to every exercise
5. **Fix prerequisites**: Change "basic logic" to explicit requirements with diagnostic test
6. **Reduce lecture time**: Cut to 3 hours/week (2 × 90 min)
7. **Add Week 2 warmup exercises**: 3 intermediate induction proofs before merge sort

### SHOULD FIX (Before Full Deployment)

8. **Add model checking module** (Week 9, 1.5 lectures)
9. **Add abstract interpretation primer** (Week 10, 1 lecture)
10. **Restructure capstone**: Proposal Week 9, checkpoint Week 10, final Week 12
11. **Add symbolic execution** (Week 5, 1 lecture - replace one effect lecture)
12. **Simplify Week 11 tracks**: 2 tracks instead of 4
13. **Add formative assessments**: Weekly auto-graded check-ins
14. **Document common mistakes** for each exercise

### NICE TO HAVE (Quality Improvements)

15. **Field test with 5-10 students** before advertising broadly
16. **Record video lectures** for asynchronous access
17. **Build auto-grading infrastructure** for Weeks 1-6
18. **Create peer review rubrics** for mini-projects
19. **Shorten examples**: Cut EXAMPLES.md from 20 to 12 examples

---

## 12. Estimated Effort to Reach Competitive

### To Match Software Foundations Quality

**Core Content** (300-400 hours):
- Write all instructor solutions: 80 hours
- Add 30 more exercises (with solutions): 90 hours
- Model checking module: 40 hours
- Abstract interpretation module: 40 hours
- Revise Week 2 difficulty curve: 20 hours
- Capstone project specs (8 projects): 40 hours

**Assessment Materials** (100-150 hours):
- Grading rubrics: 30 hours
- Midterm exam creation: 20 hours
- Final exam creation: 20 hours
- Auto-grading setup: 40 hours

**Instructor Support** (80-120 hours):
- Common mistakes guide: 40 hours
- Office hours guidelines: 10 hours
- Teaching notes per week: 60 hours (12 weeks × 5 hours)

**Testing & Iteration** (200+ hours):
- Pilot with 5 students: 100 hours (grading, feedback, revision)
- Second pilot with 10 students: 100 hours

**TOTAL**: **680-870 hours** (roughly 4-6 months full-time work)

### To Match CMU 15-414 Practicality

**Additional Tools** (150-200 hours):
- SAT solver module: 60 hours
- Why3 integration examples: 40 hours
- Model checking labs: 50 hours

**TOTAL (including above)**: **830-1070 hours**

---

## 13. Market Positioning

### Where F* Labs Fits

**Best Use Cases**:
1. **Security engineering programs**: Cybersecurity MS/PhD
2. **Industry workshops**: 2-week intensive for crypto engineers
3. **Self-study supplement**: Alongside F* official tutorial
4. **Capstone for systems courses**: Advanced verification module

**Poor Fit**:
1. **Intro formal methods**: Software Foundations better
2. **General PL theory**: MIT 6.820 better
3. **Automated verification tools**: CMU 15-414 better
4. **Intro to Coq**: Software Foundations Volume 1

### Competitive Positioning

**Unique Value Proposition**:
> "Learn to build cryptographically secure, formally verified software using F*, the language behind Microsoft's HACL* cryptographic library. Focus on security properties (constant-time, information flow) and practical extraction to production C code."

**Target Student**:
- Background: Strong CS undergrad or MS student
- Interest: Security, cryptography, verified systems
- Goal: Work on verified systems (HACL*, miTLS, EverParse)
- Willing to: Invest 12-15 hours/week for 12 weeks

**NOT For**:
- Students wanting gentle intro to formal methods → Send to SF
- Students wanting tool-based verification → Send to CMU 15-414
- Students wanting PL theory depth → Send to MIT 6.820
- Students wanting Coq specifically → Send to SF

---

## Final Recommendation

### Should You Run F* Labs?

**IF**:
- ✅ You have 400-600 hours to invest in course development
- ✅ You can field test with 5-10 students first
- ✅ You're targeting security/crypto professionals or students
- ✅ You have F* expertise to provide instructor support
- ✅ You can commit to iterating based on feedback

**THEN**: Yes, F* Labs can become a competitive specialized course

**IF**:
- ❌ You need course-ready materials immediately
- ❌ You're teaching general formal methods
- ❌ You lack time for 400+ hours of development
- ❌ You can't field test first

**THEN**: Use Software Foundations or F* official tutorial instead

---

## Conclusion

**F* Labs is ambitious, modern, and addresses a real gap (security-focused formal verification education). However, it is not yet competitive with established courses due to:**

1. Lack of field testing
2. Unproven pedagogical design
3. Missing core topics (model checking, abstract interpretation)
4. Insufficient support materials (solutions, rubrics, time estimates)
5. Difficulty calibration issues

**With 400-600 hours of additional work and successful pilot testing, F* Labs could become the go-to course for security-focused formal verification education.**

**Current status**: Promising research prototype, not production-ready educational materials.

**Path forward**:
1. Fix MUST FIX items (80-100 hours)
2. Pilot with 5 students (100 hours)
3. Iterate based on feedback (100-200 hours)
4. Second pilot with 10 students (100 hours)
5. Public beta (200+ hours of ongoing support)

**Estimated timeline**: 6-12 months to competitive quality, assuming dedicated effort.

---

**END OF BENCHMARK ANALYSIS**
