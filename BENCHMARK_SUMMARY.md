# F* Labs Benchmark Analysis - Executive Summary

**Date**: 2025-11-19
**Status**: Weeks 1-2 Implemented (of 12 total)
**Verdict**: 🟡 **Promising but Not Yet Competitive**

---

## TL;DR - Critical Findings

### 🔴 Critical Weaknesses
1. **Zero field testing** - no real students have attempted this
2. **Week 2 difficulty spike** - merge sort proof is brutal (equivalent to research-level exercises in Software Foundations)
3. **Missing major topics** - no model checking, no abstract interpretation
4. **Vague capstone** - "novel architectures" is terrifying and unclear
5. **No instructor solutions** - cannot grade consistently without reference solutions
6. **4.5 hours lectures/week** - 50% more than industry standard (should be 3 hours)

### 🟢 Unique Strengths
1. **Security focus** - constant-time verification, information flow (no other course covers this)
2. **Modern effect system** - F* effects more advanced than Coq
3. **SMT integration** - practical automation (complementary to interactive proving)
4. **Real-world extraction** - to C, OCaml, F#, WASM (production-ready)
5. **HACL* case studies** - actual Microsoft production cryptography

### 🟡 Competitive Status

| Comparison | Verdict |
|-----------|---------|
| **vs. Software Foundations** | Not competitive (less mature, fewer exercises) but more modern/practical |
| **vs. CMU 15-414 (Bug Catching)** | Complementary (different focus: proving vs. bug-finding) |
| **vs. MIT 6.820 (Program Analysis)** | Not competitive (less theory) but more practical for security |
| **vs. F* Official Tutorial** | Adds structure but unclear if worth the overhead |

---

## Comparison Matrix

| Dimension | Software Foundations | CMU 15-414 | MIT 6.820 | F* Labs | Grade |
|-----------|---------------------|------------|-----------|---------|-------|
| **Maturity** | 15+ years, 1000s students | 10+ years | 10+ years | 0 students | ❌ F |
| **Exercise Count** | 100+ | ~30-40 | 6 problem sets | ~40 planned | ⚠️ C |
| **Solutions Provided** | Yes (instructor) | Yes | Yes | **No** | ❌ F |
| **Time Estimates** | Yes (star system) | Implicit | Yes | **No** | ❌ F |
| **Grading Rubrics** | Yes | Yes | Yes | **Partial** | ⚠️ D |
| **Security Depth** | Low | Medium | Low | **Very High** | ✅ A |
| **Cryptography** | None | Minimal | None | **Deep** | ✅ A |
| **Model Checking** | Minimal | Deep | Deep | **None** | ❌ F |
| **Abstract Interpretation** | None | Some | Deep | **None** | ❌ F |
| **SMT Automation** | Low | High | Low | **High** | ✅ A |
| **Modern Effects** | Low | Medium | Low | **High** | ✅ A |
| **Practical Extraction** | Medium | Medium | Low | **High** | ✅ A |

**Overall**: 🟡 C+ (Potential A- with 400-600 hours of work)

---

## Time Investment Analysis

### Lecture Hours

| Course | Lectures/Week | Hours/Week | Our Course | Status |
|--------|--------------|-----------|------------|--------|
| Software Foundations | 2 × 1.5h | 3 hours | 3 × 1.5h = **4.5 hours** | ⚠️ 50% too high |
| CMU 15-414 | 2 × 1.5h | 3 hours | | |
| MIT 6.820 | 2 × 1.5h | 3 hours | | |

**Recommendation**: Cut to 2 × 90 min lectures/week

### Student Workload

| Course | Student Hours/Week | Total/Week | Our Estimate | Sustainable? |
|--------|-------------------|-----------|--------------|-------------|
| Software Foundations | 8-16 | 11-19 | 10-15 | ✓ |
| CMU 15-414 | 8-12 | 11-15 | | ✓ |
| MIT 6.820 | 12-15 | 15-18 | | ⚠️ (grad-level) |
| **F* Labs** | **10-15** | **14.5-19.5** | Peak: 20+ | ❌ Unsustainable |

**Problem**: Peak weeks (midterm, capstone) are 15-20 hours - will burn out students

---

## Specific Exercise Difficulty Comparison

### Software Foundations Star System
- ⭐ (1 star): 1-10 minutes - simple application
- ⭐⭐ (2 stars): 10-30 minutes - requires thought
- ⭐⭐⭐ (3 stars): 30-90 minutes - challenging, helper lemmas
- ⭐⭐⭐⭐ (4 stars): 1-3 hours - advanced proof engineering
- ⭐⭐⭐⭐⭐ (5 stars): 3+ hours - research-level

**Distribution**: 40% (1⭐) | 30% (2⭐) | 20% (3⭐) | 10% (4-5⭐)

### F* Labs Week 2 Examples

| Exercise | F* Labs Time | SF Equivalent | Comment |
|----------|-------------|---------------|---------|
| Exercise 2.1 (Fibonacci) | 20-30 min | 2⭐ | Appropriate |
| Exercise 2.3 (Reverse involution) | 45-90 min | 3⭐ | Challenging but OK |
| **Mini-Project (Merge sort proof)** | **3-5 hours** | **4⭐** | ⚠️ TOO HARD for Week 2 |

**Critical Issue**: We assign a 4-star (research-level) proof in Week 2. Software Foundations builds to this difficulty over 4-5 chapters.

**Fix**: Add 3 intermediate 2-star exercises before merge sort

---

## Topic Coverage Gaps

### Major Gaps (Topics They Have, We Don't)

| Topic | Software Foundations | CMU 15-414 | MIT 6.820 | F* Labs | Priority |
|-------|---------------------|------------|-----------|---------|----------|
| **Model Checking** | ⭐ (minimal) | ⭐⭐⭐⭐⭐ (3 weeks) | ⭐⭐⭐⭐⭐ | ❌ None | 🔴 Critical |
| **Abstract Interpretation** | ❌ | ⭐⭐⭐ (1 week) | ⭐⭐⭐⭐⭐ (2 weeks) | ❌ None | 🔴 Critical |
| **Symbolic Execution** | ❌ | ⭐⭐⭐ (1 week) | ⭐⭐⭐ | ❌ None | 🟡 High |
| **SAT Solver Internals** | ❌ | ⭐⭐⭐⭐⭐ (implement from scratch) | ⭐⭐ | ⭐ (primer only) | 🟡 Medium |
| **Type Soundness Proofs** | ⭐⭐⭐⭐⭐ (full proof) | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ (Week 10) | 🟡 Medium |
| **Operational Semantics** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | 🟡 Medium |

### Unique Strengths (Topics We Have, They Don't)

| Topic | Software Foundations | CMU 15-414 | MIT 6.820 | F* Labs | Value |
|-------|---------------------|------------|-----------|---------|-------|
| **Constant-Time Verification** | ❌ | ❌ | ❌ | ⭐⭐⭐⭐⭐ (Week 8) | 🔥 Unique |
| **Information Flow Security** | ❌ | ⭐ | ⭐ | ⭐⭐⭐⭐⭐ (Week 8) | 🔥 Unique |
| **Cryptographic Primitives** | ❌ | ⭐ | ❌ | ⭐⭐⭐⭐⭐ (Week 8) | 🔥 Unique |
| **Effect System Depth** | ⭐⭐ | ⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐⭐ (Weeks 5-6) | ✅ Strong |
| **Concurrent Separation Logic** | ❌ | ❌ | ⭐⭐ | ⭐⭐⭐⭐ (Week 9) | ✅ Strong |
| **HACL* Case Studies** | ❌ | ❌ | ❌ | ⭐⭐⭐⭐ (throughout) | ✅ Strong |

**Key Insight**: We excel at **security-focused verification** but lack **automated verification techniques** (model checking, abstract interpretation)

---

## Prerequisites Reality Check

### What We Say

> "Prerequisites: Python/OCaml/F# experience, basic logic, willingness to learn"

### What's Actually Needed (Week 2 Evidence)

Based on merge sort mini-project requirements:
- ✅ Functional programming: **Intermediate** (pattern matching, recursion, higher-order functions)
- ❌ "Basic logic" → **Proof experience required** (propositional + predicate logic with proof writing)
- ❌ "Willingness to learn" → **Mathematical maturity** (comfort with induction, helper lemmas, proof decomposition)
- ❌ Not mentioned → **Prior type system exposure helpful** (TAPL or similar)

### Updated Prerequisites Should Say

**Required**:
- Intermediate functional programming (OCaml, Haskell, F#, or ML)
- Propositional and predicate logic with proof writing experience
- Discrete mathematics (induction, structural recursion)
- Comfort with mathematical notation

**Recommended**:
- Type systems (TAPL chapters 1-15 or equivalent)
- Prior Coq/Isabelle/Lean exposure (helpful but not required)
- Cryptography background (for Weeks 8+)

**Diagnostic Test**: Add Week 0 self-assessment on these topics

---

## Capstone Project Analysis

### What Other Courses Do

**Software Foundations**:
- No single capstone
- Culminates in verified red-black trees (~20 hours)
- Clear specification, worked examples

**CMU 15-414**:
- Two mini-projects (not capstone):
  1. Why3 verification (~20 hours)
  2. SAT solver competition (~25 hours)
- Very clear specifications
- Auto-grading + performance competition

**MIT 6.820**:
- No capstone - focus on problem sets

### What We Currently Specify

> Week 12 Capstone: "Design novel verification architectures. Contribute to formal methods research. Publication-quality proofs."

**Problems**:
1. ❌ "Novel architectures" - vague and terrifying
2. ❌ "Research contribution" - unrealistic for undergrads in 2 weeks
3. ❌ "Publication-quality" - absurd expectation
4. ❌ No concrete examples
5. ❌ No grading rubric details
6. ❌ No scaffolding (proposal, checkpoint, peer review)

### Recommended Capstone Structure

**Week 9**: Capstone proposal (1 page) - choose from 6-8 provided options
**Week 10**: Checkpoint presentation (5 min)
**Week 11**: Peer review draft exchange
**Week 12**: Final presentation (15 min + 5 min Q&A)

**Example Projects** (Clear Specs Needed):
1. **Track A (Crypto)**: Verify ChaCha20 stream cipher (spec provided, 200-300 LOC)
2. **Track A (Crypto)**: Verify Poly1305 MAC (spec provided, 150-250 LOC)
3. **Track B (Systems)**: Verify in-place quicksort with safety proof
4. **Track B (Systems)**: Verify bounded queue with full specification
5. **Track C (PL)**: Type soundness for STLC + effects
6. **Track C (PL)**: Small-step semantics + equivalence proof

**Grading Rubric** (30% of grade):
- 40%: Correctness (does it verify in F*?)
- 20%: Specification quality (clear, appropriate scope)
- 20%: Proof engineering (well-structured, reusable lemmas)
- 20%: Presentation (clear communication, live demo)

---

## What to Add (Priority Order)

### 🔴 Critical (Must Fix Before Any Pilot)

1. **Instructor solutions** for all exercises (Est: 80 hours)
   - Every exercise needs reference solution
   - Multiple approaches where applicable
   - Common mistakes documented

2. **Detailed grading rubrics** for all assessments (Est: 30 hours)
   - Mini-projects: point breakdown
   - Midterm: problem-by-problem rubric
   - Capstone: detailed rubric (see above)

3. **Capstone project specifications** (Est: 40 hours)
   - 6-8 concrete project options
   - Full specifications with starter code
   - Expected solution outlines

4. **Time estimates** for every exercise (Est: 10 hours)
   - Add to each exercise: "Estimated time: 30-60 min"
   - Calibrate during pilot testing

5. **Fix prerequisites** (Est: 20 hours)
   - Honest prerequisite list
   - Diagnostic test (10 questions)
   - Recommended prep materials

6. **Reduce lecture time** to 3 hours/week (Est: 30 hours)
   - Cut from 3 × 90 min to 2 × 90 min
   - Restructure content accordingly

7. **Week 2 warmup exercises** (Est: 15 hours)
   - Add 3 intermediate induction proofs
   - Scaffold: list length → list append → reverse
   - Before merge sort mini-project

**Total Critical**: ~225 hours

### 🟡 High Priority (Before Full Deployment)

8. **Model checking module** (Est: 40 hours)
   - Add to Week 9: CTL/LTL basics
   - F* model checker integration
   - 1-2 exercises

9. **Abstract interpretation primer** (Est: 40 hours)
   - Add to Week 10: lattices, fixpoints
   - Interval analysis example
   - Connection to refinement types

10. **Restructure capstone timeline** (Est: 20 hours)
    - Spread over Weeks 9-12 (not just Week 12)
    - Add proposal, checkpoint, peer review

11. **Symbolic execution module** (Est: 30 hours)
    - Add to Week 5: basic symbolic execution
    - Integration with SMT
    - Replace one effect lecture

12. **Simplify Week 11 tracks** (Est: 15 hours)
    - Cut from 4 tracks to 2
    - Merge Track A+B (Security/Systems)
    - Cut Track D (Research)

13. **Formative assessments** (Est: 30 hours)
    - Weekly auto-graded check-ins
    - Simple proof problems (10-15 min)

14. **Common mistakes documentation** (Est: 40 hours)
    - For each exercise: anticipated errors
    - Debugging SMT failures guide
    - How to get unstuck

**Total High Priority**: ~215 hours

### 🔵 Nice to Have (Quality Polish)

15. **Field test** (Est: 100 hours per pilot)
    - 5-10 students
    - Collect feedback
    - Iterate on materials

16. **Video lectures** (Est: 120 hours)
    - Record all 24 lectures
    - Short explainers (5-10 min each)

17. **Auto-grading** (Est: 60 hours)
    - Pytest + F* integration
    - Weeks 1-6 only (basic exercises)

**Total Nice to Have**: ~280 hours

---

## What to Cut (Simplify Scope)

### 🔴 High Priority Cuts

1. **Week 9 Steel Framework** → Make optional
   - Current: Mandatory concurrent separation logic
   - Cut: Steel framework (too advanced)
   - Keep: Basic race-freedom reasoning
   - Why: Steel is research-level

2. **Week 7 Metaprogramming** → Reduce scope
   - Current: Custom tactics + reflection + code generation
   - Cut: Reflection API, code generation
   - Keep: Basic tactic usage only
   - Why: Too much for one week, low ROI

3. **L7 "Genius" Framing** → Rebrand
   - Current: "Novel architectures, publication-quality"
   - Cut: Research expectations
   - New: "Advanced Integration Project"
   - Why: Unrealistic and demotivating

4. **Week 11 Four Tracks** → Simplify to two
   - Current: Crypto, Systems, PL, Research
   - Cut: Research track (too vague)
   - Merge: Crypto + Systems → "Security"
   - Keep: Security vs. PL Theory
   - Why: Too much instructor prep, splits classes

### 🟡 Medium Priority Cuts

5. **Week 8 AES Mini-Project** → Replace
   - Current: "Verified AES (simplified)"
   - Problem: AES complex, hard to simplify
   - Replace: ChaCha20 (simpler, HACL* example)
   - Why: More teachable

6. **Week 10 Compiler Verification** → Reduce
   - Current: Full compiler correctness
   - Cut: Multi-pass compiler
   - Keep: Single-pass expression → stack machine
   - Why: Compiler verification is entire courses

7. **Daily Quizzes** → Weekly only
   - Current: 5-10 min quiz every lecture
   - Cut: Reduce to Friday only
   - Why: Too much overhead

---

## Effort to Reach Competitive Status

### Path to Beta (Minimal Viable Course)

**Phase 1: Fix Critical Issues** (225 hours)
- All instructor solutions
- Grading rubrics
- Capstone specs
- Prerequisites update
- Week 2 warmup exercises

**Phase 2: First Pilot** (100 hours)
- 5 students, structured feedback
- Grading + iteration
- Revisions based on feedback

**Phase 3: Add Missing Topics** (215 hours)
- Model checking module
- Abstract interpretation
- Symbolic execution
- Restructure capstone

**Phase 4: Second Pilot** (100 hours)
- 10 students
- More feedback
- Polish materials

**TOTAL**: ~640 hours (4 months full-time)

### Path to Production (Competitive Quality)

Add to Beta:
- Video lectures: 120 hours
- Auto-grading: 60 hours
- Advanced polish: 100 hours
- Third pilot (20 students): 120 hours

**TOTAL**: ~1,040 hours (6-7 months full-time)

---

## Market Positioning

### Best Use Cases

✅ **Security engineering programs** - MS/PhD in cybersecurity
✅ **Industry crypto training** - 2-week intensive for HACL* engineers
✅ **Self-study supplement** - Alongside F* official tutorial
✅ **Advanced elective** - After intro formal methods course

### Poor Fit

❌ **First formal methods course** - Use Software Foundations instead
❌ **General PL theory** - MIT 6.820 better choice
❌ **Automated verification focus** - CMU 15-414 better
❌ **Coq-specific learning** - Software Foundations

### Unique Value Proposition

> "Learn to build cryptographically secure, formally verified systems using F*, the language behind Microsoft's HACL* cryptographic library. Master security properties (constant-time verification, information flow) and practical extraction to production C code."

**Target Student**:
- CS undergrad (junior/senior) or MS with security focus
- Strong functional programming background
- Interest in cryptography, verified systems, security
- Willing to invest 12-15 hours/week × 12 weeks

---

## Final Recommendation

### Should You Deploy F* Labs?

**✅ YES, IF**:
- You have 400-600 hours for course development
- You can field test with 5-10 students first
- You're targeting security/crypto programs
- You have F* expertise for support
- You can iterate based on feedback

**❌ NO, IF**:
- You need ready-to-use materials now
- You're teaching general formal methods
- You lack development time
- You can't pilot test

### Bottom Line

**F* Labs has excellent potential as a specialized security-focused formal verification course, but it is currently 400-600 hours of work away from being competitive with established courses.**

**Current grade**: 🟡 C+ (Untested prototype)
**Potential grade**: 🟢 A- (With fixes and testing)
**Timeline**: 6-12 months to production quality

**Recommendation**: Complete critical fixes, pilot with small group, iterate to competitive quality before wide deployment.

---

**END SUMMARY**
