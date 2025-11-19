# F* Practical Development & Debugging Skill

**Expert-level F* development and debugging knowledge for productive verification engineering.**

---

## What This Skill Provides

While `/skill/SKILL.md` covers **theoretical foundations** (dependent types, refinement types, effect system), this skill provides **practical engineering expertise**:

### Core Capabilities

1. **Systematic Debugging**
   - Three failure modes: timeout, unknown, unsat
   - Step-by-step diagnostic workflows
   - Tool mastery: --query_stats, --log_queries, --debug

2. **Performance Optimization**
   - Profiling verification bottlenecks
   - Fuel minimization techniques
   - SMTPat pattern engineering
   - Sub-5-second verification targets

3. **Production Development**
   - IDE integration (VS Code, Emacs)
   - CI/CD pipeline setup (GitHub Actions)
   - Testing strategies (unit, property-based, regression)
   - Migration and upgrade workflows

4. **Common Pitfalls**
   - NIA (nonlinear arithmetic) failures
   - Fuel explosion
   - Missing decreases clauses
   - Module resolution issues

5. **Real-World Patterns**
   - Stateful verification (ST monad)
   - Ghost code and erasure
   - Refinement subtyping
   - Verified data structures

---

## When to Use This Skill

### ✅ Use for:
- Debugging verification failures
- Optimizing slow proofs (<5 sec target)
- Setting up development environment
- Production verified systems
- CI/CD integration
- Teaching practical F* skills

### ⏸️ Use `/skill/SKILL.md` for:
- Type theory foundations
- Refinement type semantics
- Effect system design
- Theoretical proofs
- Mathematical properties

---

## Quick Start

### Most Important F* Flags

```bash
# Profiling (ESSENTIAL)
fstar.exe --query_stats file.fst   # Find slow queries
fstar.exe --log_queries file.fst   # Inspect SMT-LIB

# Debugging
fstar.exe --debug SMT file.fst     # Verbose Z3 output
fstar.exe --fuel 3 file.fst        # Add recursive unfolding

# Performance
fstar.exe --z3rlimit 20 file.fst   # Increase Z3 timeout
```

### Debugging Workflow

```
1. ERROR → Read message carefully
2. ISOLATE → Find minimal failing case
3. PROFILE → Run with --query_stats
4. INSPECT → Check --log_queries output
5. FIX → Apply targeted solution
6. VERIFY → Confirm it works
```

### Performance Targets

- Simple refinement: <50ms
- List proof: <200ms
- Complex proof: <2 seconds
- Full file: <5 seconds
- CI/CD suite: <5 minutes

---

## Key Patterns

### Pattern: Debugging NIA Failures

```fsharp
// ❌ FAILS with "unknown"
let multiply (x:positive) (y:positive) : positive =
  x * y  // Variable * variable = nonlinear

// ✅ FIXED with assertions
let multiply_fixed (x:positive) (y:positive) : positive =
  assert (x > 0 && y > 0);  // Help Z3
  x * y
```

### Pattern: Minimizing Fuel

```fsharp
// ❌ BAD: Global high fuel
#set-options "--fuel 20"  // Slow for everything!

// ✅ GOOD: Localized minimal fuel
#push-options "--fuel 3"
let specific_proof = ...
#pop-options
```

### Pattern: Automatic Lemma Application

```fsharp
// ❌ Manual calls everywhere
val lemma: xs:list 'a -> Lemma (property xs)
let proof xs ys =
  lemma xs;  // Manual
  lemma ys;  // Manual
  ...

// ✅ Automatic with SMTPat
val lemma_auto: xs:list 'a -> Lemma (property xs)
                                    [SMTPat (pattern xs)]
let proof xs ys =
  ()  // Z3 applies automatically!
```

---

## Course Integration

### Week 3 Focus
This skill is heavily used in **Week 3: SMT Solver Foundations**:
- Exercise 3.1: Reading SMT-LIB queries
- Exercise 3.2: Debugging toolkit
- Exercise 3.3: LIA vs NIA
- Exercise 3.4: Fuel minimization
- Exercise 3.5: SMTPat patterns
- Mini-Project: Performance optimization

### Teaching Notes
- `instructor_guide/week_03_teaching_notes.md` - Complete SMT module
- `TESTING.md` - Verification framework
- `SMT_COVERAGE_ANALYSIS.md` - Why this matters

---

## Expertise Progression

| Level | Capabilities |
|-------|--------------|
| **L2 Apprentice** | Debug basic failures, use --query_stats, understand error messages |
| **L3 Competent** | Optimize fuel, handle NIA, use SMTPat patterns effectively |
| **L4 Proficient** | Read SMT-LIB, design patterns, achieve <5s verification |
| **L5 Expert** | Build production systems, CI/CD, advanced optimization |
| **L6 Master** | F* internals, custom tactics, Z3 theory customization |

---

## Resources

### Documentation
- **SKILL.md** - Complete practical F* knowledge base
- **Week 3 Teaching Notes** - 270 minutes of SMT debugging
- **TESTING.md** - Verification quality gates

### Official F* Resources
- Tutorial: https://fstar-lang.org/tutorial
- Wiki: https://github.com/FStarLang/FStar/wiki
- Zulip Chat: https://fstar.zulipchat.com/

### Installation
- `scripts/install_fstar.sh` - Automated installation
- `scripts/verify_all.sh` - Verification suite
- `INSTALLATION_GUIDE.md` - Setup documentation

---

## Skill Activation

This skill **auto-activates** when:
- Debugging F* verification failures
- Optimizing proof performance
- Working with SMT solver interaction
- Setting up F* development tools
- Building production verified systems

Works alongside:
- `/skill/SKILL.md` - Theoretical foundations (82KB)
- `.claude/skills/category-master/` - Mathematical rigor
- `.claude/skills/cc2-verify/` - Testing and QA

---

**File:** `.claude/skills/fstar-practical/SKILL.md`
**Size:** ~25KB
**Focus:** Production F* development and debugging
**Expertise:** L2-L6 (Apprentice to Master)
**Status:** Production-ready
