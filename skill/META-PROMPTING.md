# F* Meta-Prompting Framework Integration

**Quick Reference**: 7-Level Categorical Framework for F* Verification

---

## Level Selection Guide

```
Choose verification approach based on task complexity:

L1 (Refinement) ──→ Bounds, safety, simple properties
L2 (Lemmas) ─────→ Inductive proofs, recursive structures
L3 (Dependent) ──→ Type-level computation, indexed families
L4 (Effects) ────→ Stateful reasoning, heap manipulation
L5 (Tactics) ────→ Proof automation, custom decision procedures
L6 (Security) ───→ Information flow, non-interference, crypto
L7 (Research) ───→ Novel techniques, foundational extensions
```

---

## Quick Examples by Level

### L1: Simple Refinement
```fstar
let safe_div (x: int) (y: int{y <> 0}) : int = x / y
```

### L2: Inductive Lemma
```fstar
val reverse_involutive: l:list 'a -> Lemma (reverse (reverse l) == l)
let rec reverse_involutive l = match l with
  | [] -> ()
  | hd::tl -> reverse_involutive tl
```

### L3: Dependent Types
```fstar
type vec (a: Type) : nat -> Type =
  | VNil : vec a 0
  | VCons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)
```

### L4: Stateful Effects
```fstar
let swap (#a: Type) (r1 r2: ref a) : ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 ->
    sel h1 r1 == sel h0 r2 &&
    sel h1 r2 == sel h0 r1))
```

### L5: Tactics
```fstar
let ring_solver () : Tac unit =
  norm [delta];
  trefl () <|> apply_lemma (`add_comm)
```

### L6: Security Properties
```fstar
val constant_time_eq:
  x:string -> y:string{length x = length y} ->
  b:bool{b <==> (x = y)} /\
  Lemma (forall x' y'. length x' = length y' ==>
    timing (constant_time_eq x' y') = O(length x'))
```

### L7: Novel Research
```fstar
effect JitST (a: Type) (time: nat) =
  ST a (fun h -> True) (fun h0 x h1 ->
    compile_time h0 h1 <= time)
```

---

## Categorical Foundation (Brief)

The framework is grounded in **natural equivalence** from category theory:

```
Hom(Level, Program^Task) ≅ Hom(Level × Task, Program)
```

This means:
- **Left**: Level-specific meta-prompt → (Task → VerifiedProgram)
- **Right**: (Level, Task) → VerifiedProgram

Both approaches are **mathematically equivalent**, validated by the Rewrite category.

---

## When to Use Each Level

| Level | Complexity | Automation | Manual Effort | Typical Time |
|-------|-----------|------------|---------------|--------------|
| L1 | Low | High (SMT) | Minimal | Minutes |
| L2 | Medium | Medium | Moderate | Hours |
| L3 | Medium-High | Medium | Moderate | Hours-Days |
| L4 | High | Low | Significant | Days |
| L5 | Variable | Custom | Initial investment | Days-Weeks |
| L6 | Very High | Low | Significant | Weeks |
| L7 | Research | None | Extensive | Months |

---

## Common Patterns

### Pattern 1: Start Simple, Escalate
```fstar
// Try L1 first
let abs (x: int) : y:int{y >= 0} = if x >= 0 then x else -x

// If SMT fails, add L2 lemma
val abs_spec: x:int -> Lemma (let y = abs x in y >= 0 && (y == x || y == -x))
```

### Pattern 2: Compose Levels
```fstar
// L3 (dependent types) + L2 (lemma) + L1 (refinement)
let safe_vec_head (#n: pos) (v: vec int n) : x:int{x == vhead v} =
  vhead v  // L3: Type ensures n > 0
           // L2: Lemma proves x is first element
           // L1: Refinement captures return value
```

### Pattern 3: Level Migration
```fstar
// Start at L4 (stateful)
let increment (r: ref int) : ST unit ... = r := !r + 1

// Migrate to L6 (security) if needed
let secure_increment (r: ref int{is_low r}) : SecureST unit
  (ensures non_interference)
= r := !r + 1
```

---

## Complete Framework

For the full 4,145-line framework with:
- 42 complete code examples
- 7 formal categorical proofs
- Detailed L1-L7 templates
- Research extensions (L8-L10)

See: `LUXOR/PROJECTS/fstar-framework/FSTAR_META_PROMPTING_FRAMEWORK.md`

---

## Integration with fstar-verification Skill

This meta-framework **extends** the base fstar-verification skill by:

1. **Systematic Classification**: Guides level selection for any task
2. **Template Library**: Provides reusable verification patterns
3. **Theoretical Foundation**: Ensures correctness via category theory
4. **Progressive Learning**: Natural path from L1 → L7

**Usage**: When facing a verification task, consult this guide to select the appropriate level, then refer to the main SKILL.md for detailed techniques and examples at that level.
