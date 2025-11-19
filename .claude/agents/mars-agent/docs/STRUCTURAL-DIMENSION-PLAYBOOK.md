# MARS: Structural Dimension Playbook

**Dimension**: How domains organize, relate, and depend on each other
**Agent**: MARS
**Usage**: Reference during decomposition phase

---

## Core Question
"How are the functional domains of this system organized, and what depends on what?"

---

## The Structural Lens

### What MARS Looks For
- **Functional domains**: What capabilities/areas of function exist?
- **Dependencies**: What domain must precede another? What's prerequisite?
- **Hierarchy**: What's foundation vs built on foundation?
- **Connections**: How do domains influence each other?
- **Bottlenecks**: Where is flow constrained?
- **Integration points**: Where must domains coordinate?

---

## Domain Identification Process

### Functional Domain Categories
```
Production Domains:
├─ Manufacturing/Operations
├─ Logistics/Supply Chain
├─ Quality/Testing
└─ Materials/Resources

Customer Domains:
├─ Marketing
├─ Sales
├─ Support/Service
└─ User Experience

Product Domains:
├─ Engineering/Development
├─ Design
├─ Product Management
└─ Research

Enabling Domains:
├─ Finance
├─ HR/People
├─ IT/Technology
├─ Legal/Compliance
└─ Learning/Improvement
```

### How to Identify Problem-Specific Domains
1. **Ask: What capabilities are needed?**
   - To deliver the product/service?
   - To manage people?
   - To manage resources?
   - To learn and improve?

2. **Ask: What functions must occur?**
   - What must be built/made?
   - What must be sold/delivered?
   - What must be supported?
   - What must be measured?

3. **Ask: Who does what?**
   - What teams exist?
   - What are their accountabilities?
   - What's missing?

4. **Ask: What could fail?**
   - What if this domain doesn't work?
   - What cascades from that failure?

---

## Dependency Mapping

### Types of Dependencies
```
Sequential Dependencies:
A → B → C
(B can't start until A done; C can't start until B done)

Parallel Dependencies:
A ┐
B ├→ D
C ┘
(A, B, C can happen simultaneously, but all must finish before D)

Resource Dependencies:
A requires resources from B
(B must provide budget/people/knowledge for A)

Information Dependencies:
A needs information from B before deciding
(B's output informs A's input)

Causal Dependencies:
Change in A causes ripple through B, C, D
(Understanding how changes cascade)
```

### Mapping Process
1. **List all domains identified**
2. **For each domain, ask:**
   - What must be done before this?
   - What blocks this domain?
   - What does this enable?
   - What's the minimum information needed to start?

3. **Identify critical paths**
   - What sequence is longest/most constrained?
   - What's the bottleneck?
   - What's on the critical path to completion?

4. **Look for hidden dependencies**
   - What's assumed but not explicit?
   - What fails if someone isn't aware?
   - What informal dependencies exist?

---

## Execution Sequencing

### The Sequencing Question
"What order can we do things such that what comes later has what it needs from what comes before?"

### Sequencing Strategies

**Strategy 1: Sequential (One after another)**
```
Phase 1: Domain A (creates foundation)
Phase 2: Domain B (depends on A)
Phase 3: Domain C (depends on B)
Phase 4: Domain D (depends on C)

Use when: Heavy dependencies, prerequisites essential
Risk: Long timeline
```

**Strategy 2: Parallel (Independent domains simultaneously)**
```
Phase 1 (Parallel):
├─ Domain A
├─ Domain B
├─ Domain C
└─ Domain D

Phase 2: Integration of A, B, C, D

Use when: Domains are independent
Benefit: Shorter timeline
```

**Strategy 3: Mixed (Some parallel, some sequential)**
```
Phase 1 (Parallel): Domain A + Domain B (independent)
Phase 2 (Parallel): Domain C + Domain D (depend on 1 & 2, but not each other)
Phase 3 (Sequential): Domain E (depends on all above)
Phase 4: Integration

Use when: Complex dependency mix
Best for: Most real-world problems
```

### Creating the Execution Plan
1. **Identify critical constraints**
   - What must be true before anything else starts?
   - What's the hardest/longest/most risky?

2. **Identify independent work streams**
   - What can happen in parallel?
   - How do they coordinate?

3. **Identify integration points**
   - Where must domains come together?
   - What handoffs are required?
   - How do we verify alignment?

4. **Build the timeline**
   - Phase by phase
   - With clear entry/exit criteria
   - With integration checkpoints

---

## Integration Point Analysis

### What Are Integration Points?
Places where:
- Two domains must coordinate
- One domain's output becomes another's input
- Decisions affect multiple domains
- Communication is critical
- Misalignment causes cascading problems

### Finding Integration Points
1. **Trace dependencies**
   - Where does Domain A's output go to Domain B?
   - Where does Domain B need clarity from Domain C?

2. **Identify decision points**
   - What decisions are made in one domain?
   - Who else must know about them?
   - What can't proceed without alignment?

3. **Recognize communication needs**
   - What information must flow?
   - Who needs to know what?
   - How do we ensure shared understanding?

4. **Design handoffs**
   - How does work transfer from one domain to another?
   - What makes a successful handoff?
   - What goes wrong in bad handoffs?

### Integration Point Protocol
```
For each integration point:

Domains: A ↔ B

What's being exchanged:
├─ Information (what does each need to know?)
├─ Resources (budget, people, time)
├─ Decisions (what must be decided before proceeding?)
└─ Quality standards (what's success criteria?)

Timing:
├─ When does information need to flow?
├─ What's the sequence?
└─ What could cause delays?

Governance:
├─ Who decides if information is adequate?
├─ How do we escalate disagreements?
└─ How do we verify successful handoff?
```

---

## Structural Analysis Template

```markdown
## PROBLEM: [Description]

## DOMAINS IDENTIFIED
1. Domain 1: [Description & key functions]
2. Domain 2: [Description & key functions]
3. Domain 3: [Description & key functions]
...

## DEPENDENCY MAP
```
Domain 1 ──depends on──> Domain 2
                             │
                             ├──depends on──> Domain 3
                             │
                             └──depends on──> Domain 4
```

## CRITICAL PATH
[Longest/most constrained sequence]

## EXECUTION STRATEGY
Phase 1 (Duration):
├─ Domain A parallel with Domain B
└─ Entry criteria: X
  Exit criteria: Y

Phase 2 (Duration):
├─ Domain C sequential after Phase 1
└─ Entry criteria: Z
  Exit criteria: Integration verified

...

## INTEGRATION POINTS
### Point 1: Domain A ↔ Domain B
- Information exchange: [specific info]
- Timing: [when needed]
- Success criteria: [what makes it work]
- Risk if fails: [impact]

### Point 2: ...

## BOTTLENECKS
- Constraint 1: [what limits flow]
- Constraint 2: ...

## STRUCTURAL HEALTH CHECK
- [ ] All domains identified?
- [ ] Dependencies explicit?
- [ ] Sequence feasible?
- [ ] Integration points clear?
- [ ] Risks identified?
```

---

## Common Structural Patterns

### The Waterfall Pattern
```
Domain A → Domain B → Domain C → Domain D
[Phase 1] [Phase 2] [Phase 3] [Phase 4]
```
Use when: Heavy sequential dependencies
Risk: Long timeline, problems discovered late

### The Parallel Pattern
```
Domain A ┐
Domain B ├→ Integration
Domain C ┘
```
Use when: Domains are independent
Benefit: Fast timeline, issues visible early

### The Hub-and-Spoke Pattern
```
        ╭─ Domain A
        │
Domain X ─ Domain B
        │
        ╰─ Domain C
```
Use when: One domain is central (usually tech, finance, or people)
Risk: Center domain becomes bottleneck

### The Iterative Pattern
```
Version 1: Domains A, B, C
    ↓
Version 2: Add Domain D, improve A
    ↓
Version 3: Scale, optimize all
```
Use when: Complexity too high to sequence perfectly
Benefit: Learning loops, adaptive approach

---

## Structural Red Flags

**Warning Signs**:
- ❌ "We can't even identify our domains" (means lack of clarity)
- ❌ "Everything depends on everything" (means tight coupling)
- ❌ "We have 20+ domains" (means fragmentation)
- ❌ "Domain owners disagree on dependencies" (means assumption gaps)
- ❌ "We've never made explicit sequence" (means hidden dependencies)

**What to Do**:
1. **Host working session** to surface assumptions
2. **Create visible map** (whiteboard, diagram, doc)
3. **Test sequence** with SMEs
4. **Identify risks** in dependencies
5. **Build buffer** for uncertain dependencies

---

## When MARS Uses Structural Dimension

### In Problem Decomposition
"What's the basic architecture of this system?"

### In Feasibility Analysis
"Can we actually sequence this in the real world?"

### In Risk Identification
"Where are critical dependencies? Where will it break?"

### In Team Organization
"Who should own what? How do teams coordinate?"

### In Technology Selection
"What technology architecture matches our domain structure?"

---

## Connection to Other Dimensions

**Structural + Causal**:
"This dependency matters, but where's the leverage?"

**Structural + Temporal**:
"This sequence is necessary, but how long until we see benefit?"

**Structural + Cultural**:
"This org structure enables the work, but do people see why it matters?"

**Structural + Epistemic**:
"We've mapped structure, but what don't we know about it?"

**Structural + Integrative**:
"All domains are clear, but how do they form coherent whole?"
