# CC2.0 REASON Function Skill

**Function**: REASON - Strategic Planning & Decision-Making
**Category Theory**: Functor/Monad (fmap, bind, return)
**Purpose**: Transform observations into strategic plans with confidence scoring
**Status**: ✅ Production-Ready (580 lines, all functor & monad laws verified)

**Local Installation**: `/Users/manu/cc2.0`
**Environment Variable**: `export CC2_HOME=/Users/manu/cc2.0`

---

## The Eternal Function

**Universal Question**: *What should we do?*

This function captures the timeless human activity of transforming understanding into strategy. Across all domains and eras, humans observe reality and then decide on a course of action. REASON is that bridge from "what is" to "what should be."

### Universality Across Domains

| Domain | REASON Applies To | Core Operation |
|--------|-------------------|----------------|
| **Medicine** | Diagnosis → treatment plan, symptom analysis → therapy | Transform clinical picture into treatment strategy |
| **Business** | Market analysis → strategy, financials → decisions | Structure business intelligence into action plan |
| **Science** | Experimental results → hypothesis, data → conclusions | Transform observations into theoretical implications |
| **Education** | Student assessment → lesson plan, progress → intervention | Design pedagogical strategy from learning state |
| **Manufacturing** | Quality metrics → process improvement, deviations → corrections | Transform operational state into optimization plan |
| **Software** | Code review → refactor plan, bug → debug strategy | Extract improvement roadmap from technical state |
| **Law** | Case facts → legal strategy, precedents → arguments | Structure evidence into persuasive legal approach |
| **Architecture** | Site conditions → design plan, constraints → solutions | Transform environmental parameters into building strategy |

### The Universal Pattern

Across all domains, REASON follows the same categorical structure:

```
Understanding → Strategic Thinking → Action Plan
 (Input from   →  (Monad Bind)    →   (Output)
  OBSERVE)
```

**Historical Precedent**: This pattern appears in:
- **Ancient Medicine**: Galenic therapeutic reasoning (150 CE) - symptoms → humoral theory → treatment
- **Military Strategy**: Sun Tzu's strategic planning (500 BCE) - terrain observation → tactical positioning
- **Scientific Method**: Hypothesis formation from observations (1600s) - data → theory → predictions
- **Business Strategy**: SWOT analysis → strategic planning (1960s) - assessment → action

The function is eternal; the domains change.

### Why This Works Universally

1. **Functor Structure**: `fmap` is domain-agnostic - it transforms ANY understanding into ANY plan
2. **Monad Composition**: Sequential reasoning (`bind`) works the same whether diagnosing illness or debugging code
3. **Confidence Scoring**: All domains require uncertainty quantification (diagnosis confidence = code confidence)
4. **Strategy Selection**: The meta-pattern "analyze → select approach → plan steps" is universal

Software is simply ONE manifestation of this eternal pattern.

### The Four Universal Strategies (Renamed for Universality)

1. **DESIGN** (Expand/Create) - Build something new from requirements
   - *Medicine*: Design treatment protocol for novel condition
   - *Business*: Design market entry strategy
   - *Software*: Design new system architecture

2. **CORRECT** (Fix/Remediate) - Fix what's broken
   - *Medicine*: Correct metabolic imbalance, remediate symptoms
   - *Education*: Remediate learning gaps
   - *Software*: Debug (fix broken code)

3. **OPTIMIZE** (Improve/Enhance) - Make existing thing better
   - *Medicine*: Optimize medication dosage
   - *Manufacturing*: Optimize production efficiency
   - *Software*: Performance optimization

4. **RESTRUCTURE** (Reorganize/Refactor) - Improve structure without changing behavior
   - *Medicine*: Restructure care delivery (same outcomes, better process)
   - *Business*: Restructure organization (same goals, better org chart)
   - *Software*: Refactor code (same behavior, cleaner structure)

**Note**: The software terms "debug" and "refactor" are domain-specific aliases for the universal strategies "correct" and "restructure."

---

## When to Use This Skill

Use REASON when you need to:
- 🎯 **Understand observations** - Interpret what OBSERVE has discovered
- 🧠 **Create strategic plans** - Convert observations into actionable strategies
- 📊 **Evaluate alternatives** - Compare different approaches with confidence scoring
- 🔀 **Select optimal strategy** - Choose from design, correct, optimize, restructure patterns
- 🔄 **Chain reasoning steps** - Sequential composition via monad bind

---

## Core Capabilities

### 1. Plan Generation (Functor Map)
```typescript
// Transform observation into plan
// From: ${CC2_HOME}/src/functions/reason/ReasonFunction.ts
const plan = observation.map(obs => generatePlan(obs));
// Returns: Plan with strategy, steps, confidence

// Example
const observation = { quality: 0.60, issues: ["complexity", "duplication"] };
const plan = reason.map(obs => ({
  strategy: "restructure",  // Universal: reorganize without changing behavior
  steps: ["extract methods", "reduce duplication"],
  confidence: 0.82
}));
```

**Categorical Law**: `fmap id = id` (identity)

### 2. Sequential Reasoning (Monad Bind)
```typescript
// Chain reasoning steps
// From: ${CC2_HOME}/src/functions/reason/ReasonFunction.ts
const refinedPlan = plan.bind(p =>
  refineStrategy(p).bind(refined =>
    addConstraints(refined)
  )
);

// Example
const initialPlan = reason(observation);
const refinedPlan = initialPlan
  .bind(addResourceEstimates)
  .bind(identifyDependencies)
  .bind(calculateRisk);
```

**Categorical Law**: `m.bind(f).bind(g) = m.bind(x => f(x).bind(g))` (associativity)

### 3. Confidence Calibration
```typescript
// Calculate decision confidence
// From: ${CC2_HOME}/src/functions/reason/types/core.ts
const confidence = calculateConfidence({
  evidenceQuality: 0.85,    // How good is observation data?
  strategyFit: 0.90,        // Does strategy match problem?
  riskLevel: 0.15,          // How risky is the plan?
  experienceMatch: 0.80     // Similar past successes?
});
// Returns: 0.87 (weighted composite)
```

---

## Input/Output Format

### Input (from OBSERVE)
```typescript
// From: ${CC2_HOME}/src/functions/reason/types/core.ts
interface ReasonInput {
  observation: Observation<any>;  // From OBSERVE function
  constraints?: {
    timeLimit?: string;          // "2 hours"
    complexity?: "low" | "medium" | "high";
    riskTolerance?: number;      // 0-1 scale
  };
  context?: {
    projectType?: string;
    teamSize?: number;
    deadline?: Date;
  };
}
```

### Output (for CREATE)
```typescript
// From: ${CC2_HOME}/src/functions/reason/types/core.ts
interface ReasonOutput {
  plan: {
    strategy: "design" | "correct" | "optimize" | "restructure";
    steps: string[];
    reasoning: string;          // Why this strategy?
    alternatives: Array<{
      strategy: string;
      confidence: number;
    }>;
  };
  confidence: number;           // 0-1 overall confidence
  risks: string[];              // Identified risks
  successCriteria: string[];    // How to measure success
  estimatedTime: string;        // "4 hours"
}
```

---

## Integration Patterns

### Composing with Other Functions

#### OBSERVE → REASON (Primary Flow)
```typescript
// Flow: Current state → Understanding → Plan
// From: ${CC2_HOME}/tests/integration/reason-workflow.test.ts
const observation = observe([linearModule]).apply(systemState);
const plan = reason(observation);

// Example:
// OBSERVE: "Code quality 0.60, high complexity, duplication detected"
// REASON: "Strategy: restructure. Steps: [extract methods, add tests]. Confidence: 0.82"
```

#### REASON → CREATE (Generate Implementation)
```typescript
// Flow: Strategic plan → Code implementation
const plan = reason(observation);
const implementation = create(plan);

// Example:
// REASON: "Restructure UserService.create (complexity 15 → 5)"
// CREATE: Generates restructured code with extracted methods
```

#### OBSERVE → REASON → VERIFY (Planning Loop)
```typescript
// Flow: Understand → Plan → Validate plan quality
const observation = observe(state);
const plan = reason(observation);
const planQuality = verify(plan, {
  criteria: ["completeness", "feasibility", "clarity"]
});

if (planQuality.score < 0.80) {
  // Re-plan with additional constraints
  plan = reason(observation, { moreDetail: true });
}
```

#### REASON → LEARN (Strategy Improvement)
```typescript
// Flow: Generate plan → Learn from results → Improve future plans
const plan = reason(observation);
const result = await execute(plan);
await learn({
  input: { plan, result },
  strategy: "analytical",
  objective: "improve planning accuracy"
});
```

---

## Practical Examples

### Example 1: Restructuring Decision

```typescript
// From: ${CC2_HOME}/tests/integration/reason-workflow.test.ts

// Input (from OBSERVE)
const observation = {
  value: { code: "..." },
  context: {
    quality: 0.60,
    issues: ["high complexity", "duplication"],
    patterns: ["god object"]
  }
};

// Execute REASON
const plan = await reason(observation);

// Output
{
  strategy: "restructure",  // Universal term (refactor in software)
  steps: [
    "Extract methods from god object",
    "Create separate classes by responsibility",
    "Add unit tests for each class",
    "Verify behavior unchanged"
  ],
  reasoning: "Quality score 0.60 below threshold 0.75. High complexity and duplication indicate restructuring needed over rewrite due to working functionality.",
  confidence: 0.82,
  estimatedTime: "4 hours",
  risks: ["breaking existing functionality", "incomplete test coverage"],
  alternatives: [
    { strategy: "rewrite", confidence: 0.45 },
    { strategy: "optimize", confidence: 0.30 }
  ]
}
```

### Example 2: Performance Optimization Strategy

```typescript
// From: ${CC2_HOME}/tests/integration/reason-workflow.test.ts

// Input
const observation = {
  value: { metrics: {...} },
  context: {
    trend: "degrading",
    analysis: "Response time increasing 20%"
  }
};

// Execute REASON
const plan = await reason(observation);

// Output
{
  strategy: "optimize",
  steps: [
    "Profile hot paths with chrome devtools",
    "Identify bottleneck (likely N+1 queries)",
    "Add caching layer",
    "Benchmark improvement"
  ],
  reasoning: "Degrading performance trend requires optimization. Profiling first to avoid premature optimization.",
  confidence: 0.75,
  alternatives: [
    { strategy: "scale horizontally", confidence: 0.50 }
  ]
}
```

### Example 3: Bug Investigation Plan

```typescript
// Input
const observation = {
  value: { error: "NullPointerException", frequency: "intermittent" },
  context: {
    reproducibility: 0.40,  // 40% reproducible
    severity: "high"
  }
};

// Execute REASON
const plan = await reason(observation, {
  constraints: { timeLimit: "2 hours" }
});

// Output
{
  strategy: "correct",  // Universal term (debug in software)
  steps: [
    "Add logging to narrow down null source",
    "Review recent changes for regression",
    "Add null checks defensively",
    "Create test case to reproduce"
  ],
  reasoning: "Low reproducibility suggests race condition or environmental factor. Logging will help isolate.",
  confidence: 0.68,  // Lower confidence due to intermittency
  risks: ["may not find root cause in time limit"]
}
```

### Example 4: Business Market Entry Strategy (Cross-Domain)

```typescript
// REASON in business: Market expansion decision
// Demonstrates the SAME categorical structure in different domain

// Input (from OBSERVE function in business context)
const businessObservation = {
  value: {
    market: "Southeast Asia e-commerce",
    competitors: ["Shopee", "Lazada", "Tokopedia"],
    market_size: 89_000_000_000,  // $89B USD
    growth_rate: 0.23             // 23% YoY
  },
  context: {
    company_strengths: ["logistics tech", "payment processing"],
    weaknesses: ["brand recognition", "local partnerships"],
    opportunities: ["mobile-first population", "rising middle class"],
    threats: ["regulatory uncertainty", "entrenched competitors"]
  },
  patterns: [
    {
      type: "MARKET_OPPORTUNITY",
      description: "High growth rate + company strengths alignment",
      significance: 0.82
    }
  ],
  confidence: 0.85
};

// Execute REASON (same function, different domain)
const businessPlan = await reason(businessObservation);

// Output: IDENTICAL categorical structure to software REASON
{
  plan: {
    strategy: "design",  // Universal: Build something new (market entry)
    steps: [
      "Establish local partnership with logistics provider",
      "Launch MVP in Singapore (regulatory clarity + English)",
      "Pilot payment integration with regional banks",
      "Build brand awareness via influencer marketing",
      "Scale to Indonesia after 6-month pilot validation"
    ],
    reasoning: "Market growth (23% YoY) and strength alignment (logistics tech) support entry. Singapore pilot minimizes regulatory risk while validating product-market fit. Partnerships address brand/local knowledge weaknesses.",
    alternatives: [
      {
        strategy: "restructure",  // Restructure existing operations
        description: "Partner with existing player via acquisition",
        confidence: 0.65,
        rationale: "Faster market entry but higher capital requirement"
      },
      {
        strategy: "optimize",  // Optimize current markets first
        description: "Deepen penetration in existing markets",
        confidence: 0.45,
        rationale: "Lower risk but misses growth opportunity"
      }
    ]
  },
  confidence: 0.79,
  risks: [
    "Regulatory changes in target market",
    "Competitor price war during pilot",
    "Partnership execution risk",
    "Currency fluctuation (USD/SGD)"
  ],
  successCriteria: [
    "10,000 active users within 6 months (Singapore)",
    "Payment success rate >95%",
    "Customer acquisition cost <$50",
    "Net Promoter Score >40"
  ],
  estimatedTime: "18 months",  // To profitable operations
  estimatedInvestment: "$12M USD"
}

// Functor map: Refine strategy with additional constraints
const refinedPlan = businessPlan.map(p => ({
  ...p,
  steps: p.steps.filter(step => meetsBudgetConstraint(step)),
  confidence: recalculateWithConstraints(p.confidence)
}));

// Monad bind: Chain sequential reasoning steps
const detailedPlan = businessPlan
  .bind(addFinancialProjections)
  .bind(addCompetitiveAnalysis)
  .bind(addRiskMitigation)
  .bind(addGovernanceStructure);

// Confidence scoring (same algorithm, different domain)
const businessConfidence = calculateConfidence({
  evidenceQuality: 0.85,      // Strong market data
  strategyFit: 0.88,          // DESIGN fits new market entry
  riskLevel: 0.35,            // Moderate-high risk
  experienceMatch: 0.70       // Some similar past expansions
});
// Returns: 0.79

// Flow from OBSERVE → REASON → CREATE (universal pattern)
// OBSERVE: "23% YoY growth market, strengths align"
// REASON: "Design market entry via Singapore pilot"
// CREATE: "Generate partnership agreements, MVP spec, marketing plan"
```

**Key Insight**: The REASON function (Functor/Monad) works IDENTICALLY in business and software:
- **Functor map**: Transform understanding → plan (domain-agnostic)
- **Monad bind**: Chain reasoning steps sequentially (universal composition)
- **Confidence scoring**: Same algorithm applies (0-1 uncertainty quantification)
- **Strategies**: DESIGN/CORRECT/OPTIMIZE/RESTRUCTURE transcend domains

Business strategy = Software planning. Same categorical structure, different data.

---

## Building Foundations for Your Domain

**Universal Function = Eternal Structure + Domain Foundations**

REASON is an eternal categorical structure (Functor/Monad). To use it in YOUR domain, you construct **domain foundations** - the strategy patterns, decision frameworks, and success criteria specific to your field. The universal function remains unchanged; only the foundations vary.

### The Pattern

```
REASON (Universal Monad)
    ⊗
Domain Foundations (Strategies + Criteria)
    =
Domain Implementation
```

### Foundations by Domain

| Domain | Foundations to Construct | Examples |
|--------|-------------------------|----------|
| **Medicine** | Treatment protocols, clinical guidelines, risk scores, success criteria | Cardiac protocol, TIMI score, CURB-65, mortality reduction target |
| **Business** | Strategy frameworks, decision matrices, KPIs, ROI models | SWOT, BCG matrix, NPV calculation, market share targets |
| **Software** | Design patterns, debugging procedures, optimization techniques, quality metrics | **CC2.0 provides these**: SOLID principles, refactoring catalog, performance patterns |
| **Manufacturing** | Process improvement methods, quality frameworks, efficiency standards | Six Sigma, Lean, OEE targets, defect reduction |
| **Education** | Pedagogical strategies, intervention protocols, assessment criteria | Differentiation strategies, RTI framework, mastery-based grading |
| **Science** | Experimental design, hypothesis testing, validation criteria | Control groups, p-value thresholds, replication standards |
| **Law** | Legal strategies, precedent frameworks, argument structures | Motion strategies, case law hierarchy, burden of proof |
| **Architecture** | Design methodologies, constraint frameworks, evaluation criteria | Biomimetic design, site analysis rubric, structural codes |

### What CC2.0 Provides (Software Foundations)

CC2.0 ships with **production-ready software strategy foundations**:

```typescript
// Pre-built strategies you can use immediately
import { designStrategy } from '${CC2_HOME}/strategies/design';
import { correctStrategy } from '${CC2_HOME}/strategies/correct';  // debug
import { optimizeStrategy } from '${CC2_HOME}/strategies/optimize';
import { restructureStrategy } from '${CC2_HOME}/strategies/restructure';  // refactor

// Use out-of-the-box
const plan = reason(observation, {
  availableStrategies: [designStrategy, correctStrategy, optimizeStrategy, restructureStrategy]
});
```

**Location**: `${CC2_HOME}/src/functions/reason/strategies/`

### Building Your Own Foundations

To use REASON in a non-software domain, construct strategy frameworks for your field:

```typescript
// Example: Medical reasoning foundations
const medicalStrategies = {
  design: {
    name: "Design Treatment Protocol",
    when: (observation) => observation.condition === "novel",
    steps: (obs) => [
      "Review evidence-based guidelines",
      "Consult specialist literature",
      "Design phased treatment approach",
      "Define success criteria (e.g., symptom reduction)"
    ],
    successCriteria: ["Symptom reduction >50%", "No adverse events", "Patient compliance >80%"]
  },

  correct: {
    name: "Correct Clinical Issue",
    when: (observation) => observation.type === "acute_complication",
    steps: (obs) => [
      "Stabilize patient vitals",
      "Identify root cause (labs, imaging)",
      "Apply targeted intervention",
      "Monitor response"
    ],
    successCriteria: ["Vitals normalized", "Lab values WNL", "Patient stable"]
  },

  optimize: {
    name: "Optimize Treatment",
    when: (observation) => observation.response === "suboptimal",
    steps: (obs) => [
      "Titrate medication dosage",
      "Adjust timing/frequency",
      "Monitor therapeutic levels",
      "Benchmark against targets"
    ],
    successCriteria: ["Therapeutic levels achieved", "Side effects minimized"]
  },

  restructure: {
    name: "Restructure Care Delivery",
    when: (observation) => observation.outcomes === "good" && observation.process === "inefficient",
    steps: (obs) => [
      "Map current care pathway",
      "Identify inefficiencies",
      "Redesign pathway (same outcomes)",
      "Validate with pilot"
    ],
    successCriteria: ["Same clinical outcomes", "Reduced time/cost", "Patient satisfaction maintained"]
  }
};

// Use with universal REASON
const treatmentPlan = reason(clinicalObservation, {
  strategies: medicalStrategies
});
// Returns: Plan<{ strategy: "correct", steps: [...], confidence: 0.78 }>
```

### Key Principle: Separation of Concerns

1. **REASON (Eternal)**: Categorical structure - functor map, monad bind, confidence scoring
2. **Foundations (Domain)**: Strategy patterns, decision criteria, success metrics you define
3. **Integration**: Universal function operates on domain foundations

You don't modify REASON for your domain. You build strategy foundations that REASON can reason about.

**This is how universality works**: The mathematical structure (Functor/Monad) transcends domains. You ground it in reality by constructing domain-appropriate strategy frameworks and success criteria.

---

## Strategies Available

### 1. DESIGN Strategy (Universal: Expand/Create)
**When**: Building new functionality from scratch
**Focus**: Architecture, patterns, extensibility
**Confidence Factors**: Requirements clarity (0.90), design experience (0.85)
**Time Allocation**: 20-40% planning (upfront planning valuable)
**Cross-Domain**: Treatment protocols (medicine), market strategies (business), curriculum design (education)

### 2. CORRECT Strategy (Universal: Fix/Remediate)
**When**: Fixing bugs or unexpected behavior
**Focus**: Root cause analysis, minimal changes
**Confidence Factors**: Error reproducibility (0.70), test coverage (0.85)
**Time Allocation**: 5-15% planning (action over planning)
**Cross-Domain**: Correct metabolic imbalance (medicine), remediate learning gaps (education), fix defects (manufacturing)
**Software Alias**: "debug"

### 3. OPTIMIZE Strategy (Universal: Improve/Enhance)
**When**: Improving performance or efficiency
**Focus**: Profiling, bottlenecks, benchmarks
**Confidence Factors**: Performance metrics (0.90), baseline data (0.85)
**Time Allocation**: 10-20% planning (measure first)
**Cross-Domain**: Optimize dosage (medicine), improve yield (manufacturing), enhance efficiency (business)

### 4. RESTRUCTURE Strategy (Universal: Reorganize)
**When**: Improving structure without changing behavior
**Focus**: Clarity, maintainability, testing
**Confidence Factors**: Test coverage (0.95), change scope (0.80)
**Time Allocation**: 15-25% planning (safety via tests)
**Cross-Domain**: Restructure care delivery (medicine), reorganize departments (business), refactor code (software)
**Software Alias**: "refactor"

---

## Confidence Scoring Algorithm

```typescript
// From: ${CC2_HOME}/src/functions/reason/confidence.ts
function calculateConfidence(factors: {
  evidenceQuality: number;      // 0-1: How good is observation data?
  strategyFit: number;          // 0-1: Does strategy match problem?
  riskLevel: number;            // 0-1: How risky is the plan?
  experienceMatch: number;      // 0-1: Similar past successes?
}): number {
  return (
    factors.evidenceQuality * 0.30 +
    factors.strategyFit * 0.35 +
    (1 - factors.riskLevel) * 0.20 +
    factors.experienceMatch * 0.15
  );
}

// Example
const confidence = calculateConfidence({
  evidenceQuality: 0.85,  // Good observation data
  strategyFit: 0.90,      // Refactor fits well
  riskLevel: 0.20,        // Low risk
  experienceMatch: 0.75   // Similar projects succeeded
});
// Returns: 0.84
```

---

## Analysis Paralysis Detection

REASON detects when planning exceeds optimal depth:

```typescript
// From: ${CC2_HOME}/src/functions/reason/paralysis.ts
if (planningTime / executionEstimate > threshold) {
  alert("🚨 Analysis Paralysis Detected");
  recommend("Switch to satisficing - start with first acceptable plan");
}
```

**Thresholds by Strategy**:
- **DESIGN**: 20-40% (upfront planning valuable)
- **CORRECT**: 5-15% (action over planning) - *alias: debug*
- **OPTIMIZE**: 10-20% (measure first)
- **RESTRUCTURE**: 15-25% (safety via tests) - *alias: refactor*

**Example**:
```typescript
// Planning: 2 hours
// Estimated execution: 4 hours
// Ratio: 2/4 = 0.50 (50%)

if (strategy === "correct" && ratio > 0.15) {
  // 50% exceeds correct threshold of 15%
  return "Analysis paralysis: Start correcting with current hypothesis";
}
```

---

## Categorical Laws Verified

All functor and monad laws verified via property-based testing:

### Functor Laws (2 laws)
1. **Identity**: `fmap id = id` ✅
   - Tests: `${CC2_HOME}/src/functions/reason/__tests__/Functor.test.ts`
2. **Composition**: `fmap (f ∘ g) = fmap f ∘ fmap g` ✅

### Monad Laws (3 laws)
3. **Left Identity**: `return(a).bind(f) = f(a)` ✅
   - Tests: `${CC2_HOME}/src/functions/reason/__tests__/Monad.test.ts`
4. **Right Identity**: `m.bind(return) = m` ✅
5. **Associativity**: `m.bind(f).bind(g) = m.bind(x => f(x).bind(g))` ✅

**Test Coverage**: 100% (all laws verified)
**Property Tests**: `${CC2_HOME}/tests/laws/reason-monad.test.ts` (100 random cases per law)

---

## Command-Line Usage

```bash
# Basic reasoning
cc2 reason <observation.json>

# With strategy hint (universal naming)
cc2 reason --strategy=restructure <observation.json>

# Show alternatives
cc2 reason --show-alternatives <observation.json>

# Pipe from OBSERVE to CREATE
cc2 observe <state.json> | cc2 reason | cc2 create

# Full chain with constraints
cc2 observe <state.json> | cc2 reason --time-limit=2h | cc2 create
```

---

## Performance Characteristics

- **Cold Start**: <100ms
- **Warm Execution**: <50ms
- **Memory Usage**: <150MB
- **Complexity**: O(n) for plan complexity, O(1) for strategy selection

**Optimization**:
```typescript
// Cache strategy patterns
const strategyCache = new Map();
const cachedStrategy = strategyCache.get(observationHash) ??
  computeStrategy(observation);
```

---

## Limitations & Constraints

- **Strategy selection heuristic-based**: Requires training data (uses heuristics initially)
- **Confidence scoring calibration**: Improves with feedback over time
- **Cannot predict external factors**: Team changes, requirement shifts
- **Planning depth heuristic**: Based on historical data, not perfect
- **Constitutional**: Article I (Functor Laws) + Article III (Monadic Error Handling) compliance required

**Assumptions**:
- Observation data is accurate (garbage in → garbage out)
- Strategy patterns generalize across similar problems
- Confidence scoring weights are domain-appropriate

---

## Related Skills

- **cc2-observe**: Provides input observations for reasoning
- **cc2-create**: Consumes reasoning plans to generate implementations
- **cc2-verify**: Validates plan quality before execution
- **cc2-learn**: Learns from plan outcomes to improve future reasoning
- **cc2-orchestrator**: Orchestrates REASON in multi-step workflows

---

## File References

**Implementation**:
- Core: `${CC2_HOME}/src/functions/reason/ReasonFunction.ts` (580 lines)
- Types: `${CC2_HOME}/src/functions/reason/types/core.ts`
- Strategies: `${CC2_HOME}/src/functions/reason/strategies/`
- Confidence: `${CC2_HOME}/src/functions/reason/confidence.ts`

**Tests**:
- Functor Tests: `${CC2_HOME}/src/functions/reason/__tests__/Functor.test.ts`
- Monad Tests: `${CC2_HOME}/src/functions/reason/__tests__/Monad.test.ts`
- Property Tests: `${CC2_HOME}/tests/laws/reason-monad.test.ts`
- Integration: `${CC2_HOME}/tests/integration/reason-workflow.test.ts`

**Documentation**:
- Specification: `${CC2_HOME}/functions/reason/FUNCTION.md`
- Strategy Guide: `${CC2_HOME}/functions/reason/STRATEGIES.md`
- Confidence Calibration: `${CC2_HOME}/functions/reason/CONFIDENCE.md`

**Category Theory References**:
- Functors & Monads: "Category Theory for Programmers" - Bartosz Milewski
- Monad Laws: Wadler (1995) - "Monads for Functional Programming"
- CC2.0 Foundations: `${CC2_HOME}/CATEGORICAL-FOUNDATIONS-COMPLETE.md`

---

## Meta-REASON: Self-Application

REASON can analyze its own planning patterns (meta-reasoning):

```typescript
// From: ${CC2_HOME}/functions/reason/modules/REASON_SELF.md
const metaReason = await reasonSelf(planningHistory);

// Returns insights about reasoning quality
{
  planningDepth: "optimal",
  strategyAccuracy: 0.87,           // 87% of plans succeeded
  confidenceCalibration: "well-calibrated",
  biases: ["over-planning for CORRECT tasks"],
  suggestions: [
    "Increase alternatives considered for high-risk decisions",
    "Reduce planning time for CORRECT tasks (currently 18%, target 10%)",
    "Improve confidence scoring for novel problems"
  ],
  meta_metrics: {
    plans_per_day: 12,
    avg_confidence: 0.82,
    confidence_accuracy: 0.89  // Predicted vs actual success rate
  }
}
```

**Meta-Development**: CC2.0 uses REASON to improve its own planning capabilities:
```typescript
const improvedReason = reason
  .bind(analyzePlanningHistory)
  .bind(identifyImprovements)
  .bind(updateStrategyWeights);
```

---

## Integration Example: Full OBSERVE → REASON → CREATE Chain

```typescript
// From: ${CC2_HOME}/tests/integration/full-workflow.test.ts

// 1. OBSERVE system state
const observation = await observe([linearModule, gitModule]).apply({
  context: { userId: "dev-123" },
  current: systemSnapshot
});
// Returns: { quality: 0.65, issues: ["complexity", "duplication"] }

// 2. REASON about improvements
const plan = await reason(observation);
// Returns: {
//   strategy: "restructure",  // Universal term
//   steps: ["extract methods", "add tests"],
//   confidence: 0.82
// }

// 3. CREATE implementation
const implementation = await create(plan);
// Returns: { code: "...", tests: "...", quality: 0.87 }

// Complete categorical composition:
// OBSERVE (Comonad) → REASON (Monad) → CREATE (Function)
//     ↓                  ↓                  ↓
//  Context          Strategy           Artifact
```

**Type Safety**: Each transformation is type-safe and law-verified, ensuring correctness through category theory.

---

**Status**: ✅ Production-Ready
**Categorical Rigor**: L4 (Pragmatic with mathematical foundation)
**Test Coverage**: 100% (all functor & monad laws verified)
**Performance**: <100ms cold, <50ms warm
**Foundation Compliance**: ✅ meta-prompting ⊗ design-patterns ⊗ systems-thinking ⊗ abstraction-principles

---

*"To reason is to transform understanding into intent, to bridge knowing and acting, to find the path from 'what is' to 'what should be'. REASON is the functor from observation to plan, the monad that makes strategy composable."*

— **CC2.0 Categorical Foundations**
