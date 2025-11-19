---
name: mars
description: Multi-Agent Research Synthesis - Orchestrate complex multi-domain operations requiring systems-level intelligence. Use /mars to decompose strategic challenges, execute parallel research, synthesize integrated frameworks, and generate organizational blueprints that enable SpaceX-level innovation. Operations - research (parallel discovery), synthesize (integration), apply (real-world mapping), optimize (leverage points), validate (constraint testing), iterate (learning loops).
---

# /mars - Multi-Agent Research Synthesis Command

**Purpose**: Universal orchestration for complex operations requiring multi-dimensional analysis and systems-level intelligence.

**Agent**: MARS (Multi-Agent Research Synthesis)
**Model**: Opus (synthesis) | Sonnet (execution)
**Status**: Production-Ready

---

## Quick Start

```bash
# Multi-domain research (parallel execution)
/mars research "festival-operations" \
  --domains "logistics,talent,marketing,tech,finance"

# Synthesize research into blueprint
/mars synthesize docs/research/ \
  --constraints "budget:2M,timeline:3months"

# Optimize existing system
/mars optimize "emergency-department" \
  --mode optimization

# Validate blueprint against reality
/mars validate docs/blueprint.md "real-context"
```

---

## Command Structure

```bash
/mars <operation> <scope> [options]
```

### Operations

| Operation | Purpose | Output |
|-----------|---------|--------|
| `research` | Multi-domain parallel discovery | Domain research extracts |
| `synthesize` | Integrate findings into unified framework | Systems blueprint |
| `apply` | Map framework to real-world context | Executable plan |
| `optimize` | Find leverage points for improvement | Optimization roadmap |
| `validate` | Test blueprint against constraints | Feasibility report |
| `iterate` | Learn from execution results | Learnings + improvements |

---

## 1. Research Operation

**Purpose**: Orchestrate parallel multi-domain research

```bash
/mars research <problem-description> \
  --domains <comma-separated-list> \
  --constraints <key:value,key:value> \
  --budget <total-tokens> \
  --output <path>
```

### Parameters

- `<problem-description>`: Brief description or slug
- `--domains`: Domains to research (logistics, tech, people, finance, marketing, legal, etc.)
- `--constraints`: Hard/soft constraints (budget:2M, timeline:3months, capacity:50k)
- `--budget`: Total token budget (default: 30K)
- `--output`: Output directory (default: docs/)

### Example 1: Festival Operations

```bash
/mars research "festival-operations-blueprint" \
  --domains "logistics,talent,marketing,technology,finance" \
  --constraints "budget:2M,timeline:3months,attendance:50k,venue:downtown" \
  --output docs/festival/
```

**Execution Flow**:
```
1. MARS decomposes into 5 domains
2. Queries consciousness for optimal budgets
3. Generates Hekat DSL query:
   (deep-researcher || deep-researcher || deep-researcher || api-architect || deep-researcher) :
     "Research festival operations across domains with constraints"

4. Orchestrates parallel execution:
   ├─ Logistics research (5.5K budget, 450-word extract)
   ├─ Talent research (5K budget, 400-word extract)
   ├─ Marketing research (4.5K budget, 400-word extract)
   ├─ Technology design (6K budget, 500-word extract)
   └─ Finance analysis (4K budget, 350-word extract)

5. Outputs:
   docs/festival/logistics-research.md
   docs/festival/talent-research.md
   docs/festival/marketing-research.md
   docs/festival/technology-research.md
   docs/festival/finance-research.md
   docs/festival/research-summary.md (execution metadata)
```

**Token Budget**: ~25K actual (30K budgeted with buffer)
**Execution Time**: ~4-6 minutes (parallel)

### Example 2: Organizational Transformation

```bash
/mars research "manufacturing-transformation" \
  --domains "process,technology,workforce,quality,supply-chain,finance,safety,continuous-improvement" \
  --constraints "union:yes,legacy-systems:yes,budget:500k,timeline:12months" \
  --output docs/manufacturing/
```

**Outputs**: 8 domain research documents + summary (40K tokens, ~8 min)

---

## 2. Synthesize Operation

**Purpose**: Integrate multi-domain research into unified systems blueprint

```bash
/mars synthesize <research-directory> \
  --constraints <key:value> \
  --mode <synthesis|application|optimization> \
  --validate \
  --output <path>
```

### Parameters

- `<research-directory>`: Path to domain research docs
- `--constraints`: Real-world constraints to consider
- `--mode`: synthesis (default), application (real-world mapping), optimization (leverage points)
- `--validate`: Run constraint validation checks
- `--output`: Output file (default: docs/integrated-blueprint.md)

### Example 1: Festival Blueprint Synthesis

```bash
/mars synthesize docs/festival/research/ \
  --constraints "budget:2M,timeline:3months,venue:sherbrooke-downtown" \
  --mode synthesis \
  --validate \
  --output docs/festival/integrated-blueprint.md
```

**Execution Flow**:
```
1. MARS reads all domain research extracts (~2,500 words total)

2. Synthesis (Opus-level reasoning):
   - Cross-domain pattern recognition
   - Integration point mapping (talent → marketing → logistics → tech)
   - Constraint interaction analysis (budget limits tech, tech constrains logistics)
   - Feedback loop design (operational, tactical, strategic)
   - Leverage point identification (Meadows hierarchy)
   - Risk analysis (what could fail?)

3. Generates integrated blueprint:
   ├─ Executive Summary (problem, insights, approach)
   ├─ Domain Analysis (logistics, talent, marketing, tech, finance)
   ├─ Systems Synthesis (cross-domain insights, integration architecture)
   ├─ Organizational Design (structure, decision rights, metrics)
   ├─ Implementation Roadmap (Phase 1/2/3 with timeline)
   ├─ Risk Analysis (identified risks, mitigation strategies)
   ├─ Validation Framework (how to test in bounded system)
   └─ Appendices (detailed research, references, tools)

4. Validates against constraints:
   ✅ Budget: Within $2M (breakdown by phase)
   ✅ Timeline: Achievable in 3 months (critical path analysis)
   ⚠️ Venue capacity: May need overflow plan for 50K+
   ✅ Technology: Compatible with existing systems

5. Outputs:
   docs/festival/integrated-blueprint.md (3,500 words)
   docs/festival/synthesis-metadata.yaml (token accounting, learnings)
```

**Token Budget**: 12-15K
**Execution Time**: ~3-5 minutes

### Example 2: Manufacturing Transformation Blueprint

```bash
/mars synthesize docs/manufacturing/research/ \
  --constraints "union:yes,regulatory:osha,budget:500k" \
  --mode synthesis \
  --output docs/manufacturing/transformation-blueprint.md
```

**Output**: Comprehensive transformation plan with org redesign, metrics, feedback loops

---

## 3. Apply Operation

**Purpose**: Map generic framework to specific real-world context

```bash
/mars apply <blueprint-file> <context-description> \
  --constraints <key:value> \
  --validate \
  --output <path>
```

### Parameters

- `<blueprint-file>`: Path to integrated blueprint
- `<context-description>`: Specific context (e.g., "FIMAV-2026", "Plant-B-Detroit")
- `--constraints`: Context-specific constraints
- `--validate`: Test against real constraints
- `--output`: Output file

### Example: Apply Festival Blueprint to FIMAV 2026

```bash
/mars apply docs/festival/integrated-blueprint.md "FIMAV-2026" \
  --constraints "actual-budget:1.8M,venue:downtown-sherbrooke,timeline:feb-to-may" \
  --validate \
  --output docs/festival/fimav-2026-plan.md
```

**Execution Flow**:
```
1. MARS reads integrated blueprint
2. Maps to specific context:
   - Budget adjusted: $2M blueprint → $1.8M actual (identify cuts)
   - Venue specific: Sherbrooke downtown venues (capacity, logistics)
   - Timeline specific: Feb-May (weather, permits, marketing windows)

3. Validates feasibility:
   ✅ Can deliver with 10% budget reduction (defer some tech features)
   ⚠️ Timeline tight for talent booking (recommend expedited process)
   ✅ Venue capacity adequate for 45K (scale back from 50K target)

4. Generates context-specific plan:
   - Adjusted scope and timeline
   - Risk mitigation for tight constraints
   - Phased approach if needed
   - Go/no-go recommendation

5. Outputs:
   docs/festival/fimav-2026-plan.md (feasibility analysis + adjusted plan)
```

**Token Budget**: 8-10K
**Execution Time**: ~2-3 minutes

---

## 4. Optimize Operation

**Purpose**: Find leverage points for system improvement

```bash
/mars optimize <system-description> \
  --constraints <key:value> \
  --goals <metric:target> \
  --output <path>
```

### Parameters

- `<system-description>`: Current system to optimize
- `--constraints`: Hard/soft constraints
- `--goals`: Optimization targets (e.g., throughput:2x, cost:-30%, satisfaction:80%)
- `--output`: Output file

### Example: Emergency Department Optimization

```bash
/mars optimize "hospital-emergency-department" \
  --constraints "patient-safety:critical,budget:500k,timeline:6months,staff:union" \
  --goals "wait-time:90min,satisfaction:80%,safety:zero-incidents" \
  --output docs/hospital/ed-optimization.md
```

**Execution Flow**:
```
1. MARS researches current state:
   - Patient flow analysis (intake → triage → treatment → discharge)
   - Bottleneck identification (triage? bed availability? discharge?)
   - Constraint mapping (safety regs, union rules, budget)

2. Applies Meadows leverage point hierarchy:

   Highest Leverage (Recommended):
   - Change system goal: From "process all patients" to "fast-track low acuity"
     Impact: 40% of patients bypass bottleneck
     Cost: Minimal (workflow redesign)
     ROI: 2x improvement in average wait time

   Medium Leverage:
   - Redesign feedback: Real-time bed status → dynamic staff allocation
     Impact: 20% better resource utilization
     Cost: $50K (software + training)

   Lower Leverage:
   - Adjust parameters: Hire 3 more nurses
     Impact: 10% improvement
     Cost: $300K/year

3. Generates optimization roadmap:
   - Phase 1 (Months 1-2): Fast-track workflow (high leverage, low cost)
   - Phase 2 (Months 3-4): Real-time feedback system (medium leverage)
   - Phase 3 (Months 5-6): Staffing adjustments if needed (lower leverage)

4. Models expected impact:
   - Current: 240 min average wait
   - After Phase 1: 140 min (-42%)
   - After Phase 2: 95 min (-60%)
   - After Phase 3: 85 min (-65%)

5. Outputs:
   docs/hospital/ed-optimization.md (roadmap with ROI analysis)
```

**Token Budget**: 10-12K
**Execution Time**: ~3-4 minutes

---

## 5. Validate Operation

**Purpose**: Test blueprint against real-world constraints

```bash
/mars validate <blueprint-file> <context> \
  --constraints <key:value> \
  --output <path>
```

### Parameters

- `<blueprint-file>`: Path to blueprint
- `<context>`: Real-world context to test against
- `--constraints`: Actual constraints
- `--output`: Output file

### Example: Validate Festival Blueprint

```bash
/mars validate docs/festival/integrated-blueprint.md "FIMAV-2026" \
  --constraints "budget:1.8M,venue:sherbrooke,permits:pending,timeline:tight" \
  --output docs/festival/fimav-feasibility.md
```

**Execution Flow**:
```
1. MARS reads blueprint assumptions:
   - Budget: $2M
   - Venue: Generic downtown
   - Permits: Assumed available
   - Timeline: 3 months

2. Tests against reality:
   ✅ Budget: $1.8M (90% of plan) → Feasible with minor cuts
   ⚠️ Venue: Sherbrooke has capacity limits → Need overflow plan
   🔴 Permits: Pending approval → BLOCKER (must resolve before proceeding)
   ⚠️ Timeline: 2.5 months actual → Tight but doable with expedited process

3. Risk analysis:
   HIGH: Permit approval timing (could delay entire project)
   MEDIUM: Venue capacity (mitigation: overflow venues, ticket caps)
   LOW: Budget shortfall (identified cuts that preserve quality)

4. Recommendations:
   - URGENT: Fast-track permit applications (engage legal, government relations)
   - HIGH: Secure overflow venues (contingency planning)
   - MEDIUM: Finalize budget cuts (defer non-critical tech features)
   - GO/NO-GO: Recommend "CONDITIONAL GO" pending permit resolution

5. Outputs:
   docs/festival/fimav-feasibility.md (go/no-go recommendation + risk mitigation)
```

**Token Budget**: 6-8K
**Execution Time**: ~2 minutes

---

## 6. Iterate Operation

**Purpose**: Learn from execution results and improve

```bash
/mars iterate <execution-results-file> \
  --consciousness-query \
  --output <path>
```

### Parameters

- `<execution-results-file>`: Post-execution analysis
- `--consciousness-query`: Query for similar historical patterns
- `--output`: Output file with learnings

### Example: Post-Festival Learning

```bash
/mars iterate docs/festival/execution-results.md \
  --consciousness-query \
  --output docs/festival/learnings-and-improvements.md
```

**Execution Flow**:
```
1. MARS reads execution results:
   - What was planned vs what happened
   - Successes (what worked well?)
   - Failures (what didn't work?)
   - Surprises (what was unexpected?)

2. Root cause analysis (5 Whys):
   Problem: "Ticket sales slower than expected"
   Why? Marketing campaign started too late
   Why? Talent booking delayed confirmation
   Why? Contract negotiations took longer than planned
   Why? Legal review process was underestimated
   Why? No historical data on contract timelines
   Root cause: Lack of feedback loop from previous events

3. Identifies learnings:
   ✅ Fast-track workflow reduced wait times by 45% (replicate)
   ❌ Underestimated legal review time (build in 2x buffer next time)
   ✅ Real-time dashboards enabled rapid adjustments (expand to more metrics)
   🔴 Permit delays almost derailed project (start 6 months early next time)

4. Updates consciousness:
   Pattern: festival-operations
   Success rate: 85% (ticket sales, satisfaction)
   Token efficiency: 72% (better than expected 68%)
   Learnings:
     - Legal/permits take 2x longer than estimated
     - Fast-track workflows are highest leverage
     - Real-time feedback is critical success factor

5. Recommendations for next cycle:
   - Start permit process 6 months early (not 3)
   - Build legal review buffer (2x estimates)
   - Invest in real-time dashboard expansion
   - Replicate fast-track workflow across all processes

6. Outputs:
   docs/festival/learnings-and-improvements.md
   consciousness-update.yaml (for future pattern matching)
```

**Token Budget**: 8-10K
**Execution Time**: ~2-3 minutes

---

## Operational Modes

Use `--mode` flag to specify execution mode:

### Mode: research (default for `research` operation)
- Parallel discovery across domains
- Produces focused extracts (400-500 words each)
- Optimized for breadth

### Mode: synthesis (default for `synthesize` operation)
- Integration and framework generation
- Cross-domain pattern recognition
- Produces unified blueprint (3,000-4,000 words)

### Mode: application (for `apply` operation)
- Real-world context mapping
- Constraint testing and validation
- Produces feasibility analysis and adjusted plan

### Mode: optimization (for `optimize` operation)
- Leverage point identification (Meadows hierarchy)
- ROI analysis for interventions
- Produces optimization roadmap

---

## Options Reference

### Global Options (all operations)

| Option | Description | Default |
|--------|-------------|---------|
| `--budget <tokens>` | Total token budget | 30K |
| `--output <path>` | Output file/directory | docs/ |
| `--validate` | Run validation checks | false |
| `--consciousness-query` | Query historical patterns | false |

### Research-Specific Options

| Option | Description | Required |
|--------|-------------|----------|
| `--domains <list>` | Comma-separated domain list | Yes |
| `--constraints <list>` | Key:value constraint pairs | No |

### Synthesis-Specific Options

| Option | Description | Default |
|--------|-------------|---------|
| `--mode <type>` | synthesis, application, optimization | synthesis |

### Optimize-Specific Options

| Option | Description | Required |
|--------|-------------|----------|
| `--goals <list>` | Metric:target pairs | Yes |

---

## Token Budgets (Typical)

| Operation | Typical Budget | Actual (70% efficiency) |
|-----------|----------------|-------------------------|
| Research (5 domains) | 30K | ~22K |
| Synthesize | 15K | ~11K |
| Apply | 10K | ~7K |
| Optimize | 12K | ~9K |
| Validate | 8K | ~6K |
| Iterate | 10K | ~7K |

**Full workflow** (research → synthesize → apply → validate):
- Budgeted: 63K
- Actual: ~46K (73% efficiency)
- Time: ~15-20 minutes

---

## Use Cases

### 1. Strategic Operations
```bash
# Festival, conference, product launch, military operation
/mars research "operation-name" --domains "relevant,domains"
/mars synthesize docs/research/
/mars apply docs/blueprint.md "specific-context"
```

### 2. Organizational Transformation
```bash
# Manufacturing, government, healthcare, startup
/mars research "transformation-challenge" --domains "process,tech,people,culture"
/mars synthesize docs/research/ --mode synthesis
/mars validate docs/blueprint.md "real-org-context"
```

### 3. System Optimization
```bash
# Supply chain, patient flow, software delivery, factory
/mars optimize "system-description" --goals "throughput:2x,cost:-30%"
/mars validate docs/optimization.md "real-system"
```

### 4. Continuous Improvement
```bash
# After any major execution
/mars iterate docs/execution-results.md --consciousness-query
```

---

## Integration with Hekat DSL

MARS automatically generates Hekat DSL queries for orchestration:

**Research operation** → Pattern 4 (Parallel)
```
(deep-researcher || deep-researcher || api-architect || deployment-orchestrator) :
  "Multi-domain research with constraints"
```

**Phased execution** → Pattern 5 (Mixed)
```
finance-research -> (logistics || talent || marketing) -> technology-design :
  "Sequential phases with parallel domains"
```

**High-stakes synthesis** → Pattern 7 (Ensemble)
```
sample^3 ; merge ; synthesize :
  "Multiple perspectives on critical decision"
```

---

## Consciousness Integration

MARS queries consciousness before execution:

```yaml
# Before research operation
consciousness_query: "festival-operations with 5 domains"
response:
  pattern: parallel_research_5_domains
  proven_budgets: [logistics:5.5K, talent:5K, marketing:4.5K, tech:6K, finance:4K]
  extract_sizes: 400-500 words
  efficiency: 68%
  learnings:
    - "Logistics needs more context (aim for 5.5K)"
    - "Finance is typically shortest (4K sufficient)"

# After execution
consciousness_update:
  actual_tokens: 22400
  efficiency: 74.7% (better than expected)
  learnings:
    - "This agent combination works exceptionally well"
    - "Extract quality was high, enabled better synthesis"
```

---

## Output Format

All MARS operations produce structured Markdown documents:

```markdown
# [Operation] - [Title]

## Executive Summary
- Problem definition
- Key insights
- Recommended approach
- Expected outcomes

## [Domain/Section 1]
...

## [Domain/Section 2]
...

## Systems Synthesis (for synthesize operation)
- Cross-domain insights
- Integration architecture
- Feedback loops
- Leverage points

## Organizational Design (when relevant)
- Structure recommendations
- Decision frameworks
- Metrics architecture

## Implementation Roadmap
- Phase 1/2/3 with timeline and resources

## Risk Analysis
- Identified risks
- Mitigation strategies

## Validation Framework
- Success metrics
- Learning mechanisms

## Appendices
- Detailed research
- References
- Tools and resources
```

---

## Best Practices

### 1. Start with Research
Always begin with `research` operation to gather domain knowledge before synthesis.

### 2. Validate Early and Often
Use `--validate` flag to catch constraint violations early.

### 3. Query Consciousness
Use `--consciousness-query` to leverage historical patterns and budgets.

### 4. Iterate After Execution
Always run `iterate` operation post-execution to capture learnings.

### 5. Budget Appropriately
- Simple problems: 20-30K tokens
- Complex problems: 50-70K tokens
- Multi-phase problems: 100K+ tokens (use multiple sessions)

### 6. Be Specific with Constraints
More specific constraints → better validation → higher success rate

### 7. Use Bounded Systems for Validation
Test frameworks in small-scale environments before full deployment.

---

## Examples Gallery

### Example 1: Complete Festival Workflow
```bash
# Phase 1: Research (5 domains, parallel)
/mars research "electronic-music-festival" \
  --domains "logistics,talent,marketing,technology,finance" \
  --constraints "budget:2M,timeline:3mo,capacity:50k" \
  --output docs/festival/

# Phase 2: Synthesize into blueprint
/mars synthesize docs/festival/research/ \
  --mode synthesis \
  --validate \
  --output docs/festival/blueprint.md

# Phase 3: Apply to specific context
/mars apply docs/festival/blueprint.md "FIMAV-2026" \
  --constraints "budget:1.8M,venue:sherbrooke" \
  --output docs/festival/fimav-plan.md

# Phase 4: Validate feasibility
/mars validate docs/festival/fimav-plan.md "FIMAV-2026" \
  --constraints "permits:pending,timeline:2.5mo" \
  --output docs/festival/feasibility.md

# Phase 5: Post-event learning
/mars iterate docs/festival/execution-results.md \
  --consciousness-query \
  --output docs/festival/learnings.md
```

### Example 2: Manufacturing Transformation
```bash
# Research transformation domains
/mars research "plant-transformation" \
  --domains "process,technology,workforce,quality,supply-chain,safety" \
  --constraints "union:yes,budget:500k,timeline:12mo" \
  --output docs/manufacturing/

# Synthesize transformation blueprint
/mars synthesize docs/manufacturing/research/ \
  --mode synthesis \
  --output docs/manufacturing/blueprint.md

# Optimize for specific KPIs
/mars optimize "production-line-A" \
  --goals "throughput:2x,quality:95%,cost:-20%" \
  --output docs/manufacturing/optimization.md
```

### Example 3: Emergency Department Redesign
```bash
# Research current state and best practices
/mars research "ed-redesign" \
  --domains "patient-flow,staffing,technology,quality,safety" \
  --constraints "union:yes,budget:500k,patient-safety:critical" \
  --output docs/hospital/

# Optimize system
/mars optimize "emergency-department" \
  --goals "wait-time:90min,satisfaction:80%,safety:zero-incidents" \
  --output docs/hospital/optimization.md

# Validate against reality
/mars validate docs/hospital/optimization.md "County-General-ED" \
  --constraints "staff:150,beds:40,volume:200-per-day" \
  --output docs/hospital/feasibility.md
```

---

## Troubleshooting

### Token Budget Exceeded
- **Symptom**: Operations exceed allocated budget
- **Solution**:
  - Query consciousness for historical budgets (`--consciousness-query`)
  - Reduce domain count (fewer domains per research operation)
  - Use `--budget` to allocate more tokens
  - Split into multiple sessions if >100K needed

### Low-Quality Extracts
- **Symptom**: Synthesis struggles due to incomplete research
- **Solution**:
  - Increase per-domain budget (aim for 5-6K per domain)
  - Be more specific in constraint definition
  - Query consciousness for optimal extract sizes

### Validation Failures
- **Symptom**: Blueprint doesn't pass constraint checks
- **Solution**:
  - Be more realistic with constraints in research phase
  - Use `--validate` earlier in workflow
  - Iterate on blueprint before applying to real context

### Consciousness Not Found
- **Symptom**: No historical patterns for this problem type
- **Solution**:
  - Use conservative budget estimates (assume 50% efficiency)
  - Document learnings carefully for future use
  - Start with simpler similar patterns to build consciousness

---

## Related Commands

- `/task-relay`: For manual agent orchestration (if MARS not suitable)
- `/hekat`: For direct Hekat DSL execution (when implemented)
- `/crew`: To discover available agents for domain research
- `/ctx7`: To enhance research with library documentation
- `/actualize`: To sync MARS agent updates

---

**File**: `/Users/manu/.claude/commands/mars.md`
**Version**: 1.0.0
**Status**: Production-Ready
**Agent**: MARS (Multi-Agent Research Synthesis)

**Next Steps**:
1. Test MARS with FIMAV festival blueprint
2. Validate token budgets against consciousness
3. Build consciousness entries for common patterns
4. Create workflow templates for common use cases
5. Integrate with Linear for project tracking
