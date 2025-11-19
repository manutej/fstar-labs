---
description: Run Mixture of Experts (MoE) analysis with mercurio-orchestrator agent
---

Execute mercurio-orchestrator agent with MoE pattern for comprehensive multi-dimensional analysis.

**Pattern**: `moe::(||):sample^auto "<query>" document <path>`

**Usage**:
```bash
/mercurio "<query>"
/mercurio "<query>" --doc <path>
```

**Defaults**:
- Document: `/Users/manu/Documents/LUXOR/PROJECTS/LUMINA/moe-generalized-pattern.md`
- Expert count: Dynamically determined by agent based on query complexity
- Parallel execution: enabled

**Examples**:
```bash
/mercurio "Design authentication system"
/mercurio "Evaluate microservices architecture"
/mercurio "System design tradeoffs" --doc custom-pattern.md
```

---

# Task Execution

Launch mercurio-orchestrator agent with MoE workflow. The agent will:

1. **Analyze query complexity** and determine optimal expert count (typically 3-7)
2. **Select relevant expert perspectives** based on domain requirements
3. **Execute parallel analysis** with weighted confidence scoring
4. **Synthesize findings** with epistemic rigor and practical constraints

**Query**: {{QUERY}}
**Document**: `/Users/manu/Documents/LUXOR/PROJECTS/LUMINA/moe-generalized-pattern.md`

Execute pattern:
```
moe::(||):sample^auto "{{QUERY}}" document {{DOC_PATH}}
```

The agent autonomously determines:
- Number of experts needed (3 for simple, 5-7 for complex)
- Which expert perspectives to sample
- How to weight each expert's contribution
- Convergence criteria for synthesis

Analysis includes:
- Multi-dimensional expert perspectives (parallel execution)
- Weighted confidence scoring with uncertainty quantification
- Convergent synthesis with practical and ethical constraints
- Actionable recommendations with tradeoff analysis
