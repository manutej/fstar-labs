# F* Labs Claude Code Configuration

**Project-Specific Configuration** for formal verification research, category theory, and pedagogical content creation.

---

## Configuration Overview

This `.claude/` directory provides F* Labs with specialized skills, agents, and commands for:
- Formal verification and dependent type programming
- Category theory and categorical computing
- Functional programming across multiple paradigms
- Research synthesis and documentation generation
- Pedagogical content creation and diagram generation

---

## Inventory

**Last Updated**: 2025-11-18

| Category | Count | Purpose |
|----------|-------|---------|
| **Skills** | 15 | Domain expertise auto-loaded by context |
| **Agents** | 12 | Task-specific orchestrators |
| **Commands** | 8 | Slash commands for workflows |
| **Total** | **35** | Complete research ecosystem |

---

## Skills (15)

### Category Theory & Formal Methods
| Skill | Size | Purpose |
|-------|------|---------|
| **category-master** | 33KB | PhD-level category theory, proving theorems, universal properties |
| **discopy-categorical-computing** | ~50KB | String diagrams, QNLP, quantum circuits, compositional computing |
| **fstar-verification** | 82KB | F* language, dependent types, formal verification *(already in /skill/)* |

### Functional Programming
| Skill | Purpose |
|-------|---------|
| **functional-programming** | General FP principles, immutability, composition |
| **fp-ts** | TypeScript functional programming with fp-ts library |
| **typescript-fp** | TypeScript FP patterns, types, and techniques |
| **purify** | Purify-ts library for algebraic data types |
| **elm-development** | Elm language for functional web development |

### CC2 Universal Skills (Task-Agnostic Developer Functions)
| Skill | Purpose |
|-------|---------|
| **cc2-observe** | Systematic observation and data gathering |
| **cc2-reason** | Analytical reasoning and inference |
| **cc2-create** | Creative synthesis and artifact generation |
| **cc2-verify** | Validation, testing, and quality assurance |
| **cc2-learn** | Knowledge acquisition and skill development |
| **cc2-collaborate** | Team coordination and communication |
| **cc2-orchestrator** | Multi-skill workflow coordination |
| **cc2-meta-orchestrator** | Meta-level orchestration and strategy |

**CC2 Philosophy**: Universal developer functions that apply across ALL domains (medicine, business, science, education, manufacturing, software, law, architecture) with domain-specific adaptations.

---

## Agents (12)

### Research & Documentation
| Agent | Model | Purpose |
|-------|-------|---------|
| **deep-researcher** | Sonnet | Comprehensive technical research, codebase analysis, structured documentation |
| **docs-generator** | Sonnet | API documentation, JSDoc, user guides, technical writing |

### Multi-Perspective Synthesis (MERCURIO Suite)
| Agent | Model | Purpose |
|-------|-------|---------|
| **mercurio-orchestrator** | Opus | Comprehensive research synthesis across Mental/Physical/Spiritual planes |
| **mercurio-synthesizer** | Sonnet | Information integration and holistic knowledge maps |
| **mercurio-pragmatist** | Sonnet | Real-world viability and practical feasibility assessment |

### Systems Thinking (MARS Suite)
| Agent | Model | Purpose |
|-------|-------|---------|
| **mars-agent** (multi-file) | Opus | Multi-domain research synthesis, SpaceX-level innovation |
| **mars-architect** | Sonnet | System design enabling transformation at scale |
| **mars-innovator** | Sonnet | Breakthrough solutions, novel frameworks |
| **mars-executor** | Sonnet | Manifest designs into reality, navigate constraints |

### Meta-Architecture
| Agent | Model | Purpose |
|-------|-------|---------|
| **meta2** | Opus | Universal meta-meta-prompt generator, categorical frameworks |
| **api-architect** | Sonnet | RESTful API design, database schemas, OpenAPI specs |

---

## Commands (8)

### Extended Reasoning
| Command | Purpose |
|---------|---------|
| **/think** | Sequential-thinking MCP with beautiful formatting |
| **/sequential-thinking** | Activate sequential thinking for systematic problem-solving |

### Research & Synthesis
| Command | Purpose |
|---------|---------|
| **/mercurio** | Run Mixture of Experts (MoE) analysis with mercurio-orchestrator |
| **/mars** | Multi-Agent Research Synthesis for complex operations |
| **/ctx7** | Quick Context7 library documentation lookup |

### Pedagogical Content
| Command | Purpose |
|---------|---------|
| **/diagram-coordinator** | Coordinate with agents to generate educational diagrams |
| **/diagram-from-file** | Generate educational diagram from source file |
| **/cheatsheet** | Generate engaging cheat sheets for commands/tools |

---

## Usage Patterns

### 1. Formal Verification Workflow

```bash
# Skills auto-load when you reference F*, dependent types, or verification
"Write an F* function proving list reversal correctness"
# → fstar-verification skill activates

# For category theory reasoning
"Prove this functor preserves limits using universal properties"
# → category-master skill activates

# For compositional computing
"Create a QNLP pipeline with DisCoPy"
# → discopy-categorical-computing skill activates
```

### 2. Research & Documentation

```bash
# Deep research on new technology
/ctx7 coq  # Look up Coq documentation first
# Then use agent for comprehensive analysis
Task(deep-researcher): "Research Coq proof assistant and write comparison with F*"

# Generate pedagogical content
/diagram-from-file FSTAR_META_PROMPTING_FRAMEWORK.md
/cheatsheet  # Generate F* syntax cheat sheet
```

### 3. Multi-Perspective Analysis

```bash
# MERCURIO: Three-plane synthesis
/mercurio "Analyze formal verification adoption in industry"
# → Mental (understanding), Physical (feasibility), Spiritual (ethics)

# MARS: Systems-level innovation
/mars "Design formal verification platform for critical systems"
# → Research → Synthesize → Apply → Optimize → Validate
```

### 4. CC2 Universal Skills

```bash
# CC2 skills auto-activate based on task type:
Skill(cc2-observe)      # When gathering data, reading code
Skill(cc2-reason)       # When analyzing, inferring patterns
Skill(cc2-create)       # When generating artifacts
Skill(cc2-verify)       # When testing, validating
Skill(cc2-learn)        # When acquiring new knowledge
Skill(cc2-collaborate)  # When coordinating work
Skill(cc2-orchestrator) # When managing multi-step workflows
```

### 5. Meta-Prompting & Framework Generation

```bash
# Generate categorical frameworks
Task(meta2): "Create 5-level meta-prompting framework for proof engineering"

# Multi-domain orchestration
Task(mars-agent): "Research proof automation techniques across Coq, Lean, Isabelle"
```

---

## Skill Selection Logic

### Automatic Activation
Skills auto-load when you mention relevant concepts:

| You mention... | Skill activates... |
|----------------|-------------------|
| F*, dependent types, refinement types | fstar-verification |
| Categories, functors, adjunctions | category-master |
| DisCoPy, string diagrams, QNLP | discopy-categorical-computing |
| fp-ts, Either, Option, Task | fp-ts |
| Elm, TEA, ports, subscriptions | elm-development |
| Reading code, exploring systems | cc2-observe |
| Analyzing patterns, debugging | cc2-reason |
| Writing code, generating docs | cc2-create |
| Testing, validation, CI/CD | cc2-verify |

### Explicit Reference
```bash
# Force skill activation when needed
Skill(category-master)  # For rigorous proofs
Skill(cc2-orchestrator) # For complex multi-step tasks
```

---

## Agent Selection Matrix

| Need | Agent | Why |
|------|-------|-----|
| Deep research report | deep-researcher | Systematic codebase analysis + structured docs |
| API documentation | docs-generator | JSDoc, OpenAPI, technical writing |
| Multi-perspective synthesis | mercurio-orchestrator | Mental/Physical/Spiritual integration |
| Holistic knowledge map | mercurio-synthesizer | Cross-source synthesis |
| Practical feasibility | mercurio-pragmatist | Real-world constraints |
| Systems-level innovation | mars-agent | SpaceX-level breakthrough thinking |
| System architecture | mars-architect | Transformation enablement at scale |
| Novel solutions | mars-innovator | Breakthrough frameworks |
| Execution under constraints | mars-executor | Ship designs to reality |
| Meta-prompting framework | meta2 | Categorical meta-meta-prompts |
| API/DB design | api-architect | RESTful patterns, schemas |

---

## Integration with F* Labs

### Skill Alignment
- **fstar-verification** (82KB in `/skill/`) - Core F* expertise
- **category-master** (33KB) - Theoretical foundations for verification
- **discopy-categorical-computing** - Computational category theory
- **CC2 universal skills** - Task-agnostic developer functions

### Agent Orchestration
```bash
# Research new proof technique
Task(deep-researcher): "Research Liquid Types and compare with F* refinement types"

# Generate comprehensive comparison
Task(mercurio-synthesizer): "Synthesize formal methods landscape (F*, Coq, Lean, Agda)"

# Create pedagogical materials
/diagram-coordinator "Create visual guide to F* effect system"
/cheatsheet  # Generate F* syntax reference
```

### Command Workflows
```bash
# Extended reasoning for proof strategies
/think  # Use sequential-thinking for complex proof planning

# Library documentation
/ctx7 coq  # Look up Coq Proof Assistant
/ctx7 lean  # Look up Lean Theorem Prover

# Multi-domain research
/mars "Research formal verification in aerospace industry"
```

---

## Best Practices

### 1. **Progressive Disclosure**
- Skills auto-activate (no explicit calls needed for basic use)
- Reference skills explicitly only when forcing specific expertise
- Use agents for complex, multi-step research tasks

### 2. **Combining Skills & Agents**
```bash
# Good: Auto-activation
"Prove this F* function preserves invariants"
# → fstar-verification + cc2-reason auto-activate

# Better: Explicit orchestration for complex tasks
Task(deep-researcher): "Research F* extraction to OCaml, document patterns"
# → Uses fstar-verification + cc2-observe + cc2-create
```

### 3. **Leveraging CC2 Universal Skills**
The CC2 skills provide eternal developer functions:
- **Observation** before action (cc2-observe)
- **Reasoning** before decisions (cc2-reason)
- **Creation** with intention (cc2-create)
- **Verification** for quality (cc2-verify)
- **Learning** for growth (cc2-learn)
- **Collaboration** for scale (cc2-collaborate)
- **Orchestration** for complexity (cc2-orchestrator)

### 4. **Documentation Workflow**
```bash
# 1. Research
Task(deep-researcher): "Analyze F* standard library structure"

# 2. Generate docs
Task(docs-generator): "Create API documentation for verified modules"

# 3. Pedagogical content
/diagram-from-file verified-module.fst
/cheatsheet  # Generate syntax reference
```

---

## Directory Structure

```
fstar-labs/
├── .claude/
│   ├── CLAUDE.md                    # This file
│   ├── skills/                      # 15 domain skills
│   │   ├── category-master/
│   │   ├── discopy-categorical-computing/
│   │   ├── fp-ts/
│   │   ├── functional-programming/
│   │   ├── typescript-fp/
│   │   ├── purify/
│   │   ├── elm-development/
│   │   ├── cc2-observe/
│   │   ├── cc2-reason/
│   │   ├── cc2-create/
│   │   ├── cc2-verify/
│   │   ├── cc2-learn/
│   │   ├── cc2-collaborate/
│   │   ├── cc2-orchestrator/
│   │   └── cc2-meta-orchestrator/
│   ├── agents/                      # 12 specialized agents
│   │   ├── deep-researcher.md
│   │   ├── docs-generator.md
│   │   ├── mercurio-orchestrator.md
│   │   ├── mercurio-synthesizer.md
│   │   ├── mercurio-pragmatist.md
│   │   ├── mercurio-agent/          # Multi-file agent
│   │   ├── mars-agent/              # Multi-file agent
│   │   ├── mars-architect.md
│   │   ├── mars-innovator.md
│   │   ├── mars-executor.md
│   │   ├── meta2.md
│   │   └── api-architect.md
│   └── commands/                    # 8 slash commands
│       ├── think.md
│       ├── sequential-thinking.md
│       ├── mercurio.md
│       ├── mars.md
│       ├── ctx7.md
│       ├── diagram-coordinator.md
│       ├── diagram-from-file.md
│       └── cheatsheet.md
├── skill/                           # F* verification (82KB)
├── README.md                        # Lab overview
├── FSTAR_META_PROMPTING_FRAMEWORK.md
└── MERCURIO_THREE_PLANE_ANALYSIS.md
```

---

## Metrics

### Skills Coverage
| Domain | Skills | Total Size |
|--------|--------|------------|
| Category Theory | 2 | 83KB |
| Formal Verification | 1 | 82KB |
| Functional Programming | 5 | ~200KB |
| CC2 Universal | 8 | ~150KB |
| **Total** | **16** | **~515KB** |

*(Includes fstar-verification in /skill/)*

### Agent Capabilities
| Type | Count | Models |
|------|-------|--------|
| Research | 2 | Sonnet |
| Synthesis | 3 | Opus, Sonnet |
| Systems Thinking | 4 | Opus, Sonnet |
| Meta | 2 | Opus, Sonnet |
| **Total** | **12** | Mixed |

---

## Integration with Global Claude Config

This project config **extends** the global `~/.claude/` configuration:
- Global skills remain available
- Project skills take precedence when conflicts arise
- All MCP servers (Context7, Linear, Sequential-Thinking, etc.) work here
- Global agents and commands are accessible

**Philosophy**: Project-specific configuration for F* Labs research, with full access to global ecosystem.

---

## Quick Reference

### Essential Commands
```bash
/think              # Sequential reasoning
/mercurio           # Multi-perspective synthesis
/mars               # Systems-level research
/ctx7 <library>     # Library documentation
/diagram-from-file  # Generate educational diagrams
/cheatsheet         # Create syntax references
```

### Key Skills (Auto-Activate)
- **fstar-verification** - F* language expertise
- **category-master** - Rigorous theorem proving
- **discopy-categorical-computing** - Compositional computing
- **cc2-***  - Universal developer functions

### Primary Agents
- **deep-researcher** - Technical research reports
- **mercurio-orchestrator** - Multi-plane synthesis
- **mars-agent** - Systems innovation
- **meta2** - Meta-prompting frameworks

---

## Resources

- **F* Labs README**: Complete lab overview and learning path
- **Skill Documentation**: Each skill has comprehensive README + examples
- **Agent Documentation**: YAML frontmatter + detailed instructions
- **Command Documentation**: Slash command specs with examples

---

## Philosophy

F* Labs embodies **formal rigor + pedagogical clarity**:
- **Formal Verification**: Mathematical certainty (F*, category theory)
- **Pedagogical Content**: Progressive learning frameworks (L1-L7)
- **Research Excellence**: Deep synthesis (MERCURIO, MARS)
- **Universal Patterns**: Task-agnostic functions (CC2)

**Agent + Skills + Commands** = Complete formal verification research environment.

---

**Status**: Project configuration loaded ✅
**Last Updated**: 2025-11-18
**Skills**: 15 domain-specific + 1 in /skill/ = 16 total
**Agents**: 12 specialized orchestrators
**Commands**: 8 slash commands
**Total Resources**: 35 items + global ecosystem

---

*Formal methods meet pedagogical excellence.*
*Category theory powers compositional reasoning.*
*Universal patterns enable eternal developer functions.*
