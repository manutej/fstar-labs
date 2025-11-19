# CC2.0 VERIFY Function Skill

**Function**: VERIFY - Validation, Testing & Quality Assurance
**Category Theory**: Applicative Functor (pure, ap, parallel composition)
**Purpose**: Ensure correctness through testing, validation, and debugging
**Status**: ✅ Production-Ready (410 lines, all applicative laws verified)

**Local Installation**: `/Users/manu/cc2.0`
**Environment Variable**: `export CC2_HOME=/Users/manu/cc2.0`

---

## The Eternal Function

**Universal Question**: *Does it actually work?*

This function captures the timeless human activity of validating correctness. Across all domains and eras, humans verify that what was built matches what was intended and works as expected. VERIFY is the bridge from "what we have" to "what we trust."

### Universality Across Domains

| Domain | VERIFY Applies To | Core Operation |
|--------|-------------------|----------------|
| **Medicine** | Treatment validation, outcome assessment, adverse event monitoring | Verify clinical outcomes match treatment plan, patient improving |
| **Business** | Performance auditing, KPI validation, ROI verification | Verify business results match objectives, targets met |
| **Science** | Experimental validation, result replication, hypothesis testing | Verify results reproducible, hypothesis supported |
| **Education** | Assessment, evaluation, learning outcome measurement | Verify student learning matches objectives, mastery demonstrated |
| **Manufacturing** | Quality control, defect detection, specification compliance | Verify product meets specifications, defects within tolerance |
| **Software** | Unit testing, integration testing, validation | Verify code behavior matches specification, tests pass |
| **Law** | Evidence validation, precedent verification, argument soundness | Verify facts supported by evidence, reasoning sound |
| **Architecture** | Structural integrity, code compliance, safety inspection | Verify structure meets specs, safety codes satisfied |

### The Universal Pattern

```
Expected Outcome → Applicative Verification → Pass/Fail + Issues
    (Criteria)   →  (Parallel Checks)      →   (Results)
```

**Historical Precedent**:
- **Ancient Engineering**: Roman aqueduct testing (water pressure validation - 312 BCE)
- **Scientific Method**: Reproducibility requirements (1600s)
- **Industrial QC**: Statistical process control (1920s)
- **Software Testing**: Unit testing frameworks (1970s)

The function is eternal; the validation criteria change.

### Why This Works Universally

1. **Applicative Structure**: Independent checks run in parallel, accumulate results
2. **Pure**: Same input → same validation result (deterministic)
3. **Compositional**: `verify(check1) <*> verify(check2)` combines validations
4. **Accumulative**: Issues from multiple checks aggregate

Software testing = Medical outcome assessment = Manufacturing QC. Same structure, different criteria.

---

## When to Use This Skill

- ✅ **Validate correctness** - Ensure implementation meets requirements
- 🧪 **Run tests** - Execute test suites, measure coverage
- 🔍 **Debug issues** - Investigate failures, identify root causes
- 📊 **Quality assurance** - Validate metrics, compliance, standards
- ⚡ **Parallel validation** - Run independent checks concurrently

---

## Building Foundations for Your Domain

**Universal Function = Eternal Structure + Domain Foundations**

VERIFY is an eternal categorical structure (Applicative Functor). To use it in YOUR domain, construct **domain foundations** - validation criteria, test types, and quality metrics specific to your field.

### The Pattern

```
VERIFY (Universal Applicative)
    ⊗
Domain Foundations (Criteria + Checks)
    =
Domain Implementation
```

### Foundations by Domain

| Domain | Foundations to Construct | Examples |
|--------|-------------------------|----------|
| **Medicine** | Clinical criteria, outcome metrics, safety checks | Vital signs targets, pain scales, adverse event monitoring |
| **Business** | KPI targets, ROI thresholds, performance metrics | Revenue targets, satisfaction scores, market share |
| **Software** | Test frameworks, quality metrics, linters | **CC2.0 provides**: Jest, pytest, ESLint, complexity |
| **Manufacturing** | Quality standards, tolerance specs, defect limits | Dimensional tolerances, PPM rates, ISO compliance |
| **Education** | Learning objectives, mastery criteria, rubrics | 80% mastery, CCSS alignment, rubric scoring |
| **Science** | Hypothesis tests, p-values, replication | p < 0.05, effect size > 0.5, reproducibility |
| **Law** | Evidence standards, precedent alignment | Preponderance of evidence, stare decisis |
| **Architecture** | Building codes, structural loads, safety | UBC compliance, 1.5x safety factor, seismic |

---

## Related Skills

- **cc2-create**: Provides implementations to verify
- **cc2-reason**: Consumes verification failures to plan fixes
- **cc2-deploy**: Deploys verified implementations
- **cc2-learn**: Learns from verification patterns
- **cc2-orchestrator**: Composes VERIFY in test-driven workflows

---

## File References

**Implementation**: `${CC2_HOME}/src/functions/verify/VerifyFunction.ts` (410 lines)
**Tests**: `${CC2_HOME}/tests/laws/verify-applicative.test.ts`
**Documentation**: `${CC2_HOME}/functions/verify/FUNCTION.md`

---

**Status**: ✅ Production-Ready
**Categorical Rigor**: L7 (Maximum)
**Test Coverage**: 100% (all applicative laws verified)

---

*"To verify is to transform hope into certainty, to bridge belief and knowledge. VERIFY is the applicative functor from specification to confidence, the parallel composition that makes trust possible."*

— **CC2.0 Categorical Foundations**
