# Bibliography and Research Citations
## Formal Verification Course Development

**Last Updated**: 2025-11-19
**Purpose**: Document all research sources used in course design to avoid confabulation and maintain academic rigor.

---

## Primary Research Sources

### Teaching Formal Methods - Challenges and Pedagogical Findings

**Key Finding**: Student difficulties with theorem proving are well-documented in research literature.

#### Source 1: "From the Coq Proof Assistant to Textbook Style" (arXiv:1803.01466)
- **URL**: https://arxiv.org/pdf/1803.01466
- **Authors**: [To be retrieved from paper]
- **Year**: 2018
- **Key Quote**: "Most computer science students have difficulties with proving theorems, and many of their solutions avoid formalisms or apply them in a wrong way. The blending of formal and more informal aspects of proofs is suspected to be the main obstacle to learning how to prove."
- **Application to Course**: This directly informed our pedagogical principle #2 (Example-Driven Learning) - we start with concrete examples before formal theory to avoid overwhelming students with formalism early.

#### Source 2: "Introduction to the Coq proof-assistant for practical software verification"
- **URL**: https://www.lri.fr/~paulin/LASER/course-notes.pdf
- **Authors**: Christine Paulin-Mohring
- **Institution**: Laboratoire de Recherche en Informatique (LRI)
- **Key Finding**: "All interactive theorem proving systems are relatively challenging to learn, and each has its own specific culture. Learning them is like learning a foreign language, and these topics are not easily digested without a background in (mathematical) logics."
- **Application to Course**: Informed our progressive L1→L7 framework and the emphasis on building intuition before formalism. We explicitly tell students "proofs are like a foreign language" in Week 1.

#### Source 3: "Comparison of Two Theorem Provers: Isabelle/HOL and Coq" (arXiv:1808.09701)
- **URL**: https://arxiv.org/abs/1808.09701
- **Authors**: [To be retrieved]
- **Year**: 2018
- **Key Findings**:
  - "Predefined Coq tactics have unwanted features - for instance split also works on goals like A →B →A∧B"
  - "The majority of Coq's learning resources (beyond the absolute basic level) are out of date by a few years, in the sense that they often use deprecated libraries"
  - "Isabelle's Isar is quite hard to get the hang of at first (mostly due to lack of documentation)"
- **Application to Course**: We committed to using current F* versions and up-to-date documentation. We also designed custom exercises that avoid confusing behavior in built-in tactics.

#### Source 4: Proof Assistants Stack Exchange - "Proof assistants for beginners - a comparison"
- **URL**: https://proofassistants.stackexchange.com/questions/43/proof-assistants-for-beginners-a-comparison
- **Community**: Proof Assistants Stack Exchange
- **Key Finding**: "Most of the tutorials for Coq/Lean/Isabelle do stuff with propositional logic or number theory, and students haven't gotten to the point where they would even know how to define basic structures."
- **Application to Course**: This directly influenced our choice to start with **practical examples** (safe division, array bounds checking) instead of abstract propositional logic. Week 1 focuses on refinement types for real-world use cases, not toy mathematical examples.

---

### Formal Methods Education - Academic Courses and Practices

#### Source 5: ETH Zurich - "Formal Methods and Functional Programming" (SS2024)
- **URL**: https://infsec.ethz.ch/education/ss2024/fmfp.html
- **Institution**: ETH Zurich, Information Security Group
- **Year**: 2024
- **Key Features**:
  - Used CodeExpert for programming exercises and auto-grading
  - Covered model checking and linear temporal logic
  - Combined formal methods with functional programming
- **Application to Course**: Informed our decision to include auto-grading infrastructure (pytest-based) for exercises in Weeks 1-6. Also validated our approach of combining FP concepts with verification.

#### Source 6: Coursera - "University Teaching" by University of Hong Kong
- **URL**: https://www.coursera.org/learn/university-teaching
- **Institution**: University of Hong Kong
- **Key Topics**: Effective university teaching, instructional design, assessment calibration
- **Application to Course**: General pedagogical principles applied to structuring 90-minute lectures with active learning components.

---

### Formal Methods Conferences and Recent Research

#### Source 7: ISoLA 2024 - 12th International Symposium on Leveraging Applications of Formal Methods
- **URL**: https://link.springer.com/book/10.1007/978-3-031-75387-9
- **Conference**: ISoLA 2024 (Crete, Greece, October 27-31, 2024)
- **Focus**: "Software Engineering Methodologies" and "Application Areas"
- **Key Finding**: Active community discussing adoption and use of rigorous tools for specification, analysis, verification, certification, construction, test, and maintenance of systems
- **Application to Course**: Kept us informed of current trends in formal methods tooling and industrial adoption (referenced in Week 11's research frontiers module).

#### Source 8: FormaliSE 2025 - Research Track
- **URL**: https://conf.researchr.org/home/Formalise-2025
- **Conference**: Formal Methods in Software Engineering (co-located with major SE conferences)
- **Key Finding**: "While formal methods research and practical software development historically had limited interactions, the outlook has improved with formal methods delivering more flexible techniques and tools that can support various aspects of the software development process"
- **Application to Course**: Reinforced the importance of showing **real-world relevance** (Principle #4) with HACL*, Project Everest case studies throughout the course.

#### Source 9: "Formal Verification of Code Conversion: A Comprehensive Survey" (MDPI 2024)
- **URL**: https://www.mdpi.com/2227-7080/12/12/244
- **Journal**: Computers (MDPI)
- **Volume**: 12, Issue 12, Article 244
- **Year**: 2024
- **Key Finding**: "Formal verification emerges as a crucial methodology to address limitations in traditional validation methods for code conversion"
- **Application to Course**: Motivated inclusion of F* code extraction topics (OCaml/F#/C) in Week 6, emphasizing that verified code can be extracted to practical targets.

---

### F* Language and Ecosystem Resources

#### Source 10: F* Official Tutorial
- **URL**: https://fstar-lang.org/tutorial/
- **Maintainers**: F* development team (MSR, Inria, CMU)
- **Status**: Official documentation, actively maintained
- **Application to Course**: Required reading for students, referenced throughout all 12 weeks. Our course extends and pedagogically structures the tutorial content.

#### Source 11: F* Zulip Community Chat
- **URL**: https://fstar-lang.zulipchat.com/
- **Community**: F* users, developers, researchers
- **Channels**: #beginner-questions, #teaching (instructor-only), #general
- **Application to Course**: Recommended in instructor guide as primary support channel for both instructors and students. Active community provides rapid technical support.

#### Source 12: HACL* - High-Assurance Cryptographic Library
- **URL**: https://github.com/hacl-star/hacl-star
- **Project**: Verified cryptographic library written in F* and extracted to C
- **Significance**: Used in production (Firefox, Linux kernel, etc.)
- **Application to Course**: Major case study in Week 8 (Cryptography and Constant-Time). Demonstrates real-world impact of formal verification.

---

## Methodology: Avoiding Confabulation

### What We Did RIGHT
✅ **Web research with citations**: Used WebSearch to discover authoritative sources
✅ **Direct quotes**: Extracted specific claims from academic papers
✅ **URL documentation**: Maintained links to all sources
✅ **Cross-validation**: Checked claims across multiple sources

### What We Avoided (Confabulation Risks)
❌ **Made-up statistics**: Initial instructor guide included claims like "30-40% of students struggle with installation" - these were estimates, not research-backed
❌ **Unverified percentages**: Claims like "80%+ of students struggle with error messages" - plausible but not evidence-based
❌ **Assumed timelines**: "10-20 hours to learn F*" - no empirical data to support this

### Correction Strategy
**For the instructor guide**:
1. Replace specific percentages with qualitative language: "Many students..." instead of "30-40%..."
2. Add disclaimers: "Based on teaching experience (not formal research)"
3. Mark estimates explicitly: "Estimated grading time: 10-15 min/student (adjust based on your experience)"

**For future content**:
1. Every factual claim must have a citation OR be marked as estimate/opinion
2. Use this bibliography as single source of truth
3. Update bibliography immediately when adding new research sources

---

## Research Gaps and Future Work

### Areas Where We Lack Citations
1. **Student struggle percentages**: No empirical studies on F* learning specifically
2. **Time estimates**: No published data on grading times, exercise completion times
3. **Optimal class size**: No research on ideal cohort sizes for proof-assistant courses
4. **Office hours effectiveness**: No studies on best practices for proof-assistant support

### Recommended Future Research
1. Conduct empirical study after first course offering (track student struggles, time-on-task)
2. Survey students about learning obstacles and effective teaching methods
3. Publish findings to contribute to formal methods education research
4. Share anonymized student data (with permission) to build evidence base

---

## Using This Bibliography

### For Course Developers
- **Adding content**: Check this file first - can you cite existing sources?
- **Making claims**: Ask "Is this cited?" If not, mark as estimate or find citation
- **Updating**: Add new sources in chronological order with full metadata

### For Instructors
- **Teaching**: Share relevant papers with students (e.g., "Coq to Textbook Style" paper)
- **Justifying pedagogy**: Use citations to explain why we structure course this way
- **Improving**: If you find better sources, submit PRs to update this bibliography

### For Students
- **Understanding context**: See why course is structured the way it is
- **Further reading**: Follow URLs to dive deeper into formal methods education research
- **Research opportunities**: Identify gaps and propose research projects

---

## Citation Format

**For academic papers**: Author(s). "Title". Journal/Conference. Year. URL.
**For technical documentation**: Project Name. "Page Title". Maintainer. URL.
**For community resources**: Platform. "Topic". Community. URL.

**All citations include**:
- Direct URLs for verification
- Key quotes (exact text, in quotation marks)
- Application to our course (how it informed design decisions)

---

## Acknowledgments

This course design was informed by:
- Academic research on teaching theorem proving (cited above)
- F* development team's official tutorial and documentation
- Pedagogical frameworks from Software Foundations and other successful proof-assistant courses
- Community wisdom from Proof Assistants Stack Exchange and F* Zulip

**We explicitly avoid**:
- Unsubstantiated claims about student performance
- Made-up statistics or percentages
- Assertions without evidence or citation

**Transparency principle**: When we estimate or opine, we say so explicitly.

---

## Version History

- **2025-11-19**: Initial bibliography created during course development
- Future updates: Track all research sources added during course iterations

---

**Maintained by**: Course development team
**Contact for corrections**: [To be added]
**License**: Same as main repository
