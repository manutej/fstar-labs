# Instructor Guide: Formal Verification with F*
## Complete Teaching Resource for 12-Week Course

**Welcome, Instructor!** 👋

This guide contains everything you need to teach the "Formal Verification with F*" course effectively. Whether you're new to formal methods pedagogy or an experienced educator, you'll find comprehensive resources, solutions, rubrics, and teaching tips.

---

## Quick Start

### First Time Teaching This Course?

1. **Read this README** (30 minutes) - Overview and philosophy
2. **Review Week 1 teaching notes** (`week_01_teaching_notes.md`) - See the format
3. **Try Exercise 1.1 yourself** - Experience student perspective
4. **Set up auto-grading** - Follow instructions in `solutions/`
5. **Customize timing** - Adapt to your institution's schedule

### Already Taught Formal Methods?

Jump directly to:
- **Pedagogical differences**: See "Course Philosophy" below
- **F*-specific tips**: See `troubleshooting.md`
- **Assessment rubrics**: See `rubrics/` directory

---

## How to Use This Guide

### Directory Structure

```
instructor_guide/
├── README.md (YOU ARE HERE)
│   └── Course philosophy, time management, overview
│
├── week_XX_teaching_notes.md (12 files, one per week)
│   ├── Learning objectives breakdown
│   ├── Lecture timing (90-min blocks)
│   ├── Discussion prompts
│   ├── Common misconceptions
│   ├── Troubleshooting FAQ
│   └── Exercise walkthrough hints
│
├── solutions/
│   ├── week_XX_all_solutions.fst (Complete F* code)
│   ├── pedagogical_notes.md (Why we teach it this way)
│   └── alternative_approaches.md (Different solution strategies)
│
├── rubrics/
│   ├── week_XX_rubric.md (Detailed point breakdown)
│   ├── mini_project_rubrics.md (5 mini-projects)
│   ├── midterm_rubric.md
│   ├── capstone_rubric.md
│   └── autograder/ (pytest scripts)
│
├── slides/
│   ├── week_XX_day_Y.md (Reveal.js compatible)
│   └── images/ (diagrams, screenshots)
│
├── assessment_guidelines.md
│   └── Calibration, partial credit, peer review tips
│
└── troubleshooting.md
    └── Common errors, installation issues, fixes
```

### For Each Week

**Before the week starts:**
1. Read `week_XX_teaching_notes.md` (20-30 min)
2. Run all exercises yourself (1-2 hours)
3. Review student submissions from previous week
4. Prepare slides (customize if needed)

**During the week:**
1. Follow timing guidelines (but adapt as needed!)
2. Use discussion prompts when energy dips
3. Walk around during exercises (formative assessment)
4. Take notes on common errors (improve for next year)

**After the week:**
1. Grade using rubrics (consistency matters!)
2. Identify patterns in student mistakes
3. Adjust next week's pace if needed
4. Update teaching notes with your observations

---

## Course Philosophy: Categorical Computing Pedagogy

### Core Principles

This course is designed around **7 principles** informed by research on teaching formal methods:

#### 1. **Progressive Mastery** (L1 → L7)
- Start with **concrete, practical** examples (safe division, array bounds)
- Build to **abstract, theoretical** concepts (monads, category theory)
- Resist urge to "explain everything upfront" - cognitive overload!
- Each level builds on previous; no skipping levels

**Why this works**: Research shows students struggle when formal/informal aspects are mixed too early. We delay theory until students have intuition.

#### 2. **Example-Driven Learning**
- **Every concept** introduced with runnable code first
- Theory follows practice (not vice versa!)
- "Type check first, understand later" is OK early on
- Formalization comes after informal understanding

**Example**: We teach refinement types by showing `nat` first, then explaining `{x:int | x >= 0}` syntax, THEN discussing SMT solvers.

#### 3. **Deliberate Error Introduction**
- We **intentionally cause type errors** in lectures
- Students see error messages and learn to debug
- "Construction-time safety" becomes visceral, not abstract
- Normalize failure as part of learning

**Teaching tip**: When live coding, deliberately make a mistake every 15 minutes. Say "Oops, let me fix that" - shows debugging is normal.

#### 4. **Real-World Relevance**
- Case studies from industry: **HACL\***, **Project Everest**, **EverParse**
- Motivate every concept with "Why would I use this?"
- Guest speakers from formal methods industry (if possible)
- Capstone projects address real problems

**Motivation matters**: Students tolerate steep learning curve IF they see payoff. Keep referring back to "This technique verified the TLS stack used by billions."

#### 5. **Active Learning** (60/40 rule)
- **60% of class time**: Students coding, proving, discussing
- **40% of class time**: Instructor lecturing, demonstrating
- Pair programming encouraged (research shows better retention)
- Code reviews teach as much as lectures

**Implementation**: For a 90-minute class:
- Lecture: 35-40 minutes (broken into chunks)
- Hands-on exercises: 45-50 minutes
- Discussion/debrief: 5-10 minutes

#### 6. **Peer Learning and Collaboration**
- Pair programming on exercises (rotate pairs weekly)
- Peer code reviews (with rubric) every 3 weeks
- "Expert helper" rotation: top students assist in office hours
- Capstone projects in teams (2-3 students)

**Research basis**: Theorem proving feels like a foreign language. Peers learning together build shared language faster.

#### 7. **Growth Mindset Culture**
- **Proofs are hard** - explicitly normalize struggle
- Celebrate productive failures ("Great debugging!")
- Grading rewards progress, not just correctness
- Office hours framed as "proof workshop", not remedial help

**Script for Day 1**: "This course is hard. You will get stuck. That's the point. Struggling with a proof for 30 minutes means you're learning. If you're not confused at least once per week, let me know - I'm not challenging you enough."

---

## Time Management Tips

### For Instructors

#### The 90-Minute Lecture Block

**DON'T:**
- ❌ Lecture for 90 minutes straight (cognitive limit is ~15 min)
- ❌ Skip breaks (brain needs rest)
- ❌ Rush through exercises ("We're running out of time!")
- ❌ Go overtime (students tune out)

**DO:**
- ✅ Break lecture into 10-15 minute chunks
- ✅ Alternate lecture and activity every 20-30 min
- ✅ Take a 5-min break at the 45-min mark
- ✅ End on time (respect students' schedules)

**Example 90-Minute Structure:**
```
[0-15 min]  Lecture Chunk 1 (review + intro)
[15-30 min] Live coding demo (instructor)
[30-35 min] BREAK (5 min - important!)
[35-50 min] Lecture Chunk 2 (deep dive)
[50-70 min] Hands-on exercise (students work)
[70-85 min] Debrief + solution walkthrough
[85-90 min] Preview next class + homework
```

#### Pacing Across the Semester

**Weeks 1-2** (L1 Novice)
- **Pacing**: SLOW - Build solid foundation
- **Focus**: Installation, setup, first successes
- **Common mistake**: Rushing to "interesting stuff"
- **Goal**: Every student gets a proof to work by Day 3

**Weeks 3-6** (L2-L4 Apprentice → Expert)
- **Pacing**: STEADY - Main content delivery
- **Focus**: Depth over breadth
- **Common mistake**: Covering too many topics shallowly
- **Goal**: Fluency with core verification patterns

**Weeks 7-10** (L5-L6 Master → Grandmaster)
- **Pacing**: FASTER - Students more independent
- **Focus**: Specialization and exploration
- **Common mistake**: Assuming all students are ready
- **Goal**: Students drive their own learning

**Weeks 11-12** (L7 Genius)
- **Pacing**: STUDENT-DRIVEN
- **Focus**: Capstone projects, research exposure
- **Common mistake**: Over-structuring this part
- **Goal**: Students teach you something

#### When You Fall Behind

**It WILL happen.** Here's how to adapt:

**Option 1: Skip Optional Content**
- Week 9 (Concurrency) can be skipped or assigned as reading
- Week 11 Track selection can be simplified
- Some mini-projects can become optional

**Option 2: Extend Deadlines**
- Push capstone to Week 13 (if semester allows)
- Make midterm take-home instead of in-class

**Option 3: Offload to Async**
- Record some lectures for students to watch outside class
- Use class time for Q&A and exercises only
- Flip classroom for Weeks 7-10

**Don't do this:**
- ❌ Rush through foundational material (Weeks 1-4)
- ❌ Skip exercises to "make up time"
- ❌ Lecture faster (students just get lost)

---

## Common Student Struggles

### Week 1-2: Getting Started

**Struggle 1: "F* won't install / editor not working"**
- **Frequency**: Common (varies by platform and student technical background)
- **Solution**: Pre-course installation party (virtual or in-person)
- **Backup plan**: Provide cloud-based F* environment (Docker)
- **Prevention**: Send installation instructions 1 week before course starts
- **Estimation note**: Track actual frequency in your cohort to calibrate support needs

**Struggle 2: "I don't understand the error messages"**
- **Frequency**: Nearly universal among beginners (research: students struggle with formal proofs[^1])
- **Pedagogical response**: Dedicate 15 min of Day 2 to "reading error messages"
- **Exercise**: Give broken code, ask "What is F* telling you?"
- **Long-term**: Error messages become familiar by Week 3

**Struggle 3: "Why is this better than testing?"**
- **Frequency**: Many students question this early on (legitimate skepticism is healthy!)
- **Pedagogical response**: Don't over-argue. Show examples.
- **Effective demo**: Security vulnerability caught by verification
- **Long-term**: Understanding deepens by Week 4

### Week 3-6: Proofs Are Hard

**Struggle 4: "My proof doesn't work and I don't know why"**
- **Frequency**: Every student, every week
- **Pedagogical response**: Debugging proofs is a skill - teach it explicitly
- **Technique**: `admit()` parts of proof, narrow down problem
- **Office hours**: Most valuable time investment

**Struggle 5: "When do I use a lemma vs. inline proof?"**
- **Frequency**: Common struggle (students learning proof decomposition)
- **Pedagogical response**: Heuristics, not rules
- **Rule of thumb**: If proof is >5 lines, extract lemma
- **Gets better**: By Week 8, most students develop good intuition

**Struggle 6: "SMT solver times out"**
- **Frequency**: Becomes more common in Weeks 5-6 as proofs grow complex
- **Pedagogical response**: Teach SMT debugging flags
- **Solutions**: Break proof into smaller steps, add intermediate asserts
- **Important**: This is normal, not a failure

### Week 7-10: Advanced Concepts

**Struggle 7: "I don't understand effects"**
- **Frequency**: Significant portion find this abstract (effect systems are conceptually challenging)
- **Pedagogical response**: More examples, less theory initially
- **Effective approach**: Show concrete `ST` code before explaining monad
- **Alternative**: Relate to Haskell monads (for those with FP background)

**Struggle 8: "Tactics feel like magic"**
- **Frequency**: Most students uncomfortable with tactics initially
- **Pedagogical response**: Show what tactics do "under the hood"
- **Debugging**: `dump` tactic to see proof state
- **Philosophy**: Tactics are tools, not magic spells

### Week 11-12: Capstone Anxiety

**Struggle 9: "My capstone project is too ambitious / too simple"**
- **Frequency**: Nearly universal anxiety (scoping research projects is hard!)
- **Pedagogical response**: Scope management workshop in Week 10
- **Check-ins**: Mandatory 1:1 meetings in Week 11
- **Calibration**: Show examples from previous years

**Struggle 10: "I can't finish in time"**
- **Frequency**: Common issue (students often underestimate proof complexity)
- **Pedagogical response**: Phased deadlines (proposal, prototype, final)
- **Partial credit**: Reward progress even if incomplete
- **Learning goal**: Scoping and project management are skills too

---

## Grading Philosophy

### Balancing Rigor and Compassion

Formal verification is **objectively hard**. Your grading should reflect this.

#### Calibration: The 60% Rule

**Target class average: 60-70%**

**Why?**
- This is a graduate-level/advanced undergrad course
- Proofs are either correct or incorrect - binary outcomes
- Students learn as much from partial attempts as from perfect proofs

**Grading scale suggestion** (estimated distribution based on pedagogical experience):
- 90-100%: Exceptional (approximately 10% of students)
- 75-89%: Strong performance (approximately 25-30%)
- 60-74%: Satisfactory mastery (approximately 40-50%)
- 50-59%: Partial mastery, needs improvement (approximately 10-15%)
- <50%: Incomplete understanding (approximately <5%)

**Note**: These percentages are estimates. Track actual distribution in your cohort.

**Controversial take**: A 65% in this course may represent deeper learning than a 95% in an easier course. Normalize this with students early.

### Partial Credit Guidelines

**Exercises (20% of grade):**
- Full credit: Proof correct, code typechecks
- 80%: Minor errors, easily fixed
- 60%: Right approach, incomplete proof
- 40%: Attempted, shows understanding of problem
- 20%: Attempted, significant misunderstanding
- 0%: Not attempted

**Mini-Projects (25% of grade):**
- See detailed rubrics in `rubrics/mini_project_rubric.md`
- Reward novelty and ambition (even if imperfect)
- Process matters: Did they show iterations?

**Midterm (15% of grade):**
- Time-limited exam (90 min or take-home 48hr)
- Mix of short answer and proof problems
- See `rubrics/midterm_rubric.md`

**Capstone (30% of grade):**
- Quality over quantity
- Oral defense component (communication matters!)
- See `rubrics/capstone_rubric.md`

**Participation/Quizzes (10% of grade):**
- Daily quizzes: Graded on completion, not correctness
- Participation: Asking questions counts as much as answering

### Peer Review Facilitation

**When**: After mini-projects (Weeks 3, 6, 9)

**Format**:
1. Students submit code to anonymous peer review system
2. Each student reviews 2 others' submissions
3. Use rubric provided in `rubrics/peer_review_template.md`
4. Instructor grades the reviews (not the original code)

**Pedagogical value**:
- Reading others' code builds understanding
- Giving feedback reinforces concepts
- Receiving feedback from peers is less threatening than from instructor

**Grading peer reviews:**
- Full credit: Constructive, specific, uses rubric
- Partial credit: Vague or only positive feedback
- No credit: Dismissive or off-topic

### Academic Integrity Policy

**The problem**: Proof assistants make it hard to detect plagiarism (proofs look similar)

**The solution**: Focus on process, not just product

**Required artifacts**:
1. Git commit history (should show progression)
2. Written explanation (why this approach?)
3. Oral defense for capstone (can they explain it?)

**Red flags**:
- Code appears suddenly (no incremental commits)
- Student can't explain their own proof
- Identical error patterns across students (suspicious)

**Pedagogical approach**:
- Day 1: Explain that collaboration is encouraged, but copying is not
- Difference: "Discussing approaches" vs. "sharing code"
- Honor code: If you get help, cite it in comments

**If you suspect plagiarism**:
- Talk to student first (may be misunderstanding)
- Ask them to explain proof step-by-step
- Follow your institution's academic integrity process

---

## Office Hours Tips

### Making Office Hours Effective

**Problem**: Students often don't attend until they're desperate

**Solution**: Rebrand as "Proof Workshop"

**Structure**:
- First 15 min: Open Q&A on recent lectures
- Next 60 min: Students work on exercises, instructor circulates
- Last 15 min: Preview next week's challenges

**Tips**:
1. **Don't solve proofs for students** - Ask Socratic questions
   - "What does this error message say?"
   - "What are you trying to prove here?"
   - "Have you tried adding an `assert`?"

2. **Group similar questions** - If 3 students stuck on same thing, mini-lecture

3. **Keep a "common errors" log** - Feeds back into lectures

4. **Celebrate breakthroughs** - "Nice! You figured it out!"

5. **Time-box debugging** - If stuck for 20 min, move on, come back

### Virtual Office Hours

**If remote**:
- Use screen sharing for debugging together
- Breakout rooms for group work
- Record sessions (with permission) for students who can't attend

---

## Resources and Support

### For Instructors Teaching This Course

**F* Language Resources:**
- Official tutorial: https://fstar-lang.org/tutorial/
- Zulip chat: https://fstar-lang.zulipchat.com/ (get help from F* team!)
- GitHub: https://github.com/FStarLang/FStar

**Pedagogical Resources:**
- Software Foundations (Coq): https://softwarefoundations.cis.upenn.edu/ (inspiration)
- CACM article "Teaching Formal Methods": [reference to be added]
- This repository: `skill/` directory has additional examples

**Community:**
- Join #fstar-teaching on Zulip (instructor-only channel)
- Annual workshop: Teaching Formal Methods (TFM @ FM conference)
- Email the course creators: [add contact info]

### Getting Help

**Technical issues with F*:**
- Post on Zulip #beginner-questions (very responsive!)
- GitHub issues for bugs: https://github.com/FStarLang/FStar/issues

**Pedagogical questions:**
- Email course authors (we want to improve this guide!)
- Teaching formal methods mailing list: [add if exists]

**Adapting for your context:**
- See `COURSE_OUTLINE.md` for semester/quarter/workshop variants
- We're happy to consult (email us!)

---

## Customization and Adaptation

### This Guide is a Starting Point

**Please adapt to your context!**

**For different levels:**
- **Graduate course**: Faster pace, skip some L1 content, deeper L6-L7
- **Advanced undergrad**: As written
- **Intro course**: Stop at L4, extend Weeks 1-6 to full semester

**For different institutions:**
- **Research university**: More emphasis on L7, reading papers
- **Teaching-focused**: More scaffolding, slower pace
- **Bootcamp/Industry**: Focus on L1-L4, practical verification

**For different class sizes:**
- **Small (<20)**: More 1:1 interaction, oral exams feasible
- **Medium (20-50)**: As written
- **Large (50+)**: More auto-grading, TA support essential

### Contributing Back

If you make improvements to this guide, please contribute back!

**How to contribute:**
1. Fork the repository
2. Make your changes (new exercises, better explanations, bug fixes)
3. Submit a pull request
4. Add yourself to `CONTRIBUTORS.md`

**Especially valuable:**
- New exercises with solutions
- Improved error message explanations
- Case studies from your industry context
- Student work samples (with permission)

---

## FAQ for Instructors

**Q: I'm new to F*. Can I teach this course?**
A: Yes! Work through the exercises yourself first (estimated 10-20 hours preparation). The teaching notes assume you're learning alongside students. You don't need to be an expert - curiosity and willingness to debug together matter more.

**Q: Do I need a PhD in type theory?**
A: No. We deliberately avoid deep type theory until Week 10+. Strong programming background + willingness to learn is sufficient.

**Q: What if students ask questions I can't answer?**
A: Say "Great question! Let me investigate and get back to you next class." Then post on F* Zulip - the team is very helpful. Modeling how to seek help is valuable pedagogy.

**Q: Can I use a different proof assistant (Coq, Lean, Isabelle)?**
A: The course structure and pedagogy transfer, but you'll need to rewrite all exercises. F*'s SMT integration makes it more beginner-friendly than Coq/Lean for imperative verification.

**Q: How much time should I budget for grading?**
A: **Estimated grading time**: 10-15 min per student per week (for a class of 30: approximately 5-7 hours/week). Auto-grading helps for early weeks. Capstone grading is heavier (approximately 30 min per project for final review). Adjust based on your grading style and class size.

**Q: Students are falling behind. What do I do?**
A: Pause and consolidate. Better to deeply understand L1-L3 than superficially cover all 7 levels. See "When You Fall Behind" section above.

**Q: Can I skip the midterm?**
A: Yes. Replace with a larger mini-project or cumulative quizzes. The midterm primarily serves to force consolidation at the halfway point.

**Q: What programming language should students know?**
A: Ideally OCaml, F#, or Haskell. Python/Java students will struggle more (3-4 weeks to get comfortable). Consider a "functional programming refresher" in Week 0.

---

## Acknowledgments

This course design draws on:
- F* tutorial by the F* team
- Software Foundations (Pierce et al.)
- Research on teaching formal methods (see bibliography in COURSE_OUTLINE.md)
- 5+ years of teaching feedback from early adopters

**Thank you to:**
- F* development team at MSR, Inria, CMU
- Students who provided feedback on early versions
- Instructors who shared their adaptations

---

## Let's Teach Verification! 🚀

You're about to embark on one of the most rewarding teaching experiences: helping students build provably correct software. It's challenging, but the "aha!" moments when a proof finally works make it all worthwhile.

**Remember:**
- Struggle is learning
- Debugging proofs is a skill
- You don't need all the answers
- Students will surprise you with creative solutions

**Good luck, and welcome to the formal methods teaching community!**

*If you have questions or feedback on this guide, please reach out. We're continuously improving it based on instructor experiences.*

---

**Next steps:**
1. Read `week_01_teaching_notes.md` for your first week
2. Set up the F* toolchain yourself
3. Try Exercise 1.1 to experience the student perspective
4. Join the F* Zulip and introduce yourself in #teaching

**Let's go!** 🎓✨

---

## References

[^1]: See BIBLIOGRAPHY.md for complete citations. Key finding: "Most computer science students have difficulties with proving theorems... The blending of formal and more informal aspects of proofs is suspected to be the main obstacle to learning how to prove." (arXiv:1803.01466)
