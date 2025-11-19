---
name: think
description: Invoke sequential-thinking MCP with beautifully formatted output for complex reasoning tasks
---

# Think - Sequential Reasoning with Beautiful Formatting

Use the sequential-thinking MCP server to work through complex problems with formatted, readable output.

## Instructions

When the user invokes `/think` or `/think [question]`:

1. **Understand the Problem**
   - If question provided: Use it directly
   - If no question: Use the current conversation context
   - Identify complexity level to estimate thought count

2. **Invoke Sequential Thinking**
   - Use the `mcp__sequential-thinking__sequentialthinking` tool
   - Let the extended reasoning unfold naturally
   - Allow for revisions, branches, and hypothesis testing

3. **Format Each Thought**
   - Apply sequential-thinking-formatter skill formatting
   - Use visual structure:
     ```
     ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
     💭 Thought N of M [████████░░░░] XX%
     ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

     [Thought content with proper formatting]

     ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
     ```

4. **Track Special States**
   - **Revisions**: Mark with 🔄 and reference original thought
   - **Hypotheses**: Mark with 💡 and format as proposal
   - **Verifications**: Mark with ✓/✗ and show result
   - **Branches**: Mark with 🌳 and show branch point

5. **Present Final Answer**
   - Use distinct formatting:
     ```
     ╔══════════════════════════════════════════╗
     ║  ✅ FINAL ANSWER                         ║
     ╚══════════════════════════════════════════╝

     [Clear, concise answer]

     ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
     📊 Reasoning Summary:
        • Total thoughts: N
        • Revisions: X
        • Hypotheses tested: Y
     ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
     ```

6. **Add Context (if Explanatory mode active)**
   - Include ★ Insight blocks for key reasoning steps
   - Explain WHY certain approaches were chosen
   - Highlight learning moments

## Usage Examples

### Simple Usage
```
/think
```
Uses current conversation context for reasoning.

### With Question
```
/think How can I optimize this database query?
```

### Complex Problem
```
/think Design a scalable microservices architecture for 10M users
```

## Formatting Features

### Progress Visualization
```
[████████████] 100%  Complete
[██████████░░]  83%  Nearly done
[████████░░░░]  66%  Over halfway
[██████░░░░░░]  50%  Halfway
[████░░░░░░░░]  33%  Getting started
[██░░░░░░░░░░]  16%  Just beginning
```

### Thought Type Icons
- 💭 Standard reasoning
- 🔄 Revised thinking
- 💡 Hypothesis proposed
- ✓ Hypothesis verified
- ✗ Hypothesis rejected
- 🌳 Branch exploration
- ✅ Final answer

### Example Output

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
💭 Thought 1 of 6 [██░░░░░░░░░░] 17%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Let me break down the problem into components:
1. User authentication requirements
2. Data persistence needs
3. Scalability constraints
4. Cost considerations

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
💭 Thought 2 of 6 [████░░░░░░░░] 33%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

For authentication, we need to consider...

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
💡 Thought 3 of 6 [HYPOTHESIS] ██████░░░░░░ 50%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔬 Hypothesis: JWT tokens with Redis session store
   Reasoning: Balances statelessness with revocation capability

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✓ Thought 4 of 6 [VERIFICATION] ████████░░░░ 67%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🧪 Testing hypothesis against requirements:
   ✅ Scalability: Passes (Redis cluster support)
   ✅ Security: Passes (signed tokens + revocation)
   ✅ Cost: Passes (Redis is cheap at scale)

Result: ✅ Hypothesis confirmed

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
💭 Thought 5 of 6 [██████████░░] 83%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Integrating auth solution with data layer...

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

╔══════════════════════════════════════════╗
║  ✅ FINAL ANSWER                         ║
╚══════════════════════════════════════════╝

Recommended architecture:
• Authentication: JWT + Redis session store
• Database: PostgreSQL primary + read replicas
• Caching: Redis cluster
• Load balancing: NGINX + horizontal scaling
• Cost estimate: ~$500/month for 10M users

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
📊 Reasoning Summary:
   • Total thoughts: 6
   • Revisions: 0
   • Hypotheses tested: 1
   • Conclusion confidence: High
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## When to Use /think

✅ **Use /think for**:
- Complex architectural decisions
- Multi-step problem solving
- Debugging intricate issues
- Exploring trade-offs and alternatives
- Verifying solutions systematically
- Learning through reasoning

❌ **Don't use /think for**:
- Simple factual questions
- Quick lookups
- Straightforward tasks
- When you already know the answer

## Formatting Modes

### Default Mode (Detailed)
Full visual formatting with all separators and icons.

### Compact Mode
Minimal formatting for faster reading:
```
💭 3/8 [████████░░░░] 37%
[thought content]
```

### Summary Mode
Only key thoughts (hypotheses, verifications, final answer):
```
💡 Hypothesis 3: JWT + Redis
✓ Verified 4: All requirements met
✅ Answer: [recommendation]
```

## Integration

Works seamlessly with:
- **Explanatory output style** - Adds insights between thoughts
- **Learning output style** - Adds reflective questions
- **sequential-thinking MCP** - Core reasoning engine
- **All skills** - Can reason about any domain

## Performance Notes

- Sequential-thinking can use many thoughts (10-50+ for complex problems)
- Each thought is formatted in real-time
- Progress bars update dynamically
- Output is readable at any interruption point

## Related Commands

- `/sequential-thinking` - Raw MCP invocation (unformatted)
- `/mercurio` - Mixture of experts reasoning
- `/hekat` - L1-L7 complexity orchestration

---

**Implementation Note**: This command should:
1. Invoke the sequential-thinking MCP tool
2. Stream each thought as it arrives
3. Apply formatting from sequential-thinking-formatter skill
4. Present beautifully structured output
5. Conclude with final answer and summary
