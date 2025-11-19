---
description: Activate sequential thinking MCP for extended reasoning and systematic problem-solving
allowed-tools: Task(*), Read(**), Write(**), Bash(*)
---

# /sequential-thinking

Invoke the Sequential Thinking MCP server for extended reasoning, systematic analysis, and step-by-step problem-solving.

The sequential thinking MCP enables Claude to break down complex problems, explore multiple approaches, and show working transparently.

## Usage

### Basic Usage
```bash
# Activate sequential thinking for a complex task
/sequential-thinking "Analyze the LUXOR system architecture"

# With problem description
/sequential-thinking analyze-architecture "Break down the core components and dependencies"

# For debugging
/sequential-thinking debug "Why is this test failing?"

# For research
/sequential-thinking research "Compare MCP server options for our use case"
```

### Command Variants

```bash
# Detailed analysis
/sequential-thinking --deep "Comprehensive system analysis"

# Step-by-step walkthrough
/sequential-thinking --steps "Walk through the algorithm design"

# Exploration mode (multiple approaches)
/sequential-thinking --explore "Explore different solutions to this problem"

# With output formatting
/sequential-thinking --verbose "Detailed reasoning with full traces"

# Quick reasoning (still sequential, but more concise)
/sequential-thinking --quick "Fast sequential reasoning"
```

## When to Use

Sequential thinking is ideal for:

- **Complex System Design**: Breaking architectures into understandable components
- **Debugging**: Systematic root cause analysis of issues
- **Research**: Deep investigation with visible reasoning
- **Algorithm Development**: Step-by-step problem-solving
- **Decision Making**: Evaluating multiple options methodically
- **Planning**: Breaking large projects into phases
- **Code Review**: Systematic evaluation of implementations
- **Mathematical Reasoning**: Working through proofs and calculations

## Examples

### Example 1: Architecture Analysis
```bash
/sequential-thinking analyze-architecture "Review LUXOR system and identify bottlenecks"
```

The MCP will systematically:
1. Identify core components
2. Map dependencies
3. Find potential bottlenecks
4. Suggest improvements

### Example 2: Debugging Complex Issues
```bash
/sequential-thinking debug "This test failure seems intermittent - help diagnose"
```

The MCP will:
1. Trace through expected behavior
2. Identify actual behavior
3. Find the discrepancy
4. Suggest fixes

### Example 3: Research with Extended Reasoning
```bash
/sequential-thinking research --deep "Best approach for implementing [feature]"
```

The MCP will:
1. Identify available options
2. Compare pros/cons
3. Analyze trade-offs
4. Recommend approach with reasoning

### Example 4: Algorithm Design
```bash
/sequential-thinking --steps "Design an efficient caching strategy"
```

The MCP will:
1. Break down requirements
2. Explore design approaches
3. Evaluate each approach
4. Recommend solution with detailed reasoning

## Configuration

The Sequential Thinking MCP is configured in:
- **Project**: `/Users/manu/Documents/LUXOR/.claude/settings.json`
- **Global**: `~/.claude/settings.json`

Both include the sequential-thinking MCP server with full configuration.

## MCP Details

- **Server**: `@modelcontextprotocol/server-sequential-thinking`
- **Type**: Local (runs via npx)
- **Status**: Enabled by default
- **Startup**: Automatic when Claude Code initializes

## Performance Considerations

- ⏱️ **Takes longer**: Extended reasoning is more thorough than quick analysis
- 💾 **Uses more tokens**: Longer reasoning process requires more tokens
- 🎯 **High quality**: Superior results for complex problems
- ✨ **Transparent**: Shows all working, not just conclusions

**Recommendation**: Use for complex problems where depth matters; use regular reasoning for simple queries.

## Documentation

For more information:
- **Full Guide**: See `SEQUENTIAL-THINKING-GUIDE.md`
- **Quick Reference**: See `SEQUENTIAL-THINKING-QUICK-REFERENCE.md`
- **Configuration**: See `.claude/settings.json`

## Combining with Other MCPs

Sequential thinking works well with:

```bash
# Sequential thinking + Context7 for deep research
/sequential-thinking research --ctx7 "Research [library] architecture"

# Sequential thinking + Linear for strategic planning
/sequential-thinking planning "Plan LUXOR project next phase"

# Sequential thinking + Playwright for test strategy
/sequential-thinking testing "Design comprehensive test strategy"
```

## Troubleshooting

### MCP Not Available
1. Check settings.json for `"enabled": true`
2. Ensure Node.js and npm are installed
3. Restart Claude Code
4. Verify MCP server package is installed

### Server Not Starting
1. Check Node.js: `node --version`
2. Verify settings: `cat .claude/settings.json | grep sequential`
3. Try explicit invocation: `"Use sequential thinking to..."`

### Performance Issues
- Sequential thinking is thorough but slower
- For simple tasks, use regular reasoning instead
- Consider token usage for very long analyses

## Tips for Best Results

1. **Be Specific**: Provide clear problem descriptions
2. **Ask for Steps**: Use `--steps` flag to see reasoning process
3. **Use Exploration**: Use `--explore` for complex decisions
4. **Provide Context**: More context = better reasoning
5. **Combine MCPs**: Use with Context7 or Linear for richer analysis

## Integration with LUXOR Projects

### LUMINA (CLI Development)
- Analyze CLI architecture systematically
- Debug complex interaction patterns
- Plan Phase 2 enhancements

### Research-Plan-DSL
- Deep analysis of DSL design
- Evaluate orchestration approaches
- Systematic validation of concepts

### Copilot Course
- Structured course planning
- Evaluation of content approaches
- Analysis of learning paths

### HALCON (Astrological Analysis)
- Verify complex calculations
- Systematic data analysis
- Algorithm validation

## Related Commands

- `/ctx7` - Library documentation with context
- `/crew` - Agent discovery and management
- `/workflows` - Multi-agent orchestration

---

**Type**: MCP Router
**Status**: Active and Enabled
**Last Updated**: 2025-10-22
**Maintenance**: See `.claude/docs/SEQUENTIAL-THINKING-GUIDE.md`
