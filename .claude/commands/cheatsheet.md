---
description: Generate engaging cheat sheets for commands, tools, and workflows
---

Generate beautiful, printable HTML cheat sheets in the style of Claude Code keyboard shortcuts poster.

**Usage**:
```bash
/cheatsheet <topic>
/cheatsheet <topic> --output <path>
/cheatsheet <topic> --theme dark|light|both
```

**Features**:
- 📄 11x17" printable poster format
- 🎨 Dark and light themes
- 💡 Engaging notes and pro tips
- 📊 Visual hierarchy with heat colors
- 🏆 Quick wins and common patterns
- 🔧 Troubleshooting section
- ⚡ Examples with real-world context

**Examples**:
```bash
/cheatsheet "Git workflows"
/cheatsheet "Docker commands" --theme both
/cheatsheet "PostgreSQL queries" --output ~/docs/
```

**Topics to Try**:
- Shell commands & shortcuts
- Programming language syntax
- Tool CLIs (git, docker, kubectl)
- Framework patterns
- Keyboard shortcuts
- Workflow orchestrations

---

# Task Execution

Generate an engaging, visually appealing cheat sheet for: **{{TOPIC}}**

## Style Requirements

Follow the Claude Code shortcuts poster style:
1. **Visual Hierarchy**: Use color-coded sections (critical/important/useful/rare)
2. **Engaging Notes**: Add fun, memorable notes with emojis
3. **Real Examples**: Show actual commands, not placeholders
4. **Pro Tips**: Include power user tips in highlight boxes
5. **Quick Wins**: Learning progression (Day 1, Day 2, Day 3)
6. **Troubleshooting**: Common mistakes and solutions
7. **Golden Rules**: Big picture principles in prominent boxes

## Structure

```html
<!DOCTYPE html>
<html>
<head>
    <title>{{TOPIC}} Cheat Sheet</title>
    <style>
        /* Poster-style CSS with sections, heat colors, pro tips */
    </style>
</head>
<body>
    <div class="page">
        <!-- Header with title and tagline -->
        <!-- Golden Rule box -->
        <!-- Core concepts section -->
        <!-- Quick wins section -->
        <!-- Common patterns section -->
        <!-- Pro tips section -->
        <!-- Troubleshooting section -->
        <!-- Footer with call to action -->
    </div>
</body>
</html>
```

## Output

Generate TWO files:
1. `{{topic}}-cheat-sheet-dark.html`
2. `{{topic}}-cheat-sheet-light.html`

Save to: {{OUTPUT_PATH}} or `/Users/manu/Documents/LUXOR/`

## Content Guidelines

✅ **Do Include**:
- Real, working examples
- Time savings estimates (⏱️ 2s vs 30s)
- Frequency hints (5+/day, 10+/day)
- Visual emojis (🚀 ⚡ 🔥 💡 🏆)
- Memorable mnemonics
- Progressive complexity
- Common mistakes to avoid

❌ **Don't Include**:
- Placeholder text like "example here"
- Generic descriptions
- Walls of text without visual breaks
- Boring, dry technical writing
- Missing context or use cases

## Example Sections

**Golden Rule Box**:
```html
<div class="golden-rule">
    <div class="golden-rule-title">⚡ THE GOLDEN RULE ⚡</div>
    <div class="golden-rule-content">
        [Big picture principle]<br>
        [Key insight that changes everything]
    </div>
</div>
```

**Pro Tip Box**:
```html
<div class="pro-tip">
    <div class="pro-tip-title">⚡ PRO TIP</div>
    [Actionable power user insight]<br>
    ✅ When to use<br>
    ⏱️ Time saved
</div>
```

**Command Example**:
```html
<div class="cmd-example">$ git commit -am "feat: add feature"</div>
<div class="cmd-note">
    ⏱️ 2s vs 15s typing full commands<br>
    💡 Use 20+/day for rapid commits
</div>
```

Make it **FUN**, **ENGAGING**, and **PRACTICAL**!
