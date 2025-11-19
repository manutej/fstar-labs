# F* Formal Verification Skill

Comprehensive skill for building formally verified software using F* (F-star), a proof-oriented programming language that combines dependent types, refinement types, monadic effects, and SMT-backed automated verification.

## Overview

F* is a general-purpose functional programming language aimed at program verification. It combines:

- **Dependent Types**: Types that depend on values for precise specifications
- **Refinement Types**: Subset types qualified by logical predicates
- **Effect System**: Fine-grained tracking of computational effects
- **SMT Integration**: Automated verification via Z3 solver
- **Interactive Proving**: Tactic-based manual proofs when automation fails
- **Code Extraction**: Compile verified code to OCaml, F#, C, WebAssembly, and Assembly

F* has been used to build production systems including:
- **HACL***: High-assurance cryptographic library
- **Project Everest**: Verified HTTPS stack (TLS 1.2 and 1.3)
- **EverParse**: Verified parser generator
- **miTLS**: Verified TLS implementation
- **Low***: Verified low-level C code generation

## When to Use F* vs Other Proof Assistants

### Choose F* When:

1. **Building Production Systems**: F* excels at extracting verified code to efficient executables
2. **Cryptography & Security**: Strong track record with HACL*, Project Everest
3. **Low-Level Systems Code**: Low* subset compiles to verified C with memory safety
4. **SMT Automation**: Leverage automated reasoning for arithmetic, data structures
5. **Effect Verification**: Need to verify stateful, concurrent, or I/O code
6. **Quick Verification**: SMT automation speeds up development vs manual proving
7. **C Integration**: Need verified code that integrates with existing C codebases

### Choose Coq When:

- Deep mathematical proofs with extensive manual proving
- Rich ecosystem of formalized mathematics (MathComp, etc.)
- Teaching formal methods and constructive mathematics
- Proofs about programming language semantics
- Mature library ecosystem for specific domains

### Choose Lean When:

- Mathematical formalization (strong for pure mathematics)
- Rapid development with extensive automation
- Metaprogramming and proof automation
- Modern dependent type theory features
- Integration with mathematics community

### Choose Agda When:

- Research in dependent type theory
- Proof-relevant mathematics
- Experimenting with type theory features
- Computational interpretations of proofs
- Teaching type theory concepts

### Choose Isabelle/HOL When:

- Mathematical proofs in higher-order logic
- Large-scale formal verification projects
- Hardware verification
- Strong automated reasoning capabilities
- Mature archive of formalizations

## F*'s Unique Strengths

1. **Production-Ready Extraction**: Best-in-class code generation to multiple targets
2. **Verification Efficiency**: SMT automation reduces proof burden significantly
3. **Security Focus**: Designed for cryptography and security-critical systems
4. **Effect System**: Track and verify side effects precisely
5. **Low-Level Verification**: Verify C-level code with memory safety
6. **Industry Adoption**: Used in real-world production systems (Azure, Firefox)
7. **Pragmatic Balance**: Automation for common cases, tactics for edge cases

## Installation and Setup

### Prerequisites

- **Z3 SMT Solver** (version 4.8.5 or later)
- **OCaml** (4.10 or later) for extraction
- **OPAM** (recommended for package management)

### Installation via OPAM (Recommended)

```bash
# Install OPAM (package manager for OCaml)
# On macOS:
brew install opam

# On Ubuntu/Debian:
sudo apt install opam

# Initialize OPAM
opam init
eval $(opam env)

# Install F*
opam install fstar
```

### Installation via Binary Release

```bash
# Download latest release from GitHub
wget https://github.com/FStarLang/FStar/releases/download/v2024.01.13/fstar_2024.01.13_Linux_x86_64.tar.gz

# Extract
tar -xzf fstar_2024.01.13_Linux_x86_64.tar.gz

# Add to PATH
export FSTAR_HOME=$HOME/fstar
export PATH=$FSTAR_HOME/bin:$PATH

# Add to .bashrc or .zshrc for persistence
echo 'export FSTAR_HOME=$HOME/fstar' >> ~/.bashrc
echo 'export PATH=$FSTAR_HOME/bin:$PATH' >> ~/.bashrc
```

### Installation via Docker

```bash
# Pull F* Docker image with Emacs
docker pull fstarlang/fstar-emacs:latest

# Run interactive session
docker run -it fstarlang/fstar-emacs

# Or mount local directory
docker run -it -v $(pwd):/workspace fstarlang/fstar-emacs
```

### Building from Source

```bash
# Clone repository
git clone https://github.com/FStarLang/FStar.git
cd FStar

# Install OCaml dependencies
opam install --deps-only ./fstar.opam

# Build F*
make

# Add to PATH
export FSTAR_HOME=$(pwd)
export PATH=$FSTAR_HOME/bin:$PATH
```

### Installing Z3

```bash
# Via package manager (macOS)
brew install z3

# Via package manager (Ubuntu/Debian)
sudo apt install z3

# Or download from GitHub
# https://github.com/Z3Prover/z3/releases
```

### Verifying Installation

```bash
# Check F* version
fstar --version

# Check Z3 version
z3 --version

# Test with simple file
echo 'let x : int = 42' > test.fst
fstar test.fst
```

## Quick Start Guide

### Hello World Example

Create `HelloWorld.fst`:

```fstar
module HelloWorld

// Simple function
val greet: string -> string
let greet name = "Hello, " ^ name ^ "!"

// Verified function with postcondition
val greet_non_empty: name:string{length name > 0} ->
  Tot (result:string{length result > length name})
let greet_non_empty name = "Hello, " ^ name ^ "!"
```

Verify:

```bash
fstar HelloWorld.fst
```

### First Verified Program

Create `SafeDiv.fst`:

```fstar
module SafeDiv

// Division with precondition preventing division by zero
val safe_div: x:int -> y:int{y <> 0} -> Tot int
let safe_div x y = x / y

// Test it
let example1 = safe_div 10 2  // OK: 5
// let example2 = safe_div 10 0  // Error: refinement not satisfied
```

### Refinement Types Example

Create `RefinementTypes.fst`:

```fstar
module RefinementTypes

// Natural numbers
type nat = x:int{x >= 0}

// Positive integers
type pos = x:int{x > 0}

// Factorial with verified type
val factorial: nat -> Tot nat
let rec factorial n =
  if n = 0 then 1
  else n * factorial (n - 1)

// Safe array indexing
val safe_index: #a:Type -> arr:array a -> i:nat{i < length arr} -> Tot a
let safe_index #a arr i = index arr i
```

### Extracting to OCaml

Create `Fibonacci.fst`:

```fstar
module Fibonacci

val fib: nat -> Tot nat
let rec fib n =
  if n <= 1 then n
  else fib (n - 1) + fib (n - 2)
```

Extract and compile:

```bash
# Extract to OCaml
fstar --codegen OCaml Fibonacci.fst

# Compile extracted OCaml code
ocamlopt -o fibonacci Fibonacci.ml

# Run
./fibonacci
```

## Project Structure and Workflow

### Typical Project Layout

```
my-fstar-project/
├── src/
│   ├── Core.fst              # Core definitions
│   ├── Verified.fst          # Verified implementations
│   ├── Spec.fst              # Specifications
│   └── Lemmas.fst            # Proof lemmas
├── tests/
│   └── Tests.fst             # Test code
├── extract/
│   └── extracted OCaml/C code
├── Makefile                  # Build configuration
├── .fstar                    # F* options file
└── README.md
```

### F* Options File

Create `.fstar` in project root:

```
--include src
--include tests
--cache_checked_modules
--cache_dir .cache
--warn_error -272
```

### Makefile Example

```makefile
FSTAR = fstar
FSTAR_FLAGS = --cache_checked_modules --cache_dir .cache

SRC_FILES = $(wildcard src/*.fst)
CHECKED_FILES = $(SRC_FILES:.fst=.checked)

all: verify

verify: $(CHECKED_FILES)

%.checked: %.fst
	$(FSTAR) $(FSTAR_FLAGS) $<
	@touch $@

extract: verify
	$(FSTAR) --codegen OCaml $(SRC_FILES)

clean:
	rm -rf .cache *.checked src/*.checked

.PHONY: all verify extract clean
```

### Development Workflow

1. **Write Specification**: Define types and function signatures
2. **Implement**: Write function bodies
3. **Verify**: Run F* to check verification conditions
4. **Debug**: Add assertions, lemmas, or manual proofs as needed
5. **Test**: Extract and run tests on extracted code
6. **Iterate**: Refine specifications and implementations

## Editor Setup

### VS Code

1. Install "F*" extension from marketplace
2. Configure settings:

```json
{
  "fstar.executable": "fstar.exe",
  "fstar.flyCheck": true,
  "fstar.verifyOnOpen": true,
  "fstar.verifyOnSave": true,
  "fstar.z3Path": "z3"
}
```

3. Features:
   - Syntax highlighting
   - On-the-fly verification
   - Error messages inline
   - Hover for type information
   - Go to definition

### Emacs

1. Install fstar-mode:

```elisp
;; Add to .emacs or init.el
(add-to-list 'load-path "/path/to/fstar/emacs")
(require 'fstar-mode)

(setq fstar-executable "fstar.exe")
(setq fstar-smt-executable "z3")
(setq fstar-subp-prover-args '("--query_stats"))
```

2. Key bindings:
   - `C-c C-n`: Verify next
   - `C-c C-p`: Verify previous
   - `C-c C-r`: Verify region
   - `C-c C-b`: Verify buffer
   - `C-c C-x`: Reset verification

### Vim

1. Install fstar-mode.vim:

```bash
mkdir -p ~/.vim/syntax
cp /path/to/fstar/vim/syntax/fstar.vim ~/.vim/syntax/

mkdir -p ~/.vim/ftdetect
echo 'au BufRead,BufNewFile *.fst set filetype=fstar' > ~/.vim/ftdetect/fstar.vim
```

2. Add to `.vimrc`:

```vim
au FileType fstar setlocal commentstring=//%s
au FileType fstar setlocal shiftwidth=2
au FileType fstar setlocal tabstop=2
```

## Learning Path

### Beginner (Weeks 1-2)

1. **Basic Syntax**: Learn F* syntax, functions, types
2. **Refinement Types**: Understand subset types and predicates
3. **Simple Verification**: Verify basic properties with SMT
4. **Lists and Recursion**: Work with inductive datatypes
5. **Resources**:
   - F* Tutorial chapters 1-3
   - Online F* editor for experimentation

### Intermediate (Weeks 3-6)

1. **Dependent Types**: Master dependent function types
2. **Effect System**: Understand Tot, ST, and custom effects
3. **Lemmas**: Write and use lemmas for proof reuse
4. **Tactics**: Basic tactic usage for manual proofs
5. **Code Extraction**: Extract to OCaml and test
6. **Resources**:
   - F* Tutorial chapters 4-8
   - F* examples repository
   - HACL* source code (simple modules)

### Advanced (Weeks 7-12)

1. **Low* Programming**: Write verified C code
2. **Stateful Verification**: Master ST monad and heap reasoning
3. **Custom Effects**: Define and use custom effects
4. **Metaprogramming**: Write tactics for custom automation
5. **Large Projects**: Build multi-module verified systems
6. **Resources**:
   - Low* tutorial
   - Project Everest code
   - Meta-F* paper
   - Advanced F* summer school materials

### Expert (Ongoing)

1. **Protocol Verification**: Verify network protocols
2. **Cryptography**: Implement verified crypto primitives
3. **Compiler Verification**: Verify transformations and optimizations
4. **Custom Tooling**: Build F*-based verification tools
5. **Contribute**: Contribute to F* and ecosystem projects

## Common Patterns

### Pattern 1: Verified Data Structure

```fstar
module Stack

type stack (a:Type) = list a

val empty: #a:Type -> stack a
let empty #a = []

val push: #a:Type -> stack a -> a -> stack a
let push #a s x = x :: s

val pop: #a:Type -> s:stack a{length s > 0} -> a * stack a
let pop #a s = match s with
  | hd :: tl -> hd, tl
```

### Pattern 2: Preconditions and Postconditions

```fstar
val max: x:int -> y:int -> Tot (r:int{r >= x /\ r >= y})
let max x y = if x >= y then x else y

val min: x:int -> y:int -> Tot (r:int{r <= x /\ r <= y})
let min x y = if x <= y then x else y
```

### Pattern 3: Invariant Preservation

```fstar
type sorted_list = l:list int{is_sorted l}

val insert: sorted_list -> int -> Tot sorted_list
let rec insert l x =
  match l with
  | [] -> [x]
  | hd :: tl ->
    if x <= hd then x :: l
    else hd :: insert tl x
```

## Troubleshooting

### Common Issues

**"Unknown assertion failed"**
- Add intermediate assertions to help SMT solver
- Break complex proofs into lemmas
- Increase Z3 timeout with `--z3rlimit`

**"Subtyping check failed"**
- Refinement type not satisfied
- Add proof obligations or change specification
- Check preconditions are met

**"Ill-typed term"**
- Type mismatch in function application
- Check implicit arguments with `#`
- Verify universe polymorphism constraints

**"Pattern match not exhaustive"**
- Add missing cases to pattern match
- Use wildcard `_` for unreachable cases
- Add refinement types to make cases provably exhaustive

**Slow verification**
- Use `--cache_checked_modules` for incremental builds
- Mark complex functions opaque with `[@ opaque_to_smt]`
- Split large verification conditions
- Optimize SMT patterns

## Next Steps

1. **Work through examples**: See `EXAMPLES.md` for 18+ practical examples
2. **Read F* Tutorial**: Official book at https://fstar-lang.org/tutorial/
3. **Study HACL***: Real-world verified cryptography
4. **Join community**: F* Zulip chat and GitHub discussions
5. **Build projects**: Start with small verified programs, scale up
6. **Contribute**: Help improve F* and ecosystem

## Resources

### Official Resources

- **Website**: https://fstar-lang.org/
- **Tutorial Book**: https://fstar-lang.org/tutorial/
- **API Docs**: https://fstarlang.github.io/docs/
- **GitHub**: https://github.com/FStarLang/FStar
- **Zulip Chat**: https://fstar.zulipchat.com/

### Example Code

- **F* Examples**: https://github.com/FStarLang/FStar/tree/master/examples
- **HACL***: https://github.com/project-everest/hacl-star
- **Project Everest**: https://github.com/project-everest
- **EverParse**: https://github.com/project-everest/everparse

### Academic Papers

- "Dependent Types and Multi-Monadic Effects in F*" (POPL 2016)
- "Meta-F*: Proof Automation with SMT, Tactics, and Metaprograms" (ESOP 2019)
- "Verified Low-Level Programming Embedded in F*" (ICFP 2017)
- "HACL*: A Verified Modern Cryptographic Library" (CCS 2017)

### Video Tutorials

- F* Summer School lectures
- OPLSS (Oregon Programming Languages Summer School)
- DeepSpec Summer School

### Community

- **Mailing List**: fstar-club@lists.gforge.inria.fr
- **GitHub Discussions**: https://github.com/FStarLang/FStar/discussions
- **Stack Overflow**: Tag questions with `fstar`

---

**Last Updated**: November 2025
**Skill Version**: 1.0.0
