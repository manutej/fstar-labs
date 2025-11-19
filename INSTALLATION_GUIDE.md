# F* Installation Guide for F* Labs Course

**Purpose**: Install F* compiler and Z3 SMT solver to verify course materials

**Estimated Time**: 15-30 minutes

---

## Quick Start (Recommended)

### Option 1: Automated Installation Script

```bash
cd /home/user/fstar-labs
./scripts/install_fstar.sh
```

This will:
- Download F* binary release (v2024.01.13)
- Download Z3 SMT solver (v4.12.2)
- Install to `/opt/fstar/`
- Add to your PATH

### Option 2: Docker (If Available)

```bash
docker pull fstar/fstar:latest
docker run -it -v $(pwd):/home/fstar fstar/fstar:latest

# Inside container:
cd /home/fstar
fstar.exe --version
```

### Option 3: Manual Installation

See detailed instructions below.

---

## Detailed Installation Instructions

### Prerequisites

**Linux/macOS**:
- `wget` or `curl` (for downloading)
- `tar` and `unzip` (for extracting)
- `bash` shell

**Windows**:
- WSL2 (Windows Subsystem for Linux)
- Or use pre-built Windows binaries

### Step 1: Download F*

**Latest Release**: https://github.com/FStarLang/FStar/releases

```bash
# Create installation directory
mkdir -p /opt/fstar
cd /opt/fstar

# Download F* (Linux x86_64 example)
wget https://github.com/FStarLang/FStar/releases/download/v2024.01.13/fstar_2024.01.13_Linux_x86_64.tar.gz

# Extract
tar -xzf fstar_2024.01.13_Linux_x86_64.tar.gz
cd fstar_2024.01.13_Linux_x86_64/
```

### Step 2: Add F* to PATH

```bash
# Add to ~/.bashrc or ~/.zshrc
echo 'export PATH="/opt/fstar/fstar_2024.01.13_Linux_x86_64/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc

# Verify
fstar.exe --version
# Expected output: F* 2024.01.13
```

### Step 3: Install Z3 (SMT Solver)

**F* comes bundled with Z3**, but if you need a specific version:

```bash
cd /opt/fstar

# Download Z3
wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip
unzip z3-4.12.2-x64-glibc-2.31.zip

# Add to PATH
echo 'export PATH="/opt/fstar/z3-4.12.2-x64-glibc-2.31/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc

# Verify
z3 --version
# Expected output: Z3 version 4.12.2
```

### Step 4: Verify Installation

```bash
# Check F* works
fstar.exe --version

# Check Z3 works
z3 --version

# Test on a simple file
echo 'module Test' > test.fst
echo 'let x : nat = 5' >> test.fst
fstar.exe test.fst
# Expected: "Verified module Test"
```

---

## Verifying Course Materials

Once F* is installed, verify all course materials:

```bash
cd /home/user/fstar-labs

# Run automated verification
./scripts/verify_all.sh
```

This will test:
- ✓ All solution files (must pass 100%)
- ✓ All exercise templates (should typecheck with admits)

**Expected results**:
- Week 1 solutions: PASS (if we wrote them correctly!)
- Week 2 solutions: PASS (if we wrote them correctly!)
- Week 1 exercises: PASS (templates with admits)
- Week 2 exercises: PASS (templates with admits)

**If tests fail**:
- Check error output
- Fix type errors in source files
- Re-run verification

---

## Troubleshooting

### Issue: `fstar.exe: command not found`

**Solution**: PATH not set correctly

```bash
# Check current PATH
echo $PATH

# Manually add F* to PATH for this session
export PATH="/opt/fstar/fstar_2024.01.13_Linux_x86_64/bin:$PATH"

# Or source your shell config again
source ~/.bashrc
```

### Issue: `z3: command not found`

**Solution**: F* bundle includes Z3, check:

```bash
# Find bundled Z3
find /opt/fstar -name "z3" -type f

# Should find: /opt/fstar/fstar_.../bin/z3
# If F* works, Z3 should work automatically
```

### Issue: `error while loading shared libraries: libgmp.so.10`

**Solution**: Install missing library

```bash
# Ubuntu/Debian
sudo apt-get install libgmp-dev

# macOS
brew install gmp

# Fedora/CentOS
sudo yum install gmp-devel
```

### Issue: Verification times out (>60 seconds)

**Solution**: Increase timeout or reduce problem size

```bash
# Increase Z3 timeout
fstar.exe --z3rlimit 100000 file.fst

# Reduce fuel (if recursive functions)
fstar.exe --fuel 2 --ifuel 2 file.fst
```

### Issue: Windows installation

**Solution**: Use WSL2

```bash
# Install WSL2
wsl --install

# Inside WSL2, follow Linux instructions above
cd /mnt/c/Users/YourName/fstar-labs
./scripts/install_fstar.sh
```

---

## Alternative: Build from Source

**For advanced users or contributors:**

```bash
git clone https://github.com/FStarLang/FStar.git
cd FStar

# Install OPAM (OCaml package manager)
# Follow instructions at https://opam.ocaml.org/doc/Install.html

# Build F*
make -j4

# Install
make install
```

**Build time**: ~20-30 minutes
**Requires**: OCaml, OPAM, Z3, build tools

---

## Editor Integration (Optional)

### VS Code + F* Extension

```bash
# Install VS Code extension
code --install-extension fstar-lang.fstar-vscode-assistant

# Configure F* path in VS Code settings.json:
{
  "fstar.executable": "/opt/fstar/fstar_2024.01.13_Linux_x86_64/bin/fstar.exe"
}
```

### Emacs + fstar-mode

```elisp
;; Add to ~/.emacs or ~/.emacs.d/init.el
(add-to-list 'load-path "/opt/fstar/fstar_.../emacs")
(require 'fstar-mode)
```

### Vim + fstar-vim

```bash
git clone https://github.com/FStarLang/fstar.vim ~/.vim/pack/plugins/start/fstar.vim
```

---

## Next Steps

After installation:

1. **Verify course materials**: `./scripts/verify_all.sh`
2. **Fix any errors** found during verification
3. **Update TESTING.md** with verification status
4. **Proceed to Week 3 development** (SMT module)

---

## References

- **F* Website**: https://www.fstar-lang.org/
- **F* Tutorial**: https://fstar-lang.org/tutorial/
- **F* GitHub**: https://github.com/FStarLang/FStar
- **Z3 Website**: https://microsoft.github.io/z3/
- **Installation Guide**: https://github.com/FStarLang/FStar/blob/master/INSTALL.md

---

## Support

**Issues with F* installation**:
- F* GitHub Issues: https://github.com/FStarLang/FStar/issues
- F* Zulip Chat: https://fstar-lang.zulipchat.com/

**Issues with course materials**:
- Course GitHub Issues: https://github.com/yourusername/fstar-labs/issues
- Contact instructor: [your email]

---

**Last Updated**: 2025-11-19
**F* Version**: 2024.01.13
**Z3 Version**: 4.12.2
