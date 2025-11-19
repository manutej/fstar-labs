#!/bin/bash
# F* Installation Script for F* Labs Course
# This script installs F* and Z3 for verifying course materials

set -e  # Exit on error

echo "=== F* Labs Installation Script ==="
echo ""

# Detect OS
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    OS="linux"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    OS="macos"
else
    echo "Unsupported OS: $OSTYPE"
    exit 1
fi

echo "Detected OS: $OS"
echo ""

# Installation directory
INSTALL_DIR="/opt/fstar"
BIN_DIR="$INSTALL_DIR/bin"

echo "Installation directory: $INSTALL_DIR"
echo ""

# Create directories
echo "Creating directories..."
mkdir -p "$INSTALL_DIR"
mkdir -p "$BIN_DIR"

# Download F* binary release
FSTAR_VERSION="2024.01.13"
FSTAR_URL="https://github.com/FStarLang/FStar/releases/download/v${FSTAR_VERSION}/fstar_${FSTAR_VERSION}_Linux_x86_64.tar.gz"

echo "Downloading F* ${FSTAR_VERSION}..."
cd "$INSTALL_DIR"

if command -v wget &> /dev/null; then
    wget -q "$FSTAR_URL" -O fstar.tar.gz
elif command -v curl &> /dev/null; then
    curl -sL "$FSTAR_URL" -o fstar.tar.gz
else
    echo "ERROR: Neither wget nor curl found. Please install one."
    exit 1
fi

echo "Extracting F*..."
tar -xzf fstar.tar.gz
rm fstar.tar.gz

# Find extracted directory
FSTAR_DIR=$(ls -d fstar_*/ | head -1)
cd "$FSTAR_DIR"

# Add to PATH
echo ""
echo "Adding F* to PATH..."
echo "export PATH=\"$INSTALL_DIR/$FSTAR_DIR/bin:\$PATH\"" >> ~/.bashrc
export PATH="$INSTALL_DIR/$FSTAR_DIR/bin:$PATH"

# Verify F* installation
echo ""
echo "Verifying F* installation..."
if command -v fstar.exe &> /dev/null; then
    echo "✓ F* installed successfully!"
    fstar.exe --version
else
    echo "✗ F* installation failed"
    exit 1
fi

# Check Z3
echo ""
echo "Checking Z3..."
if command -v z3 &> /dev/null; then
    echo "✓ Z3 already installed"
    z3 --version
else
    echo "Installing Z3..."

    # Download Z3
    Z3_VERSION="4.12.2"
    Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-2.31.zip"

    cd "$INSTALL_DIR"
    if command -v wget &> /dev/null; then
        wget -q "$Z3_URL" -O z3.zip
    else
        curl -sL "$Z3_URL" -o z3.zip
    fi

    unzip -q z3.zip
    rm z3.zip

    Z3_DIR=$(ls -d z3-*/ | head -1)
    ln -sf "$INSTALL_DIR/$Z3_DIR/bin/z3" "$BIN_DIR/z3"

    echo "export PATH=\"$BIN_DIR:\$PATH\"" >> ~/.bashrc
    export PATH="$BIN_DIR:$PATH"

    if command -v z3 &> /dev/null; then
        echo "✓ Z3 installed successfully!"
        z3 --version
    else
        echo "✗ Z3 installation failed"
        exit 1
    fi
fi

echo ""
echo "=== Installation Complete ==="
echo ""
echo "F* and Z3 are now installed!"
echo ""
echo "To use in new shells, run:"
echo "  source ~/.bashrc"
echo ""
echo "Or add to your PATH manually:"
echo "  export PATH=\"$INSTALL_DIR/$FSTAR_DIR/bin:$BIN_DIR:\$PATH\""
echo ""
echo "Test with:"
echo "  fstar.exe --version"
echo "  z3 --version"
echo ""
