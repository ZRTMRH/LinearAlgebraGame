#!/bin/bash
# Fix permissions for lake and lean executables
echo "Fixing permissions for Lean/Lake/Elan..."

# Ensure elan is in the PATH
export ELAN_HOME=/home/node/.elan
export PATH=/home/node/.elan/bin:$PATH

# Ensure the game directory has proper permissions
if [ -d "/home/node/game" ]; then
    echo "Fixing game directory permissions..."
    # Make sure .lake directory is writable
    if [ -d "/home/node/game/.lake" ]; then
        chmod -R u+rwx /home/node/game/.lake 2>/dev/null || true
    fi
    # Also ensure lake-packages is writable
    if [ -d "/home/node/game/lake-packages" ]; then
        chmod -R u+rwx /home/node/game/lake-packages 2>/dev/null || true
    fi
fi

# Clone lean4game if it doesn't exist
if [ ! -d "/home/node/lean4game" ]; then
    echo "Cloning lean4game repository..."
    cd /home/node
    git clone https://github.com/leanprover-community/lean4game.git --branch v4.28.0 || echo "Failed to clone lean4game"
fi

# Ensure lean toolchain is installed
echo "Checking Lean toolchain..."
if ! elan toolchain list | grep -q "v4.28.0"; then
    echo "Installing Lean toolchain v4.28.0..."
    elan toolchain install leanprover/lean4:v4.28.0 || echo "Failed to install toolchain"
fi

# Set default toolchain
echo "Setting default toolchain..."
elan default leanprover/lean4:v4.28.0 || echo "Failed to set default toolchain"

# Test that everything works
echo "Testing Lean installation..."
which lean || echo "Lean not found in PATH!"
which lake || echo "Lake not found in PATH!"
lean --version || echo "Lean not working!"
lake --version || echo "Lake not working!"

echo "Current PATH: $PATH"
echo "ELAN_HOME: $ELAN_HOME"
echo "Permissions fixed!"
