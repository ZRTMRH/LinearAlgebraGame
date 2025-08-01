#!/bin/bash
set -e  # Exit on any error

echo "=== Starting Linear Algebra Game Deployment ==="

# Check environment
echo "Current user: $(whoami)"
echo "Current directory: $(pwd)"
echo "Lean version: $(lean --version)"
echo "Lake version: $(lake --version)"

# Navigate to the game directory
echo "=== Navigating to game directory ==="
cd /home/node/game
echo "Game directory contents:"
ls -la

# Update and build the Lean project
echo "=== Building Lean project ==="
lake update -R
echo "Getting mathlib cache..."
lake exe cache get || echo "Cache get failed, continuing with build..."
echo "Building game..."
lake build
echo "Lean build completed successfully!"

# Check lean4game directory
echo "=== Checking lean4game directory ==="
ls -la /home/node/lean4game
cd /home/node/lean4game

# Install npm dependencies
echo "=== Installing npm dependencies ==="
npm install
echo "npm install completed!"

# Check package.json scripts
echo "Available npm scripts:"
npm run || true

echo "=== Starting game server ==="
export VITE_LEAN4GAME_SINGLE=true
export HOST=0.0.0.0
export PORT=3000
export VITE_HOST=0.0.0.0
export VITE_PORT=3000

echo "Environment variables:"
echo "VITE_LEAN4GAME_SINGLE=$VITE_LEAN4GAME_SINGLE"
echo "HOST=$HOST"
echo "PORT=$PORT"

echo "Starting server with: npm start -- --host 0.0.0.0 --port 3000"
exec npm start -- --host 0.0.0.0 --port 3000