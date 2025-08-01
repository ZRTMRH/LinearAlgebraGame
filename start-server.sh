#!/bin/bash
# Removed set -e to allow continuing after non-critical failures

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

# Check if game was pre-built, if not try a quick build
echo "=== Checking Lean project build status ==="
if [ -d ".lake/build" ]; then
    echo "Lean project appears to be pre-built during Docker build!"
else
    echo "Lean project not pre-built, attempting quick build..."
    lake build --no-update || echo "Build failed, continuing anyway..."
fi

# Check lean4game directory
echo "=== Checking lean4game directory ==="
ls -la /home/node/lean4game
cd /home/node/lean4game

# Check if npm dependencies are pre-installed
echo "=== Checking npm dependencies ==="
if [ -d "node_modules" ]; then
    echo "npm dependencies already installed during Docker build!"
else
    echo "npm dependencies not found, installing now..."
    npm install
    echo "npm install completed!"
fi

# Check package.json scripts
echo "Available npm scripts:"
npm run || true

echo "=== Starting game server ==="
export VITE_LEAN4GAME_SINGLE=true
export HOST=0.0.0.0

# Use Render's assigned PORT or fallback to 3000 for local development
ASSIGNED_PORT=${PORT:-3000}
export VITE_HOST=0.0.0.0
export VITE_PORT=$ASSIGNED_PORT

echo "Environment variables:"
echo "VITE_LEAN4GAME_SINGLE=$VITE_LEAN4GAME_SINGLE"
echo "HOST=$HOST"
echo "ASSIGNED_PORT=$ASSIGNED_PORT"
echo "PORT (from Render)=${PORT:-'not set'}"

echo "Starting server in production mode for memory efficiency..."
echo "Building production client..."
npm run build_client
echo "Starting production server with: npm run production"
exec npm run production