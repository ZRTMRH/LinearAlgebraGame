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
export VITE_LEAN4GAME_OWNER=local
export VITE_LEAN4GAME_REPO=game
export NODE_ENV=development
export LEAN4GAME_LOCAL_GAMES=true
export VITE_LEAN4GAME_LOCAL_GAMES=true
export ALLOW_LOCAL_GAMES=true
export HOST=0.0.0.0

# Use Render's assigned PORT or fallback to 3000 for local development
ASSIGNED_PORT=${PORT:-3000}
export VITE_HOST=0.0.0.0
export VITE_PORT=$ASSIGNED_PORT

echo "Environment variables:"
echo "VITE_LEAN4GAME_SINGLE=$VITE_LEAN4GAME_SINGLE"
echo "VITE_LEAN4GAME_OWNER=$VITE_LEAN4GAME_OWNER"
echo "VITE_LEAN4GAME_REPO=$VITE_LEAN4GAME_REPO"
echo "NODE_ENV=$NODE_ENV"
echo "LEAN4GAME_LOCAL_GAMES=$LEAN4GAME_LOCAL_GAMES"
echo "VITE_LEAN4GAME_LOCAL_GAMES=$VITE_LEAN4GAME_LOCAL_GAMES"
echo "ALLOW_LOCAL_GAMES=$ALLOW_LOCAL_GAMES"
echo "HOST=$HOST"
echo "ASSIGNED_PORT=$ASSIGNED_PORT"
echo "PORT (from Render)=${PORT:-'not set'}"

echo "Starting server in production mode for memory efficiency..."
echo "Client should be pre-built during Docker build phase..."
echo "Checking games directory structure..."
ls -la /home/node/lean4game/games/
ls -la /home/node/lean4game/games/local/ || echo "local directory not found"
echo "Checking if our game symlink exists..."
ls -la /home/node/lean4game/games/local/game || echo "game symlink not found"
echo "Checking game directory contents..."
ls -la /home/node/game/
echo "Checking if Game.lean exists at symlink target..."
ls -la /home/node/lean4game/games/local/game/Game.lean || echo "Game.lean not found through symlink"
echo "Verifying lean4game relay server exists..."
if [ -f "/home/node/lean4game/relay/index.mjs" ]; then
    echo "✅ Relay server found!"
else
    echo "❌ Relay server not found - this shouldn't happen!"
    exit 1
fi
echo "Starting server with local games enabled..."
cd /home/node/lean4game
export PORT=$ASSIGNED_PORT

# Aggressive workarounds for Lean server finalizeExtensions deadlock in Render
export LEAN_SERVER_ARGS="--server --no-worker --memory=1024"
export LEAN_NO_CACHE=1
export LEAN_WATCHDOG_TIMEOUT=30
export NODE_OPTIONS="--max-old-space-size=1024 --no-warnings"

echo "Applied Lean server deadlock workarounds for Render environment..."

# Create a restart loop to handle finalizeExtensions hangs
echo "Starting automatic restart loop to handle Lean server hangs..."
while true; do
    echo "[$(date)] Starting Lean4Game server (attempt $((++attempt)))"
    
    # Start server with 2-minute timeout
    timeout 120 node relay/index.mjs
    exit_code=$?
    
    if [ $exit_code -eq 124 ]; then
        echo "[$(date)] Server timed out (likely finalizeExtensions hang), restarting..."
    elif [ $exit_code -eq 0 ]; then
        echo "[$(date)] Server exited normally"
        break
    else
        echo "[$(date)] Server crashed with exit code $exit_code, restarting..."
    fi
    
    # Brief pause before restart
    sleep 2
done