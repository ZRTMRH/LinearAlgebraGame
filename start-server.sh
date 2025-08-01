#!/bin/bash

# Navigate to the game directory
cd /home/node/game

# Update and build the Lean project
echo "Building Lean project..."
lake update -R
lake build

# Navigate to lean4game directory and start server
cd /home/node/lean4game
echo "Installing npm dependencies..."
npm install

echo "Starting game server..."
export VITE_LEAN4GAME_SINGLE=true
export HOST=0.0.0.0
export PORT=3000
# Also try Vite-specific environment variables
export VITE_HOST=0.0.0.0
export VITE_PORT=3000
exec npm start -- --host 0.0.0.0 --port 3000