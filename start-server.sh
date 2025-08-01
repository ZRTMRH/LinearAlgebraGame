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
exec npm start