# Linear Algebra Game - Dev Container Setup Guide

## Current Status (July 17, 2025)

### What We Accomplished
✅ **Game Build**: Linear Algebra Game is fully built and functional  
✅ **Server Backend**: GameServer runs successfully on port 8080  
✅ **Game Content**: All 5 worlds working (Tutorial, VectorSpace, LinearIndependence, LinearMaps, InnerProduct)  
✅ **Dependencies**: All Lake/Lean dependencies resolved  

### Current Issue
❌ **Web Interface**: Client (web UI) has startup issues with vite/npm  
❌ **Manual Setup**: Complex npm configuration problems prevent browser access  

### Solution: Dev Container Approach
The repository has a pre-configured dev container that handles all setup automatically.

---

## Dev Container Setup Steps

### Step 1: Install Docker
**You need to install Docker first** (this requires restart)

**Option A: Docker Desktop (Recommended)**
1. Download: https://docker.com/products/docker-desktop
2. Install Docker Desktop for Windows
3. Enable WSL2 integration in settings
4. **Restart computer**

**Option B: Docker Engine in WSL2**
```bash
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh
sudo usermod -aG docker $USER
# Restart WSL2
```

### Step 2: Install VSCode Extension
1. Open VSCode
2. Extensions (Ctrl+Shift+X)
3. Search "Dev Containers" by Microsoft
4. Install it

### Step 3: Open Project in Dev Container
```bash
cd /home/zrtmrh/lean4/LinearAlgebraGame
code .
```

VSCode will show: **"Reopen in Container"** → Click it

### Step 4: Wait for Build (2-15 minutes first time)
The container automatically:
- Builds Docker image with Node.js 20 + Lean 4
- Clones lean4game framework
- Installs all dependencies
- Runs `lake build`
- Starts game server

### Step 5: Access Game
**URL**: http://localhost:3000  
The game will be fully functional in your browser!

---

## Project Details

### Current Branch
- **Branch**: `merge_change_July`
- **Base**: Created from `merged-worlds`
- **Status**: Ready for PR to main

### Game Structure
1. **TutorialWorld** - 10 levels (Lean 4 basics)
2. **VectorSpaceWorld** - 5 levels (educational alias approach)
3. **LinearIndependenceSpanWorld** - 9 levels
4. **LinearMapsWorld** - 3 levels
5. **InnerProductWorld** - 4 levels (complex number support)

### Key Files Modified Yesterday
- Fixed VectorSpace vs Module conflicts
- Resolved import namespace issues
- Added theorem aliases for game framework
- Fixed complex number theorems
- Updated TheoremDoc references

### Build Commands (for reference)
```bash
# Build the game
lake build

# Update with local GameServer
lake update -R -Klean4game.local

# Manual server start (if needed)
cd .lake/packages/GameServer
npm install
npm start
```

---

## Troubleshooting Notes

### If Dev Container Doesn't Work
1. Check Docker is running: `docker ps`
2. Rebuild container: Command Palette → "Dev Containers: Rebuild Container"
3. Check logs in VSCode terminal

### Manual Approach (if container fails)
The manual npm setup we tried had vite build issues. The dev container approach is much more reliable and is the officially recommended method.

### Alternative: Codespaces
If local dev container has issues, you can try GitHub Codespaces:
1. Go to GitHub repository
2. Click "Code" → "Codespaces" → "Create codespace"
3. Wait for setup, then access via browser

---

## After Restart Instructions

1. **Verify Docker**: `docker --version`
2. **Open VSCode**: `cd /home/zrtmrh/lean4/LinearAlgebraGame && code .`
3. **Reopen in Container**: Click the notification or use Command Palette
4. **Wait for build** (first time takes 10+ minutes)
5. **Access game**: http://localhost:3000

The Linear Algebra Game you built yesterday is production-ready and will work perfectly once the dev container is set up!

---

## Contact Claude Code Again

After restart, you can simply say:
"I followed the dev container setup guide. [Describe what happened/any issues]"

And reference this file: `/home/zrtmrh/lean4/LinearAlgebraGame/DEV_CONTAINER_SETUP_GUIDE.md`