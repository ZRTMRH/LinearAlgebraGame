# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a **Linear Algebra Game** built using the [lean4game](https://github.com/leanprover-community/lean4game) framework. It's an educational game that teaches linear algebra concepts through interactive theorem proving in Lean 4, based on Sheldon Axler's "Linear Algebra Done Right" textbook.

## Build System and Development Commands

The project uses Lake (Lean 4's build system):

- `lake build` - Build the entire project
- `lake clean` - Remove build outputs
- `lake update` - Update dependencies and save to manifest
- `lake exe <exe>` - Build and run an executable
- `lake env <cmd>` - Execute command in Lake's environment

## Project Structure

### Core Game Files
- `Game.lean` - Main game configuration with title, introduction, and world dependencies
- `Game/Data.lean` - Extensive mathlib imports for mathematical definitions
- `Game/Metadata/Metadata.lean` - Game metadata and server commands
- `Game/MyTactic.lean` - Custom tactic imports for the game

### Game Worlds (Educational Levels)
The game is organized into sequential worlds:

1. **TutorialWorld** (`Game/Levels/TutorialWorld/`) - Introduction to Lean 4 basics
2. **VectorSpaceWorld** (`Game/Levels/VectorSpaceWorld/`) - Vector space concepts
3. **LinearIndependenceSpanWorld** (`Game/Levels/LinearIndependenceSpanWorld/`) - Linear independence and span

Each world:
- Has a main `.lean` file (e.g., `TutorialWorld.lean`) that imports all levels
- Contains individual level files (`Level01.lean`, `Level02.lean`, etc.)
- Uses the `World`, `Level`, `Title`, `Introduction`, `Statement`, `Conclusion` commands

### Level Management
- `sofi.sh` - Script for reordering and renaming level files within worlds
- Levels must follow `L**.lean` or `L**_*****.lean` naming convention
- The script automatically updates level numbers and imports

## Key Dependencies

- **Lean 4.7.0** - The proof assistant
- **mathlib 4.7.0** - Comprehensive mathematics library
- **lean4game** - Game framework (local or remote depending on `LEAN4GAME` env var)
- **checkdecls** - Declaration checking tool (currently experiencing compatibility issues)

## Development Workflow

1. **Adding New Levels**: Create level files following naming convention, then run `./sofi.sh <world_path>` to reorder
2. **Level Structure**: Each level includes `World`, `Level`, `Title`, `Introduction`, `Statement`, `Conclusion`
3. **Tactic Documentation**: Use `TacticDoc` and `NewTactic` commands to document tactics
4. **World Dependencies**: Configure in `Game.lean` (e.g., VectorSpaceWorld → LinearIndependenceSpanWorld)

## Mathematical Content

The game covers:
- Vector spaces and their properties
- Linear independence and span
- Bases and linear transformations
- Proof techniques using Lean 4 tactics (`rfl`, `apply`, `intro`, etc.)

## Local Development

For local development with the game framework:
- Set `LEAN4GAME.local=true` in Lake configuration
- Ensure the lean4game server is available at `../lean4game/server`
- Use `lake build` to compile the game
- The game generates a web interface for interactive theorem proving

## Architecture Notes

- **Game Framework Integration**: Uses lean4game's `GameServer.Commands` for web interface
- **Tactic System**: Imports extensive mathlib tactics while filtering some for educational purposes
- **World Organization**: Sequential progression with dependency management
- **Educational Design**: Focuses on proof techniques rather than computation

## Known Issues

### Blueprint CI Failure (Commit 26b662f)
The blueprint setup commit fails in CI due to checkdecls compatibility issues:
- **Issue**: checkdecls package has syntax errors with current Lean 4.7.0
- **Temporary Fix**: Checkdecls step is commented out in `.github/workflows/blueprint.yml`
- **Resolution**: Need to update checkdecls to a compatible version or fix the syntax issue
- **Files affected**: `lakefile.lean`, `blueprint/lean_decls`, `.github/workflows/blueprint.yml`

### Checkdecls Usage
- `blueprint/lean_decls` should list Lean declarations referenced in blueprint
- Currently empty as blueprint content is minimal
- Use `--` for comments in `lean_decls` file, not `#`