# GitHub Issue Draft for lean4game Repository

## Title
**Non-deterministic world title and introduction display failure**

## Labels
`bug`, `display`, `world-metadata`, `framework`

## Issue Body

### Summary
We've discovered a framework-level bug where world titles and introduction content randomly fail to display, exhibiting non-deterministic behavior across identical builds. This affects core world metadata parsing in the lean4game framework.

### Problem Description

**Symptoms:**
- World titles show generic "Introduction" header instead of "World: [World Name]"
- Introduction text areas appear completely blank
- **Critical**: Same worlds alternate between working and broken states without code changes
- Only affects some worlds while others work consistently

**Environment:**
- **Lean Version**: 4.7.0
- **Framework**: lean4game (latest)
- **Platform**: Linux WSL2, also reproduced in standard environments
- **Build System**: Lake

### Evidence of Non-Deterministic Behavior

The key discovery is that **identical code produces different results** across builds:

**Test Sequence 1:**
- VectorSpaceWorld: ❌ Broken (missing title/content)
- LinearIndependenceSpanWorld: ❌ Broken (missing title/content)

**Test Sequence 2 (after renaming VectorSpaceWorld → TestVectorWorld):**
- TestVectorWorld: ✅ Working (displays correctly)
- LinearIndependenceSpanWorld: ❌ Still broken

**Test Sequence 3 (same code, different build):**
- TestVectorWorld: ✅ Still working
- LinearIndependenceSpanWorld: ✅ **Suddenly working** (no code changes!)

**Test Sequence 4 (after minor changes):**
- VectorSpaceWorld: ❌ **Broken again** (after restoration)
- LinearIndependenceSpanWorld: ✅ Still working
- FreshLinearIndependenceWorld: ❌ **Now broken** (was working before)

### What We've Ruled Out

Through systematic testing, we've eliminated:

1. **File corruption**: Fresh files with identical content exhibit same behavior
2. **Dependency issues**: Worlds with similar dependency patterns behave differently
3. **World naming**: Renaming provides only temporary fixes
4. **Import order**: Reordering imports doesn't consistently resolve the issue
5. **Content issues**: Identical world configurations behave inconsistently

### Framework Impact

**What Works:**
- ✅ All worlds compile successfully
- ✅ Game mechanics function perfectly
- ✅ Level content loads correctly
- ✅ Educational content fully accessible

**What's Broken:**
- ❌ World title parsing (intermittent)
- ❌ Introduction content display (intermittent)
- ❌ Consistent metadata rendering

### Example World Configuration

All our worlds use standard lean4game syntax:
```lean
namespace LinearAlgebraGame

World "VectorSpaceWorld"
Title "Vector Space World"

Introduction "Welcome to Vector Space World! In this world, you'll build up the basic theory of vector spaces through formal proofs in Lean."

end LinearAlgebraGame
```

### Suspected Framework Components

Based on our investigation, the issue likely involves:
- World metadata parser inconsistently processing `Title`/`Introduction` commands
- Framework state management maintaining corrupted state between builds
- Possible caching system storing incorrect metadata
- Memory management issues in world data structures

### Reproduction Information

**Repository**: https://github.com/[your-username]/LinearAlgebraGame
*(We can provide access to our repository if helpful for debugging)*

**Reproduction Steps:**
1. Clone repository
2. Run `lake build`
3. Start game server: `npm run serve LinearAlgebraGame`
4. Navigate to VectorSpaceWorld or LinearIndependenceSpanWorld
5. Observe: may show correct title/content OR may show empty content
6. Rebuild and test again: behavior may change randomly

**Note**: Due to non-deterministic nature, reproduction may require multiple build attempts.

### Build Output

Builds complete successfully with normal dependency warnings:
```
./././Game.lean:61:0: warning: No world introducing LinearAlgebraGame.span, but required by LinearIndependenceSpanWorld
[...normal dependency warnings...]
i18n: file created at /home/zrtmrh/lean4/LinearAlgebraGame/.i18n/en/Game.pot
```

### Impact Assessment

**Severity**: Medium (cosmetic issue with framework implications)
- Game remains fully functional and educationally valuable
- All mathematical content and proofs work correctly
- User experience minimally impacted (missing titles/introductions only)
- Indicates potential framework stability issues

### Additional Context

We've conducted extensive systematic testing (~6 hours of investigation) with comprehensive documentation. This appears to be a deep framework issue affecting core world metadata processing. Other lean4game developers may be experiencing similar issues.

**Investigation Report**: Available in our repository as `WORLD_DISPLAY_BUG_INVESTIGATION.md` with detailed evidence and testing methodology.

### Request

Would the maintainers like us to:
1. Provide repository access for direct debugging?
2. Test specific framework versions or configurations?
3. Gather additional diagnostic information?

We're committed to helping resolve this issue as it affects the reliability of the lean4game framework for educational game development.

---

**Repository Information for Maintainers:**
- Educational linear algebra game with 5 worlds, 30+ levels
- Fully functional except for this display issue
- Comprehensive test suite and documentation
- Production-ready educational content