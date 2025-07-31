# Autonomous Work Template for Claude Code - July 20, 2025

## Template for Task Assignment

### **Basic Assignment Format**
```
Task: [Brief description]
Scope: [What to accomplish]
Constraints: [Any limitations or requirements]
Success Criteria: [How to know when done]
Context Files: [Reference documents to read]
```

### **Example Assignment for LinearMapsWorld Redesign**
```
Task: Complete LinearMapsWorld educational redesign following Axler's approach
Scope: Implement Phase 1-3 as outlined in SESSION_SUMMARY_2025_07_20_LinearMapsWorld_Analysis.md
Constraints:
- Follow custom educational definition pattern from other worlds
- Maintain mathematical rigor and pedagogical quality
- Ensure complete game builds successfully
Success Criteria:
- All 7 levels redesigned with Axler-inspired content
- Custom definitions (is_linear_map_v, null_space_v, range_v) implemented
- Zero build errors, zero sorry statements
- Educational hints and progression consistent with other worlds
Context Files:
- SESSION_SUMMARY_2025_07_20_LinearMapsWorld_Analysis.md
- CLAUDE.md
- Existing world files for educational patterns
```

## **Suggestions for Autonomous Work Sessions**

### **1. Clear Mandate Strategy**
**Best for**: Complex projects requiring multiple sessions
**Format**: Give comprehensive project assignment with full authority to make implementation decisions
**Example**: "Complete the entire LinearMapsWorld redesign project. You have full authority to make design decisions consistent with the educational approach. Ensure mathematical correctness and build success."

### **2. Phased Assignment Strategy**
**Best for**: Large projects where you want control over direction
**Format**: Assign specific phases with checkpoints
**Examples**:
- "Phase 1: Create custom linear map definitions and basic lemmas"
- "Phase 2: Implement Levels 1-3 following Axler's progression"
- "Phase 3: Complete advanced levels (rank-nullity, isomorphisms)"

### **3. Problem-Solving Authority Strategy**
**Best for**: When you want work to continue despite obstacles
**Format**: Give problem-solving authority within scope
**Example**: "If you encounter build errors or API changes, fix them using best judgment. Document all changes and reasoning."

### **4. Research and Planning Strategy**
**Best for**: When unsure about approach
**Format**: Ask for analysis and detailed plans
**Example**: "Research how to best implement rank-nullity theorem educationally and create implementation plan"

## **Resumption Strategies**

### **Method 1: Reference Session Summaries**
```
"Resume work on LinearMapsWorld redesign. Read AUTONOMOUS_WORK_Order_7_20.md for context and continue from where left off."
```

### **Method 2: Check Git Status and Continue**
```
"Check git status for uncommitted work on LinearMapsWorld, review recent commits, and continue the educational redesign project."
```

### **Method 3: Build Status Assessment**
```
"Test current build status, identify any LinearMapsWorld issues, and continue fixing/implementing per the redesign plan."
```

## **Communication Templates**

### **Assignment Message Template**
```
PROJECT ASSIGNMENT:

Task: [Description]
Authority Level: [Full/Limited/Consultation-required]
Timeline: [Work during token refresh periods / Complete by next session]
Quality Standards: [Mathematical rigor, educational consistency, build success]
Documentation: [Update session summaries, commit messages, etc.]

CONTEXT:
- Read: [relevant files]
- Follow patterns from: [reference implementations]
- Constraints: [any limitations]

SUCCESS DEFINITION:
[Clear criteria for completion]

You have my permission to work autonomously on this during token refresh periods.
```

### **Check-in Message Template**
```
PROJECT CHECK-IN:

What did you accomplish during autonomous work?
Any obstacles encountered and how resolved?
Current status and next steps?
Any decisions made that need review?
```

## **Recommended Autonomous Work Projects**

### **High Confidence Projects** (Safe to assign autonomously)
1. ✅ **LinearMapsWorld Redesign** - Well-planned, clear requirements
2. ✅ **Bug Fixes and Build Issues** - Clear success criteria
3. ✅ **Educational Content Enhancement** - Following established patterns
4. ✅ **Documentation and Comments** - Low risk, high value

### **Medium Confidence Projects** (Require clear guidelines)
1. 🟡 **New World Creation** - Need educational scope definition
2. 🟡 **Advanced Mathematical Content** - Need mathematical approach clarity
3. 🟡 **Game Framework Changes** - Need compatibility requirements

### **Consultation Required Projects**
1. 🔴 **Major Architectural Changes** - Need approval
2. 🔴 **Educational Philosophy Changes** - Need direction
3. 🔴 **External Dependencies** - Need permission

## **File References for Context**
- **`CLAUDE.md`** - Project overview and development guidelines
- **`SESSION_SUMMARY_2025_07_20_LinearMapsWorld_Analysis.md`** - Detailed redesign plan
- **`Game/Levels/VectorSpaceWorld/`** - Educational pattern reference
- **`Game/Levels/InnerProductWorld/`** - Mathematical rigor examples

## **Quality Assurance Checklist**
- [ ] Complete build success (`lake build`)
- [ ] Zero sorry statements in core content
- [ ] Educational hints and progression consistent
- [ ] Mathematical correctness verified
- [ ] Proper git commits with clear messages
- [ ] Documentation updated appropriately

## **Emergency Protocols**
- **Build Failures**: Focus on fixing rather than adding new content
- **Compatibility Issues**: Update APIs conservatively, document changes
- **Mathematical Errors**: Prioritize correctness over completion
- **Scope Creep**: Stay within assigned project boundaries

---

**Created**: July 20, 2025
**Purpose**: Template for autonomous work assignments during token refresh periods
**Status**: Ready for use
