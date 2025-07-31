# Autonomous Work Order for Claude Code - July 20, 2025

```
Task: Complete LinearMapsWorld educational redesign following Axler's approach
Scope: Implement Phase 1-3 as outlined in SESSION_SUMMARY_2025_07_20_LinearMapsWorld_Analysis.md, and try to shorten the proofs of all worlds
Constraints:
- Do this in a new branch called "LinearMapsRewrite"
- You have full authority to make implementation decisions
- Write a local summary at 12pm each day of your work done today on this project, labeled with date
- Write a local summary after you finish each Phase, labeled with date and phase number
- only do the work from 6pm to 5am each day (i.e. during night time), do not work in other time slots
- Follow custom educational definition pattern from other worlds
- Maintain mathematical rigor and pedagogical quality
- Ensure complete game builds successfully
- If you encounter build errors or API changes, fix them using best judgment. Document all changes and reasoning.
- When shortening the proofs, do not cut off hints. You should try to write a mathematically shorter proof with less lean4 lines needed.
- If you use a lemma or tactic that's not introducted, you must add its documentation, similar to what was done in other worlds.
- Check among other worlds if tactics and lemmas are introduced with proper documentation. If not, add them.
- Research how to best implement rank-nullity theorem educationally and create implementation plan
Success Criteria:
- All 7+ levels redesigned with Axler-inspired content
- Custom definitions (is_linear_map_v, null_space_v, range_v, e.g.) implemented
- Zero build errors, zero sorry statements
- Remove `set_option checkBinderAnnotations false` from all levels (also considered "cheating")
- Educational hints and progression consistent with other worlds
- All Lemma and tactic used are introduced properly with valid documentation
- Attempt made to shorten proof in each levels, while not diminishing the theorems themselves
Context Files:
- SESSION_SUMMARY_2025_07_20_LinearMapsWorld_Analysis.md
- CLAUDE.md
- Existing world files for educational patterns



You have my permission to work autonomously on this during token refresh periods. But you can only work at night (6pm to 5am, i.e)
```

## **Emergency Protocols**
- **Build Failures**: Focus on fixing rather than adding new content
- **Compatibility Issues**: Update APIs conservatively, document changes
- **Mathematical Errors**: Prioritize correctness over completion
- **Scope Creep**: Stay within assigned project boundaries

**Created**: July 20, 2025
