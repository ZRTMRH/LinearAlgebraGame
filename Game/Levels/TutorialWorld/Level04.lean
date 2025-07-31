import Game.Metadata.Metadata

World "TutorialWorld"
Level 4
Title "The `constructor` tactic"


/--
## Summary

The constructor tactic splits the goal into multiple parts. This is helpful for goals that are
difficult to solve all at once, like "and" (`∧`) and "if and only if" (`↔`).

## Example

If we have the goal `P ∧ Q`, `constructor` will change the goal into two goals: `P` and `Q`.

## Example

If we have the goal`P ↔ Q`, `constructor` will change the goal into two goals: `P → Q`, and `Q → P`.
-/
TacticDoc constructor

NewTactic constructor

Introduction "
In this level we will learn `constructor` in the context of logical 'and' (∧).
Our goal is to prove `P ∧ Q`, \"P and Q\", given hypotheses `p: P` and `q: Q`.

### Constructor:

The `constructor` tactic works by splitting up the goal. If you have a goal `P ∧ Q`, the tactic makes
progress by turning this one goal into two goals: to prove `P` and to prove `Q`. Constructor also
works similarly for `↔` \"if and only if\" goals.
"

Statement (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  Hint "Try using `constructor` to split up the goal."
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint "Both remaining goals are exactly your hypotheses. What tactic can solve the goals?"
  Hint (hidden := true) "Try `exact p`"
  exact p
  Hint (hidden := true) "Try `exact q`"
  exact q

Conclusion "
You can now prove goals by splitting them into multiple steps with the `constructor` tactic!
"
