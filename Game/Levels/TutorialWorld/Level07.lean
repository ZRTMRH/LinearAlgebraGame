import Game.Metadata.Metadata

World "TutorialWorld"
Level 7
Title "The `linarith` tactic"

/--
## Summary
The `linarith` tactic simplifies the goal by using the hypotheses. It works well on linear inequalities
and equalities. It works by looking for contradictions, although the actual algorithmic implementation
is very complicated.

## Example

If you have a bunch of hypotheses like h1 : a < b, h2 : b <= c, h3 : c = d and a goal of a < d,
then linarith will solve it. Linarith knows how to combine linear relations: it knows a ton of
results about how to put inequalities together and will close such goals.
-/
TacticDoc linarith

NewTactic linarith

Introduction "
The `linarith` tactic aims to simplify the process of proofs. Specifically, it solves certain kinds
of linear equalities and inequalities. It attempts to solve or simplify the goal using the hypotheses
and certain properties of the numbers you are working with.
"

Statement (x y a b : ℝ) (h1 : x < y) (h2: a < b) : x + a < y + b := by
  Hint "In this level, simply trying `linarith` should solve the level."
  Hint (hidden := true) "Try `linarith`"
  linarith

Conclusion "
Linarith is very useful to simplify goals involving linear terms.
"
