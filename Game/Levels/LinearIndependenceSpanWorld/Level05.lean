import Game.Levels.LinearIndependenceSpanWorld.Level04

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 5

Title "Linear Independence of Subsets"

Introduction "
### The Goal
In this level, we will prove that subsets of linearly independent sets are also linearly independent.
This is because if any set of nonzero vectors in the smaller set were to sum to zero, then the same set
of vectors would be in the larger set, and also must sum to zero.

### The `have` tactic
One very powerful tactic that you have not learned yet is the `have` tactic. This tactic allows you
to create your own hypotheses, as long as you can prove that they are correct. This allows you to take
more of a \"forward reasoning\" approach to Lean proofs, as you can create new hypotheses from your old
ones, slowly changing your hypotheses to the goal, instead of changing your goal to the hypotheses.
The syntax for a `have` statement is `have h : 0 • v = 0 := zero_smul_v v`. The `h` is the name of your
new hypothesis, `0 • v = 0` is the statement of the hypothesis, and `zero_smul_v v` is the proof of the
new hypothesis. You can read more about the tactic on the right side of the screen.
"

/--
## Summary
`have` allows you to create your own statements. It allows you to prove hypotheses which you can then
use to prove the goal.

The syntax for `have` is `have h : Hypothesis := proof` to create a hypothesis `h : Hypothesis` where
`proof` is a proof of the hypothesis

## `by`
`by` allows you to write muli-line proofs. When your have statement is a lemma that will take multiple
steps to prove, replacing your proof with `by` will add a subgoal to prove your hypothesis. All the
lines proving this hypothesis will need to be indented.

Using `by` can also only be done in editor mode, which can be accessed by clicking the "<\>" button in the
top right.

## Example
If you want to have a hypothesis `h : 0 • v = 0`, then `have h : 0 • v = 0 := zero_smul_v v` will create
that hypothesis

## Example
If you want to prove a lemma `simple_lemma : ∀ (a b c n : ℕ+), n > 2 → a ^ n + b ^ n ≠ c ^ n`, then
`have simple_lemma : ∀ (a b c n : ℕ+), n > 2 → a ^ n + b ^ n ≠ c ^ n := by` will change the goal to
proving your lemma, and once you prove it, you can then use the lemma.
-/
TacticDoc «have»

/--
`subset_linear_independent` is a proof that if `A` is a linearly independent set, and we have `B ⊆ A`,
then `B` is also linearly independent. The syntax is as follows: if `hBsubA : B ⊆ A` and `hA : linear_independent_v K V A`
are hypotheses, then `subset_linear_independent hBsubA hA` is a proof that `linear_independent_v K V B`.
-/
TheoremDoc LinearAlgebraGame.subset_linear_independent as "subset_linear_independent" in "Vector Spaces"

NewTactic «have»

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/-- If `A` is a linearly independent set, and we have `B ⊆ A`, then `B` is also linearly independent. -/
Statement subset_linear_independent {A B : Set V} (hBsubA : B ⊆ A) (hA : linear_independent_v K V A) :
    linear_independent_v K V B := by
  Hint (hidden := true) "Try `unfold linear_independent_v at *`"
  unfold linear_independent_v at *
  Hint (hidden := true) "Try `intros s f hsB sum_zero v hv`"
  intros s f hsB sum_zero v hv
  Hint "Look at hA. When all the assumptions are met, we get `f v = 0`, which is our goal. This means
  that if we are able to get all of the assumptions as hypotheses, we can solve with an exact statement.
  However, we still don't have a hypothesis that `↑s ⊆ A`."
  Hint (hidden := true) "Try `have hsA : ↑s ⊆ A := subset_trans hsB hBsubA`"
  have hsA : ↑s ⊆ A := subset_trans hsB hBsubA
  Hint "Now, the level can be solved with a (slightly long) `exact` statement"
  Hint (hidden := true) "Try `exact hA s f hsA sum_zero v hv`"
  exact hA s f hsA sum_zero v hv
