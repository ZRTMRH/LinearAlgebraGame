import Game.Levels.LinearIndependenceSpanWorld.Level03

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 4

Title "Monotonicity of Span"

Introduction "
### The Goal
In this level, you will prove that the span of a set of vectors is monotonic. That is, that if `A ⊆ B`,
then `span K V A ⊆ span K V B`. To understand why this is true, think about any arbitrary vector `x ∈ span K V A`.
`x` must be a linear combination of vectors of `A`, and since all those vectors are in `A`, they must
also be in `B`, so `x` is a linear combination of vectors in `B`, and must be in `span K V B`.

### `subset_trans`
To solve this level, we need a theorem `subset_trans`. This theorem shows that subsets are transitive,
so if you have `h1 : A ⊆ B` and `h2 : B ⊆ C`, then `subset_trans h1 h2` is a proof that `A ⊆ C`. This can be proven quite easily, but since we have
a theorem already proving it, why not use it?
"

/--
`subset_trans` is a proof that subsets are transitive. The syntax is that if you have `h1 : A ⊆ B`
and `h2 : B ⊆ C`, then `subset_trans h1 h2` is a proof that `A ⊆ C`.
-/
TheoremDoc subset_trans as "subset_trans" in "Sets"

/--
`span_mono` is a proof that the span of sets is monotonic. Simply, this means that if you have `h : A ⊆ B`,
then `span_mono K V h` is a proof that `span K V A ⊆ span K V B`.
-/
TheoremDoc LinearAlgebraGame.span_mono as "span_mono" in "Vector Spaces"

NewTheorem subset_trans

TheoremTab "Sets"

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/-- The span of sets is monotonic. Simply, this means that if you have `h : A ⊆ B`,
then `span_mono K V h` is a proof that `span K V A ⊆ span K V B`. -/
Statement span_mono {A B : Set V} (hAB : A ⊆ B) : span K V A ⊆ span K V B := by
  Hint "First, I would take an arbitrary `x`, then unfold and simplify our goals."
  Hint (hidden := true) "Try `intro x hxA`"
  intro x hxA
  Hint (hidden := true) "Try `unfold span at *`"
  unfold span at *
  Hint (hidden := true) "Try `unfold is_linear_combination at *`"
  unfold is_linear_combination at *
  Hint (hidden := true) "Try `simp at *`"
  simp at *
  Hint "Now, what information can we get out of {hxA}?"
  Hint (hidden := true) "Try `obtain ⟨s, hsA, f, h1, h2⟩ := hxA`"
  obtain ⟨s, hsA, f, h1, h2⟩ := hxA
  Hint "What set should we be summing over?"
  Hint (hidden := true) "Try `use s`"
  use s
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint (hidden := true) "Try `exact subset_trans hsA hAB`"
  exact subset_trans hsA hAB
  Hint "What function should we be using?"
  Hint (hidden := true) "Try `use f`"
  use f

Conclusion "The idea of unfolding all the definitions and then using `simp at *` is very helpful. I
would recommend using this sequence of tactics at the start of most levels.

Also, note that `use f` closed the goal. This is because the `use` tactic attempts `rfl` after it
executes, similarly to `rw`."
