import Game.Levels.LinearMapsWorld.Level02

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 3

Title "The Space Where Everything is Zero"

Introduction "
## The Space Where Everything is Zero

Imagine living in a space where every vector is zero.
No movement, no direction—just the origin.
In this level, you show that such a space must have dimension zero.

Your goal: show that any vector space where all elements are zero has dimension zero.
"

open FiniteDimensional
variable (K V : Type) [Field K] [AddCommGroup V] [Module K V]

TheoremDoc LinearAlgebraGame.dim_zero_space as "Zero-Dimensional Space" in "BasisWorld"

/--
If every vector in `V` is zero, then the finite rank of `V` is 0.
-/
Statement dim_zero_space (hV : ∀ v : V, v = 0) : FiniteDimensional.finrank K V = 0 := by
  Hint "We need to show this space has finrank 0. Since every vector is zero, the space is just {0}."
  Hint (hidden := true) "Try `have h_zero : (⊤ : Submodule K V) = ⊥ := by`"
  have h_zero : (⊤ : Submodule K V) = ⊥ := by
    Hint (hidden := true) "Try `ext v`"
    ext v
    Hint (hidden := true) "Try `simp [Submodule.mem_bot, hV v]`"
    simp [Submodule.mem_bot, hV v]
  Hint (hidden := true) "Try `rw [← finrank_top, h_zero]`"
  rw [← finrank_top, h_zero]
  Hint (hidden := true) "Try `exact finrank_bot K V`"
  exact finrank_bot K V

Conclusion
"
The only possible basis for the zero space is the empty set, so its dimension is zero.
"

end LinearAlgebraGame
