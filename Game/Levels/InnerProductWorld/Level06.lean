import Game.Levels.InnerProductWorld.Level05

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 6

Title "Orthogonal Decomposition"

Introduction "
One of the most important theorems in linear algebra is orthogonal decomposition. This allows you to
represent a vector as a scalar multiple of one vector, along with a vector orthogonal to that vector.
This includes the concepts of projections and othogonal components.

## The Goal
In this level, we are given two vectors, `u` and `v`. `u` is the vector we want to rewrite, and `v`
is the vector we are scaling and getting the orthogonal component of. We also assume `h : v ≠ 0`. From
this, we can calculate our sum as `u = (⟪u,v⟫ / (‖v‖^2)) • v + (u - (⟪u,v⟫ / (‖v‖^2)) • v))`. The equality
is trivial, since we are adding and subtracting the same vector to `u` on the right side. Also,
`(⟪u,v⟫ / (‖v‖^2)) • v` is clearly a scalar multiple of `v`. The only thing we have to prove is that
`v` is orthogonal to `u - ((⟪u,v⟫ / (‖v‖^2)) • v)`.
"

/--
`ortho_decom` is a proof that given vectors `u v : V` and `h : v ≠ 0`, then `orthogonal (u - (⟪u,v⟫ / (‖v‖^2)) • v) v`.
This allows you to rewrite `u` as a scalar multiple of `v` added to a vector orthogonal to `v`. 
-/
TheoremDoc LinearAlgebraGame.ortho_decom as "ortho_decom" in "Inner Product"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

Statement ortho_decom (u v : V) (h : v ≠ 0) : orthogonal (u - (⟪u,v⟫ / (‖v‖^2)) • v) v := by
  Hint "Start by unfolding the definition of orthogonal."
  Hint (hidden := true) "Try `unfold orthogonal`"
  unfold orthogonal
  Hint "Expand the inner product using linearity properties."
  Hint (hidden := true) "Try `rw[inner_minus_left, InnerProductSpace_v.inner_smul_left]`"
  rw[inner_minus_left, InnerProductSpace_v.inner_smul_left]
  Hint "Simplify the norm squared expression."
  Hint (hidden := true) "Try `unfold norm_v`"
  unfold norm_v
  Hint (hidden := true) "Try `norm_cast`"
  norm_cast
  Hint (hidden := true) "Try `rw[sq_sqrt (inner_self_nonneg v), ← inner_self_real]`"
  rw[sq_sqrt (inner_self_nonneg v), ← inner_self_real]
  Hint "Use ring operations to simplify the algebra."
  Hint (hidden := true) "Try `ring_nf`"
  ring_nf
  Hint "The key step: cancel ⟪v,v⟫ in numerator and denominator."
  Hint (hidden := true) "Try `rw[mul_assoc, mul_inv_cancel]`"
  rw[mul_assoc, mul_inv_cancel]
  Hint (hidden := true) "Try `simp`"
  simp
  Hint "We need v ≠ 0 to ensure ⟪v,v⟫ ≠ 0 for cancellation."
  Hint (hidden := true) "Try `intro x`"
  intro x
  Hint (hidden := true) "Try `exact h ((inner_self_eq_zero v).1 x)`"
  exact h ((inner_self_eq_zero v).1 x)

end LinearAlgebraGame
