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
  unfold orthogonal
  rw[inner_minus_left]
  rw[InnerProductSpace_v.inner_smul_left]
  unfold norm_v
  norm_cast
  rw[sq_sqrt (inner_self_nonneg v)]
  rw [← inner_self_real]
  ring_nf
  rw[mul_assoc, mul_inv_cancel]
  simp
  intro x
  apply h
  exact (inner_self_eq_zero v).1 x

end LinearAlgebraGame
