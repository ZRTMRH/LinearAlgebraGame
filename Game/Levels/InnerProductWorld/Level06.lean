import Game.Levels.InnerProductWorld.Level05

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 6

Title "Orthogonal Decomposition"

Introduction "
One of the most important theorems in linear algebra is orthogonal decomposition. This allows you to
represent a vector as a scalar multiple of one vector, along with a vector orthogonal to that vector.
This includes the concepts of projections and orthogonal components.

## The Goal
In this level, we are given two vectors, `u` and `v`. `u` is the vector we want to rewrite, and `v`
is the vector we are scaling and getting the orthogonal component of. We also assume `h : v ≠ 0`. From
this, we can calculate our sum as `u = (⟪u,v⟫ / (‖v‖^2)) • v + (u - (⟪u,v⟫ / (‖v‖^2)) • v))`. The equality
is trivial, since we are adding and subtracting the same vector to `u` on the right side. Also,
`(⟪u,v⟫ / (‖v‖^2)) • v` is clearly a scalar multiple of `v`. The only thing we have to prove is that
`v` is orthogonal to `u - ((⟪u,v⟫ / (‖v‖^2)) • v)`.

**Note:** If you see hints appearing multiple times, this is a known issue with the game framework. Simply continue with your proof - the level will work correctly despite any duplicate hints.
"

/--
`ortho_decom` is a proof that given vectors `u v : V` and `h : v ≠ 0`, then `orthogonal (u - (⟪u,v⟫ / (‖v‖^2)) • v) v`.
This allows you to rewrite `u` as a scalar multiple of `v` added to a vector orthogonal to `v`.
-/
TheoremDoc LinearAlgebraGame.ortho_decom as "ortho_decom" in "Inner Product"

/--
`inner_minus_left` extends linearity of the inner product in the first argument to subtraction:
`⟪u - v, w⟫ = ⟪u, w⟫ - ⟪v, w⟫`.
-/
TheoremDoc LinearAlgebraGame.inner_minus_left as "inner_minus_left" in "Inner Product"

/--
`inner_self_real` states that in a complex inner product space, `⟪v,v⟫` is always a real number:
`⟪v,v⟫ = (⟪v,v⟫.re : ℂ)`.
-/
TheoremDoc LinearAlgebraGame.inner_self_real as "inner_self_real" in "Inner Product"

NewTheorem LinearAlgebraGame.inner_self_nonneg LinearAlgebraGame.inner_self_eq_zero LinearAlgebraGame.inner_minus_left LinearAlgebraGame.inner_self_real

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [InnerProductSpace_v V]
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
  Hint (hidden := true) "Try `rw[sq_sqrt (LinearAlgebraGame.inner_self_nonneg v), ← inner_self_real]`"
  rw[sq_sqrt (LinearAlgebraGame.inner_self_nonneg v), ← inner_self_real]
  Hint "Use ring operations to simplify the algebra."
  Hint (hidden := true) "Try `ring_nf`"
  ring_nf
  Hint "The key step: cancel ⟪v,v⟫ in numerator and denominator."
  Hint (hidden := true) "Try `rw[mul_assoc]` then use `suffices` to show ⟪v,v⟫ ≠ 0"
  rw[mul_assoc]
  Hint "We need v ≠ 0 to ensure ⟪v,v⟫ ≠ 0 for cancellation."
  Hint (hidden := true) "Try `suffices h_nonzero : ⟪v, v⟫ ≠ 0`"
  suffices h_nonzero : ⟪v, v⟫ ≠ 0
  Hint (hidden := true) "Try `field_simp [h_nonzero]`"
  · field_simp [h_nonzero]
    Hint (hidden := true) "Try `ring`"
    ring
  Hint "Now prove that ⟪v,v⟫ ≠ 0 when v ≠ 0"
  Hint (hidden := true) "Try `intro contr`"
  intro contr
  Hint (hidden := true) "Try `apply h`"
  apply h
  Hint (hidden := true) "Try `exact (LinearAlgebraGame.inner_self_eq_zero v).1 contr`"
  exact (LinearAlgebraGame.inner_self_eq_zero v).1 contr

end LinearAlgebraGame
