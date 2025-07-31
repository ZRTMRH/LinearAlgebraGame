import Game.Levels.InnerProductWorld.Level07

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 8

Title "Triangle Inequality for the Norm"

Introduction "
## Triangle Inequality

In any inner product space, the norm satisfies the triangle inequality:
$$\\|u+v\\| \\leq \\|u\\| + \\|v\\|$$

Geometrically, this says the straight-line path is the shortest. In this level, you'll prove this fundamental result using the inner product, the Cauchy–Schwarz inequality, and basic algebra.

## Summary
The triangle inequality is a cornerstone of normed spaces. For any vectors $u$ and $v$, the straight-line distance ($\\|u+v\\|$) is never greater than the sum of the distances ($\\|u\\| + \\|v\\|$).

## Key idea
- Expand $\\|u+v\\|^2$ using the inner product.
- Bound the cross term $2\\,\\Re\\,\\langle u,v\\rangle$ using the Cauchy–Schwarz inequality.
- Finish by taking square roots, using nonnegativity of norm.

This property is what makes $\\|\\cdot\\|$ a norm, ensuring our vector space is a metric space!
"

/--
The triangle inequality is a fundamental property of norms in inner product spaces.
It states that `‖u+v‖ ≤ ‖u‖ + ‖v‖` for any vectors `u` and `v`.
This ensures that the norm defines a proper distance on the vector space.
-/
TheoremDoc LinearAlgebraGame.triangle_v as "Triangle Inequality" in "Norms"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

Statement triangle_v (u v : V) : ‖u+v‖ ≤ ‖u‖ + ‖v‖ := by
  Hint "It's easier to prove the squared version first."
  Hint (hidden := true) "Try `suffices ‖u+v‖^2 ≤ (‖u‖ + ‖v‖)^2 by exact le_of_sq_le_sq this (add_nonneg (norm_nonneg_v u) (norm_nonneg_v v))`"
  suffices ‖u+v‖^2 ≤ (‖u‖ + ‖v‖)^2 by
    Hint (hidden := true) "Try `exact le_of_sq_le_sq this (add_nonneg (norm_nonneg_v u) (norm_nonneg_v v))`"
    exact le_of_sq_le_sq this (add_nonneg (norm_nonneg_v u) (norm_nonneg_v v))
  
  Hint "Expand using the inner product and apply Cauchy-Schwarz."
  Hint (hidden := true) "Try `rw [norm_sq_eq, add_sq, norm_sq_eq, norm_sq_eq]`"
  rw [norm_sq_eq, add_sq, norm_sq_eq, norm_sq_eq]
  
  -- Expand ⟪u+v, u+v⟫.re
  Hint "First expand the inner product ⟪u+v, u+v⟫ using linearity."
  Hint "This will give us ⟪u,u⟫ + ⟪v,v⟫ + ⟪u,v⟫ + ⟪v,u⟫."
  Hint (hidden := true) "Try `have inner_expansion : ⟪u+v, u+v⟫.re = ⟪u,u⟫.re + ⟪v,v⟫.re + 2*⟪u,v⟫.re := by rw [InnerProductSpace_v.inner_add_left, inner_add_right_v, inner_add_right_v]; simp only [Complex.add_re]; rw [InnerProductSpace_v.inner_conj_symm v u, Complex.conj_re]; ring`"
  have inner_expansion : ⟪u+v, u+v⟫.re = ⟪u,u⟫.re + ⟪v,v⟫.re + 2*⟪u,v⟫.re := by
    rw [InnerProductSpace_v.inner_add_left, inner_add_right_v, inner_add_right_v]
    simp only [Complex.add_re]
    rw [InnerProductSpace_v.inner_conj_symm v u, Complex.conj_re]
    ring
    
  Hint (hidden := true) "Try `rw [inner_expansion]`"
  rw [inner_expansion]
  
  -- Use Cauchy-Schwarz to bound the cross term
  Hint "Now we bound the cross term 2*⟪u,v⟫.re using Cauchy-Schwarz."
  Hint "We know |⟪u,v⟫| ≤ ‖u‖ * ‖v‖, so ⟪u,v⟫.re ≤ ‖u‖ * ‖v‖."
  Hint (hidden := true) "Try `have cross_bound : ⟪u,v⟫.re ≤ ‖u‖ * ‖v‖ := by have cs := Cauchy_Schwarz u v; rw [norm_inner_eq_abs] at cs; exact le_trans (re_le_abs ⟪u,v⟫) cs`"
  have cross_bound : ⟪u,v⟫.re ≤ ‖u‖ * ‖v‖ := by
    have cs := Cauchy_Schwarz u v
    rw [norm_inner_eq_abs] at cs
    exact le_trans (re_le_abs ⟪u,v⟫) cs
  
  Hint "Finally, use linear arithmetic to complete the proof."
  Hint (hidden := true) "Try `linarith [cross_bound]`"
  linarith [cross_bound]

Conclusion "
You have proven the triangle inequality!  
This key result guarantees that norm defines a 'distance' on the vector space.
"

end LinearAlgebraGame