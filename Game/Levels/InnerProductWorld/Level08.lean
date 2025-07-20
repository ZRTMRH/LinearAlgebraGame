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
  Hint "It's easier to prove the squared version first: `‖u+v‖^2 ≤ (‖u‖ + ‖v‖)^2`."
  Hint (hidden := true) "Try `suffices ‖u+v‖^2 ≤ (‖u‖ + ‖v‖)^2 by`"
  suffices ‖u+v‖^2 ≤ (‖u‖ + ‖v‖)^2 by
    exact le_of_sq_le_sq this (add_nonneg (norm_nonneg_v u) (norm_nonneg_v v))
  
  Hint "Expand the squared norm using the inner product."
  Hint (hidden := true) "Try `rw [norm_sq_eq]`"
  rw [norm_sq_eq]
  
  Hint "We need to expand `⟪u+v, u+v⟫.re` using linearity of the inner product."
  Hint (hidden := true) "Try `have expand : ⟪u+v, u+v⟫.re = ⟪u,u⟫.re + ⟪v,v⟫.re + 2*⟪u,v⟫.re := by`"
  have expand : ⟪u+v, u+v⟫.re = ⟪u,u⟫.re + ⟪v,v⟫.re + 2*⟪u,v⟫.re := by
    Hint (hidden := true) "Try `rw [InnerProductSpace_v.inner_add_left, inner_add_right_v, inner_add_right_v]`"
    rw [InnerProductSpace_v.inner_add_left, inner_add_right_v, inner_add_right_v]
    Hint (hidden := true) "Try `simp only [Complex.add_re]`"
    simp only [Complex.add_re]
    Hint (hidden := true) "Try `rw [InnerProductSpace_v.inner_conj_symm v u, Complex.conj_re]`"
    rw [InnerProductSpace_v.inner_conj_symm v u, Complex.conj_re]
    Hint (hidden := true) "Try `ring`"
    ring
    
  Hint (hidden := true) "Try `rw [expand, add_sq, norm_sq_eq, norm_sq_eq]`"
  rw [expand, add_sq, norm_sq_eq, norm_sq_eq]
  
  Hint "Bound the cross term `2*⟪u,v⟫.re` by `2*‖u‖*‖v‖` using Cauchy–Schwarz."
  Hint (hidden := true) "Try `have bound := re_le_abs ⟪u,v⟫`"
  have bound := re_le_abs ⟪u,v⟫
  Hint (hidden := true) "Try `have cs := Cauchy_Schwarz u v`"
  have cs := Cauchy_Schwarz u v
  Hint (hidden := true) "Try `rw [norm_inner_eq_abs] at cs`"
  rw [norm_inner_eq_abs] at cs
  Hint (hidden := true) "Try `have cross_bound : ⟪u,v⟫.re ≤ ‖u‖ * ‖v‖ := by linarith [bound, cs]`"
  have cross_bound : ⟪u,v⟫.re ≤ ‖u‖ * ‖v‖ := by linarith [bound, cs]
  Hint (hidden := true) "Try `linarith [cross_bound]`"
  linarith [cross_bound]

Conclusion "
You have proven the triangle inequality!  
This key result guarantees that norm defines a 'distance' on the vector space.
"

end LinearAlgebraGame