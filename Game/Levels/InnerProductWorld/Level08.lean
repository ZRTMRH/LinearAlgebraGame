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

-- Helper lemmas to eliminate have...by blocks in web interface
lemma inner_product_expansion (u v : V) :
  ⟪u+v, u+v⟫.re = ⟪u,u⟫.re + ⟪v,v⟫.re + 2*⟪u,v⟫.re := by
  rw [InnerProductSpace_v.inner_add_left, inner_add_right_v, inner_add_right_v]
  simp only [Complex.add_re]
  rw [InnerProductSpace_v.inner_conj_symm v u, Complex.conj_re]
  ring

lemma cross_term_bound (u v : V) : 
  ⟪u,v⟫.re ≤ ‖u‖ * ‖v‖ := 
le_trans (re_le_abs ⟪u,v⟫) (by 
  have cs := Cauchy_Schwarz u v
  rwa [norm_inner_eq_abs] at cs)

Statement triangle_v (u v : V) : ‖u+v‖ ≤ ‖u‖ + ‖v‖ := by
  Hint "We'll prove the squared version first, then take square roots."
  
  -- First establish that the RHS is non-negative (needed for le_of_sq_le_sq)
  Hint (hidden := true) "Try `have rhs_nonneg : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg (norm_nonneg_v u) (norm_nonneg_v v)`"
  have rhs_nonneg : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg (norm_nonneg_v u) (norm_nonneg_v v)
  
  Hint "We'll work with the squared versions of both sides."
  
  -- Get the expansion for later use
  Hint "First get the inner product expansion for ⟪u+v, u+v⟫."
  Hint (hidden := true) "Try `have inner_expansion := inner_product_expansion u v`"
  have inner_expansion := inner_product_expansion u v
  
  -- Use Cauchy-Schwarz to bound the cross term
  Hint "Now we bound the cross term 2*⟪u,v⟫.re using Cauchy-Schwarz."
  Hint "We know |⟪u,v⟫| ≤ ‖u‖ * ‖v‖, so ⟪u,v⟫.re ≤ ‖u‖ * ‖v‖."
  Hint "Use Cauchy-Schwarz to bound the real part of the inner product."
  Hint "This follows from our helper lemma for cross term bounds."
  Hint (hidden := true) "Try `have cross_bound := cross_term_bound u v`"
  have cross_bound := cross_term_bound u v
  
  Hint "Now we'll prove the squared inequality and take square roots."
  Hint "We'll show ‖u+v‖² ≤ (‖u‖ + ‖v‖)² using the expansion and Cauchy-Schwarz."
  
  -- Use le_of_sq_le_sq: need to provide the squared inequality and then the non-negativity
  Hint (hidden := true) "Try `apply le_of_sq_le_sq`"
  apply le_of_sq_le_sq
  
  -- First prove the squared inequality
  Hint "First we prove ‖u+v‖² ≤ (‖u‖ + ‖v‖)²."
  · Hint "Expand both sides using norm_sq_eq and algebra."
    Hint (hidden := true) "Try `rw [norm_sq_eq, add_sq, norm_sq_eq, norm_sq_eq, inner_expansion]`"
    rw [norm_sq_eq, add_sq, norm_sq_eq, norm_sq_eq, inner_expansion]
    
    Hint "Use the cross term bound from Cauchy-Schwarz."
    Hint (hidden := true) "Try `linarith [cross_bound]`"
    linarith [cross_bound]
  
  -- Then provide the non-negativity
  Hint "The right-hand side ‖u‖ + ‖v‖ is non-negative."
  · Hint (hidden := true) "Try `exact rhs_nonneg`"
    exact rhs_nonneg

Conclusion "
You have proven the triangle inequality!  
This key result guarantees that norm defines a 'distance' on the vector space.
"

end LinearAlgebraGame