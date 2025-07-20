import Game.Levels.InnerProductWorld.Level06

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 7

Title "Cauchy-Schwarz Inequality"

Introduction "
The Cauchy-Schwarz inequality is one of the most fundamental inequalities in mathematics. It states that for any two vectors `u` and `v` in an inner product space:

$$|\\langle u, v \\rangle| \\leq \\|u\\| \\cdot \\|v\\|$$

This inequality has deep geometric meaning: the absolute value of the inner product (which relates to the cosine of the angle between vectors) is bounded by the product of their lengths. This ensures that when we define angles using inner products, the cosine stays between -1 and 1.

## The Goal
We prove this using orthogonal decomposition. The key insight is to decompose `u` relative to `v` as `u = c • v + w` where `w` is orthogonal to `v`. Then we use the Pythagorean theorem and algebraic manipulation to establish the inequality.

## The Strategy
1. Handle the case `v = 0` separately (trivial)
2. For `v ≠ 0`, use orthogonal decomposition: `u = c • v + w` with `w ⊥ v`  
3. Apply Pythagorean theorem: `‖u‖² = ‖c • v‖² + ‖w‖²`
4. Since `‖w‖² ≥ 0`, we get `‖u‖² ≥ ‖c • v‖²`
5. Substitute `c = ⟪u,v⟫ / ‖v‖²` and algebraically simplify
"

/--
The Cauchy-Schwarz inequality: `‖⟪u,v⟫‖ ≤ ‖u‖ * ‖v‖` for any vectors `u` and `v`.
This is one of the most important inequalities in linear algebra and analysis.
-/
TheoremDoc LinearAlgebraGame.Cauchy_Schwarz as "Cauchy_Schwarz" in "Inner Product"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

Statement Cauchy_Schwarz (u v : V) : ‖⟪u,v⟫‖ ≤ ‖u‖ * ‖v‖ := by
  Hint "We need to consider two cases: when `v = 0` and when `v ≠ 0`."
  Hint (hidden := true) "Try `by_cases v_zero : v = 0`"
  by_cases v_zero : v = 0
  
  case pos =>
    Hint "First, let's handle the case when `v = 0`. When `v = 0`, both sides become 0."
    Hint (hidden := true) "Try `rw[v_zero]`"
    rw[v_zero]
    Hint (hidden := true) "Try `rw [inner_zero_right_v]`"
    rw [inner_zero_right_v]
    have h := norm_zero_v (0:V)
    simp at h
    rw[h]
    simp
    
  case neg =>
    Hint "Now for the main case where `v ≠ 0`. We'll use orthogonal decomposition."
    
    -- Set up orthogonal decomposition manually
    Hint (hidden := true) "Try `let c := ⟪u,v⟫ / (‖v‖^2)`"
    let c := ⟪u,v⟫ / (‖v‖^2)
    Hint (hidden := true) "Try `let w := u - c • v`"
    let w := u - c • v
    
    -- Get the decomposition properties directly 
    have h3 : u = c • v + w := by simp [c, w]
    have h4 : orthogonal w v := ortho_decom u v v_zero
    have h1 : c = ⟪u,v⟫ / (‖v‖^2) := rfl
    have h2 : w = u - c • v := rfl
    
    Hint (hidden := true) "Try `have h5:= left_smul_ortho v w c (ortho_swap w v h4)`"
    have h5:= left_smul_ortho v w c (ortho_swap w v h4)
    
    -- Establish non-negativity 
    have g1 := norm_nonneg_v u
    have g2 := norm_nonneg_v v
    have g3 : 0 ≤ ‖u‖ * ‖v‖ := Left.mul_nonneg g1 g2
    
    -- Use suffices to reduce to squared version
    Hint "We reduce to proving the squared version of the inequality."
    Hint (hidden := true) "Try `suffices ‖⟪u,v⟫‖^2 ≤ ‖u‖^2 * ‖v‖^2 by exact le_of_sq_le_sq this g3`"
    suffices ‖⟪u,v⟫‖^2 ≤ ‖u‖^2 * ‖v‖^2 by
      have ts : ‖u‖^2 * ‖v‖^2 = (‖u‖ * ‖v‖)^2 := by ring
      rw [ts] at this
      exact le_of_sq_le_sq this g3
    
    -- Apply Pythagorean theorem
    Hint "Apply the Pythagorean theorem using orthogonality."
    Hint (hidden := true) "Try `have h6 := pythagorean (c• v) w h5`"
    have h6 := pythagorean (c• v) w h5
    Hint (hidden := true) "Try `nth_rw 2 [h3]`"
    nth_rw 2 [h3]
    Hint (hidden := true) "Try `rw [h6]`"
    rw [h6]
    
    -- Establish that ‖v‖ ≠ 0
    have v_norm_zero : ‖v‖ ≠ 0 := by
      by_contra h
      rw [norm_zero_v v] at h
      contradiction
    
    -- Key transformation: ‖c • v‖² = ‖⟪u,v⟫‖²/‖v‖²
    Hint "Transform ‖c • v‖² using the definition of c."
    Hint (hidden := true) "Try `have kt : ‖c • v‖^2 = ‖⟪u,v⟫‖^2/‖v‖^2 := by ...`"
    have kt : ‖c • v‖^2 = ‖⟪u,v⟫‖^2/‖v‖^2 := by
      rw [sca_mul c v]
      ring_nf
      -- Direct algebraic proof: (a * b⁻¹)² * b = a² * b⁻¹
      simp [c]
      -- Apply the algebraic identity directly
      have algebra_fact : ∀ (a b : ℝ), b ≠ 0 → (a * (b^2)⁻¹)^2 * b^2 = a^2 * (b^2)⁻¹ := by
        intros a b hb
        field_simp [hb]
        ring
      have v_pos : 0 < ‖v‖ := by
        rw [norm_v]
        apply Real.sqrt_pos.2
        have nonneg := inner_self_nonneg v
        apply lt_of_le_of_ne nonneg
        intro h
        -- We have h : ⟪v,v⟫.re = 0 and need to show ⟪v,v⟫ = 0
        have inner_zero : ⟪v,v⟫ = 0 := by
          rw [inner_self_real v]
          simp [h]
        have v_eq_zero : v = 0 := (inner_self_eq_zero v).1 inner_zero
        exact v_zero v_eq_zero
      exact algebra_fact (Complex.abs ⟪u,v⟫) ‖v‖ (ne_of_gt v_pos)
    
    -- Complete the proof
    Hint (hidden := true) "Try `rw [kt]`"
    rw [kt]
    Hint (hidden := true) "Try `rw [add_mul]`"
    rw [add_mul]
    Hint (hidden := true) "Try `field_simp [v_norm_zero]`"
    field_simp [v_norm_zero]
    -- The final goal should be showing ‖w‖² ≥ 0, which follows from norm non-negativity
    Hint (hidden := true) "Try `exact norm_sq_nonneg w`"
    rw [norm_sq_eq]; exact inner_self_nonneg w

end LinearAlgebraGame