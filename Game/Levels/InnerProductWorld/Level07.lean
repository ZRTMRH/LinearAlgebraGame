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

**⚠️ Note:** There may be a bug where hints repeat - this is a known issue with the game framework. Simply continue with your proof if you see duplicate hints.
"

/--
The Cauchy-Schwarz inequality: `‖⟪u,v⟫‖ ≤ ‖u‖ * ‖v‖` for any vectors `u` and `v`.
This is one of the most important inequalities in linear algebra and analysis.
-/
TheoremDoc LinearAlgebraGame.Cauchy_Schwarz as "Cauchy_Schwarz" in "Inner Product"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

/-- Helper lemma: The norm of a nonzero vector is nonzero -/
lemma norm_nonzero_of_nonzero {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
  (v : V) (v_zero : v ≠ 0) : ‖v‖ ≠ 0 := by
  by_contra h
  rw [norm_zero_v v] at h
  contradiction

/-- Helper lemma: From Pythagorean theorem, if u = c•v + w with orthogonal c•v and w, then ‖u‖² = ‖c•v‖² + ‖w‖² -/
lemma norm_sq_decomposition {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
  (u v w : V) (c : ℂ) (h_decomp : u = c • v + w) (h_ortho : orthogonal (c • v) w) :
  ‖u‖^2 = ‖c • v‖^2 + ‖w‖^2 := by
  rw [h_decomp]
  exact pythagorean (c • v) w h_ortho

/-- Helper lemma: If ‖u‖² = ‖c•v‖² + ‖w‖², then ‖c•v‖² ≤ ‖u‖² -/
lemma scaled_norm_le_original {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
  (u v w : V) (c : ℂ) (h_eq : ‖u‖^2 = ‖c • v‖^2 + ‖w‖^2) :
  ‖c • v‖^2 ≤ ‖u‖^2 := by
  rw [h_eq]
  simp
  rw [norm_sq_eq]
  exact inner_self_nonneg w

/-- Helper lemma: For nonzero v, we have 0 < ‖v‖ -/
lemma norm_pos_of_nonzero {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
  (v : V) (v_zero : v ≠ 0) : 0 < ‖v‖ := by
  rw [norm_v]
  apply Real.sqrt_pos.2
  exact lt_of_le_of_ne (inner_self_nonneg v) (fun h => v_zero ((inner_self_eq_zero v).1 (by rw [inner_self_real]; simp [h])))

/-- Helper lemma: Express ‖c • v‖² in terms of c and v -/
lemma norm_sq_scaled_eq {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
  (u v : V) (c : ℂ) (v_pos : 0 < ‖v‖) (c_def : c = ⟪u,v⟫ / ‖v‖^2) :
  ‖c • v‖^2 = ‖⟪u,v⟫‖^2/‖v‖^2 := by
  rw [sca_mul c v]
  ring_nf
  simp [c_def]
  field_simp [ne_of_gt v_pos]
  ring



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
    Hint (hidden := true) "Try `have h := norm_zero_v (0:V)`"
    have h := norm_zero_v (0:V)
    Hint (hidden := true) "Try `simp at h`"
    simp at h
    Hint (hidden := true) "Try `rw[h]`"
    rw[h]
    Hint (hidden := true) "Try `simp`"
    simp
    
  case neg =>
    Hint "Now for the main case where `v ≠ 0`. We'll use orthogonal decomposition."
    
    -- Set up orthogonal decomposition manually
    Hint "We'll decompose u as c•v + w where w is orthogonal to v."
    Hint "The key insight: choose c = ⟪u,v⟫ / ‖v‖² to make w orthogonal to v."
    Hint "This choice ensures ⟪w, v⟫ = ⟪u - c•v, v⟫ = ⟪u,v⟫ - c•‖v‖² = 0."
    Hint (hidden := true) "Try `let c := ⟪u,v⟫ / (‖v‖^2)`"
    let c := ⟪u,v⟫ / (‖v‖^2)
    Hint (hidden := true) "Try `let w := u - c • v`"
    let w := u - c • v
    
    -- Get the decomposition properties directly 
    Hint "Now we establish the key properties of our decomposition."
    Hint "We have u = c • v + w by definition of w."
    Hint "Think of this geometrically: u is split into a part parallel to v (c•v) and a part perpendicular to v (w)."
    Hint (hidden := true) "Try `have h3 : u = c • v + w := by simp [w]`"
    have h3 : u = c • v + w := by simp [w]
    Hint "The orthogonality follows from our choice of c."
    Hint (hidden := true) "Try `have h4 : orthogonal w v := ortho_decom u v v_zero`"
    have h4 : orthogonal w v := ortho_decom u v v_zero
    Hint (hidden := true) "Try `have h5:= left_smul_ortho v w c (ortho_swap w v h4)`"
    have h5:= left_smul_ortho v w c (ortho_swap w v h4)
    
    -- Establish non-negativity 
    Hint (hidden := true) "Try `have g3 : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg_v u) (norm_nonneg_v v)`"
    have g3 : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg_v u) (norm_nonneg_v v)
    
    -- We'll prove the squared version first, then derive the original
    Hint "We'll prove the squared version ‖⟪u,v⟫‖² ≤ ‖u‖² * ‖v‖² and then take square roots."
    
    -- Apply Pythagorean theorem
    Hint "Apply the Pythagorean theorem using orthogonality."
    Hint "We want to show ‖u‖² = ‖c • v‖² + ‖w‖²"
    Hint "Since c•v and w are orthogonal, the Pythagorean theorem tells us their norms add in quadrature."
    Hint "Rewrite u using our decomposition u = c • v + w."
    Hint (hidden := true) "Try `have u_norm_sq : ‖u‖^2 = ‖c • v‖^2 + ‖w‖^2 := norm_sq_decomposition u v w c h3 h5`"
    have u_norm_sq : ‖u‖^2 = ‖c • v‖^2 + ‖w‖^2 := norm_sq_decomposition u v w c h3 h5
    
    -- Establish that ‖v‖ ≠ 0 (needed for division)
    Hint (hidden := true) "Try `have v_norm_zero : ‖v‖ ≠ 0 := norm_nonzero_of_nonzero v v_zero`"
    have v_norm_zero : ‖v‖ ≠ 0 := norm_nonzero_of_nonzero v v_zero
    
    -- Key transformation: ‖c • v‖² = ‖⟪u,v⟫‖²/‖v‖²
    Hint "The crucial step: express ‖c • v‖² in terms of the inner product."
    Hint "Since c = ⟪u,v⟫/‖v‖², we get ‖c • v‖² = ‖⟪u,v⟫‖²/‖v‖²."
    -- Get positivity of norm and the key transformation
    Hint (hidden := true) "Try `have v_pos : 0 < ‖v‖ := norm_pos_of_nonzero v v_zero`"
    have v_pos : 0 < ‖v‖ := norm_pos_of_nonzero v v_zero
    Hint (hidden := true) "Try `have kt : ‖c • v‖^2 = ‖⟪u,v⟫‖^2/‖v‖^2 := norm_sq_scaled_eq u v c v_pos rfl`"
    have kt : ‖c • v‖^2 = ‖⟪u,v⟫‖^2/‖v‖^2 := norm_sq_scaled_eq u v c v_pos rfl
    
    -- From ‖u‖² = ‖c • v‖² + ‖w‖², and since ‖w‖² ≥ 0, we get ‖u‖² ≥ ‖c • v‖²
    Hint "Since ‖u‖² = ‖c • v‖² + ‖w‖² and ‖w‖² ≥ 0, we have ‖c • v‖² ≤ ‖u‖²."
    Hint "This is the key inequality: the projection of u onto v has norm at most ‖u‖."
    Hint (hidden := true) "Try `have cv_le_u : ‖c • v‖^2 ≤ ‖u‖^2 := scaled_norm_le_original u v w c u_norm_sq`"
    have cv_le_u : ‖c • v‖^2 ≤ ‖u‖^2 := scaled_norm_le_original u v w c u_norm_sq
    
    -- Substitute kt to get ‖⟪u,v⟫‖²/‖v‖² ≤ ‖u‖²
    Hint "Substituting our expression for ‖c • v‖², we get ‖⟪u,v⟫‖²/‖v‖² ≤ ‖u‖²."
    Hint (hidden := true) "Try `rw [kt] at cv_le_u`"
    rw [kt] at cv_le_u
    
    -- Multiply both sides by ‖v‖² to get ‖⟪u,v⟫‖² ≤ ‖u‖² * ‖v‖²
    Hint "Multiplying both sides by ‖v‖² gives ‖⟪u,v⟫‖² ≤ ‖u‖² * ‖v‖²."
    Hint "We're almost there! This is the squared version of Cauchy-Schwarz."
    -- Since cv_le_u says Complex.abs ⟪u,v⟫^2 / ‖v‖^2 ≤ ‖u‖^2
    -- Multiplying by ‖v‖^2 gives Complex.abs ⟪u,v⟫^2 ≤ ‖u‖^2 * ‖v‖^2
    -- Get the squared inequality by multiplying both sides by ‖v‖^2
    Hint (hidden := true) "Try `have h_mul := mul_le_mul_of_nonneg_right cv_le_u (sq_nonneg ‖v‖)`"
    have h_mul := mul_le_mul_of_nonneg_right cv_le_u (sq_nonneg ‖v‖)
    Hint (hidden := true) "Try `simp [div_mul_cancel, v_norm_zero] at h_mul`"
    simp [div_mul_cancel, v_norm_zero] at h_mul
    Hint (hidden := true) "Try `have sq_ineq : Complex.abs ⟪u,v⟫^2 ≤ ‖u‖^2 * ‖v‖^2 := h_mul`"
    have sq_ineq : Complex.abs ⟪u,v⟫^2 ≤ ‖u‖^2 * ‖v‖^2 := h_mul
    
    -- Convert squared inequality to original
    Hint "Now we can take square roots of both sides to get the original inequality."
    Hint "Taking square roots preserves inequalities for non-negative numbers."
    Hint "First, rewrite the goal using the fact that ‖⟪u,v⟫‖ = Complex.abs ⟪u,v⟫."
    Hint (hidden := true) "Try `rw [norm_inner_eq_abs]`"
    rw [norm_inner_eq_abs]
    -- Convert to the product squared
    Hint (hidden := true) "Try `have ts : ‖u‖^2 * ‖v‖^2 = (‖u‖ * ‖v‖)^2 := by (ring)`"
    have ts : ‖u‖^2 * ‖v‖^2 = (‖u‖ * ‖v‖)^2 := by (ring)
    Hint (hidden := true) "Try `rw [ts] at sq_ineq`"
    rw [ts] at sq_ineq
    Hint (hidden := true) "Try `exact le_of_sq_le_sq sq_ineq g3`"
    exact le_of_sq_le_sq sq_ineq g3

end LinearAlgebraGame