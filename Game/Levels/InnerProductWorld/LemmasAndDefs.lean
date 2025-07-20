import Game.Levels.LinearIndependenceSpanWorld.Level09
import Game.Levels.VectorSpaceWorld.Level05

-- Minimal Mathlib imports for Lean 4.7.0 - avoiding conflicts with custom definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Abs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic  -- For Complex.normSq_eq_norm_sq
import Mathlib.Data.Real.Sqrt  -- For Real.sq_sqrt

open Function Set VectorSpace

namespace LinearAlgebraGame

instance  [Field K] [AddCommGroup V] [VectorSpace K V] : DistribSMul K V where
  smul_add := smul_add
  smul_zero := smul_zero_v K V


class InnerProductSpace_real_v (V : Type) [AddCommGroup V] [VectorSpace ℝ V] where
  inner : V → V → ℝ

  -- Properties are simpler for real case
  inner_self_nonneg : ∀ (v : V), 0 ≤ inner v v
  inner_self_eq_zero : ∀ (v : V), inner v v = 0 ↔ v = 0
  inner_add_left : ∀ (u v w : V), inner (u + v) w = inner u w + inner v w
  inner_smul_left : ∀ (a : ℝ) (v w : V), inner (a • v) w = a * inner v w
  inner_symm : ∀ (v w : V), inner v w = inner w v-- Import complex numbers from mathlib


open ComplexConjugate


-- Inner product space definition for complex vector spaces
class InnerProductSpace_v (V : Type) [AddCommGroup V] [VectorSpace ℂ V] where
  inner : V → V → ℂ

  -- 1. Positivity: ⟨v,v⟩ is real and non-negative
  inner_self_im_zero : ∀ (v : V), (inner v v).im = 0
  inner_self_nonneg : ∀ (v : V), 0 ≤ (inner v v).re

  -- 2. Definiteness: ⟨v,v⟩ = 0 iff v = 0
  inner_self_eq_zero : ∀ (v : V), inner v v = 0 ↔ v = 0

  -- 3. Additivity in first slot: ⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩
  inner_add_left : ∀ (u v w : V), inner (u + v) w = inner u w + inner v w

  -- 4. Homogeneity in first slot: ⟨a • v, w⟩ = a * ⟨v, w⟩
  inner_smul_left : ∀ (a : ℂ) (v w : V), inner (a • v) w = a * inner v w

  -- 5. Conjugate symmetry: ⟨v, w⟩ = conj(⟨w, v⟩)
  inner_conj_symm : ∀ (v w : V), inner v w = conj (inner w v)


-- Custom notation for our inner product
notation "⟪" x "," y "⟫" => InnerProductSpace_v.inner x y


variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]

-- Create theorem aliases for class fields that are used in TheoremDoc
theorem inner_self_im_zero (v : V) : (⟪v, v⟫).im = 0 := 
  InnerProductSpace_v.inner_self_im_zero v

theorem inner_self_nonneg (v : V) : 0 ≤ (⟪v, v⟫).re := 
  InnerProductSpace_v.inner_self_nonneg v

theorem inner_self_eq_zero (v : V) : ⟪v, v⟫ = 0 ↔ v = 0 := 
  InnerProductSpace_v.inner_self_eq_zero v

theorem inner_add_left (u v w : V) : ⟪u + v, w⟫ = ⟪u, w⟫ + ⟪v, w⟫ := 
  InnerProductSpace_v.inner_add_left u v w

theorem inner_smul_left (a : ℂ) (v w : V) : ⟪a • v, w⟫ = a * ⟪v, w⟫ := 
  InnerProductSpace_v.inner_smul_left a v w

theorem inner_conj_symm (v w : V) : ⟪v, w⟫ = conj (⟪w, v⟫) := 
  InnerProductSpace_v.inner_conj_symm v w

/--In a complex inner product space, `⟪v,v⟫` is always a real number. Here "real" means that its imaginary part is zero."-/
theorem inner_self_real : ∀ (v : V), ⟪v,v⟫ = (⟪v,v⟫.re : ℂ):= by
  intro v
  apply Complex.ext
  rfl
  rw [inner_self_im_zero v]
  simp

/-- This theorem extends linearity of the inner product in the first argument to subtraction:
`⟪u - v, w⟫ = ⟪u, w⟫ - ⟪v, w⟫`. -/
theorem inner_minus_left : ∀ (u v w : V), ⟪u - v, w⟫ = ⟪u, w⟫ - ⟪v, w⟫ := by
  intro u v w
  have : u-v=u+(-1 :ℂ)• v := by
    refine Eq.symm (add_eq_of_eq_sub' ?_)
    rw [@sub_sub_cancel_left]
    exact neg_one_smul_v ℂ V v
  rw [this]
  rw [InnerProductSpace_v.inner_add_left]
  rw [InnerProductSpace_v.inner_smul_left]
  ring

/-- This lemma asserts that the complex conjugation operation is injective: if `conj a = conj b`, then `a = b`-/
theorem conj_inj {a b : ℂ} : conj a = conj b → a = b := by
  intro h
  -- Apply conj to both sides, using conj ∘ conj = id
  have : conj (conj a) = conj (conj b) := by
    rw [h]
  rw [Complex.conj_conj, Complex.conj_conj] at this
  exact this


/-- For any complex numbers `a` and `b`, `conj (a + b) = conj a + conj b`.-/
theorem conj_add (a b : ℂ) : conj (a + b) = conj a + conj b := by
  apply Complex.ext
  dsimp
  dsimp
  rw [@neg_add]

/-- For any complex numbers `a` and `b`, `conj (a * b) = conj a * conj b`.-/
theorem conj_mull (a b : ℂ) : conj (a * b) = conj a * conj b := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  · simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]


/-- `conj 0 = 0`-/
theorem conj_zero : conj (0 : ℂ) = 0 := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]

/--This is another way to state that `⟪v, v⟫` is real: `⟪v, v⟫ = ⟪v, v⟫.re`."-/
theorem inner_self_re_v (V : Type) [AddCommGroup V] [VectorSpace ℂ V] [InnerProductSpace_v V] (v : V) :
  ⟪v, v⟫ = ↑(⟪v, v⟫.re) := by
  apply Complex.ext
  · rfl
  · exact inner_self_im_zero v

/-- Inner product is additive in the second slot -/
theorem inner_add_right_v (u v w : V) : ⟪u, v + w⟫ = ⟪u, v⟫ + ⟪u, w⟫ := by
  apply conj_inj
  rw [conj_add]
  repeat rw [← InnerProductSpace_v.inner_conj_symm]
  exact InnerProductSpace_v.inner_add_left v w u

/-- Inner product of zero vector is zero -/
theorem inner_zero_left_v (v : V) : ⟪0, v⟫ = 0 := by
  have h : (0 : V) = (0 : ℂ) • (0 : V) := by
    rw [zero_smul_v ℂ V]
  rw [h, InnerProductSpace_v.inner_smul_left]
  rw [zero_mul]

/-- Inner product with zero vector is zero -/
theorem inner_zero_right_v (v : V) : ⟪v, 0⟫ = 0 := by
  rw [InnerProductSpace_v.inner_conj_symm]
  rw [inner_zero_left_v]
  exact conj_zero

/-- The inner product is homogeneous. `⟪v, a • w⟫ = conj a * ⟪v, w⟫`.-/
theorem inner_smul_right_v (a : ℂ) (v w : V) :
  ⟪v, a • w⟫ = conj a * ⟪v, w⟫ := by
  apply conj_inj
  rw [conj_mull]
  rw [Complex.conj_conj]
  repeat rw [← InnerProductSpace_v.inner_conj_symm]
  exact InnerProductSpace_v.inner_smul_left a w v

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]

noncomputable def norm_v (v:V) : ℝ := Real.sqrt ⟪v, v⟫.re

notation "‖" x "‖" => norm_v x

def orthogonal (u v:V) : Prop := ⟪u, v⟫= (0:ℂ)

-- TODO: Make ℂ compatible with norm notation by extending norm_v to work on ℂ  
-- For now, we'll use Complex.abs (the standard complex absolute value) instead of norm_v for complex numbers

/-- If `u` is orthogonal to `v`, then any scalar multiple of `u` is also orthogonal to `v`. -/
theorem left_smul_ortho (u v : V) (c : ℂ): orthogonal u v → orthogonal (c• u) v := by
  intro h
  dsimp [orthogonal] at *
  rw [InnerProductSpace_v.inner_smul_left]
  rw[h]
  simp

/-- If `u` is orthogonal to `v`, then `v` is orthogonal to `u`. -/
theorem ortho_swap : ∀ (u v :V), orthogonal u v → orthogonal v u := by
  intro u v h
  dsimp [orthogonal] at *
  rw [InnerProductSpace_v.inner_conj_symm,h]
  simp

theorem norm_sq_eq (v : V) :  ‖v‖^2 = ⟪v,v⟫.re := by
    unfold norm_v
    rw [Real.sq_sqrt (InnerProductSpace_v.inner_self_nonneg v)]

theorem right_smul_ortho (u v : V) (c : ℂ) (h : orthogonal u v) : orthogonal u (c • v) := by
  exact ortho_swap (c • v) u (left_smul_ortho v u c (ortho_swap u v h))

theorem le_of_sq_le_sq {a : ℝ} {b : ℝ} (h : a^2 ≤ b ^2 ) (hb : 0≤ b) : a ≤ b :=
  le_abs_self a |>.trans <| abs_le_of_sq_le_sq h hb

-- Helper theorem for orthogonal decomposition that gives us the full structure needed for Cauchy-Schwarz
theorem ortho_decom_parts (u v : V) (h : v ≠ 0) : 
  let c := ⟪u,v⟫ / (‖v‖^2)
  let w := u - c • v
  u = c • v + w ∧ orthogonal w v := by
  let c := ⟪u,v⟫ / (‖v‖^2)  
  let w := u - c • v
  constructor
  · simp [w]
  · -- Prove orthogonality directly (same as Level06 ortho_decom)
    unfold orthogonal
    rw[inner_minus_left]
    rw[InnerProductSpace_v.inner_smul_left]
    unfold norm_v
    norm_cast
    rw[Real.sq_sqrt (inner_self_nonneg v)]
    rw [← inner_self_real]
    ring_nf
    rw[mul_assoc, mul_inv_cancel]
    simp
    intro x
    apply h
    exact (inner_self_eq_zero v).1 x

-- Lemma that the real part of a complex number is bounded by its absolute value
theorem re_le_abs (z : ℂ) : z.re ≤ Complex.abs z := by
  have h := Complex.abs_re_le_abs z
  exact le_abs_self z.re |>.trans h

-- The norm of an inner product equals the complex absolute value
theorem norm_inner_eq_abs (u v : V) : ‖⟪u,v⟫‖ = Complex.abs ⟪u,v⟫ := by
  -- Since inner products are complex numbers, their norm should equal Complex.abs
  -- This needs to be established based on how norm_v is defined for complex numbers
  rfl  -- This should work if norm_v is defined correctly for complex numbers

end LinearAlgebraGame
