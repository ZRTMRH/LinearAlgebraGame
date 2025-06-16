import Mathlib


class VectorSpace (K V : Type) [Field K] [AddCommGroup V] extends SMul K V where
  smul_add : ∀ (a : K) (x y : V), a • (x + y) = a • x + a • y           -- distributivity of scalar over vector addition
  add_smul : ∀ (a b : K) (x : V), (a + b) • x = a • x + b • x           -- distributivity of scalar addition
  mul_smul : ∀ (a b : K) (x : V), (a * b) • x = a • (b • x)             -- compatibility of scalar multiplication
  one_smul : ∀ (x : V), (1 : K) • x = x                                -- identity scalar acts as identity



variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]


def isSubspace (W : Set V) : Prop :=
  W.Nonempty ∧ (∀ (x y : V), x ∈ W → y ∈ W → x + y ∈ W) ∧ (∀ (a : K) (x : V), x ∈ W → a • x ∈ W)

#check add_right_cancel

-- Level 3: ZeroSmul.lean
--import Game.Levels.LinearAlgebra.L01_VectorSpace

theorem zero_smul_v (w : V) : (0 : K) • w = (0:V):= by
  have calc_zero : (0 : K) • w = ((0 : K) + (0 : K)) • w := by
    rw [zero_add]
  rw [VectorSpace.add_smul (0 : K) (0 : K) w] at calc_zero
  have hg : (0 : K) • w = (0:V)+(0 : K) • w := by exact Eq.symm (AddRightCancelMonoid.zero_add (0 • w))
  nth_rw 1 [hg] at calc_zero
  apply add_right_cancel at calc_zero
  exact symm calc_zero


-- Level 4: SmulZero.lean
-- import Game.Levels.LinearAlgebra.L01_VectorSpace

/-- In any vector space V over K, any scalar a multiplied by 0 (the zero vector) is 0. -/
theorem smul_zero_v (a : K) : a • (0 : V) = (0 : V) := by
  /- Hint: Write the vector 0 as 0 + 0, then use the `smul_add` axiom:
     a • (0 + 0) = a • 0 + a • 0. Cancel out `a • 0` from both sides. -/
  have calc_zero : 0 + a • (0 : V) = a • 0 + a • 0:= by
    rw [← VectorSpace.smul_add a 0 0] -- 0 + a • 0 = a• (0+0)
    repeat rw [zero_add]
  apply add_right_cancel at calc_zero -- 0= a• 0
  exact symm calc_zero

-- Level 5: NegOneSmul.lean
--import Game.Levels.LinearAlgebra.L01_VectorSpace
--import Game.Levels.LinearAlgebra.L06_ZeroSmul

/-- In any vector space V over K, multiplying a vector by -1 gives its additive inverse. -/
theorem neg_one_smul_v (v : V) : (-1 : K) • v = -v := by
  /- Hint: Use the fact that (-1 + 1) = 0. Apply the `add_smul` axiom:
     $(-1 + 1) • v = (-1)•v + 1•v$.
     Simplify the left side to 0 • v (which is 0 by Level 6),
     and simplify 1 • v to v.
     Then solve the equation 0 = (-1)•v + v$ for $(-1)•v$. -/
  have step1 : (0 : K) • v = ((-1 : K) + (1 : K)) • v := by rw [add_left_neg]
  rw [VectorSpace.add_smul] at step1                    -- now step1: 0 • v = (-1)•v + 1•v
  rw [zero_smul_v, VectorSpace.one_smul] at step1   -- substitute 0•v = 0 and 1•v = v
  symm at step1
  -- Now we have (-1)•v + v = 0, which means (-1)•v is the additive inverse of v
  -- so (-1)•v = -v
  apply neg_eq_of_add_eq_zero_left at step1
  symm
  exact step1

-- Level 1: AdditiveIdentity.lean
--import Game.Levels.LinearAlgebra.L02_Subspace
theorem subspace_contains_zero {W : Set V} (hW : isSubspace K V W) : (0 : V) ∈ W := by
  /- Hint: Use the fact that W is nonempty. Pick an element w ∈ W (from hW.1),
     then use closure under scalar multiplication with scalar 0.
     Remember that (0 : K) • w = 0 (the zero vector) by a consequence of the vector space axioms. -/
  obtain ⟨w, hw⟩ := hW.1                     -- W.Nonempty gives an element w in W
  have calc_zero : (0 : K) • w = ((0 : K) + (0 : K)) • w := by
    rw [zero_add]
  symm at calc_zero
  -- Using the distributivity axiom: 0 • w + 0 • w = (0 + 0) • w = 0 • w

  rw [VectorSpace.add_smul (0 : K) (0 : K) w] at calc_zero
   -- now calc_zero: 0 • w = 0 • w + 0 • w
  -- Subtract 0 • w from both sides (using additive cancellation) to obtain 0 = 0 • w

  --have hg : (0 : V) + (0 : K) • w = (0 : K) • w + (0 : K) • w := by exact add_right_cancel V (0 : V) (0 : K) • w (0 : K) • w
  have hg :  (0:V)+(0 : K) • w =(0 : K) • w := by exact AddRightCancelMonoid.zero_add (0 • w)
  nth_rw 3 [hg.symm] at calc_zero
  have : (0 : V) = (0 : K) • w := by
    symm
    exact add_right_cancel  calc_zero       -- cancel 0•w from the equation

  rw [this]
  -- Now 0 = 0 • w shows (0 : V) is obtained by scalar-multiplying w, hence 0 ∈ W
  exact hW.2.2 0 w hw                      -- by closure under scalar multiplication, 0 • w ∈ W

#check zero_smul

-- Level 2: ClosureInverse.lean
--import Game.Levels.LinearAlgebra.L02_Subspace

/-- If W is a subspace of V, it is closed under additive inverses: for any x ∈ W, the vector -x is also in W. -/
theorem subspace_neg {W : Set V} (hW : isSubspace K V W) : ∀ (x : V), x ∈ W → (-x) ∈ W := by
  /- Hint: Use closure under scalar multiplication with the scalar -1.
     If x ∈ W, then (-1) • x ∈ W by hW. Also, from the vector space axioms, (-1) • x = -x. -/
  intros x hx
  have h_neg : (-1 : K) • x ∈ W := hW.2.2 (-1) x hx    -- closure: -1 • x is in W
  -- To show (-1)•x = -x, use that (-1 + 1) • x = (-1)•x + 1•x and simplify:
  have eq_inv := calc
    (0 : K) • x = ((1:K) + (-1: K)  ) • x                 := by rw [add_right_neg]   -- (-1 + 1 = 0)
              _ = (1:K) • x + (-1: K) • x  := by rw [VectorSpace.add_smul]
  -- Simplify the right-hand side using 1 • x = x and 0 • x = 0:
  rw [VectorSpace.one_smul] at eq_inv           -- now eq_inv: 0 • x = (-1)•x + x
  have : (-1 : K) • x = -x := by exact neg_one_smul_v K V x --add_right_eq_zero.1 eq_inv
  rw [← this]    -- replace (-1)•x with -x in the membership proof
  exact h_neg
