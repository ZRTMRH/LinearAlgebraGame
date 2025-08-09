import Game.Levels.LinearIndependenceSpanWorld.Level07

namespace LinearAlgebraGame

open VectorSpace Set Finset
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--
**Helper Lemma: Sum of difference functions equals zero**

When we have two linear combinations that are equal, the sum of their 
difference over the union of their supports equals zero.

This technical lemma supports the proof of linear combination uniqueness.
-/
lemma sum_diff_eq_zero_of_equal_combinations 
  (s t : Finset V) (f g : V → K) 
  (hf0 : ∀ v ∉ s, f v = 0) (hg0 : ∀ v ∉ t, g v = 0)
  (heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)) :
  (Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0 := by
  -- Use the distributive property of subtraction over scalar multiplication
  simp only [Pi.sub_apply, sub_smul]
  
  -- Split the sum in two
  rw[sum_sub_distrib]
  
  -- Use subset properties to convert the sums back to the original sets
  rw [(sum_subset (subset_union_left s t) (fun v _ h => by rw[hf0 v h, zero_smul_v])).symm]
  rw [(sum_subset (subset_union_right s t) (fun v _ h => by rw[hg0 v h, zero_smul_v])).symm]
  
  -- Use the fact that the two sums are equal to finish the proof
  rw[heq]
  simp

/--
**Helper Lemma: Subset property for set difference**

When we have a set s that's a subset of S ∪ {v}, then s \ {v} is a subset of S.
This technical lemma handles the case analysis needed for linear independence proofs.
-/
lemma subset_diff_singleton (S : Set V) (s : Finset V) (v : V)
  (hs : ↑s ⊆ S ∪ {v}) :
  ↑(s \ {v}) ⊆ S := by
  intros x hx
  simp at hx
  cases' hx with xs xNev
  have xInUnion := hs xs
  simp at xInUnion
  cases' xInUnion with xEqv xInS
  exfalso
  exact xNev xEqv
  exact xInS

/--
**Helper Lemma: Subset property for linear independence context**

In the context of linear independence proofs, when we have s ⊆ S ∪ {v} and need 
to show s \ {v} ⊆ S, this handles the required case analysis.
-/
lemma subset_for_linear_independence {S : Set V} {s : Finset V} {v : V}
  (hs : ↑s ⊆ S ∪ {v}) :
  ↑(s \ {v}) ⊆ S := by
  intros x hx
  simp at hx
  cases' hx with xs xNev
  have xInUnion := hs xs
  simp at xInUnion
  cases' xInUnion with xEqv xInS
  exfalso
  exact xNev xEqv
  exact xInS

/--
**Helper Lemma: Linear combination rearrangement**

When we have a linear combination equal to zero, we can solve for one vector 
in terms of the others. This supports contradiction proofs in linear independence.
-/
lemma linear_combination_rearrangement (s : Finset V) (v : V) (f : V → K)
  (hvIns : v ∈ s) (hfv_ne_zero : f v ≠ 0)
  (hf : Finset.sum s (fun w => f w • w) = 0) :
  v = (s \ {v}).sum (fun x => (-(f v)⁻¹ * (f x)) • x) := by
  simp only [mul_smul]
  rw[(smul_sum (r := -(f v)⁻¹) (f := fun x => f x • x) (s := (s \ {v}))).symm]
  -- We need to get hf into the right form for add_right_cancel
  have hf_expanded : Finset.sum (s \ {v}) (fun w => f w • w) + f v • v = 0 := by
    rw [← sum_eq_sum_diff_singleton_add hvIns (fun w => f w • w)]
    exact hf
  rw [(neg_add_self ((f v) • v)).symm] at hf_expanded
  rw[add_right_cancel hf_expanded]
  simp
  rw[(mul_smul (f v)⁻¹ (f v) v).symm]
  rw[inv_mul_cancel hfv_ne_zero, one_smul]

end LinearAlgebraGame