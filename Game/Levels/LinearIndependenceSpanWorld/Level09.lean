import Game.Levels.LinearIndependenceSpanWorld.Level08

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 9

Title "Challenge Level - Linear Independence of Set with Insertion"

Introduction "This is your first challenge level! It is meant to be an optional challenge for those
who want to have more practice proving difficult theorems in Lean.

### The Goal
The goal of this level is to prove that if you have some linearly independent set of vectors `S`, and
some vector `v ∉ span S`, then the set `S ∪ {v}` is also linearly independent.

### How to skip the level
In this level, you will have access to the `sorry` tactic. This tactic is how you tell Lean \"I couldn't
finish the proof, but pretend like I did.\" Typing this tactic will always solve the goal, and allow
you to skip the level

### Proof overview
Linear independence means that any linear combination that adds to zero must be all zeros. This means
that in order to show `S ∪ {v}` is linearly independent, you must introduce an arbitrary linear combination
with the function `f` over a set `s`. Here, you can consider whether `v ∈ s` or not. If not, the proof
is simple, since `s` is a subset of `S` we already know `S` is linearly independent. If it is, we need
to prove `f(v) = 0`. This can be done since `v ∉ span S`, along with some clever choice of functions.
Once you have `f(v) = 0`, you can show that the function must be zero outside of `v` due to the linear
independence of `S`, which then shows `f` is zero on `s`.

### New tactics/theorems
Similarly to the last level, there are new tactics and theorems you can read about to the right side.
Also, something that may be useful is the `⁻¹` function. `x⁻¹` is the multiplicative inverse of `x`.
"

/--
`sorry` allows you to skip levels. The `sorry` tactic will solve any goal, and although it is not actually
a proof, Lean treats it as one.
-/
TacticDoc «sorry»

/--
## Summary
`by_contra` allows you to prove theorems by contradiction. When your goal is `P`, `by_contra h` will
create a hypothesis `h : ¬P` and change the goal to `False`.

## Example
If your goal is `¬(isRational √2)`, using `by_contra h` will change the goal to `False`, and
give you a hypothesis `h : isRational √2`.
-/
TacticDoc by_contra

/--
If you have some set s, where you know `h : i ∈ s`, then `sum_eq_sum_diff_singleton_add h` is a proof that
`(Finset.sum s fun x => f x) = (Finset.sum (s \ {i}) fun x => f x) + f i`
-/
TheoremDoc Finset.sum_eq_sum_diff_singleton_add as "sum_eq_sum_diff_singleton_add" in "Sets"

/--
`smul_sum` is a proof that you can distribute scalar multiplication through `Finset.sum`.
-/
TheoremDoc Finset.smul_sum as "smul_sum" in "Sets"

/--
`inv_mul_cancel` is a proof that multiplying a nonzero inverse gives 1. If you have a hypothesis `h : x ≠ 0`,
then  `inv_mul_cancel h` is a proof that `x⁻¹ * x = 1`
-/
TheoremDoc inv_mul_cancel as "inv_mul_cancel" in "Groups"

/--
`linear_independent_insert_of_not_in_span` is a proof that if you have a linearly independent set, and
you insert an element not in the span of that set, the new set is also linearly independent. The syntax
is as follows: if you have hypotheses `hS : linear_independent_v K V S`, and `hv_not_span : v ∉ span K V S`,
then `linear_independent_insert_of_not_in_span hS hv_not_span` is a proof of `linear_independent_v K V (S ∪ {v})`.
-/
TheoremDoc LinearAlgebraGame.linear_independent_insert_of_not_in_span as "linear_independent_insert_of_not_in_span" in "Vector Spaces"

NewTactic «sorry» by_contra

NewTheorem Finset.sum_eq_sum_diff_singleton_add Finset.smul_sum inv_mul_cancel

open VectorSpace Finset
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/-- Helper lemma: Elements of s \ {v} are in S when s ⊆ S ∪ {v} -/
lemma subset_diff_singleton_of_union (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]
  (S : Set V) (v : V) (s : Finset V) (hs : ↑s ⊆ S ∪ {v}) : 
  ↑(s \ {v}) ⊆ S := by
  intros x hx
  simp at hx
  cases' hx with xs xNev
  cases' (hs xs) with xInS xEqv
  · exact xInS
  · exfalso
    exact xNev xEqv

/-- Helper lemma: If v ∈ s and v ∉ span S, and the sum equals zero, then f v = 0 -/
lemma zero_coeff_from_not_in_span (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]
  (S : Set V) (v : V) (s : Finset V) (f : V → K) 
  (hv_not_span : ∀ (t : Finset V), ↑t ⊆ S → ∀ (g : V → K), ¬v = t.sum (fun x => g x • x))
  (hvIns : v ∈ s) 
  (subset : ↑(s \ {v}) ⊆ S)
  (hf : (s \ {v}).sum (fun w => f w • w) + f v • v = 0) : 
  f v = 0 := by
  by_contra hfv_ne_zero
  -- Apply the span contradiction with the linear combination function
  apply hv_not_span (s \ {v}) subset (fun x => -(f v)⁻¹ * (f x))
  -- Show v equals the linear combination by algebraic transformation
  simp only [mul_smul]
  rw[← smul_sum]
  rw[(neg_add_self ((f v) • v)).symm] at hf
  rw[add_right_cancel hf]
  simp
  rw[(mul_smul (f v)⁻¹ (f v) v).symm]
  rw[inv_mul_cancel hfv_ne_zero, one_smul]




Statement linear_independent_insert_of_not_in_span
  {S : Set V} {v : V}
  (hS : linear_independent_v K V S)
  (hv_not_span : v ∉ span K V S):
  linear_independent_v K V (S ∪ {v}) := by
    Hint "First, unfold the definitions, intro the variables and hypotheses we need, and simp where nescessary"
    Hint (hidden := true) "Try `unfold linear_independent_v at *`"
    unfold linear_independent_v at *
    Hint (hidden := true) "Try `intros s f hs hf w hw`"
    intros s f hs hf w hw
    Hint (hidden := true) "Try `unfold span at *`"
    unfold span at *
    Hint (hidden := true) "Try `unfold is_linear_combination at *`"
    unfold is_linear_combination at *
    Hint (hidden := true) "Try `simp at hv_not_span`"
    simp at hv_not_span

    Hint "We want to prove two seperate cases: v ∈ s and v ∉ s. If v ∉ s, then we know s ⊆ S, so since S
    is linearly independent, so is s. If v ∈ s, then we have more work to do. "
    Hint (hidden := true) "Try `by_cases hvIns : v ∈ {s}`"
    by_cases hvIns : v ∈ s

    Hint "Now, we want to split {hf} into two, breaking off {v} so we have a sum over a subset of {S}"
    Hint (hidden := true) "Try `rw [sum_eq_sum_diff_singleton_add {hvIns}] at {hf}`"
    rw [sum_eq_sum_diff_singleton_add hvIns] at hf

    Hint "Now, that we have a sum over `(s \\ \{v})`, we want to show `↑(s \\ \{v}) ⊆ S`."
    Hint "**Mathematical Intuition**: Elements in s \\ {v} must be in S since they can't equal v."
    Hint "We use a helper lemma that proves: if s ⊆ S ∪ {v}, then s \\ {v} ⊆ S."
    Hint (hidden := true) "Try `have subset : ↑(s \\ \{v}) ⊆ S := subset_diff_singleton_of_union K V S v s hs`"
    have subset : ↑(s \ {v}) ⊆ S := subset_diff_singleton_of_union K V S v s hs

    Hint "Now, we can prove our important lemma, that `{f} v = 0`."
    Hint "We'll use proof by contradiction. If f v ≠ 0, we can express v as a linear combination of elements in S."
    Hint (hidden := true) "Try `have lemma_fv_zero : f v = 0 := zero_coeff_from_not_in_span K V S v s f hv_not_span hvIns subset hf`"
    have lemma_fv_zero : f v = 0 := zero_coeff_from_not_in_span K V S v s f hv_not_span hvIns subset hf

    Hint "Now, consider two cases: `{w} = {v}` or not. If `{w} = {v}`, our lemma is our goal. If not,
    we need to use the linear independence of `S`"
    Hint (hidden := true) "Try `by_cases hw2 : {w} = v`"
    by_cases hw2 : w = v
    Hint (hidden := true) "Try `rw [{hw2}]`"
    rw[hw2]
    Hint (hidden := true) "Try `exact {lemma_fv_zero}`"
    exact lemma_fv_zero

    Hint "We can use our lemma to show that the sum of `{f}` over `{s} \\ \{{v}}` is equal to 0"
    Hint (hidden := true) "Try `rw[{lemma_fv_zero}] at {hf}`"
    rw[lemma_fv_zero] at hf
    Hint (hidden := true) "Try `simp at {hf}`"
    simp at hf

    Hint "Show that w is in s but not equal to v."
    Hint (hidden := true) "Try `have hwInS : w ∈ s \\ {v} := by (simp; exact ⟨hw, hw2⟩)`"
    have hwInS : w ∈ s \ {v} := by (simp; exact ⟨hw, hw2⟩)

    Hint "Now, we can apply all of our hypotheses to close the goal"
    Hint (hidden := true) "Try `exact {hS} ({s} \\ \{v}) {f} {subset} {hf} {w} {hwInS}`"
    exact hS (s \ {v}) f subset hf w hwInS

    -- Case 2: v ∉ s
    Hint "Show that s is a subset of S using case analysis."
    Hint (hidden := true) "Try `suffices s_subset_S : ↑s ⊆ S`"
    suffices s_subset_S : ↑s ⊆ S
    · -- Use the sufficient condition
      Hint "Apply linear independence to finish the proof."
      Hint (hidden := true) "Try `exact hS s f s_subset_S hf w hw`"
      exact hS s f s_subset_S hf w hw
    -- Prove the sufficient condition
    intro u hu_in_s
    cases' hs hu_in_s with hu_in_S hu_eq_v
    · exact hu_in_S
    · simp at hu_eq_v
      rw [hu_eq_v] at hu_in_s
      exfalso
      exact hvIns hu_in_s

    -- The proof is completed by the suffices approach above
