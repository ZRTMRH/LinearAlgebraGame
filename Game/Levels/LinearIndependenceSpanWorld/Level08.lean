import Game.Levels.LinearIndependenceSpanWorld.Level07

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 8

Title "Challenge Level - Linear Independence of Set with Insertion"

Introduction "This is your first challenge level! It is meant to be an optional challenge for those
who want to have more practice proving difficult theorems in Lean.

### The Goal
The goal of this level is to prove that if you have some linearly independent set of vectors `S`, and
some vector `v ∉ span S`, then the set `S ∪ {v}` is also linearly independent.

**Note:** This level may experience a hint display issue where hints repeat. If you see the same hint multiple times, the level is still working correctly - just continue with your proof as normal.

### This is an optional challenge
This level is optional and challenging. If you find it too difficult, you can:
- Skip to the next world and come back to it later
- Enable \"relaxed\" rules in the game settings to bypass this level

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
## Summary

`suffices` allows you to reduce the goal to a simpler statement. It's useful when proving `Q`
makes it easy to prove your original goal `P`.

## Syntax

- `suffices h : Q` - Creates a new goal `Q`, and after proving it, you get `h : Q` to prove the original goal
- `suffices h : Q by tactic` - Proves the original goal using `h : Q` immediately

## Example

If your goal is `x + y = 10` and you know this follows from `x = 3` and `y = 7`, you can write:
```
suffices h : x = 3 ∧ y = 7
· -- Now prove x + y = 10 using h
  cases' h with hx hy
  rw [hx, hy]
  norm_num
· -- Now prove x = 3 ∧ y = 7
  constructor
  · exact x_eq_three
  · exact y_eq_seven
```

## Common usage

Often used when the goal follows easily from a simpler fact, especially in contradiction proofs.
-/
TacticDoc «suffices»

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
`inv_mul_cancel₀` is a proof that multiplying a nonzero inverse gives 1. If you have a hypothesis `h : x ≠ 0`,
then  `inv_mul_cancel₀ h` is a proof that `x⁻¹ * x = 1`
-/
TheoremDoc inv_mul_cancel₀ as "inv_mul_cancel₀" in "Groups"

/--
`linear_independent_insert_of_not_in_span` is a proof that if you have a linearly independent set, and
you insert an element not in the span of that set, the new set is also linearly independent. The syntax
is as follows: if you have hypotheses `hS : linear_independent_v K V S`, and `hv_not_span : v ∉ span K V S`,
then `linear_independent_insert_of_not_in_span hS hv_not_span` is a proof of `linear_independent_v K V (S ∪ {v})`.
-/
TheoremDoc LinearAlgebraGame.linear_independent_insert_of_not_in_span as "linear_independent_insert_of_not_in_span" in "Vector Spaces"

/--
`subset_diff_singleton_of_union` is a helper proof that if a finset `s` is a subset of `S ∪ {v}`,
then `s \ {v}` is a subset of `S`. The syntax is as follows: if you have a hypothesis
`hs : ↑s ⊆ S ∪ {v}`, then `subset_diff_singleton_of_union K V S v s hs` is a proof of
`↑(s \ {v}) ⊆ S`.
-/
TheoremDoc LinearAlgebraGame.subset_diff_singleton_of_union as "subset_diff_singleton_of_union" in "Sets"

/--
`zero_coeff_from_not_in_span` is a helper proof that if `v` is not in the span of `S`, `v ∈ s`,
`s \ {v} ⊆ S`, and a linear combination over `s` with coefficient function `f` sums to zero,
then `f v = 0`. The syntax is as follows: given the hypotheses described above named
`hv_not_span`, `hvIns`, `subset`, and `hf`, the term
`zero_coeff_from_not_in_span K V S v s f hv_not_span hvIns subset hf` is a proof of `f v = 0`.
-/
TheoremDoc LinearAlgebraGame.zero_coeff_from_not_in_span as "zero_coeff_from_not_in_span" in "Vector Spaces"

NewTactic by_contra «suffices»

open VectorSpace Finset
variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V] [DecidableEq V]

/-- Helper lemma: Elements of s \ {v} are in S when s ⊆ S ∪ {v} -/
lemma subset_diff_singleton_of_union (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V] [DecidableEq V]
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
lemma zero_coeff_from_not_in_span (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V] [DecidableEq V]
  (S : Set V) (v : V) (s : Finset V) (f : V → K)
  (hv_not_span : ∀ (t : Finset V), ↑t ⊆ S → ∀ (g : V → K), ¬v = t.sum (fun x => g x • x))
  (hvIns : v ∈ s)
  (subset : ↑(s \ {v}) ⊆ S)
  (hf : ((s \ {v}).sum (fun w => f w • w)) + f v • v = 0) :
  f v = 0 := by
  Hint "We will prove this by contradiction. Assume f v ≠ 0, and derive a contradiction."
  by_contra hfv_ne_zero
  Hint "From our assumption, we can get that f v is nonzero, so it has a multiplicative inverse."
  have f_v_inv : f v ≠ 0 := hfv_ne_zero
  let inv_fv : K := (f v)⁻¹
  have g1 : inv_fv * (f v) = (1 : K) := inv_mul_cancel₀ hfv_ne_zero
  have g2 :f v • v =-((s \ {v}).sum (fun w => f w • w)) := by
    exact Eq.symm (neg_eq_of_add_eq_zero_right hf)
  Hint "Now, we can rearrange our equation hf to isolate v."
  have g3 : (-1 : K) • (f v • v) = ((-1 : K) * (f v)) • v := by exact smul_smul (-1) (f v) v
  have rearranged : v =  (s \ {v}).sum (fun w => (inv_fv * ((-1 : K) * (f w))) • w) := by
    calc
      v = (1: K) • v := by rw [one_smul K v]
      _ = (inv_fv * (f v)) • v := by rw [← g1]
      _ = inv_fv • (f v • v) := by rw [smul_smul]
      _ = inv_fv • (-(s \ {v}).sum (fun w => f w • w)) := by
        rw [g2]
      _ = inv_fv • ((-1 : K) • ((s \ {v}).sum (fun w => f w • w))) := by rw [neg_one_smul_v]
      _ = inv_fv • ( ((s \ {v}).sum (fun w => (-1 : K) • (f w • w)))) := by rw [@smul_sum]
      _= inv_fv • ( ((s \ {v}).sum (fun w => ((-1 : K) * (f w)) • w))) := by
        simp [smul_smul]
      _=(s \ {v}).sum (fun w => inv_fv • (((-1 : K) * (f w)) • w)) := by rw[@smul_sum]
      _= (s \ {v}).sum (fun w => (inv_fv * ((-1 : K) * (f w))) • w) := by
        simp [smul_smul]
  set g : V → K := fun w => inv_fv * ((-1 : K) * (f w))
  have g_v : v = ∑ w ∈ s \ {v}, (g w) • w := by exact rearranged
  specialize hv_not_span (s \ {v}) subset g
  exact hv_not_span g_v

NewTheorem Finset.sum_eq_sum_diff_singleton_add Finset.smul_sum inv_mul_cancel₀
  LinearAlgebraGame.subset_diff_singleton_of_union LinearAlgebraGame.zero_coeff_from_not_in_span

Statement linear_independent_insert_of_not_in_span
  {S : Set V} {v : V}
  (hS : linear_independent_v K V S)
  (hv_not_span : v ∉ span K V S):
  linear_independent_v K V (S ∪ {v}) := by
    Hint "First, unfold the definitions, intro the variables and hypotheses we need, and simp where necessary"
    Hint "Linear independence means: if a linear combination equals zero, all coefficients must be zero."
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

    Hint "We want to prove two separate cases: v ∈ s and v ∉ s. If v ∉ s, then we know s ⊆ S, so since S
    is linearly independent, so is s. If v ∈ s, then we have more work to do. "
    Hint "Strategy: Split based on whether the new vector v appears in our linear combination."
    Hint (hidden := true) (strict:=true) "Try `by_cases hvIns : v ∈ s`"
    by_cases hvIns : v ∈ s

    Hint "Now, we want to split {hf} into two, breaking off \{{v}} so we have a sum over a subset of S"
    Hint "We can rewrite the sum as: ∑(s\\\{{v}}) + f(v)•v = 0. This separation is key to our proof."
    Hint (hidden := true) "Try `rw [sum_eq_sum_diff_singleton_add {hvIns}] at {hf}`"
    rw [sum_eq_sum_diff_singleton_add hvIns] at hf

    Hint "Now, that we have a sum over `(s \\ \{{v}})`, we want to show `↑(s \\ \{{v}}) ⊆ S`."
    Hint "**Mathematical Intuition**: Elements in s \\ \{{v}} must be in S since they can't equal v."
    Hint "We use a helper lemma that proves: if s ⊆ S ∪ \{{v}}, then s \\ \{{v}} ⊆ S."
    Hint (hidden := true) "Try `have subset : ↑(s \\ \{{v}}) ⊆ S := subset_diff_singleton_of_union K
    V S v s {hs}`"
    have subset : ↑(s \ {v}) ⊆ S := subset_diff_singleton_of_union K V S v s hs

    Hint "Now, we can prove our important lemma, that `f v = 0`."
    Hint "We'll use proof by contradiction. If f v ≠ 0, we can express v as a linear combination of elements in S."
    Hint "But this contradicts our assumption that v ∉ span(S)! Therefore f(v) must be 0."
    Hint (hidden := true) "Try `have lemma_fv_zero : f v = 0 := zero_coeff_from_not_in_span K V S v
    s f hv_not_span {hvIns} subset hf`"
    have lemma_fv_zero : f v = 0 := zero_coeff_from_not_in_span K V S v s f hv_not_span hvIns subset hf

    Hint "Now, consider two cases: `w = v` or not. If `w = v`, our lemma is our goal. If not,
    we need to use the linear independence of `S`"
    Hint "Since f(v) = 0, the equation becomes: ∑(s\\\{{v}}) f(w)•w = 0, which involves only vectors from S."
    Hint (hidden := true) "Try `by_cases hw2 : w = v`"
    by_cases hw2 : w = v
    Hint (hidden := true) "Try `rw [{hw2}]`"
    rw[hw2]
    Hint (hidden := true) "Try `exact lemma_fv_zero`"
    exact lemma_fv_zero

    Hint "We can use our lemma to show that the sum of `f` over `s \\ \{{v}}` is equal to 0"
    Hint "Substituting f(v) = 0 simplifies our equation to a sum over S only."
    Hint (hidden := true) "Try `rw[lemma_fv_zero] at {hf}`"
    rw[lemma_fv_zero] at hf
    Hint (hidden := true) "Try `simp at {hf}`"
    simp at hf

    Hint "Show that w is in s but not equal to v."
    Hint (hidden := true) "Try `have hwInS : w ∈ s \\ \{{v}} := by (simp; exact ⟨{hw}, {hw2}⟩)`"
    have hwInS : w ∈ s \ {v} := by (simp; exact ⟨hw, hw2⟩)

    Hint "Now, we can apply all of our hypotheses to close the goal"
    Hint "Since S is linearly independent and we have a zero sum over s\\\{{v}} ⊆ S, all coefficients (including f(w)) are zero."
    Hint (hidden := true) "Try `exact {hS} (s \\ \{{v}}) f subset {hf} w {hwInS}`"
    exact hS (s \ {v}) f subset hf w hwInS

    -- Case 2: v ∉ s
    Hint "Show that s is a subset of S using case analysis."
    Hint "In this case, the linear combination doesn't involve v at all, so s ⊆ S directly."
    Hint (hidden := true) "Try `suffices s_subset_S : ↑s ⊆ S`"
    suffices s_subset_S : ↑s ⊆ S
    · -- Use the sufficient condition
      Hint "Apply linear independence to finish the proof."
      Hint "Since s ⊆ S and S is linearly independent, the zero sum implies all coefficients are zero."
      Hint (hidden := true) "Try `exact {hS} s f s_subset_S {hf} w {hw}`"
      exact hS s f s_subset_S hf w hw
    -- Prove the sufficient condition
    Hint (hidden := true) "Try `intro u hu_in_s`"
    intro u hu_in_s
    Hint (hidden := true) "Try `cases' {hs} {hu_in_s} with hu_in_S hu_eq_v`"
    cases' hs hu_in_s with hu_in_S hu_eq_v
    Hint (hidden := true) "For the first case, try `exact hu_in_S`"
    · exact hu_in_S
    Hint (hidden := true) "For the second case, try `simp at hu_eq_v`"
    · simp at hu_eq_v
      Hint (hidden := true) "Try `rw [hu_eq_v] at hu_in_s`"
      rw [hu_eq_v] at hu_in_s
      Hint (hidden := true) "Try `exfalso`"
      exfalso
      Hint (hidden := true) "Try `exact {hvIns} hu_in_s`"
      exact hvIns hu_in_s

    -- The proof is completed by the suffices approach above
