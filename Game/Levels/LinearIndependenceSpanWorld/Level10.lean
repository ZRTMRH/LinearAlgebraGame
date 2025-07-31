/- New Tatics/Theorems


tauto

left

right

let

if then else





-/
import Game.Levels.LinearIndependenceSpanWorld.Level09

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 10

Title "Challenge Level - Span After Removing Elements"

Introduction "
This is the second challenge level, and the last level of the Linear Independence and Span World! Similar
to the first challenge level, this level is optional and can be skipped with the `sorry` tactic, but you can
play through it if you want more practice.

### The Goal
The goal of this level is to prove that if you have some set `S`, and some vector `w` inside the span
of `S \\ {w}`, the span of `S` is the same as the span of `S \\ {w}`. This is because `w` can be written
as a sum of vectors of `S \\ {w}`, so any time you have `w` appear in a linear combination of `S`, you
can simply replace it with a sum of vectors in `S \\ {w}`.

### Proof overview
The most difficult part of this proof is showing that given a linear representation of a vector in the
span of `S`, we can represent it as a sum of vectors in `S \\ {w}`. You are able to represent a sum over
`S` as a sum over `S \\ {w}` plus the function applied to `w`. Then, rewrite `w` as a sum of vectors
in `S \\ {w}`, and recombine the sums.
"

open VectorSpace Finset Set
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--
`subset_insert` is a proof that any set is a subset of itself with an element inserted. In Lean, the
syntax is as follows: if `s : Set T` is a set, and you have `x : T`, then `s ⊆ Set.insert x s`
-/
TheoremDoc Set.subset_insert as "subset_insert" in "Sets"

/--
`Finset.Subset.antisymm_iff` is a proof that two Finsets are equal if and only if they are subsets of each other.
-/
TheoremDoc Finset.Subset.antisymm_iff as "Finset.Subset.antisymm_iff" in "Sets"

/--
`sum_eq_sum_diff_singleton_add` is a proof that if you have some set `s`, with `h : i ∈ s`, then
`Finset.sum s (fun x => f x) = Finset.sum (s / {i}) (fun x => f x) + f i. The syntax is `sum_eq_sum_diff_singleton_add h f`.
-/
TheoremDoc Finset.sum_eq_sum_diff_singleton_add as "sum_eq_sum_diff_singleton_add" in "Sets"

/--
`mem_union_right` is a proof that if `a ∈ t`, then `a ∈ s ∪ t`. The syntax is `mem_union_right s h`.
-/
TheoremDoc Finset.mem_union_right as "mem_union_right" in "Sets"

/--
`subset_diff_singleton` is a proof that if `h : s ⊆ t`, and `hx : x ∉ s`, then `s ⊆ t \ {x}`. The syntax
is `subset_diff_singleton h hx`.
-/
TheoremDoc Set.subset_diff_singleton as "subset_diff_singleton" in "Sets"

/--
`diff_subset` is a proof that `s ⊆ s \ t`. The syntax is `diff_subset s t`.
-/
TheoremDoc Set.diff_subset as "diff_subset" in "Sets"


/--
## Summary
`tauto` solves goals using simple logic. It works similarly to the `simp` and `linarith` tactics, in
that there is not just one use case. If there is a contradiction that can be easily inferred, or if
the goal is a direct result of the hypotheses, `tauto` will solve the goal.

## Example
If your goal is of the form `P ∨ ¬P`, then `tauto will solve the goal.

## Example
If your goal is of the form `A ∨ B`, and you have a hypothesis `h : A ∨ (B ∧ C)`, then `tauto` will
solve the goal.
-/
TacticDoc tauto

/--
## Summary
`left` is one of the ways of proving `or` statements. If your goal is `P ∨ Q`, then `left` changes the
goal to `P`.
-/
TacticDoc left

/--
## Summary
`right` is one of the ways of proving `or` statements. If your goal is `P ∨ Q`, then `right` changes the
goal to `Q`.
-/
TacticDoc right

/--
## Summary
`let` acts very similarly to `have`. Instead of allowing you to create new hypotheses, `let` allows you
to create new objects.

## Using `rw` after `let` statements
You may want to use `rw` with the equalities you choose in a `let` statement. To do this, you must create
a new lemma stating this equality with `have`. The proof will simply be `rfl`.

## Example
If you have objects `x y : V`, then you can say `let z := x + y`, and you will have a new object `z`,
where `z = x + y` can be solvedd by `rfl`

## Example
If you have a function `f : V → K`, and `v : V`, you can say `let f := fun x => f x • v`.
-/
TacticDoc «let»

/--
`ite` stands for `if then else`. If is used when creating functions. You can think of `ite P f1 f2` as
"If P then f1 else f2". This function gives you f1 when P is True, and f2 otherwise. This can help you
design functions that are 0 outside of certain sets.
-/
TacticDoc ite

NewTactic tauto left right «let» ite

NewTheorem Set.subset_insert Finset.Subset.antisymm_iff Finset.sum_eq_sum_diff_singleton_add Finset.mem_union_right Finset.sum_add_distrib Set.subset_diff_singleton Set.diff_subset

TheoremDoc LinearAlgebraGame.remove_redundant_span as "remove_redundant_span" in "Vector Spaces"

Statement remove_redundant_span
  {S : Set V} {w : V} (hcomb : w ∈ span K V (S \ {w})) :
  span K V S = span K V (S \ {w}) := by
  -- We will prove this result by showing the two sets are subsets of each other, which means they are equal.
  Hint "We want to prove two sets are equal. What theorem can help us with this?"
  Hint (hidden := true) "Try `apply Set.eq_of_subset_of_subset`"
  apply eq_of_subset_of_subset

  Hint "First, introduce an arbitrary element, unfold definitions and simp"
  Hint (hidden := true) "Try `intro x hx`"
  intro x hx
  Hint (hidden := true) "Try `unfold span at *`"
  unfold span at *
  Hint (hidden := true) "Try `unfold is_linear_combination at *`"
  unfold is_linear_combination at *
  Hint (hidden := true) "Try `simp at *`"
  simp at *

  Hint "Now, we have two helpful statements. We can use `obtain` to get sets and functions from them"
  Hint (hidden := true) "Try `obtain ⟨sw, hsw, fw, hfw⟩ := hcomb`"
  obtain ⟨sw, hsw, fw, hfw⟩ := hcomb
  Hint (hidden := true) "Try `obtain ⟨sx, hsx, fx, hfx⟩ := hx`"
  obtain ⟨sx, hsx, fx, hfx⟩ := hx

  Hint "Here, we can split into two cases: whether or not `w ∈ sx`"
  Hint (hidden := true) "Try `by_cases hw : w ∈ sx`"
  by_cases hw : w ∈ sx

  Hint "What set should we be summing over? Note that you have two different sets where functions are
  defined, {sw} and {sx}"
  Hint (hidden := true) "Try `use {sw} ∪ ({sx} \\ \{w})`"
  use sw ∪ (sx \ {w})

  Hint (hidden := true) "Try `constructor`"
  constructor

  Hint (hidden := true) "Try `rw[coe_union]`"
  rw[coe_union]
  Hint (hidden := true) "Try `apply Set.union_subset {hsw}`"
  apply Set.union_subset hsw
  Hint (hidden := true) "Try `simp`"
  simp
  Hint (hidden := true) "Try `exact subset_trans {hsx} (subset_insert w S)`"
  exact subset_trans hsx (subset_insert w S)

  Hint "In order to manipulate the sum better, it would be nice to rewrite the set you are summing over.
  You can use a `have` statement to show that this set is equal to `({sw} ∪ {sw} \\ \{w})`. Remember to add braces after `by`."
  Hint (hidden := true) "Try `have set_eq : {sw} ∪ ({sx} \\ \{w}) = ({sw} ∪ {sx}) \\ \{w} := by`"
  have set_eq : sw ∪ (sx \ {w}) = (sw ∪ sx) \ {w} := by
    Hint (hidden := true) "Try `apply Finset.Subset.antisymm_iff.2`"
    apply Finset.Subset.antisymm_iff.2
    Hint (hidden := true) "Try `constructor`"
    constructor

    Hint (hidden := true) "Try `intro x hx`"
    intro x hx

    Hint (hidden := true) "Try `simp`"
    simp
    Hint (hidden := true) "Try `simp at {hx}`"
    simp at hx

    Hint (hidden := true) "Try `constructor`"
    constructor
    Hint (hidden := true) "Try `tauto`"
    tauto

    Hint (hidden := true) "Try `cases' {hx} with hInsw hInsx`"
    cases' hx with hInsw hInsx

    Hint (hidden := true) "Try `intro hEqW`"
    intro hEqW
    Hint (hidden := true) "Try `rw[{hEqW}] at {hInsw}`"
    rw[hEqW] at hInsw
    Hint (hidden := true) "Try `have hContra := {hsw} {hInsw}`"
    have hContra := hsw hInsw
    Hint (hidden := true) "Try simp at {hContra}``"
    simp at hContra

    Hint (hidden := true) "Try `exact {hInsx}.2`"
    exact hInsx.2

    Hint (hidden := true) "Try `intro x hx`"
    intro x hx
    Hint (hidden := true) "Try `simp`"
    simp
    Hint (hidden := true) "Try `simp at {hx}`"
    simp at hx

    Hint (hidden := true) "Try `cases' {hx} with hl hr`"
    cases' hx with hl hr
    Hint (hidden := true) "Try `cases' {hl} with hInsw hInsx`"
    cases' hl with hInsw hInsx

    Hint (hidden := true) "Try `left`"
    left
    Hint (hidden := true) "Try `exact {hInsw}`"
    exact hInsw

    Hint (hidden := true) "Try `right`"
    right
    Hint (hidden := true) "Try `constructor`"
    constructor
    Hint (hidden := true) "Try `exact {hInsx}`"
    exact hInsx
    Hint (hidden := true) "Try `exacr {hr}`"
    exact hr

  Hint "Now, let's consider the function we will be summing. To get a sum of `{x}`, we need two parts:
  the sum over `S` getting `{x}`, and the sum over `S \\ \{w}` to get `w`. This can be thought of as
  two seperate functions. The first function will be similar to `{fx}`, but since we do not know what
  `{fx}` is outside of `{sx}`, we must make this function `0` outside of `sx`. We can define this first
  function with a `let` statement"
  Hint (hidden := true) "Try `let fx' := fun v => (ite (v ∈ {sx}) ({fx} v) 0)`"
  let fx' := fun v => (ite (v ∈ sx) (fx v) 0)
  Hint (hidden := true) "Try `have hfx' : {fx'} = (fun v => (ite (v ∈ {sx}) ({fx} v) 0)) := rfl`"
  have hfx' : fx' = (fun v => (ite (v ∈ sx) (fx v) 0)) := rfl

  Hint "Now, you can prove that summing `{fx'}` over our set gives the correct value. Prove this with
  a `have` statement. Remember to add braces after `by`."
  Hint (hidden := true) "Try `have fx'_sum : {x} - ({fx} w • w) = ({sw} ∪ ({sx} \\ \{w})).sum (fun v => {fx'} v • v) := by`"
  have fx'_sum : x - (fx w • w) = (sw ∪ (sx \ {w})).sum (fun v => fx' v • v) := by

    Hint (hidden := true) "Try `rw[set_eq]`"
    rw[set_eq]

    Hint (hidden := true) "Try `apply add_right_cancel (b := {fx} w • w)`"
    apply add_right_cancel (b := fx w • w)
    Hint (hidden := true) "Try `simp`"
    simp

    Hint (hidden := true) "Try `have hfx'w : {fx} w = {fx'} w := by`"
    have hfx'w : fx w = fx' w := by
      Hint (hidden := true) "Try `rw[{hfx'}]`"
      rw[hfx']
      Hint (hidden := true) "Try `simp only [{hw}]`"
      simp only [hw]
      Hint (hidden := true) "Try `simp`"
      simp

    Hint (hidden := true) "Try `rw[{hfx'w}]`"
    rw[hfx'w]
    Hint (hidden := true) "Try `rw[(sum_eq_sum_diff_singleton_add (mem_union_right {sw} {hw}) (fun v => {fx'} v • v)).symm]`"
    rw[(sum_eq_sum_diff_singleton_add (mem_union_right sw hw) (fun v => fx' v • v)).symm]
    Hint (hidden := true) "Try `rw[{hfx'}]`"
    rw[hfx']
    Hint (hidden := true) "Try `simp`"
    simp
    Hint (hidden := true) "Try `exact {hfx}`"
    exact hfx

  Hint "Now, we can create the second function, which will be added to get the missing `{fx} w • w`"
  Hint (hidden := true) "Try `let fw' := fun v => ite (v ∈ {sw}) ({fx} w * {fw} v) 0`"
  let fw' := fun v => ite (v ∈ sw) (fx w * fw v) 0
  Hint (hidden := true) "Try `have hfw' : {fw'} = (fun v => ite (v ∈ {sw}) ({fx} w * {fw} v) 0) := rfl`"
  have hfw' : fw' = (fun v => ite (v ∈ sw) (fx w * fw v) 0) := rfl

  Hint "Again, prove that the function sums to the correct value. Remember to add braces after `by`."
  Hint (hidden := true) "Try `have fw'_sum : {fx} w • w = ({sw} ∪ ({sx} \\ \{w})).sum (fun v => {fw'} v • v) := by`"
  have fw'_sum : fx w • w = (sw ∪ (sx \ {w})).sum (fun v => fw' v • v) := by
    Hint (hidden := true) "Try `rw[{hfw'}]`"
    rw[hfw']
    Hint (hidden := true) "Try `simp`"
    simp
    Hint (hidden := true) "Try `simp only [mul_smul]`"
    simp only [mul_smul]

    Hint (hidden := true) "Try `rw[(smul_sum (r := {fx} w) (s := {sw}) (f := fun v => {fw} v • v)).symm]`"
    rw[(smul_sum (r := fx w) (s := sw) (f := fun v => fw v • v)).symm]
    Hint (hidden := true) "Try `rw[{hfw}]`"
    rw[hfw]

  Hint "Now, use the functions we have defined"
  Hint (hidden := true) "Try `use fun v => {fx'} v + {fw'} v`"
  use fun v => fx' v + fw' v

  Hint (hidden := true) "Try `simp only [add_smul]`"
  simp only [add_smul]
  Hint (hidden := true) "Try `rw[sum_add_distrib, {fx'_sum}.symm, {fw'_sum}.symm]`"
  rw[sum_add_distrib, fx'_sum.symm, fw'_sum.symm]
  Hint (hidden := true) "Try `simp`"
  simp

  Hint "Now, we are on the second case, when `w ∉ {sx}."
  Hint (hidden := true) "Try `use {sx}`"
  use sx
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint (hidden := true) "Try `exact subset_diff_singleton {hsx} {hw}`"
  exact subset_diff_singleton hsx hw
  Hint (hidden := true) "Try `use fx`"
  use fx

  Hint "Lastly, we must prove that `span K V (S \\ \{w}) ⊆ span K V S`. This is simple with span_mono"
  Hint (hidden := true) "Try `apply span_mono`"
  apply span_mono
  Hint (hidden := true) "Try `exact diff_subset S \{w}`"
  exact diff_subset S {w}

Conclusion "You have now finished the Linear Independence and Span World!"
