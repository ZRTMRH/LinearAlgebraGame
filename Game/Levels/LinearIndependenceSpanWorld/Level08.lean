import Game.Levels.LinearIndependenceSpanWorld.Level07

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 8

Title "Uniqueness of linear combinations"

Introduction "This is the \"boss level\" of the Linear Independence and Span World. This level is a
proof that in a linearly independent set, linear combinations are unique. There are also a few new tactics
and multiple new theorems you should use.

### The Goal
In this level, we have 5 objects and 6 hypotheses about those objects. We have the set `S : Set V`,
which is the linearly independent set we are working with. We also have `s` and `f`, which are the set
and function we are summing over to get the first linear combination, and `t` and `g` are the second
linear combination. We have `hs : linear_independent_v K V S`, which states that `S` is linearly independent,
`hs : ↑s ⊆ S` and `ht : ↑t ⊆ S`, which state that `s` and `t` are both in `S`, so are valid linear
combinations of `S`. We know `hf0 : ∀ v ∉ s, f v = 0` and a similar `hg0`, which state that both functions
are zero outside of their domain. This helps us prove `f = g`, since otherwise we wouldn't know what
the values of `f` and `g` would be outside of `s` and `t`. Lastly, we have `heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)`,
which shows that the two linear combinations are equal. We then must pove that `f = g`

### The `specialize` tactic
The `specialize` tactic can be thought of as the opposite of `use`. While `use` helps specify a value
for a `∃` in the goal, `specialize` specifies a value for a `∀` in a hypothesis. For example, if you
have a hypothesis `h : ∀ v : V, v • 1 = v`, and you have a vector `x : V`, then `specialize h x` will
change `h` to `h : x • 1 = x`. `specialize` also works if `h` is an implication. If `h1 : P → Q` is a
hypothesis, and `h2 : P` is a proof of `P`, then `specialize h1 h2` will change `h2` to `h2 : Q`.

### The `by_cases` tactic
The `by_cases` tactic helps you prove something by cases. If you want to prove a statement about vectors
in `V`, but you want to split into cases where `v = 0` or `v ≠ 0`, `by_cases hv : v = 0` will split the
goal into two subgoals: one where you have a hypothesis `hv : v = 0`, and another where you have a hpyothesis
`hv : v ≠ 0`.

### The `funext` tactic
The `funext` tactic lets you prove statements about functions. It works similarly to the `intro` tactic,
where you introduce an arbitrary object, but instead of introducing from a `∀` statment, it works if
you have a goal of the form `f = g`, where `funext x` will change the goal to the form `f x = g x`, and
give you an arbitrary `x` in the domain of `f` and `g`.

### New theorems
This level requires multiple new theorems, particularly ones about Finsets and sums. There are two theorems
about vector spaces that can be proven quite easily, but they are still nice to have without needing
to prove them first. Instead of explaining them all here, you can look at them on the right side of
the screen. The new theorems are: `coe_union`, `union_subset`, `sub_smul`, 'sum_add_distrib', 'sum_sub_distrib',
`subset_union_left`, `subset_union_right`, `sum_subset`, `sub_eq_zero`, and `not_mem_union`.
If you need more theorems, you can either prove them in lemmas, or if you want, you can go to the world
select menu and turn \"Rules\" to \"none\", which should allow you to use any tactic or theorem in Lean.

### Proof overview
If you look at the hypotheses you have, the most important ones are that S is linearly independent and
that the two sums are equal. When you have a statement that a set is linearly independent, it is often
very helpful to try to find the correct set and function to sum over, then try to satisfy the assumptions
to prove that the function must be zero. Since the goal is to prove that `f = g`, maybe try to prove
instead that `f - g = 0`, so you can try proving the assumptions in `hS` with the function `f - g`. You
also need to pick the correct set to be summing over. Since this set must contain both `s` and `t`, you
can use `s ∪ t`. Also, note that this will then only prove that `f = g` on the set `s ∪ t`, so you may
need to use `by_cases` to prove it outside `s ∪ t`.

### Note on hints
With the use of `have` statements, you may have multiple goals at the same time. While this is not a
problem when writing the proof, the hint system may get confused. Starting to type where you
intend to write your next tactic will help clear up what goal you are working on, so it will help the hint
system. However, in general, try to follow your intuition without blindly following the hints.
"

/--
## Summary
The `by_cases` tactic is able to create a new hypothesis, and split the goal into two cases: one where
the hypothesis is true, and one where the hypothesis is false.

In general, if you write `by_cases h : P`, you will create one goal with a hypothesis `h : P`, and another
with a hypothesis `h : ¬P`.

## Example
If you have some vector `v : V`, and some set `s : Set V`, you can solve the proof by cases of whether
v is in s by writing `by_cases h : v ∈ s`, which will give you two goals, one with the hypothesis `h : v ∈ s`,
and one with the hypothesis `h : v ∉ s`.
-/
TacticDoc by_cases

/--
## Summary
The `funext` tactic is very helpful when dealing with functions. It uses the idea that for two functions
`f : A → B` and `g : A → B`, `f = g` if and only if `f x = g x` for all `x ∈ A`. This means that if you
have a goal `f = g`, where both functions have domain `A`, `funext x` will create an arbitrary `x : A`,
and change the goal to `f x = g x`.
-/
TacticDoc funext

/--
## Summary
The `specialize` tactic can be thought of as the opposite of `use`. While `use` helps specify a value
for a `∃` in the goal, `specialize` specifies a value for a `∀` in a hypothesis. If you have a hypothesis
`h`, `specialize h x1 x2 x3` will specify the values in `h` as `x1`, `x2`, and `x3`.

## Example
If you have a hypothesis `h : ∀ x : V, f x = 0`, and some `v : V`, then `specialize h v` will
change the hypothesis to `h : f v = 0`

## Example
If you have a hypothesis `h : x ∈ s → f x = 0`, and another hypothesis `h2 : x ∈ s`, then `specialize h h2`
will change h to `h : f x = 0`
-/
TacticDoc specialize

/--
`coe_union` is a proof that `↑(a ∪ b) = ↑a ∪ ↑b`. The `↑` means type casting, which in this case
specifically means that if `a` is a `Finset`, then `↑a` is a `Set` containing the same elements. This
theorem shows that type casting passes through unions.
-/
TheoremDoc Finset.coe_union as "coe_union" in "Sets"

/--
`union_subset` is a proof that if `a ⊆ c` and `b ⊆ c`, then `a ∪ b ⊆ c`. This means that if you
have two sets that are subsets of the same set, their union is also a subset of that set.
-/
TheoremDoc Set.union_subset as "union_subset" in "Sets"

/--
`sum_add_distrib` is a proof that you can distribute addition over sums. This means that if
you have functions `f : A → B`, and `g : A → B`, and some set `s : Finset A`, then
`Finset.sum s (fun x => f x + g x) = Finset.sum s (fun x => f x) + Finset.sum s (fun x => g x).
-/
TheoremDoc Finset.sum_add_distrib as "sum_add_distrib" in "Sets"

/--
`sum_sub_distrib` is a proof that you can distribute subtraction over sums. This means that if
you have functions `f : A → B`, and `g : A → B`, and some set `s : Finset A`, then
`Finset.sum s (fun x => f x - g x) = Finset.sum s (fun x => f x) - Finset.sum s (fun x => g x).
-/
TheoremDoc Finset.sum_sub_distrib as "sum_sub_distrib" in "Sets"

/--
`Finset.subset_union_left` is a proof that if `a b : Finset S` are sets, then `a ⊆ a ∪ b`.
-/
TheoremDoc Finset.subset_union_left as "Finset.subset_union_left" in "Sets"

/--
`Finset.subset_union_right` is a proof that if `a b : Finset S` are sets, then `b ⊆ a ∪ b`.
-/
TheoremDoc Finset.subset_union_right as "Finset.subset_union_right" in "Sets"

/--
`sum_subset` is a proof that if you have a function that is zero outside of some set, then a sum
on a superset of that set is equal to a sum on that set. If you have a hypothesis `hSub : a ⊆ b`, another hypothesis
`hZero : ∀ x ∈ b, x ∉ a → f x = 0`, then `sum_subset hSub hZero` is a proof that
`Finset.sum b f = Finset.sum a f`
-/
TheoremDoc Finset.sum_subset as "sum_subset" in "Sets"

/--
`sub_smul` is a proof that subtraction distributes over scalar multiplication. `sub_smul a b c` is a proof
that `(a - b) • c = a • c - b • c`.
-/
TheoremDoc sub_smul as "sub_smul" in "Vector Spaces"

/--
`sub_eq_zero` is a proof that `a - b = 0` if and only if `a = b`.
-/
TheoremDoc sub_eq_zero as "sub_eq_zero" in "Groups"

/--
`not_mem_union` is the contrapositive of the definition of a union of sets. It states that if
`v ∉ a ∪ b`, then `v ∉ a ∧ v ∉ b`
-/
TheoremDoc Finset.not_mem_union as "not_mem_union" in "Sets"

/--
`linear_combination_unique` is a proof that representation as a linear combination of a linearly independent
set of vectors is unique. It takes in two subsets of a linearly independent set, along with two functions
representing the linear combinations. The functions must be zero outside of the sets, and their sums
must be equal. In this case, this prooves that functions will be equal.
-/
TheoremDoc LinearAlgebraGame.linear_combination_unique as "linear_combination_unique" in "Vector Spaces"

NewTheorem Finset.coe_union Finset.sum_add_distrib Finset.sum_sub_distrib Finset.sum_subset sub_smul sub_eq_zero Finset.not_mem_union

NewTactic by_cases funext specialize

open VectorSpace Set Finset
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

Statement linear_combination_unique
{S : Set V} (hS : linear_independent_v K V S)
(s t : Finset V) (hs : ↑s ⊆ S) (ht : ↑t ⊆ S)
(f g : V → K) (hf0 : ∀ v ∉ s, f v = 0) (hg0 : ∀ v ∉ t, g v = 0)
(heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)) :
f = g := by
  Hint "First, note that you have a goal of proving two functions equal. Try to instead prove it for
  an arbitrary value."
  Hint (hidden := true) "Try `funext x`"
  funext x

  Hint "Now, we can split into cases where either x ∈ (s ∪ t) or not."
  Hint (hidden := true) "Try `by_cases h : x ∈ (s ∪ t)`"
  by_cases h : x ∈ (s ∪ t)
  Hint (hidden := true) "Try `unfold linear_independent_v at hS`"
  unfold linear_independent_v at hS

  Hint "Think about the forwards proof. What set and function are we summing over when applying the linear independence of S?"
  Hint (hidden := true) "Try `specialize hS (s ∪ t) (f - g)`"
  specialize hS (s ∪ t) (f - g)

  Hint "We now want to show `↑(s ∪ t) ⊆ S`. This is a type casted union. Instead, we want a union of
  type casts, so that we can use theorems having to do with unions. One of the theorems should help with this"
  Hint (hidden := true) "Try `rw[coe_union] at hS`"
  rw[coe_union] at hS

  Hint (hidden := true) "Try `specialize hS (union_subset hs ht)`"
  specialize hS (union_subset hs ht)

  Hint "Now, we have to show that `(Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0`. This will
  be difficult, so try proving it with a `have` statement. Remember to add braces after `by`."
  Hint (hidden := true) "Try `have lemmaSumDiffEqZero : (Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0 := by`"
  have lemmaSumDiffEqZero : (Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0 := by
    Hint "It would be nice if we could distribute the `f - g` through the `•` operator. Try proving
    `(fun v => (f - g) v • v) = (fun (v : V) => ((f v) • v) - ((g v) • v))` with another `have` statement. Remember to add braces after `by`."
    Hint (hidden := true) "Try `  have fun_dist : (fun v => (f - g) v • v) = (fun (v : V) => ((f v) • v) - ((g v) • v)) := by`"
    have fun_dist : (fun v => (f - g) v • v) = (fun (v : V) => ((f v) • v) - ((g v) • v)) := by
      Hint (hidden := true) "Try `    funext v`"
      funext v
      Hint (hidden := true) "Try `    exact sub_smul (f v) (g v) v`"
      exact sub_smul (f v) (g v) v

    Hint (hidden := true) "Try `  rw[fun_dist]`"
    rw[fun_dist]

    Hint "Now, we can split the sum in two"
    Hint (hidden := true) "Try `  rw[sum_sub_distrib]`"
    rw[sum_sub_distrib]

    Hint "We now have two sums. The first one should be equivalent to our first linear combination,
    and the second should be equivalent to our second linear combination. We need to change the sets
    they are being summed over. We have a theorem that can do this, but it needs a hypothesis that we
    don't have. Try proving these hypotheses with a `have` statement. Remember to add braces after `by`."
    Hint (hidden := true) "Try `  have hfprod0 : ∀ v ∈ s ∪ t,  v ∉ s → f v • v = 0 := by`"
    have hfprod0 : ∀ v ∈ s ∪ t,  v ∉ s → f v • v = 0 := by
      Hint (hidden := true) "Try `intros v _hv1 hv2; rw[hf0 v hv2]; exact zero_smul_v K V v`"
      intros v _hv1 hv2
      rw[hf0 v hv2, zero_smul_v]

    Hint (hidden := true) "Try `have hgprod0 : ∀ v ∈ s ∪ t,  v ∉ t → g v • v = 0 := by`"
    have hgprod0 : ∀ v ∈ s ∪ t,  v ∉ t → g v • v = 0 := by
      Hint (hidden := true) "Try `intros v _hv1 hv2; rw[hg0 v hv2]; exact zero_smul_v K V v`"
      intros v _hv1 hv2
      rw[hg0 v hv2, zero_smul_v]

    Hint (hidden := true) "Try `  rw [(sum_subset (f := fun v => f v • v) (subset_union_left s t) hfprod0).symm]`"
    rw [(sum_subset (f := fun v => f v • v) (subset_union_left s t) hfprod0).symm]
    Hint (hidden := true) "Try `  rw [(sum_subset (f := fun v => g v • v) (subset_union_right s t) hgprod0).symm]`"
    rw [(sum_subset (f := fun v => g v • v) (subset_union_right s t) hgprod0).symm]

    Hint "Now, we use the fact that the two sums are equal to finish the proof of the lemma"
    Hint (hidden := true) "Try `rw[heq]; simp`"
    rw[heq]
    simp

  Hint "Now, we simply have to prove the requirements of hS"
  Hint (hidden := true) "Try `specialize hS lemmaSumDiffEqZero`"
  specialize hS lemmaSumDiffEqZero

  Hint (hidden := true) "Try `specialize hS x h`"
  specialize hS x h

  Hint "We know now from hS that f x - g x = 0, and one of the new theorems lets us finish the proof.
  Remember that if you have a proof of `↔`, `.1` will be a proof of the forwards direction and `.2` the
  backwards."
  Hint (hidden := true) "Try `exact sub_eq_zero.1 hS`"
  exact sub_eq_zero.1 hS

  Hint (hidden := true) "Try `rw[not_mem_union] at h`"
  Hint (hidden := true) "Try `cases' h with hxs hxt`"
  Hint "Note: The game may appear to stall after the next step. If it does, you can proceed to the next level - the proof is complete."
  Hint (hidden := true) "Try `rw[hf0 x hxs, hg0 x hxt]`"
  rw[not_mem_union] at h
  cases' h with hxs hxt
  rw[hf0 x hxs, hg0 x hxt]

Conclusion "Congratulations! The next two levels are optional challenges, and although they are
difficult, if you were able to complete this level, you should be able to complete the next two."
