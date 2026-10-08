import Game.Levels.LinearMapsWorld.Level09

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 10

Title "Trivial Null Space Implies Injective"

Introduction "
In Level 8 we proved one direction of the **injectivity criterion**: if $T$ is injective, then $\\text{null } T = \\{0\\}$. Now we'll prove the other direction, completing the characterization.

## The Converse

If $\\text{null } T = \\{0\\}$, then $T$ is **injective**.

## The Idea

Suppose $T(u) = T(v)$. By linearity,
$$T(u + (-1) \\cdot v) = T(u) + (-1) \\cdot T(v) = T(v) - T(v) = 0,$$
so $u + (-1) \\cdot v$ lies in the null space. Since the null space is $\\{0\\}$, we get $u - v = 0$, i.e. $u = v$.

## Why This Matters

Together with Level 8, this gives the full theorem: *a linear map is injective if and only if its null space is $\\{0\\}$*. To check that a linear map is injective, it is enough to check that only $0$ is sent to $0$.

### Your Goal

Prove that if the null space of $T$ is $\\{0\\}$, then $T$ is injective.

**Note:** If you see hints appearing multiple times, this is a known issue with the game framework. Simply continue with your proof - the level will work correctly despite any duplicate hints.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W]
variable [VectorSpace K V] [VectorSpace K W]

/--
If null T = {0}, then T is injective (second direction of the injectivity criterion).
-/
TheoremDoc LinearAlgebraGame.trivial_null_implies_injective as "trivial_null_implies_injective" in "Linear Maps"

/--
If the null space of a linear map T contains only zero, then T is injective.
-/
Statement trivial_null_implies_injective (T : V → W) (hT : is_linear_map_v K V W T)
    (h_null : null_space_v K V W T = {0}) :
    injective_v K V W T := by
  Hint "Unfold injectivity: take two vectors `u` and `v` with `T u = T v`, and show `u = v`."
  Hint (hidden := true) "Try `intro u v huv`"
  intro u v huv
  Hint "The key step: show that `u + (-1 : K) • v` is in the null space of `T`."
  Hint (hidden := true) "Try `have h : u + (-1 : K) • v ∈ null_space_v K V W T`"
  have h : u + (-1 : K) • v ∈ null_space_v K V W T := by
    Hint "Membership in the null space unfolds to `T (u + (-1 : K) • v) = 0`."
    Hint (hidden := true) "Try `show T (u + (-1 : K) • v) = 0`"
    show T (u + (-1 : K) • v) = 0
    Hint "Use additivity (`hT.1`) and homogeneity (`hT.2`), then `huv` to replace `T u` with `T v`, and `neg_one_smul_v` to turn `(-1 : K) • T v` into `-T v`."
    Hint (hidden := true) "Try `rw [hT.1, hT.2, huv, neg_one_smul_v]`"
    rw [hT.1, hT.2, huv, neg_one_smul_v]
    Hint (hidden := true) "Try `exact add_neg_cancel (T v)`"
    exact add_neg_cancel (T v)
  Hint "Now use `h_null` to replace the null space with the set containing only zero."
  Hint (hidden := true) "Try `rw [h_null] at h`"
  rw [h_null] at h
  Hint "Membership in the set containing only zero means being equal to zero."
  Hint (hidden := true) "Try `have h2 : u + (-1 : K) • v = 0 := h`"
  have h2 : u + (-1 : K) • v = 0 := h
  Hint (hidden := true) "Try `rw [neg_one_smul_v] at h2`"
  rw [neg_one_smul_v] at h2
  Hint "We know `u + -v = 0`. To show `u = v`, add `-v` to both sides with `add_right_cancel`."
  Hint (hidden := true) "Try `apply add_right_cancel (b := -v)`"
  apply add_right_cancel (b := -v)
  Hint (hidden := true) "Try `rw [add_neg_cancel]`"
  rw [add_neg_cancel]
  Hint (hidden := true) "Try `exact h2`"
  exact h2

Conclusion "
You've proven the second half of the injectivity criterion! Combined with Level 8:

$$T \\text{ is injective} \\iff \\text{null } T = \\{0\\}$$

This gives a practical test for injectivity: instead of comparing $T(u)$ and $T(v)$ for every pair of vectors, it is enough to check which vectors $T$ sends to $0$.
"

end LinearAlgebraGame
