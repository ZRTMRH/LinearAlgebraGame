import Game.Levels.LinearMapsWorld.Level03
import Game.Levels.VectorSpaceWorld

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 4

Title "The Null Space is a Subspace"

Introduction "
We've seen that the null space of a linear map always contains zero. Now we'll prove the stronger result: the null space is always a **subspace** of the domain.

## The Three Subspace Properties

Recall that to show a set $S$ is a subspace, we must verify:

1. **Non-empty**: $S$ contains at least one element (we'll use $0$).
2. **Closed under addition**: if $u, v \\in S$, then $u + v \\in S$.
3. **Closed under scalar multiplication**: if $v \\in S$ and $a$ is a scalar, then $a \\cdot v \\in S$.

## Why This Matters

Together with Level 5, this shows every linear map produces two natural subspaces for free: the null space in $V$ and the range in $W$.

### Your Goal

Prove that the null space of any linear map is a subspace.

**Note:** If you see hints appearing multiple times, this is a known issue with the game framework. Simply continue with your proof - the level will work correctly despite any duplicate hints.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W]
variable [VectorSpace K V] [VectorSpace K W]

/--
Linear maps preserve zero: $T(0) = 0$.
-/
TheoremDoc LinearAlgebraGame.linear_map_preserves_zero as "linear_map_preserves_zero" in "Linear Maps"

theorem linear_map_preserves_zero (T : V → W) (hT : is_linear_map_v K V W T) :
    T 0 = 0 :=
  zero_in_null_space K V W T hT

/--
The null space of a linear map is a subspace.
-/
TheoremDoc LinearAlgebraGame.null_space_is_subspace as "null_space_is_subspace" in "Linear Maps"

NewTheorem LinearAlgebraGame.linear_map_preserves_zero

/--
The null space of any linear map is a subspace of the domain.
-/
Statement null_space_is_subspace (T : V → W) (hT : is_linear_map_v K V W T) :
    isSubspace (K := K) (V := V) (null_space_v K V W T) := by
  Hint "We need to verify the three subspace properties."
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint "First, show the null space is non-empty by exhibiting 0 as a member."
  · -- Non-empty
    Hint (hidden := true) "Try `use 0`"
    use 0
    Hint "Now show 0 is in the null space — this is exactly `zero_in_null_space`."
    Hint (hidden := true) "Try `exact zero_in_null_space K V W T hT`"
    exact zero_in_null_space K V W T hT
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint "For closure under addition: assume T(x) = 0 and T(y) = 0; show T(x + y) = 0."
  · -- Closed under addition
    Hint (hidden := true) "Try `intro x y hx hy`"
    intro x y hx hy
    Hint "Goal `x + y ∈ null_space_v T` unfolds to `T (x + y) = 0`."
    Hint (hidden := true) "Try `show T (x + y) = 0`"
    show T (x + y) = 0
    Hint "Use additivity (`hT.1`) to split `T (x + y)`, then rewrite using the hypotheses."
    Hint (hidden := true) "Try `rw [hT.1 x y, hx, hy]`"
    rw [hT.1 x y, hx, hy]
    Hint "Finally, simplify `0 + 0`."
    Hint (hidden := true) "Try `simp`"
    simp
  Hint "For closure under scalar multiplication: assume T(x) = 0; show T(a • x) = 0."
  · -- Closed under scalar multiplication
    Hint (hidden := true) "Try `intro a x hx`"
    intro a x hx
    Hint "Goal `a • x ∈ null_space_v T` unfolds to `T (a • x) = 0`."
    Hint (hidden := true) "Try `show T (a • x) = 0`"
    show T (a • x) = 0
    Hint "Use homogeneity (`hT.2`) to pull the scalar out, then rewrite using the hypothesis."
    Hint (hidden := true) "Try `rw [hT.2 a x, hx]`"
    rw [hT.2 a x, hx]
    Hint "Finally, simplify `a • 0`."
    Hint (hidden := true) "Try `simp`"
    simp

Conclusion "
You've proven that the null space is always a subspace!

For any linear map $T : V \\to W$, the set of vectors that $T$ sends to zero forms a subspace of $V$. Combined with the upcoming result for the range, we'll have a complete picture of how linear maps interact with subspace structure.
"

end LinearAlgebraGame
