import Game.Levels.LinearMapsWorld.Level04
import Game.Levels.VectorSpaceWorld.Level04

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 5

Title "The Range is a Subspace"

Introduction "
Just as we proved that the null space is always a subspace, we'll now prove that the range is also always a subspace.

## The Key Insight

The range of a linear map T : V → W is a subspace of the codomain W. This means we can apply all our subspace theory to understand the image of any linear map.

## Why This Matters

This result, combined with our null space theorem, shows that linear maps have a very structured behavior - both their 'input kernel' and 'output image' are subspaces.

## Proof Strategy

We need to verify the three subspace properties:
1. **Non-empty**: The range contains 0 (since T(0) = 0)
2. **Closed under addition**: If w₁, w₂ are in the range, so is w₁ + w₂
3. **Closed under scalar multiplication**: If w is in the range and a is a scalar, then a•w is in the range

### Your Goal
Prove that the range of any linear map is a subspace.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
The range of a linear map is a subspace.
-/
TheoremDoc LinearAlgebraGame.range_is_subspace as "range_is_subspace" in "Linear Maps"

/--
The range of any linear map is a subspace of the codomain.
-/
Statement range_is_subspace (T : V → W) (hT : is_linear_map_v K V W T) : 
    isSubspace (K := K) (V := W) (range_v K V W T) := by
  Hint "We need to verify the three subspace properties."
  constructor
  Hint "First, show the range is non-empty by proving 0 is in it."
  · -- Non-empty
    use 0
    show ∃ v : V, T v = 0
    use 0
    have h_zero : T 0 = 0 := by
      have h := hT.2 (0 : K) (0 : V)
      simp at h
      exact h
    exact h_zero
  constructor
  Hint "For closure under addition, if w₁ = T(v₁) and w₂ = T(v₂), then w₁ + w₂ = T(v₁ + v₂)."
  · -- Closed under addition
    intro w1 w2 hw1 hw2
    show ∃ v : V, T v = w1 + w2
    -- hw1 : w1 ∈ range_v K V W T means ∃ v1, T v1 = w1
    obtain ⟨v1, hv1⟩ := hw1
    obtain ⟨v2, hv2⟩ := hw2
    use v1 + v2
    rw [hT.1 v1 v2, hv1, hv2]
  Hint "For scalar multiplication, if w = T(v), then a•w = T(a•v)."
  · -- Closed under scalar multiplication
    intro a w hw
    show ∃ v : V, T v = a • w
    obtain ⟨v, hv⟩ := hw
    use a • v
    rw [hT.2 a v, hv]

Conclusion "
You've proven that the range is always a subspace!

Now we know that both the null space and range of any linear map are subspaces. This gives us powerful tools for analyzing the structure and behavior of linear transformations.
"

end LinearAlgebraGame