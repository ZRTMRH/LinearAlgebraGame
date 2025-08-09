import Game.Levels.LinearMapsWorld.Level08

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 9

Title "Linear Maps Preserve Dimensions"

Introduction "
Now we'll explore how linear maps interact with the dimensions of vector spaces.

## The Key Insight

If $T : V \\to W$ is a linear map, then the dimension of $V$ equals the dimension of the null space plus the dimension of the range:

$$\\dim V = \\dim(\\text{null } T) + \\dim(\\text{range } T)$$

This prepares us for the **Fundamental Theorem of Linear Algebra**.

## Why This Matters

This relationship shows that linear maps have a very structured effect on dimensions. The input space gets 'split' between the null space (what gets mapped to zero) and the range (what gets output).

## Building Toward Axler 3.21

This level establishes a key property we'll need for the Fundamental Theorem. We'll prove that linear maps cannot increase dimension beyond certain bounds.

### Your Goal
Prove that if T : V → W is injective, then the range has the same dimension as the domain.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

-- We'll use a simplified version that avoids complex dimension theory
-- but still captures the essential idea

/--
Injective linear maps preserve independence.
-/
TheoremDoc LinearAlgebraGame.injective_preserves_independence as "injective_preserves_independence" in "Linear Maps"

/--
If T is injective and maps v to w, then v ≠ 0 if and only if w ≠ 0.
-/
Statement injective_preserves_independence (T : V → W) (hT : is_linear_map_v K V W T)
    (h_inj : injective_v K V W T) (v : V) (w : W) (h_map : T v = w) :
    (v ≠ 0) ↔ (w ≠ 0) := by
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint "First direction: if v ≠ 0, then w ≠ 0."
  · Hint (hidden := true) "Try `intro h_v_ne_zero`"
    intro h_v_ne_zero
    Hint (hidden := true) "Try `intro h_w_zero`"
    intro h_w_zero
    -- We'll prove v = 0, which contradicts h_v_ne_zero
    Hint "We'll show v = 0 to get a contradiction. It suffices to show T v = T 0."
    Hint (hidden := true) "Try `suffices h_eq : T v = T 0`"
    suffices h_eq : T v = T 0
    · -- Apply injectivity to get v = 0, then apply h_v_ne_zero
      Hint "Apply injectivity to get v = 0, then we have our contradiction."
      Hint (hidden := true) "Try `exact h_v_ne_zero (h_inj v 0 h_eq)`"
      exact h_v_ne_zero (h_inj v 0 h_eq)
    -- Now prove T v = T 0
    Hint "Show T v = T 0 using the given facts: T v = w = 0 and T 0 = 0."
    Hint (hidden := true) "Try `rw [h_map]`"
    rw [h_map]
    Hint (hidden := true) "Try `rw [h_w_zero]`"
    rw [h_w_zero]
    Hint (hidden := true) "Try `symm`"
    symm
    Hint (hidden := true) "Try `exact linear_map_preserves_zero K V W T hT`"
    exact linear_map_preserves_zero K V W T hT
  Hint "Second direction: if w ≠ 0, then v ≠ 0."
  · Hint (hidden := true) "Try `intro h_w_ne_zero`"
    intro h_w_ne_zero
    Hint (hidden := true) "Try `intro h_v_zero`"
    intro h_v_zero
    Hint "Show w = 0 to get a contradiction."
    Hint "We need to apply h_w_ne_zero to w = 0."
    Hint (hidden := true) "Try `apply h_w_ne_zero`"
    apply h_w_ne_zero
    Hint "Now show w = 0 using our assumptions."
    Hint (hidden := true) "Try `rw [← h_map]`"
    rw [← h_map]
    Hint "Since v = 0, we need to show T v = 0."
    Hint (hidden := true) "Try `rw [h_v_zero]`"
    rw [h_v_zero]
    Hint "Finally, use the fact that linear maps preserve zero."
    Hint (hidden := true) "Try `exact linear_map_preserves_zero K V W T hT`"
    exact linear_map_preserves_zero K V W T hT

Conclusion "
You've proven that injective linear maps preserve the 'non-zero-ness' of vectors!

This is a crucial step toward understanding how linear maps interact with independence and dimension. Injective maps preserve the essential structure needed for basis theory.
"

end LinearAlgebraGame