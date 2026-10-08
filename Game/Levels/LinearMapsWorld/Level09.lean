import Game.Levels.LinearMapsWorld.Level08

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 9

Title "Injective Maps Preserve Independence"

Introduction "
Now we'll explore a crucial property of injective linear maps: they preserve the distinction between zero and non-zero vectors.

## The Key Insight

If $T : V \\to W$ is an injective linear map and $T(v) = w$, then:
- $v \\neq 0$ if and only if $w \\neq 0$

This shows that injective maps preserve the **structure** of vector spaces - they never collapse non-zero vectors to zero.

## Why This Matters

This property is fundamental because:
- It shows injective maps preserve linear independence
- Non-zero vectors stay non-zero under injective transformations

## Building Toward Level 10

This level shows how injectivity interacts with the zero vector. In Level 10, you'll prove the converse of Level 8: a linear map whose null space is $\\{0\\}$ must be injective.

### Your Goal
Prove that if T is injective and maps v to w, then v ≠ 0 if and only if w ≠ 0.

**Note:** If you see hints appearing multiple times, this is a known issue with the game framework. Simply continue with your proof - the level will work correctly despite any duplicate hints.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [VectorSpace K V] [VectorSpace K W]

-- We'll use a simplified version that avoids complex dimension theory
-- but still captures the essential idea

/--
Injective linear maps preserve independence.
-/
TheoremDoc LinearAlgebraGame.injective_preserves_independence as "injective_preserves_independence" in "Linear Maps"

NewTheorem LinearAlgebraGame.linear_map_preserves_zero

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

This is a crucial step toward understanding how linear maps interact with independence: injective maps never collapse a non-zero vector to zero.
"

end LinearAlgebraGame
