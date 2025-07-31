import Game.Levels.LinearMapsWorld.Level03

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 4

Title "Linear Maps Preserve Zero"

Introduction "
Now let's prove a fundamental property that every linear map must satisfy: they always map the zero vector to the zero vector.

## The Key Insight

This might seem obvious, but it's an important consequence of linearity that we'll use in many future proofs.

## Why This Matters

The fact that linear maps preserve zero is often the first step in proving that the null space is non-empty, and it's crucial for understanding the structure of linear maps.

### Your Goal
Prove that for any linear map T, we have T(0) = 0.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
Linear maps preserve zero.
-/
TheoremDoc LinearAlgebraGame.linear_map_preserves_zero as "linear_map_preserves_zero" in "Linear Maps"

/--
Every linear map maps the zero vector to the zero vector.
-/
Statement linear_map_preserves_zero (T : V → W) (hT : is_linear_map_v K V W T) : 
    T 0 = 0 := by
  Hint "Use the homogeneity property with scalar 0. Apply hT.2 with scalar 0 and vector 0."
  Hint (hidden := true) "Try `have h : T (0 • (0 : V)) = 0 • T 0 := hT.2 0 0`"
  have h : T (0 • (0 : V)) = 0 • T 0 := hT.2 0 0
  Hint "Simplify: 0 • v = 0 for any vector v. Use simp to clean up the zeros."
  Hint (hidden := true) "Try `simp at h`"
  simp at h
  Hint "Now h gives us exactly what we need: T 0 = 0."
  Hint (hidden := true) "Try `exact h`"
  exact h

Conclusion "
You've proven that linear maps always preserve zero!

This simple but fundamental property will be the foundation for many more sophisticated results about linear maps. Every linear map, no matter how complex, must map 0 to 0.
"

end LinearAlgebraGame