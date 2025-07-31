import Game.Levels.LinearMapsWorld.Level05

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 6

Title "Linear Maps Preserve Linear Combinations"

Introduction "
Now we'll prove that linear maps preserve not just addition and scalar multiplication, but any linear combination.

## The Key Insight

If we have vectors v₁, v₂ and scalars a₁, a₂, then:
T(a₁ • v₁ + a₂ • v₂) = a₁ • T(v₁) + a₂ • T(v₂)

This shows that linear maps preserve the fundamental operation of linear algebra: taking linear combinations.

## Strategy

This proof uses both defining properties of linear maps:
1. **Additivity**: T(u + v) = T(u) + T(v) - to split the sum
2. **Homogeneity**: T(a • v) = a • T(v) - to factor out scalars

## Why This Matters

This property is what makes linear maps so powerful - they preserve all the structure we care about in linear algebra. Any relationship expressed as a linear combination in the domain is preserved in the codomain.

### Your Goal
Prove that linear maps preserve linear combinations of two vectors.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W]
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
Linear maps preserve linear combinations.
-/
TheoremDoc LinearAlgebraGame.linear_map_preserves_combination as "linear_map_preserves_combination" in "Linear Maps"

/--
Linear maps preserve linear combinations of two vectors.
-/
Statement linear_map_preserves_combination (T : V → W) (hT : is_linear_map_v K V W T)
    (a1 a2 : K) (v1 v2 : V) :
    T (a1 • v1 + a2 • v2) = a1 • T v1 + a2 • T v2 := by
  Hint "Use additivity to split T(a₁ • v₁ + a₂ • v₂). The additivity property says T(u + v) = T(u) + T(v)."
  Hint (hidden := true) "Try `rw [hT.1 (a1 • v1) (a2 • v2)]`"
  rw [hT.1 (a1 • v1) (a2 • v2)]
  Hint "Now use homogeneity on each term. The homogeneity property says T(a • v) = a • T(v)."
  Hint (hidden := true) "Try `rw [hT.2 a1 v1, hT.2 a2 v2]`"
  rw [hT.2 a1 v1, hT.2 a2 v2]

Conclusion "
You've proven that linear maps preserve linear combinations!

This is a fundamental property that captures the essence of what makes a map 'linear' - it preserves the basic operations of linear algebra. This result can be extended to any finite linear combination.
"

end LinearAlgebraGame
