import Game.Levels.LinearIndependenceSpanWorld.Level08

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 1

Title "What is a Linear Map?"

Introduction "
In this level, we introduce the fundamental concept of a **linear map** between vector spaces.

## The Core Idea

A linear map (also called a linear transformation) is a function between vector spaces that preserves the essential vector space operations: addition and scalar multiplication.

## Mathematical Definition

Given vector spaces $V$ and $W$ over a field $K$, a function $T : V \\to W$ is called linear if it satisfies these two properties:

• Additivity: $T(u + v) = T(u) + T(v)$ for all $u, v \\in V$
• Homogeneity: $T(a \\cdot v) = a \\cdot T(v)$ for all $a \\in K$ and $v \\in V$

## Why This Matters

Linear maps are the structure-preserving functions of linear algebra. They respect the vector space structure, making them the natural morphisms between vector spaces.

### Your Goal
Prove that our definition captures exactly these two fundamental properties. 

In Lean, we define `is_linear_map_v K V W T` (see Definitions panel) to formalize exactly what it means for a function T to be linear.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
**Educational Definition: Linear Map**

A function `T : V → W` between vector spaces is called *linear* if it preserves
vector addition and scalar multiplication.

This follows Axler's Definition 3.1: A function T : V → W is called a linear map if
T(u + v) = Tu + Tv and T(av) = aTv for all u, v ∈ V and all a ∈ F.
-/
def is_linear_map_v (T : V → W) : Prop :=
  (∀ u v : V, T (u + v) = T u + T v) ∧ 
  (∀ a : K, ∀ v : V, T (a • v) = a • T v)

/--
`is_linear_map_v K V W T` means T preserves addition and scalar multiplication.
-/
DefinitionDoc is_linear_map_v as "is_linear_map_v"

NewDefinition is_linear_map_v

/--
A linear map preserves vector addition and scalar multiplication.
-/
TheoremDoc LinearAlgebraGame.linear_map_def as "linear_map_def" in "Linear Maps"

TheoremTab "Linear Maps"

/--
The definition of a linear map is exactly additivity and homogeneity.
-/
Statement linear_map_def (T : V → W) :
    is_linear_map_v K V W T ↔ 
    (∀ u v : V, T (u + v) = T u + T v) ∧ (∀ a : K, ∀ v : V, T (a • v) = a • T v) := by
  Hint "Try unfold is_linear_map_v to see the definition directly."
  Hint (hidden := true) "Try `unfold is_linear_map_v`"
  unfold is_linear_map_v
  Hint (hidden := true) "Try `rfl`"
  rfl

Conclusion "
You have formalized the fundamental definition of a linear map.

Linear maps are the backbone of linear algebra - they preserve the structure we care about. In the next levels, you'll explore what linear maps do to special sets like the null space and range.
"

end LinearAlgebraGame
