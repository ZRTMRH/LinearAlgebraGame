import Game.Levels.LinearMapsWorld.Level01

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 2

Title "The Null Space"

Introduction "
Now that we understand what linear maps are, let's explore one of their most important properties: the **null space**.

## The Core Idea

Given a linear map $T : V \\to W$, some vectors in $V$ get mapped to the zero vector in $W$. The collection of all such vectors forms what we call the **null space** (or kernel) of $T$.

## Mathematical Definition

The null space of a linear map $T : V \\to W$ is:
$$\\text{null } T = \\{v \\in V : T(v) = 0_W\\}$$

### Your Goal
Prove that zero is always in the null space of any linear map.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
**Educational Definition: Null Space**

The null space (or kernel) of a linear map T is the set of all vectors that T maps to zero.

Following Axler's Definition 3.2: Suppose T ∈ L(V,W). Then the null space of T,
denoted null T, is the subset of V consisting of those vectors that T maps to 0.
-/
def null_space_v (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
  [VectorSpace K V] [VectorSpace K W] (T : V → W) : Set V := { v : V | T v = 0 }

/--
`null_space_v T` is the set of vectors that T maps to zero.
-/
DefinitionDoc null_space_v as "null_space_v"

NewDefinition null_space_v

/--
Zero is always in the null space.
-/
TheoremDoc LinearAlgebraGame.zero_in_null_space as "zero_in_null_space" in "Linear Maps"

/--
Zero is always in the null space of any linear map.
-/
Statement zero_in_null_space (T : V → W) (hT : is_linear_map_v K V W T) : 
    (0 : V) ∈ null_space_v K V W T := by
  Hint "Unfold the definition of null_space_v and show T 0 = 0."
  Hint (hidden := true) "Try `show T 0 = 0`"
  show T 0 = 0
  Hint "Use the homogeneity property of linear maps with a = 0."
  Hint (hidden := true) "Try `have h : T (0 • (0 : V)) = 0 • T 0 := hT.2 0 0`"
  have h : T (0 • (0 : V)) = 0 • T 0 := hT.2 0 0
  Hint "Simplify: 0 • v = 0 for any vector v."
  Hint (hidden := true) "Try `simp at h`"
  simp at h
  Hint (hidden := true) "Try `exact h`"
  exact h

Conclusion "
You've proven that zero is always in the null space!

This shows that the null space is never empty - it always contains at least the zero vector. This is the first step toward proving that the null space is a subspace.
"

end LinearAlgebraGame