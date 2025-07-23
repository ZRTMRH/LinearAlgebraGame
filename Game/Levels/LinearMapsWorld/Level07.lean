import Game.Levels.LinearMapsWorld.Level06

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 7

Title "Surjective Linear Maps"

Introduction "
In our final level of LinearMapsWorld, we'll introduce the concept of surjectivity and prove a basic property.

## The Core Idea

A linear map is surjective (onto) if every element in the codomain can be reached. In other words, the range equals the entire codomain.

## Mathematical Definition

A linear map $T : V \\to W$ is surjective if:
$$\\text{range } T = W$$

This is equivalent to saying: for every $w \\in W$, there exists $v \\in V$ such that $T(v) = w$.

## Why This Matters

Surjectivity tells us when a linear map 'fills up' its target space completely. Combined with injectivity, it characterizes when linear maps are invertible.

### Your Goal
Prove that if T is surjective, then every element of W is in the range of T.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
**Educational Definition: Surjective Linear Map**

A linear map is surjective (onto) if every element in the target space is hit.

Following Axler's approach: T is surjective if for every w ∈ W, there exists v ∈ V such that Tv = w.
-/
def surjective_v (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
  [VectorSpace K V] [VectorSpace K W] (T : V → W) : Prop :=
  ∀ w : W, ∃ v : V, T v = w

/--
`surjective_v K V W T` means T is onto.
-/
DefinitionDoc surjective_v as "surjective_v"

NewDefinition surjective_v

/--
Surjectivity means range equals codomain.
-/
TheoremDoc LinearAlgebraGame.surjective_iff_range_eq as "surjective_iff_range_eq" in "Linear Maps"

/--
If T is surjective, then every element of W is in the range of T.
-/
Statement surjective_iff_range_eq (T : V → W) : 
    surjective_v K V W T ↔ (∀ w : W, w ∈ range_v K V W T) := by
  Hint "Show both directions of the equivalence."
  constructor
  Hint "First direction: if T is surjective, then every w is in the range."
  · intro h_surj w
    show ∃ v : V, T v = w
    exact h_surj w
  Hint "Second direction: if every w is in the range, then T is surjective."
  · intro h_range w
    exact h_range w

Conclusion "
You've connected surjectivity with the range!

You've now learned the fundamental concepts of linear maps: definition, null space, range, and the basic properties they satisfy. These form the foundation for understanding more advanced topics like the rank-nullity theorem and isomorphisms.

Congratulations on completing LinearMapsWorld!
"

end LinearAlgebraGame