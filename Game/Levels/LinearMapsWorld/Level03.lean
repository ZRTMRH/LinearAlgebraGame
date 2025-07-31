import Game.Levels.LinearMapsWorld.Level02

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 3

Title "The Range"

Introduction "
Now let's explore the other fundamental concept associated with linear maps: the **range**.

## The Core Idea

While the null space tells us which vectors get mapped to zero, the range tells us which vectors can be reached as outputs of the linear map.

## Mathematical Definition

The range of a linear map $T : V \\to W$ is:
$$\\text{range } T = \\{w \\in W : \\exists v \\in V, T(v) = w\\}$$

## Why This Matters

The range describes the 'image' or 'output space' of the linear map. Together with the null space, it gives us complete information about what the linear map does.

### Your Goal
Prove that if $T$ maps $v$ to $w$, then $w$ is in the range of $T$.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
**Educational Definition: Range**

The range (or image) of a linear map T is the set of all possible outputs of T.

Following Axler's Definition 3.3: Suppose T ∈ L(V,W). Then the range of T,
denoted range T, is the subset of W consisting of those vectors that are of
the form Tv for some v ∈ V.
-/
def range_v (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
  [VectorSpace K V] [VectorSpace K W] (T : V → W) : Set W := { w : W | ∃ v : V, T v = w }

/--
`range_v K V W T` is the set of all possible outputs of T.
-/
DefinitionDoc range_v as "range_v"

NewDefinition range_v

/--
Images are in the range.
-/
TheoremDoc LinearAlgebraGame.mem_range_of_map as "mem_range_of_map" in "Linear Maps"

/--
If T maps v to w, then w is in the range of T.
-/
Statement mem_range_of_map (T : V → W) (v : V) (w : W) (h : T v = w) : 
    w ∈ range_v K V W T := by
  Hint "Show there exists some vector that T maps to w."
  Hint (hidden := true) "Try `show ∃ u : V, T u = w`"
  show ∃ u : V, T u = w
  Hint "Use v as the witness and apply hypothesis h."
  Hint (hidden := true) "Try `use v, h`"
  use v, h

Conclusion "
You've proven that outputs of T are always in its range!

This establishes the basic relationship between a linear map and its range. The range captures exactly those vectors that can be 'reached' by applying T to some input.
"

end LinearAlgebraGame