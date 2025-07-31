import Game.Levels.LinearMapsWorld.Level07

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 8

Title "Injectivity and Null Space (Axler 3.16)"

Introduction "
Now we'll prove one of the most fundamental theorems in linear algebra: **Axler's Theorem 3.16**.

## The Fundamental Theorem

A linear map $T : V \\to W$ is injective **if and only if** $\\text{null } T = \\{0\\}$.

## Why This Is Crucial

This theorem gives us a **practical test for injectivity**. Instead of checking the abstract definition (different inputs give different outputs), we can simply check if anything other than zero gets mapped to zero.

## The Two Directions

1. **If** $T$ is injective, **then** null $T = \\{0\\}$
2. **If** null $T = \\{0\\}$, **then** $T$ is injective

This is Axler's Theorem 3.16: *Suppose T ∈ L(V,W). Then T is injective if and only if null T = {0}.*

### Your Goal
Prove the first direction: if T is injective, then the null space is trivial.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
**Educational Definition: Injective Linear Map**

A linear map is injective (one-to-one) if different inputs produce different outputs.

Following Axler's approach: T is injective if Tu = Tv implies u = v.
-/
def injective_v (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
  [VectorSpace K V] [VectorSpace K W] (T : V → W) : Prop :=
  ∀ u v : V, T u = T v → u = v

/--
`injective_v K V W T` means T is one-to-one.
-/
DefinitionDoc injective_v as "injective_v"

NewDefinition injective_v

/--
If T is injective, then null T = {0} (Axler 3.16, first direction).
-/
TheoremDoc LinearAlgebraGame.injective_implies_trivial_null as "injective_implies_trivial_null" in "Linear Maps"

/--
If T is injective, then its null space contains only zero.
-/
Statement injective_implies_trivial_null (T : V → W) (hT : is_linear_map_v K V W T) 
    (h_inj : injective_v K V W T) : 
    null_space_v K V W T = {0} := by
  Hint "Prove set equality by showing both inclusions: null space ⊆ {0} and {0} ⊆ null space."
  Hint (hidden := true) "Try `ext v`"
  ext v
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint "First direction: if v ∈ null space, then v = 0."
  · Hint (hidden := true) "Try `intro hv`"
    intro hv
    -- hv : v ∈ null_space_v K V W T means T v = 0
    show v = 0
    Hint "Use injectivity: since T(v) = T(0) = 0, we get v = 0."
    -- We know T v = 0 from hv
    Hint (hidden := true) "Try `have h_zero : T 0 = 0 := by have h := hT.2 (0 : K) (0 : V); simp at h; exact h`"
    have h_zero : T 0 = 0 := by
      -- Linear maps preserve zero (from Level 4)
      have h := hT.2 (0 : K) (0 : V)
      simp at h
      exact h
    -- Now T v = 0 = T 0, so by injectivity v = 0
    Hint (hidden := true) "Try `have h_eq : T v = T 0 := by rw [h_zero]; exact hv`"
    have h_eq : T v = T 0 := by
      rw [h_zero]
      exact hv
    Hint (hidden := true) "Try `exact h_inj v 0 h_eq`"
    exact h_inj v 0 h_eq
  Hint "Second direction: if v = 0, then v ∈ null space."
  · Hint (hidden := true) "Try `intro hv`"
    intro hv
    -- hv : v = 0
    show T v = 0
    Hint (hidden := true) "Try `rw [hv]`"
    rw [hv]
    -- T 0 = 0 from Level 4
    Hint (hidden := true) "Try `have h := hT.2 (0 : K) (0 : V); simp at h; exact h`"
    have h := hT.2 (0 : K) (0 : V)
    simp at h
    exact h

Conclusion "
You've proven half of Axler's fundamental theorem!

This direction shows that injectivity forces the null space to be as small as possible - containing only zero. Combined with the reverse direction, this gives us a complete characterization of when linear maps are injective.
"

end LinearAlgebraGame