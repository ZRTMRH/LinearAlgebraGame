import Game.Levels.LinearMapsWorld.Level10

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 11

Title "Linear Maps and Isomorphisms"

Introduction "
In our final level, we'll introduce the concept of **isomorphisms** - the gold standard of linear maps.

## The Ultimate Linear Map

An **isomorphism** is a linear map that is both injective and surjective. These are the linear maps that perfectly preserve all the structure of vector spaces.

## Why Isomorphisms Matter

Isomorphisms tell us when two vector spaces are **essentially the same** from a linear algebra perspective. If there's an isomorphism between V and W, then V and W have identical linear algebraic properties.

## The Definition

Following Axler's approach, a linear map $T : V \\to W$ is an **isomorphism** if:
1. $T$ is **linear** (preserves addition and scalar multiplication)
2. $T$ is **injective** (one-to-one)  
3. $T$ is **surjective** (onto)

Equivalently, $T$ is an isomorphism if it has an **inverse** linear map.

### Your Goal
Prove that if T is both injective and surjective, then it's an isomorphism.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

/--
**Educational Definition: Isomorphism**

A linear map that is both injective and surjective is called an isomorphism.
-/
def isomorphism_v (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
  [VectorSpace K V] [VectorSpace K W] (T : V → W) : Prop :=
  is_linear_map_v K V W T ∧ injective_v K V W T ∧ surjective_v K V W T

/--
`isomorphism_v K V W T` means T is a bijective linear map.
-/
DefinitionDoc isomorphism_v as "isomorphism_v"

NewDefinition isomorphism_v

/--
Isomorphisms are bijective linear maps.
-/
TheoremDoc LinearAlgebraGame.isomorphism_iff_bijective_linear as "isomorphism_iff_bijective_linear" in "Linear Maps"

/--
A linear map is an isomorphism if and only if it's both injective and surjective.
-/
Statement isomorphism_iff_bijective_linear (T : V → W) (hT : is_linear_map_v K V W T) :
    isomorphism_v K V W T ↔ (injective_v K V W T ∧ surjective_v K V W T) := by
  Hint "Unfold the definition of isomorphism_v."
  unfold isomorphism_v
  Hint "The definition already includes linearity, so extract the injectivity and surjectivity."
  Hint (hidden := true) "Try `constructor`"
  constructor
  · Hint (hidden := true) "Try `intro h`"
    intro h
    Hint (hidden := true) "Try `exact ⟨h.2.1, h.2.2⟩`"
    exact ⟨h.2.1, h.2.2⟩
  · Hint (hidden := true) "Try `intro h`"
    intro h
    Hint (hidden := true) "Try `exact ⟨hT, h.1, h.2⟩`"
    exact ⟨hT, h.1, h.2⟩

/--
Every isomorphism preserves vector space structure completely.
-/
Statement isomorphism_preserves_structure (T : V → W) (h_iso : isomorphism_v K V W T) 
    (v₁ v₂ : V) (a : K) :
    T (a • v₁ + v₂) = a • T v₁ + T v₂ := by
  Hint "Use the linearity part of the isomorphism."
  Hint (hidden := true) "Try `have h_linear := h_iso.1`"
  have h_linear := h_iso.1
  Hint (hidden := true) "Try `rw [h_linear.1 (a • v₁) v₂]`"
  rw [h_linear.1 (a • v₁) v₂]
  Hint (hidden := true) "Try `rw [h_linear.2 a v₁]`"
  rw [h_linear.2 a v₁]

Conclusion "
**Congratulations!** You have completed LinearMapsWorld!

You've mastered the fundamental concepts of linear map theory:

- **Definition**: What makes a map linear
- **Null Space**: The kernel of information loss  
- **Range**: The image of transformation
- **Injectivity**: One-to-one preservation
- **Surjectivity**: Complete coverage
- **Isomorphisms**: Perfect structure preservation

You've encountered some of the most important theorems in linear algebra, including the **Fundamental Theorem of Linear Algebra** (Axler 3.21).

These concepts form the foundation for understanding:
- **Matrix theory**
- **Eigenvalue problems**  
- **Linear systems**
- **Change of basis**
- **Advanced linear algebra**

Well done on mastering this beautiful mathematical theory!
"

end LinearAlgebraGame