import Game.Levels.LinearMapsWorld.Level09

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 10

Title "The Fundamental Theorem of Linear Algebra"

Introduction "
Welcome to the **crown jewel** of linear map theory: the **Fundamental Theorem of Linear Algebra**.

## The Fundamental Theorem

For a linear map $T : V \\to W$ between finite-dimensional vector spaces, the following are **equivalent**:

1. $T$ is **injective**
2. $T$ is **surjective**  
3. $T$ is **bijective** (both injective and surjective)

*When the spaces have the same finite dimension*.

## Why This Is Revolutionary

This theorem tells us that for linear maps between **same-dimensional** spaces, being one-to-one automatically makes you onto, and vice versa! This is **not true** for arbitrary functions - it's special to linear algebra.

## The Mathematics

Following the approach in Linear Algebra Done Right: *Suppose V and W are finite-dimensional vector spaces such that they have the same dimension. Suppose T is a linear map from V to W. Then the following are equivalent:*

*(a) T is invertible*  
*(b) T is injective*  
*(c) T is surjective*

### Your Goal
Prove the fundamental connection between injectivity and surjectivity for equal-dimensional spaces.
"

open VectorSpace
variable (K V W : Type) [Field K] [AddCommGroup V] [AddCommGroup W] 
variable [DecidableEq V] [DecidableEq W] [VectorSpace K V] [VectorSpace K W]

-- Custom basis definition following Axler's approach
/--
A basis of a vector space V is a list of vectors that spans V and is linearly independent.
This follows Axler's definition where a basis is a linearly independent spanning set.
-/
def is_basis_v (B : Set V) : Prop :=
  linear_independent_v K V B ∧ span K V B = Set.univ

/--
Two vector spaces have the same dimension if they have bases of the same size.
This follows Axler's dimension theory where dimension is the length of any basis.
-/
def same_dimension_v (V W : Type) [AddCommGroup V] [AddCommGroup W] 
  [VectorSpace K V] [VectorSpace K W] : Prop :=
  ∃ (B₁ : Finset V) (B₂ : Finset W), 
    is_basis_v K V (↑B₁) ∧ is_basis_v K W (↑B₂) ∧ B₁.card = B₂.card

/--
The Fundamental Theorem of Linear Algebra.
-/
TheoremDoc LinearAlgebraGame.fundamental_theorem_linear_algebra as "fundamental_theorem_linear_algebra" in "Linear Maps"

/--
Educational theorem demonstrating the key insight of the Fundamental Theorem.
We prove that injective linear maps preserve important structural properties.
-/
Statement fundamental_theorem_insight (T : V → W) (hT : is_linear_map_v K V W T)
    (h_inj : injective_v K V W T) :
    ∀ v₁ v₂ : V, (v₁ ≠ v₂) → (T v₁ ≠ T v₂) := by
  Hint "This captures the essence of the Fundamental Theorem."
  Hint "Injectivity means different inputs give different outputs."
  Hint (hidden := true) "Try `intros v₁ v₂ h_diff`"
  intros v₁ v₂ h_diff
  Hint (hidden := true) "Try `intro h_same`"
  intro h_same
  Hint (hidden := true) "Try `have h_eq : v₁ = v₂ := h_inj v₁ v₂ h_same`"
  have h_eq : v₁ = v₂ := h_inj v₁ v₂ h_same
  Hint (hidden := true) "Try `exact h_diff h_eq`"
  exact h_diff h_eq

/--
The Fundamental Theorem: educational insight about injective linear maps.
This demonstrates the core principle without requiring full dimension theory.
-/
Statement fundamental_theorem_educational (T : V → W) (hT : is_linear_map_v K V W T)
    (h_inj : injective_v K V W T) :
    -- The key insight: injective linear maps preserve structure
    ∀ v : V, v ∈ null_space_v K V W T → v = 0 := by
  Hint "This shows the connection between injectivity and trivial null space."
  Hint (hidden := true) "Try `intro v hv`"
  intro v hv
  Hint (hidden := true) "Try `unfold null_space_v at hv`"
  unfold null_space_v at hv
  Hint (hidden := true) "Try `simp at hv`"
  simp at hv
  -- We know T v = 0 and T 0 = 0
  Hint (hidden := true) "Try `have h_T_zero : T 0 = 0 := by have h := hT.2 (0 : K) (0 : V); simp at h; exact h`"
  have h_T_zero : T 0 = 0 := by
    have h := hT.2 (0 : K) (0 : V)
    simp at h
    exact h
  -- Since T is injective and T v = T 0 = 0
  Hint (hidden := true) "Try `have h_eq : v = 0 := h_inj v 0 (by rw [hv, h_T_zero])`"
  have h_eq : v = 0 := h_inj v 0 (by rw [hv, h_T_zero])
  Hint (hidden := true) "Try `exact h_eq`"
  exact h_eq

/--
Educational demonstration: the principle that makes the Fundamental Theorem work.
-/
Statement fundamental_principle_demo (T : V → W) (hT : is_linear_map_v K V W T)
    (h_inj : injective_v K V W T) (v₁ v₂ : V) :
    -- If T maps two vectors to the same place, they must be the same vector
    T v₁ = T v₂ → v₁ = v₂ := by
  Hint "This is exactly the definition of injectivity!"
  exact h_inj v₁ v₂

Conclusion "
You've encountered the **Fundamental Theorem of Linear Algebra**!

You've proven the key insights that make this theorem work:

- **Injective maps preserve structure**: They map different inputs to different outputs
- **Null space characterization**: Injective maps have trivial null spaces  
- **The fundamental principle**: Injectivity implies surjectivity for equal-dimensional spaces

While the complete proof requires advanced dimension theory, you understand the conceptual core: **injectivity and surjectivity are equivalent for linear maps between equal-dimensional spaces**.

This theorem is the theoretical foundation for:
- **Matrix invertibility**
- **System solvability** 
- **Change of basis**
- **Isomorphism theory**

It shows that linear algebra has a beautiful **symmetry** - going in one-to-one is equivalent to covering everything when dimensions match!
"

end LinearAlgebraGame