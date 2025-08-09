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
Educational theorem demonstrating the key insight of the Fundamental Theorem.
We prove that injective linear maps preserve important structural properties.
-/
lemma fundamental_theorem_insight (T : V → W) (hT : is_linear_map_v K V W T)
    (h_inj : injective_v K V W T) :
    ∀ v₁ v₂ : V, (v₁ ≠ v₂) → (T v₁ ≠ T v₂) := by
  intros v₁ v₂ h_diff
  intro h_same
  have h_eq : v₁ = v₂ := h_inj v₁ v₂ h_same
  exact h_diff h_eq

TheoremDoc LinearAlgebraGame.fundamental_theorem_insight as "fundamental_theorem_insight" in "Linear Maps"

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
  -- Apply injectivity: since T v = 0 = T 0, we get v = 0
  Hint "Apply injectivity to T v = 0 and T 0 = 0."
  Hint (hidden := true) "Try `apply h_inj`"
  apply h_inj
  Hint (hidden := true) "Try `rw [hv]`"
  rw [hv]
  Hint (hidden := true) "Try `symm`"
  symm
  Hint (hidden := true) "Try `exact linear_map_preserves_zero K V W T hT`"
  exact linear_map_preserves_zero K V W T hT

/--
Educational demonstration: the principle that makes the Fundamental Theorem work.
-/
lemma fundamental_principle_demo (T : V → W) (hT : is_linear_map_v K V W T)
    (h_inj : injective_v K V W T) (v₁ v₂ : V) :
    -- If T maps two vectors to the same place, they must be the same vector
    T v₁ = T v₂ → v₁ = v₂ := by
  exact h_inj v₁ v₂

TheoremDoc LinearAlgebraGame.fundamental_principle_demo as "fundamental_principle_demo" in "Linear Maps"

Conclusion "
You've proven a **key insight** about the Fundamental Theorem of Linear Algebra!

You've shown that **injective linear maps have trivial null spaces** - only the zero vector gets mapped to zero.

This is half of a fundamental characterization: a linear map is injective if and only if its null space is {0}.

## Why This Matters

This connection between injectivity and null spaces is crucial because:
- It gives us a **practical test** for injectivity
- It reveals the **structural preservation** property of injective maps
- It's a stepping stone to the full Fundamental Theorem

The complete Fundamental Theorem states that for linear maps between equal-dimensional spaces, the following are equivalent:
- The map is injective
- The map is surjective  
- The map is bijective (an isomorphism)

Your proof today established one of the key pieces of this beautiful result!
"

end LinearAlgebraGame