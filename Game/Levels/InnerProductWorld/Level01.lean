import Game.Levels.InnerProductWorld.LemmasAndDefs

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 1

Title "Norm Is Nonnegative"

Introduction "The first level of this world will introduce two new ideas, the inner product and the norm.
The inner product is a way of taking two vectors, and multiplying them to get a complex number. There
are five main axioms that make such a function a valid inner product. First, any vector's inner product
with itself must be a nonnegative real number. Secondly, a vector's inner product with itself must
equal zero if and only if the vector is itself 0. The third and fourth axioms are that you can distribute
vector addition and commute vector multiplication through the first element of the product. Lastly, the
inner product has conjugate symmetry, that is that `⟪u, v⟫ = conj ⟪v, u⟫. Also, note that in any inner
product space, our field K must be a subfield of ℂ. For convenience we will assume K is equal to ℂ.
This is what allows us to commute multiplication through the inner product.

```
-- Inner product space definition for complex vector spaces
class InnerProductSpace_v (V : Type) [AddCommGroup V] [VectorSpace ℂ V] where
  inner : V → V → ℂ
  inner_self_im_zero : ∀ (v : V), (inner v v).im = 0
  inner_self_nonneg : ∀ (v : V), 0 ≤ (inner v v).re
  inner_self_eq_zero : ∀ (v : V), inner v v = 0 ↔ v = 0
  inner_add_left : ∀ (u v w : V), inner (u + v) w = inner u w + inner v w
  inner_smul_left : ∀ (a : ℂ) (v w : V), inner (a • v) w = a * inner v w
  inner_conj_symm : ∀ (v w : V), inner v w = conj (inner w v)
```

Once we have the inner product, vector norms are easy to define. We simply let `‖v‖ = sqrt ⟪v, v⟫.re`,
which means that the norm of `v` is the square root of it's inner product with itself (we take `.re`)
to make sure that `⟪v, v⟫` is a real number, although we already guarantee this with the first axiom).
Note that the norm is called `norm_v`, which is what you should use if you try to `unfold`.

```
def norm_v (v : V) : ℝ := Real.sqrt ⟪v, v⟫.re
```

## The Goal
This first level requires you to prove that `0 ≤ ‖v‖`. Since norm is defined as the square root of a
nonnegative real number, it is inherenetly positive.
"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real


/--
The square root of any real number is nonnegative
-/
TheoremDoc Real.sqrt_nonneg as "sqrt_nonneg" in "ℝ"

/--
For any vector `v`, the imaginary part of `⟪v, v⟫` is zero. Equivalently, `⟪v, v⟫` is real.
-/
TheoremDoc LinearAlgebraGame.inner_self_im_zero as "inner_self_im_zero" in "Inner Product"

/--
For any vector `v` the real part of `⟪v, v⟫` is nonnegative.
-/
TheoremDoc LinearAlgebraGame.inner_self_nonneg as "inner_self_nonneg" in "Inner Product"

/--
For any vector `v`, `⟪v, v⟫ = 0` if and only if `v` is the zero vector
-/
TheoremDoc LinearAlgebraGame.inner_self_eq_zero as "inner_self_eq_zero" in "Inner Product"

/--
For any vectors `u, v, w`, ⟪(u + v), w⟫ = ⟪u, w⟫ + ⟪v, w⟫. That is, inner products distribute over addition
-/
TheoremDoc LinearAlgebraGame.inner_add_left as "inner_add_left" in "Inner Product"

/--
For any vectors `v, w`, and a scalar `a`, ⟪a • v, w⟫ = a * ⟪v, w⟫. This means that scalar multiplication
commutes with the inner product.
-/
TheoremDoc LinearAlgebraGame.inner_smul_left as "inner_smul_left" in "Inner Product"

/--
For any vectors `v, w`, `⟪v, w⟫ = conj ⟪w, v⟫`. This means that the inner product commutes if you take
the conjugate.
-/
TheoremDoc LinearAlgebraGame.inner_conj_symm as "inner_conj_symm" in "Inner Product"

/--
`InnerProductSpace_v` is how we define inner products. An `InnerProductSpace_v` is another class, similar
to how a `VectorSpace` is a class, and it defines a function `inner` that takes two elements of `V`
and gives an element of `ℂ`. `inner` can also be written as `⟪v, w⟫`. An InnerProductSpace must be a
vector space with field `K = ℂ`, and the inner product must satisfy five axioms: First, any vector's inner product
with itself must be a nonnegative real number. Secondly, a vector's inner product with itself must
equal zero if and only if the vector is itself 0. The third and fourth axioms are that you can distribute
vector addition and commute vector multiplication through the first element of the product. Lastly, the
inner product has conjugate symmetry, that is that `⟪u, v⟫ = conj ⟪v, u⟫. The Lean code defining this is

```
class InnerProductSpace_v (V : Type) [AddCommGroup V] [VectorSpace ℂ V] where
  inner : V → V → ℂ

  -- 1. Positivity: ⟨v,v⟩ is real and non-negative
  inner_self_im_zero : ∀ (v : V), (inner v v).im = 0
  inner_self_nonneg : ∀ (v : V), 0 ≤ (inner v v).re

  -- 2. Definiteness: ⟨v,v⟩ = 0 iff v = 0
  inner_self_eq_zero : ∀ (v : V), inner v v = 0 ↔ v = 0

  -- 3. Additivity in first slot: ⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩
  inner_add_left : ∀ (u v w : V), inner (u + v) w = inner u w + inner v w

  -- 4. Homogeneity in first slot: ⟨a • v, w⟩ = a * ⟨v, w⟩
  inner_smul_left : ∀ (a : ℂ) (v w : V), inner (a • v) w = a * inner v w

  -- 5. Conjugate symmetry: ⟨v, w⟩ = conj(⟨w, v⟩)
  inner_conj_symm : ∀ (v w : V), inner v w = conj (inner w v)
```
-/
DefinitionDoc InnerProductSpace_v as "Inner Product Space"

/--
`norm_v` is how we define vector norms. It can also be written as `‖v‖`. We define the norm of a vector
`v` as the square root of it's inner product with itself. The lean code defining this is

```
def norm_v (v : V) : ℝ := Real.sqrt ⟪v, v⟫.re
```
-/
DefinitionDoc norm_v as "Norm"

NewDefinition InnerProductSpace_v norm_v

NewTheorem Real.sqrt_nonneg LinearAlgebraGame.inner_self_im_zero LinearAlgebraGame.inner_self_nonneg LinearAlgebraGame.inner_self_eq_zero LinearAlgebraGame.inner_add_left LinearAlgebraGame.inner_smul_left LinearAlgebraGame.inner_conj_symm

TheoremTab "Inner Product"
TheoremTab "ℝ"

/-- The norm of any vector is non-negative. -/
TheoremDoc LinearAlgebraGame.norm_nonneg_v as "norm_nonneg_v" in "Inner Product"

Statement norm_nonneg_v (v: V): 0 ≤ ‖v‖ := by
  Hint "Try unfolding the new definition"
  Hint (hidden := true) "Try `unfold norm_v`"
  unfold norm_v
  Hint (hidden := true) "Try `exact Real.sqrt_nonneg ⟪v,v⟫.re`"
  exact sqrt_nonneg ⟪v,v⟫.re

end LinearAlgebraGame
