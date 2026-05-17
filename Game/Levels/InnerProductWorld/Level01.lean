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

## Important: Namespace Prefix
When using inner product axioms (like `inner_self_eq_zero`, `inner_self_nonneg`, etc.) in your proofs,
you must use the full namespace prefix `LinearAlgebraGame.`. For example, write
`LinearAlgebraGame.inner_self_eq_zero v` instead of just `inner_self_eq_zero v`.

## The Goal
This first level requires you to prove that `0 ≤ ‖v‖`. Since norm is defined as the square root of a
nonnegative real number, it is inherenetly positive.

**Note:** If you see hints appearing multiple times, this is a known issue with the game framework. Simply continue with your proof - the level will work correctly despite any duplicate hints.
"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [InnerProductSpace_v V]
open Function Set VectorSpace Real


/--
The square root of any real number is nonnegative
-/
TheoremDoc Real.sqrt_nonneg as "sqrt_nonneg" in "ℝ"

/--
For any vector `v`, the imaginary part of `⟪v, v⟫` is zero. Equivalently, `⟪v, v⟫` is real.

**Usage:** Use the full name `LinearAlgebraGame.inner_self_im_zero` when applying this theorem.
-/
TheoremDoc LinearAlgebraGame.inner_self_im_zero as "inner_self_im_zero" in "Inner Product"

/--
For any vector `v` the real part of `⟪v, v⟫` is nonnegative.

**Usage:** Use the full name `LinearAlgebraGame.inner_self_nonneg` when applying this theorem.
-/
TheoremDoc LinearAlgebraGame.inner_self_nonneg as "inner_self_nonneg" in "Inner Product"

/--
For any vector `v`, `⟪v, v⟫ = 0` if and only if `v` is the zero vector.

**Usage:** Use the full name `LinearAlgebraGame.inner_self_eq_zero` when applying this theorem.
-/
TheoremDoc LinearAlgebraGame.inner_self_eq_zero as "inner_self_eq_zero" in "Inner Product"

/--
For any vectors `u, v, w`, ⟪(u + v), w⟫ = ⟪u, w⟫ + ⟪v, w⟫. That is, inner products distribute over addition.

**Usage:** Use the full name `LinearAlgebraGame.inner_add_left` when applying this theorem.
-/
TheoremDoc LinearAlgebraGame.inner_add_left as "inner_add_left" in "Inner Product"

/--
For any vectors `v, w`, and a scalar `a`, ⟪a • v, w⟫ = a * ⟪v, w⟫. This means that scalar multiplication
commutes with the inner product.

**Usage:** Use `InnerProductSpace_v.inner_smul_left` when applying this theorem.
-/
TheoremDoc LinearAlgebraGame.inner_smul_left as "inner_smul_left" in "Inner Product"

/--
For any vectors `v, w`, `⟪v, w⟫ = conj ⟪w, v⟫`. This means that the inner product commutes if you take
the conjugate.

**Usage:** Use the full name `LinearAlgebraGame.inner_conj_symm` when applying this theorem.
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

/--
## Summary

`case` allows you to prove different cases of a goal separately. Often appears after using tactics like `cases'` or `split`.

## Syntax

- `case pos => tactic` - Proves the positive case
- `case neg => tactic` - Proves the negative case
- `case tag => tactic` - Proves the case with the given tag

## Example

After `split` on an if-then-else:
```
split
case pos =>
  -- Prove the case when condition is true
  sorry
case neg =>
  -- Prove the case when condition is false
  sorry
```
-/
TacticDoc «case»

/--
## Summary

`ring_nf` normalizes expressions in rings (structures with +, -, *, 0, 1). It expands and simplifies polynomial expressions.

## Example

`ring_nf` will simplify:
- `(x + y)^2` to `x^2 + 2*x*y + y^2`
- `x * (y + z) - x * y` to `x * z`

## Common usage

Use when you need to expand products, simplify polynomial expressions, or normalize ring calculations.
-/
TacticDoc ring_nf

/--
## Summary

`field_simp` simplifies expressions involving division in fields. It clears denominators and simplifies fractions.

## Example

`field_simp` will simplify:
- `x / y * y` to `x` (assuming `y ≠ 0`)
- `1 / x + 1 / y` to `(y + x) / (x * y)`

## Common usage

Essential when working with fractions, division, or expressions with denominators in fields.
-/
TacticDoc field_simp

/--
## Summary

`norm_cast` normalizes type coercions between numeric types. It pushes coercions as far inward as possible.

## Example

`norm_cast` will transform:
- `↑(n + m) = ↑n + ↑m` where the coercions are from ℕ to ℝ
- `↑n < ↑m ↔ n < m` for appropriate coercions

## Common usage

Use when dealing with mixed numeric types (ℕ, ℤ, ℚ, ℝ, ℂ) to simplify coercion expressions.
-/
TacticDoc norm_cast

/-- `mul_le_mul_of_nonneg_right` allows multiplying inequalities by nonnegative values on the right. -/
TheoremDoc mul_le_mul_of_nonneg_right as "mul_le_mul_of_nonneg_right" in "Inner Product"

/-- `div_mul_cancel` shows that division followed by multiplication cancels. -/
TheoremDoc div_mul_cancel as "div_mul_cancel" in "Inner Product"

/-- `sq_eq_sq₀` relates squared values. -/
TheoremDoc sq_eq_sq₀ as "sq_eq_sq₀" in "Inner Product"

/-- `sq_nonneg` shows that squares are nonnegative. -/
TheoremDoc sq_nonneg as "sq_nonneg" in "Inner Product"

NewTactic «case» ring_nf field_simp norm_cast
NewTheorem mul_le_mul_of_nonneg_right div_mul_cancel sq_eq_sq₀ sq_nonneg
  Real.sqrt_nonneg LinearAlgebraGame.inner_self_im_zero LinearAlgebraGame.inner_self_nonneg LinearAlgebraGame.inner_self_eq_zero LinearAlgebraGame.inner_add_left LinearAlgebraGame.inner_smul_left LinearAlgebraGame.inner_conj_symm

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
