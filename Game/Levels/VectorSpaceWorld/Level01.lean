import Game.Metadata.Metadata

namespace LinearAlgebraGame

World "VectorSpaceWorld"
Level 1

Title "Vector space intro, zero scalar multiplication"

/--
## Summary
The `symm` tactic stands for symmetry of equality. It shows that if we know `a = b`, then `b = a`.

## Example
If your goal is `a = b`, `symm` will change the goal to `b = a`.

## Example
If you have a hypothesis `h: a = b`, `symm at h` will change the hypothesis to `h: b = a`.

## Example
If you have a theorem `add_dist: ∀ a b c, (a + b) * c = a * c + b * c`, and a goal `2 * x + 5 * x = y`,
`rw[(add_dist 2 5 x).symm]` will change the goal to `(2 + 5) * x = y`.
-/
TacticDoc symm

NewTactic symm

Introduction "
## Vector Space Definition

We define a vector space `V` over a field `K` as an abelian group with four key axioms. 
In this game, `VectorSpace K V` is built on Mathlib's `Module K V` over a field, which already contains 
all the vector space properties:

```
abbrev VectorSpace (K V : Type) [Field K] [AddCommGroup V] := Module K V
```

The four fundamental vector space axioms are:
- **Distributivity over vector addition:** `a • (x + y) = a • x + a • y`
- **Distributivity over scalar addition:** `(a + b) • x = a • x + b • x`  
- **Associativity:** `(a * b) • x = a • (b • x)`
- **Identity:** `1 • x = x`

This educational approach lets us use standard mathematical terminology while leveraging Mathlib's robust
`Module`, `Field`, and `AddCommGroup` definitions, which provide notation such as `-a` and `a⁻¹`, and include
many helpful theorems that we will not need to prove ourselves.

Note that to write the `•` character, type
\"\\smul\".

Also, note that there is some strange `inst†` text in your objects. This simply means that your objects
are instances of certain classes, for example that K V is a vector space.

## Goal for this level

In this level, you'll prove that multiplying a vector by the zero scalar (`0 : K`) results in the
zero vector (`0 : V`). This is going to be a slightly involved proof, so it is important to get an
understanding of the proof before beginning to write it.

The first step of a normal proof would be writing `0 • w` as `(0 + 0) • w`, then using distributivity
to get it as `0 • w + 0 • w`. Lastly, cancelling out a `0 • w` on each side gets `0 = 0 • w`.

However, this proof relies on our assumptions and constructs the goal from them. This can be done in
Lean, however, it requires using the `have` tactic, and is unnescessarily complex. In Lean, proofs are
often done backwards, working from the goal and creating the hypotheses.

Doing the proof backwards thus must first involve adding `0 • w` to both sides of the goal, undoing
distributivity, then cancelling out some zeros.

### add_right_cancel

To use cancellation of addition, we need a new theorem, `add_right_cancel`. This theorem is a proof
that `a + b = c + b → a = c`. Since your goal is of the form `a = c`, `apply add_right_cancel` will
change the goal to `a + ?b = c + ?b`. However, you want to be able to write the value of `?b`, but
in this case, Lean doesn't know what value you want to add. You can tell Lean what to add to the
equation by `apply add_right_cancel (b := ????)`, replacing the question marks with whatever you
want to add.

### zero_add

We also need to know some basic theorems about addition. For both the scalars and vectors, adding any
vector to `0` will result in that vector. Simply `rw [zero_add]` will show this.

### symm

You will also need the `symm` tactic. `symm` stands for symmetry of equality, and it can be used to
change goals of the form `a = b` to `b = a`. `symm at h` will also change a hypothesis `h: a = b` to
`h: b = a`. However, neither of these uses are needed in this level. You may
notice that if `h: a = b` is a hypothesis, rw[h] will rewrite all `a`s to `b`s. What if you want to
rewrite all `b`s to `a`s, you can instead do `rw[h.symm]`.

Also note that when the theorem has a `∀` symbol, as in `∀ a b : S, a + b = b + a`, you need to
specify what `a` and `b` you mean to use before using `.symm`. For example, you would have to write
`rw[(h 2 3).symm]`.

One last hint is that when writing `0`, you often want to specify which zero you are talking about.
We know that the natural numbers, for example, has a `0`, but so do the Field K and the Abelian Group
V, and those `0`s are different. To specify which `0` you are talking about, write `(0 : K)` or `(0 : V)`.

### Note on simp and linarith

In this world, we are primarilly proving simple statements about vector spaces. This is exactly what
the `simp` and `linarith` tactics are meant to do. In fact, the `simp` tactic alone would be able to
solve the first three levels of this world. Because of this, you will not be able to use those tactics
in this world.
"

-- A vector space over field K with additive group V
-- This is an educational alias for Mathlib's Module over a Field
abbrev VectorSpace (K V : Type) [Field K] [AddCommGroup V] := Module K V

-- Educational theorem statements for the vector space axioms
-- These show the explicit properties that make something a vector space
theorem smul_add_explicit {K V : Type} [Field K] [AddCommGroup V] [VectorSpace K V] 
  (a : K) (x y : V) : a • (x + y) = a • x + a • y := smul_add a x y

theorem add_smul_explicit {K V : Type} [Field K] [AddCommGroup V] [VectorSpace K V]
  (a b : K) (x : V) : (a + b) • x = a • x + b • x := add_smul a b x

theorem mul_smul_explicit {K V : Type} [Field K] [AddCommGroup V] [VectorSpace K V]
  (a b : K) (x : V) : (a * b) • x = a • (b • x) := mul_smul a b x

theorem one_smul_explicit {K V : Type} [Field K] [AddCommGroup V] [VectorSpace K V]
  (x : V) : (1 : K) • x = x := one_smul K x
/--
A vector space is a space over a field K with an abelian group V. In this game, `VectorSpace K V` 
is an educational alias for Mathlib's `Module K V` over a field. It has four main properties:
- Distributivity over vector addition,
- Distributivity over scalar addition,
- Associativity of scalar multiplication,
- Identity scalar acting as identity.

These properties can be found in the theorems tab as "smul_add", "add_smul", "mul_smul", and "one_smul",
as well as the educational versions "smul_add_explicit", "add_smul_explicit", etc.
-/
DefinitionDoc VectorSpace as "Vector Space"

NewDefinition VectorSpace

/--
This is a proof that `0 • w = 0`, or that scaling any vector by `0` gives the zero vector.

It is called "zero_smul_v", since you perform scalar multiplication by zero. The "v" means that it is
scalar multiplication of a vector.
-/
TheoremDoc LinearAlgebraGame.zero_smul_v as "zero_smul_v" in "Vector Spaces"

TheoremTab "Vector Spaces"

/--
`add_right_cancel` is a proof that `a + b = c + b → a = c`. You can tell Lean what to add to the
equation by `apply add_right_cancel (b := ????)`.
-/
TheoremDoc add_right_cancel as "add_right_cancel" in "Groups"

/--
`smul_add` is one of the axioms of a vector space. It is a proof that if we know `vs : VectorSpace K V`,
then `∀ (a : K) (x y : V), a • (x + y) = a • x + a • y`. It can be considered as right distributivity
of scalar multiplication
-/
TheoremDoc smul_add as "smul_add" in "Vector Spaces"

/--
`add_smul` is one of the axioms of a vector space. It is a proof that if we know `vs : VectorSpace K V`,
then `∀ (a b : K) (x : V), (a + b) • x = a • x + b • x`. It can be considered as left distributivity
of scalar multiplication.
-/
TheoremDoc add_smul as "add_smul" in "Vector Spaces"

/--∀ (a b : K) (x : V), (a * b) • x = a • (b • x)
`mul_smul` is one of the axioms of a vector space. It is a proof that if we know `vs : VectorSpace K V`,
then `∀ (a b : K) (x : V), (a * b) • x = a • (b • x)`. It can be considered as associativity of scalar
multiplication.
-/
TheoremDoc MulAction.mul_smul as "mul_smul" in "Vector Spaces"

/--
`one_smul` is one of the axioms of a vector space. It is a proof that if we know `vs : VectorSpace K V`,
then `∀ (x : V), (1 : K) • x = x`. It can be thought of as `1` being a multiplicative identity not
only in `K`, but also through scalar multiplication in `V`.
-/
TheoremDoc one_smul as "one_smul" in "Vector Spaces"

/--
`symm` is a proof that `a = b` if and only if `b = a`
-/
TheoremDoc symm as "symm" in "Lean"
/--
`zero_add` is a proof that `0 + x = x`. This holds whether `x` is in `K` or `V`.
-/
TheoremDoc zero_add as "zero_add" in "Groups"

/--
`add_zero` is a proof that `x + 0 = x`. This holds whether `x` is in `K` or `V`.
-/
TheoremDoc add_zero as "add_zero" in "Groups"

NewTheorem add_right_cancel smul_add add_smul MulAction.mul_smul one_smul symm zero_add add_zero

TheoremTab "Groups"

DisabledTactic simp linarith

open VectorSpace

open VectorSpace Finset
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--
In any vector space V over K, the scalar 0 multiplied by any vector gives the zero vector.
-/
Statement zero_smul_v (w : V) : (0 : K) • w = (0 : V) := by
  Hint "Remember, we are trying to prove this backwards. The last step in the normal proof was to
  cancel out 0 • w from both sides, so what should the first step of the backwards proof be?"
  Hint (hidden := true) "Try `apply add_right_cancel (b := (0 : K) • w)`"
  apply add_right_cancel (b := (0 : K) • w)
  Hint "Now, there is a theorem we have from the vector space definition that can change the left
  side of the equation. Think about the second to last step in the normal proof. You may also need to
  use `.symm` here."
  Hint (hidden := true) "Try `rw[(add_smul (0 : K) (0 : K) w).symm]`"
  rw[(add_smul (0 : K) (0 : K) w).symm]
  Hint "Now, we just have to cancel out zeros."
  Hint (hidden := true) "Try rw[zero_add]"
  rw[zero_add]
  Hint (hidden := true) "Try rw[zero_add]"
  rw[zero_add]

Conclusion "You have now proven your first theorem about vector spaces! One note: if you want to use
one of the theorems you prove in one level in another level, the syntax will often be
`theorem_name K V theorem_args`. This lets Lean know what vector space you are working with."
