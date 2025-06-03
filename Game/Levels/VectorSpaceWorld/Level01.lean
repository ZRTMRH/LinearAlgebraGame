import Game.Metadata

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

We begin by defining a vector space over a field `K` with an abelian group `V`. This class includes four key axioms:

```
class VectorSpace (K V : Type) [Field K] [AddCommGroup V] extends SMul K V where
  smul_add : ∀ (a : K) (x y : V), a • (x + y) = a • x + a • y           -- distributivity of scalar over vector addition
  add_smul : ∀ (a b : K) (x : V), (a + b) • x = a • x + b • x           -- distributivity of scalar addition
  mul_smul : ∀ (a b : K) (x : V), (a * b) • x = a • (b • x)             -- compatibility of scalar multiplication
  one_smul : ∀ (x : V), (1 : K) • x = x                                -- identity scalar acts as identity
```

This foundational structure will be used throughout all future levels. No proof is needed here
— just understand the axioms and how they're represented. Note that to write the `•` character, type
\"\\smul\"

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
"

-- A vector space over field K with additive group V
class VectorSpace (K V : Type) [Field K] [AddCommGroup V] extends SMul K V where
  smul_add : ∀ (a : K) (x y : V), a • (x + y) = a • x + a • y           -- distributivity of scalar over vector addition
  add_smul : ∀ (a b : K) (x : V), (a + b) • x = a • x + b • x           -- distributivity of scalar addition
  mul_smul : ∀ (a b : K) (x : V), (a * b) • x = a • (b • x)             -- compatibility of scalar multiplication
  one_smul : ∀ (x : V) , (1 : K) • x = x

/--
A vector space is a space over a field K with an abelian group V. It has four main properties:
- Distributivity over vector addition,
- Distributivity over scalar addition,
- Associativity of scalar multiplication,
- Identity scalar acting as identity.

These properties can be found in the theorems tab as "smul_add", "add_smul", "mul_smul", and "one_smul".
-/
DefinitionDoc VectorSpace as "Vector Space"

NewDefinition VectorSpace

/--
This is a proof that `0 • w = 0`, or that scaling any vector by `0` gives the zero vector.

It is called "zero_smul_v", since you perform scalar multiplication by zero. The "v" means that it is
scalar multiplication of a vector.
-/
TheoremDoc zero_smul_v as "zero_smul_v" in "Vector Spaces"

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
TheoremDoc VectorSpace.smul_add as "smul_add" in "Vector Spaces"

/--
`add_smul` is one of the axioms of a vector space. It is a proof that if we know `vs : VectorSpace K V`,
then `∀ (a b : K) (x : V), (a + b) • x = a • x + b • x`. It can be considered as left distributivity
of scalar multiplication.
-/
TheoremDoc VectorSpace.add_smul as "add_smul" in "Vector Spaces"

/--∀ (a b : K) (x : V), (a * b) • x = a • (b • x)
`mul_smul` is one of the axioms of a vector space. It is a proof that if we know `vs : VectorSpace K V`,
then `∀ (a b : K) (x : V), (a * b) • x = a • (b • x)`. It can be considered as associativity of scalar
multiplication.
-/
TheoremDoc VectorSpace.mul_smul as "mul_smul" in "Vector Spaces"

/--
`one_smul` is one of the axioms of a vector space. It is a proof that if we know `vs : VectorSpace K V`,
then `∀ (x : V), (1 : K) • x = x`. It can be thought of as `1` being a multiplicative identity not
only in `K`, but also through scalar multiplication in `V`.
-/
TheoremDoc VectorSpace.one_smul as "one_smul" in "Vector Spaces"

/--
This is just so Lean doesn't get mad at me for having `symm` as a tactic when it is considered a theorem.
-/
TheoremDoc symm as "symm" in "Lean"

NewTheorem add_right_cancel VectorSpace.smul_add VectorSpace.add_smul VectorSpace.mul_smul VectorSpace.one_smul symm

TheoremTab "Groups"

open VectorSpace
/--
In any vector space V over K, the scalar 0 multiplied by any vector gives the zero vector.
-/
Statement zero_smul_v (fk : Field K) (acg : AddCommGroup V) (vs : VectorSpace K V) (w : V) : (0 : K) • w = (0 : V) := by
  Hint "Remember, we are trying to prove this backwards. The last step in the normal proof was to
  cancel out 0 • w from both sides, so what should the first step of the backwards proof be?"
  Hint (hidden := true) "Try `apply add_right_cancel (b := (0 : K) • w)`"
  apply add_right_cancel (b := (0 : K) • w)
  Hint "Now, there is a theorem we have from the vector space definition that can change the left
  side of the equation. Think about the second to last step in the normal proof. You may also need to
  use `.symm` here."
  Hint (hidden := true) "Try `rw[(add_smul (0 : K) (0 : K) w).symm]`"
  rw[(add_smul (0 : K) (0 : K) w).symm]
  Hint "Now, we just have to cancel out zeros. You can prove this using some theorems, or there is a
  tactic we have already learned that can simplify everything and close the goal."
  Hint (hidden := true) "Try `simp`"
  simp

Conclusion "You have now proven your first theorem about vector spaces! One note: if you want to use
one of the theorems you prove in one level in another level, the syntax will be
`theorem_name fk acg vs theorem_args`. This is because we take as hypotheses in each level that
K is a Field, V is an abelian group, and K V is a vector space. To use a theorem, we need to include
proofs of those statements."
