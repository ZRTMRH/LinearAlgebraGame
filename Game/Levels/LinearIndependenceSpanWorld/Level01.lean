import Game.Levels.VectorSpaceWorld.Level05

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 1

Title "Linear Combinations"

Introduction "The first level of this world will introduce the definition of a linear combination. Let's
say we want to express that some vector `x` is a linear combination of some set `S ⊆ V`. This means
that there is some number of elements in `S`, that after some scalar multiplication, sums to `x`.
Since infinite sums are difficult (and sometimes impossible) to work with, we can't simply sum over
all of `S`. Instead, we take some smaller subset `s : Finset V`, with `↑s ⊆ S`, and sum over that.
Note here the `↑` character. This simply takes our finite set `s`, which is a `Finset`, and treats it
as a `Set`.

Once we have the set we are summing over `s`, we need to also multiply the elements of `s` by scalars.
We do this with a function `f : V → K`, where each element of `s` gets mapped to the scalar we multiply by.
Now, we are able to understand the definition of linear combinations:

```
def is_linear_combination (S : Set V) (x : V) : Prop :=
  ∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (x = Finset.sum s (fun v => f v • v))
```

### The Goal
The goal of this level is to prove that if `v ∈ S`, then `v` is a linear combination of `s`. This can
be done simply by summing over the set `{v}`, with only multiplying by the scalar 1.

### Defining functions
In this level, we need to use the `use` tactic to specify a function `f`. A very versatile way of doing
this is with the `fun` keyword. This allows you to write the function, and for Lean to accept it as a function.
For example, to write `f(x) = x²`, we can say `fun x => x * x`.

### The return of the `simp` tactic
Since the levels in this world will become more difficult than in the last world, you are again allowed
to use the `simp` tactic. It is able to solve most simple equalities with vectors, and helps greatly
when trying to simplify properties of sets.
"

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--  Linear Combination**
A vector $x$ is called a **linear combination** of a set $S$ if it can be expressed as a finite sum of elements of $S$ scaled by scalars in the field. Here we formalize this concept. ∑ v in s, f v • v-/
def is_linear_combination (S : Set V) (x : V) : Prop :=
  ∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (x = Finset.sum s (fun v => f v • v))

/--
`is_linear_combination` is how we define a vector `x` to be a linear combination of some set `S ⊆ V`.
To say this, we write `is_linear_combination K V S x`. It is defined by the existance of some set `s ⊆ S`,
and a function `f : V → K`, such that `x` is the sum over `s` of `f(v) • v`.
-/
DefinitionDoc is_linear_combination as "is_linear_combination"

/--
`Finset.sum` is how we difine summing over a set. It uses Mathlib's `Finset` Type, which means that we
can only sum over arbitrary finite sets. The syntax is as follows: With a additive group or field `K`, some Type `T`,
some `s : Finset T`, and some `f : T → K`, `Finset.sum s (fun x => f x)` sums `f x` over all `x ∈ s`.
-/
DefinitionDoc Finset.sum as "Finset.sum"

NewDefinition is_linear_combination Finset.sum

/--
`linear_combination_of_mem` is a proof that if `v ∈ S` then `is_linear_combination K V S v`.
-/
TheoremDoc LinearAlgebraGame.linear_combination_of_mem as "linear_combination_of_mem" in "Vector Spaces"

/-- If `v ∈ S`, then `v` is a linear combination of `S`-/
Statement linear_combination_of_mem {S : Set V} {v : V} (hv : v ∈ S) : is_linear_combination K V S v := by
  Hint "It is generally helpful to unfold definitions you are unfamiliar with"
  Hint (hidden := true) "Try `unfold is_linear_combination`"
  unfold is_linear_combination
  Hint "Now, you have to specify what set you are summing over"
  Hint (hidden := true) "Try `use \{v}`"
  use {v}
  Hint "Now, you have to specify the function you are using to map vectors to the scalars they will be multiplied by"
  Hint (hidden := true) "Try `use (fun x => 1)`"
  use (fun _x => 1)
  Hint "This is an and statement, so you could use the `constructor` tactic and work from there. Instead, try `simp` and see what happens"
  Hint (hidden := true) "Try `simp`"
  simp
  Hint (hidden := true) "Try `exact hv`"
  exact hv

Conclusion "You have completed your first proof in Linear Independence and Span World!"
