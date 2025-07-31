import Game.Levels.LinearIndependenceSpanWorld.Level04

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 5

Title "Linear Independence"

Introduction "
This level will introduce linear independence of a set of vectors. A set `S` of vectors is linearly
independent if no vector in `S` can be written as a linear combination of the others. Equivalently,
we can say that `S` is linearly independent if any combination of vectors in `S` summing to `0` must
be all `0`s. In Lean, it is written as:

```
def linear_independent_v (S : Set V) : Prop :=
∀ (s : Finset V) (f : V → K),
(↑s ⊆ S) → (Finset.sum s (fun v ↦ f v • v) = 0) → (∀ v ∈ s, f v = 0)
```

Note that we use the same idea as in linear combinations, where we have a Finset `s`, a function
mapping vectors to the scalars that multiply those vectors, and use `Finset.sum`.

### The Goal
The goal of this level is to prove that the empty set is linearly independent. This makes sense,
because there are no vectors in the empty set that can be scaled be a non-zero factor.
"

/--
This is a proof that the empty set is linearly independent.
-/
TheoremDoc LinearAlgebraGame.linear_independent_empty as "linear_independent_empty" in "Vector Spaces"

/--
`linear_independent_v` means that a set of vectors is linearly independent. To say a set `S : Set V`
is linearly independent, we write `linear_independent_v K V S`. This is defined that any finite set of scalar
multiples of vectors in `S` that sum to `0` must all be `0`. It is written in Lean as

```
def linear_independent_v (S : Set V) : Prop :=
∀ (s : Finset V) (f : V → K),
(↑s ⊆ S) → (Finset.sum s (fun v ↦ f v • v) = 0) → (∀ v ∈ s, f v = 0)
```

Note that we use `Finset` here, which means that even though `S` can be infinite, `s` must be finite.
-/
DefinitionDoc linear_independent_v as "linear_independent_v"

NewDefinition linear_independent_v

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/-- A set of vectors $S$ is **linearly independent** if no vector in $S$ can be written as a linear combination of the others. Equivalently, the only solution to a linear combination of elements of $S$ equaling zero is the trivial solution (all coefficients zero). Here we formalize this condition. -/
def linear_independent_v (S : Set V) : Prop :=
∀ (s : Finset V) (f : V → K),
(↑s ⊆ S) → (Finset.sum s (fun v ↦ f v • v) = 0) → (∀ v ∈ s, f v = 0)

/-- The empty set is linearly independent. -/
Statement linear_independent_empty : linear_independent_v K V (∅ : Set V) := by
  Hint (hidden := true) "Try `unfold linear_independent_v`"
  unfold linear_independent_v
  Hint "Here, we have many ∀ and → statements in the goal. Try to move these variables to the hypotheses"
  Hint (hidden := true) "Try `intros s f hs sum_zero v hv`"
  intros _s f hs _sum_zero v hv
  Hint "We now have a hypothesis `{hv}: v ∈ {_s}` and `{hs} : `↑{_s} ⊆ ∅`. This may be a contradiction,
  so maybe we can chang eour goal to `False` and prove that"
  Hint (hidden := true) "Try `exfalso`"
  exfalso
  Hint "If you can figure out a way to get a proof of the form `{v} ∈ ∅`, that statement is equivalent
  to `False`, so an `exact` statement could work. (Actually, `exact?` should solve the goal)"
  Hint (hidden := true) "Try `exact hs hv`"
  exact hs hv

Conclusion "We won't prove it in this game (although it isn't too difficult), but any set containing
a single vector is also linearly independent."
