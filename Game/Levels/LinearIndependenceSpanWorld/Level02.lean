import Game.Levels.LinearIndependenceSpanWorld.Level01

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 2

Title "Introducing Span"

Introduction "
In this level, we will introduce the span of a set of vectors. The span of a set of vectors is simply
all the vectors that can be written as a linear combination of that set. In Lean, we define it as such:

```
def span (S : Set V) : Set V :=
  { x : V | is_linear_combination K V S x }
```

### The Goal
The goal of this level is to prove that if a vector `v ∈ S`, then `v` is in the span of `S`. This feels
very similar to the previous level, so you can use the theorem proved in the previous level in this one.
"

/--
`mem_span_of_mem` is a proof that if a vector `v ∈ S`, then `v ∈ span K V S`
-/
TheoremDoc LinearAlgebraGame.mem_span_of_mem as "mem_span_of_mem" in "Vector Spaces"

/--
The span of a set of vectors `S`, denoted `span K V S` is the set of all vectors that are a linear
combination of `S`. It is represented in Lean as

``` { x : V | is_linear_combination K V S x } ```
-/
DefinitionDoc span as "span"

NewDefinition span

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

def span (S : Set V) : Set V :=
  { x : V | is_linear_combination K V S x }

/-- If `v ∈ S`, then `v ∈ span K V S`-/
Statement mem_span_of_mem {S : Set V} {v : V} (hv : v ∈ S) : v ∈ span K V S := by
  Hint "Once again, we have a definition we are unfamiliar with in the goal. Try to change it to terms
  we are familiar with"
  Hint (hidden := true) "Try `unfold span`"
  unfold span
  Hint "The `simp` tactic is very helpful when dealing with sets."
  Hint (hidden := true) "Try `simp`"
  simp
  Hint "This seems familiar"
  Hint (hidden := true) "Try 'exact linear_combination_of_mem K V hv`"
  exact linear_combination_of_mem K V hv

Conclusion "You could have actually solved this level with simply an `exact linear_combination_of_mem K V hv`.
This is because the way set-builder notation is defined in lean is that `x ∈ { x : V | is_linear_combination K V S x }`
is the same as saying `is_linear_combination K V S x`. The `simp` tactic only directly shows you this."
