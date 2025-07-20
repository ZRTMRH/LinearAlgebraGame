import Game.Levels.InnerProductWorld.Level03

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 4

Title "Orthogonality With Self"

Introduction "
We now introduce orthogonality. Two vectors being orthogonal is equivalent to having their inner product
be 0. In Lean, we write this as

```
def orthogonal (u v : V) : Prop := ⟪u, v⟫ = (0 : ℂ)
```

## The Goal
In this level, we show that the only vector that is orthogonal to itself is the zero vector.
This proof is very similar to our axiom `inner_self_eq_zero`
"

/--
`orthogonal` is how we say vectors are orthogonal. The syntax is `orthogonal v w`. This means that the
inner product of `v` and `w` is `0`. In Lean, we define it by saying

```
def orthogonal (u v : V) : Prop := ⟪u, v⟫ = (0 : ℂ)
```
-/
 DefinitionDoc orthogonal as "orthogonal"

NewDefinition orthogonal

/--
`ortho_self_zero` is a proof that the only vector orthogonal to itself is the zero vector. If `v` is
a vector, `ortho_self_zero v` is a proof that `ortho v v ↔ v = 0`.
-/
TheoremDoc LinearAlgebraGame.ortho_self_zero as "ortho_self_zero" in "Inner Product"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

Statement ortho_self_zero (v : V): orthogonal v v ↔ v = (0:V):= by
  Hint "Try unfolding orthogonal"
  Hint (hidden := true) "Try `unfold orthogonal`"
  unfold orthogonal
  Hint (hidden := true) "Try `exact inner_self_eq_zero v`"
  exact inner_self_eq_zero v

end LinearAlgebraGame