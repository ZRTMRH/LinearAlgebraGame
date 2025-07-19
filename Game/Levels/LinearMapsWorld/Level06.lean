import Game.Levels.LinearMapsWorld.Level05

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 6

Title "Direct Sum Decomposition"

Introduction "
## Direct Sum Decomposition

If you have a subspace `U` of a finite-dimensional vector space `V`,
can you always find another subspace `W` such that every vector in `V` can be uniquely written as a sum of something in `U` and something in `W`?
Yes! Such a decomposition is called a **direct sum**.

You will prove: for any subspace `U`, there is a subspace `W` with `V = U ⊕ W`,
and the dimensions add: `dim V = dim U + dim W`.

## Summary
Every subspace `U` of a finite-dimensional vector space `V` has a complement: there exists a subspace `W` so that `V = U ⊕ W`.
The dimensions also add: `dim V = dim U + dim W`.

## Key idea
- Pick a basis for `U` and extend it to a basis for `V` by adding new vectors.
- The span of the new vectors gives a subspace `W` such that `V = U ⊕ W`.

This level guides you to show every subspace has a direct sum complement, and the dimension formula.
"

open Submodule FiniteDimensional

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (U : Submodule K V)

TheoremDoc LinearAlgebraGame.exists_direct_sum_complement as "Direct Sum Decomposition" in "Bases"

/--
Given a subspace `U`, there is a subspace `W` such that `V = U ⊕ W` and the dimension formula holds.
-/
Statement exists_direct_sum_complement :
    ∃ (W : Submodule K V), (U ⊔ W = ⊤) ∧ (U ⊓ W = ⊥) ∧
      finrank K V = finrank K U + finrank K W := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  use W
  constructor
  · exact hW.sup_eq_top
  constructor  
  · exact hW.inf_eq_bot
  · rw [← Submodule.finrank_sup_add_finrank_inf_eq U W, hW.sup_eq_top, hW.inf_eq_bot]
    simp

Conclusion "
Every subspace has a direct sum complement, and dimensions always add: `dim V = dim U + dim W`!
"

end LinearAlgebraGame