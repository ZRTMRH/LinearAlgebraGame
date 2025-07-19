import Game.Levels.LinearMapsWorld.Level04

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 5

Title "Subspace Equality from Equal Dimension"

Introduction "
## Equal Dimension Means Equal Space

Suppose you have a subspace `U` of a finite-dimensional vector space `V`.
If `U` has the same dimension as `V`, can it be smaller?
No—if `U` filled up the whole space dimensionally, it *is* the whole space!

This level asks you to prove: If `U` is a subspace and `dim U = dim V`, then `U = V`.

## Summary
If a subspace `U` has the same dimension as the whole space `V` (and `V` is finite-dimensional), then `U` must be all of `V`. In other words: if you already fill the whole space, you can't be a proper part!

## Key idea
- Use the contrapositive: if `U ≠ V`, then `dim U < dim V`.
- This follows because any *proper* subspace has strictly smaller dimension.

This is an important structural result for finite-dimensional vector spaces.
"

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (U : Submodule K V)

TheoremDoc LinearAlgebraGame.subspace_eq_of_dim_eq as "Subspace = Space from Equal Dimension" in "Bases"

/--
If `U` is a subspace of `V` and their dimensions agree, then `U = V`.
-/
Statement subspace_eq_of_dim_eq (h : FiniteDimensional.finrank K U = FiniteDimensional.finrank K V) : U = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  exact h

Conclusion "
If a subspace has the same dimension as the whole space, it must actually *be* the whole space!
"

end LinearAlgebraGame