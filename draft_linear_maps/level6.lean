import Game.Levels.LinearMapsWorld.Level05
World "LinearMapsWorld"

Level 6

Title "Direct Sum Decomposition"

/--
## Summary
Every subspace `U` of a finite-dimensional vector space `V` has a complement: there exists a subspace `W` so that `V = U ⊕ W`.  
The dimensions also add: `dim V = dim U + dim W`.

## Key idea
- Pick a basis for `U` and extend it to a basis for `V` by adding new vectors.
- The span of the new vectors gives a subspace `W` such that `V = U ⊕ W`.

This level guides you to show every subspace has a direct sum complement, and the dimension formula.
-/

Introduction "
## Direct Sum Decomposition

If you have a subspace `U` of a finite-dimensional vector space `V`,  
can you always find another subspace `W` such that every vector in `V` can be uniquely written as a sum of something in `U` and something in `W`?  
Yes! Such a decomposition is called a **direct sum**.

You will prove: for any subspace `U`, there is a subspace `W` with `V = U ⊕ W`,  
and the dimensions add: `dim V = dim U + dim W`.
"

open Submodule FiniteDimensional

TheoremDoc exists_direct_sum_complement as "Direct Sum Decomposition" in "BasisWorld"

/--
Given a subspace `U`, there is a subspace `W` such that `V = U ⊕ W` and the dimension formula holds.
-/
Statement exists_direct_sum_complement :
    ∃ (W : Submodule K V), (U ⊔ W = ⊤) ∧ (U ⊓ W = ⊥) ∧
      finrank K V = finrank K U + finrank K W := by
  Hint "Use `Submodule.exists_isCompl` to get a direct sum complement."
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  Hint "Recall: direct sum means `U ⊔ W = ⊤` and `U ⊓ W = ⊥`."
  have dirsum : U ⊔ W = ⊤ ∧ U ⊓ W = ⊥ := ⟨hW.sup_eq_top, hW.inf_eq_bot⟩
  Hint "The dimension formula is: finrank V = finrank U + finrank W."
  have dim : finrank K V = finrank K U + finrank K W := by
    have h := finrank_sup_add_finrank_inf_eq U W
    rw [dirsum.1, dirsum.2, finrank_top, finrank_bot, add_zero] at h
    exact h
  exact ⟨W, dirsum.1, dirsum.2, dim⟩

Conclusion
"
Every subspace has a direct sum complement, and dimensions always add: `dim V = dim U + dim W`!
"
