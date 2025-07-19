import Game.Levels.LinearMapsWorld.Level04
World "LinearMapsWorld"
Level 5

Title "Subspace Equality from Equal Dimension"

/--
## Summary
If a subspace `U` has the same dimension as the whole space `V` (and `V` is finite-dimensional), then `U` must be all of `V`. In other words: if you already fill the whole space, you can't be a proper part!

## Key idea
- Use the contrapositive: if `U ≠ V`, then `dim U < dim V`.
- This follows because any *proper* subspace has strictly smaller dimension.

This is an important structural result for finite-dimensional vector spaces.
-/

Introduction "
## Equal Dimension Means Equal Space

Suppose you have a subspace `U` of a finite-dimensional vector space `V`.  
If `U` has the same dimension as `V`, can it be smaller?  
No—if `U` filled up the whole space dimensionally, it *is* the whole space!

This level asks you to prove: If `U` is a subspace and `dim U = dim V`, then `U = V`.
"

axiom finrank_top_eq : FiniteDimensional.finrank K (⊤ : Submodule K V) = FiniteDimensional.finrank K V
axiom finrank_lt_finrank_of_lt : ∀ (U W : Submodule K V), U < W → FiniteDimensional.finrank K U < FiniteDimensional.finrank K W

TheoremDoc subspace_eq_of_dim_eq as "Subspace = Space from Equal Dimension" in "BasisWorld"

/--
If `U` is a subspace of `V` and their dimensions agree, then `U = V`.
-/
Statement subspace_eq_of_dim_eq (h : FiniteDimensional.finrank K U = FiniteDimensional.finrank K V) : U = ⊤ := by
  Hint "Take the contrapositive: if `U ≠ ⊤`, then `U < ⊤`."
  by_contra hU
  Hint "Apply the theorem that a proper subspace has smaller dimension."
  have hlt : U < ⊤ := lt_top_iff_ne_top.mpr hU
  have hlt_dim : FiniteDimensional.finrank K U < FiniteDimensional.finrank K (⊤ : Submodule K V) := finrank_lt_finrank_of_lt U ⊤ hlt
  Hint "Now use the definition of dimension for the top subspace."
  rw [finrank_top_eq] at hlt_dim
  rw [h] at hlt_dim
  Hint "Conclude with a contradiction: n < n is impossible."
  exact Nat.lt_irrefl (FiniteDimensional.finrank K V) hlt_dim

Conclusion
"
If a subspace has the same dimension as the whole space, it must actually *be* the whole space!
"
