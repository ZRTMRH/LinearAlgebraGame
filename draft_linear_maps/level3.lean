import Game.Levels.LinearMapsWorld.Level02
World "LinearMapsWorld"
Level 3

Title "The Space Where Everything is Zero"

/--
## Summary
If every vector in your space is zero, there is really \"no room\" for movement—this space has dimension zero.

## Key idea
- If all vectors are zero, the only possible basis is the empty set.
- Compute `dim K V` using its definition; show any other \"basis\" would contradict independence.

This shows the zero space is 0-dimensional!
-/

Introduction "
## The Space Where Everything is Zero

Imagine living in a space where every vector is zero.
No movement, no direction—just the origin.
In this level, you show that such a space must have dimension zero.

Your goal: show that any vector space where all elements are zero has dimension zero.
"

TheoremDoc dim_zero_space as "Zero-Dimensional Space" in "BasisWorld"

/--
to be filled in
-/

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- In a finite-dimensional ambient space `V`,
    any submodule `U` has `finrank U ≤ finrank V`. -/
theorem submodule_finrank_le_explicit_aux
    [FiniteDimensional K V] (U : Submodule K V) :
    Module.finrank K U ≤ Module.finrank K V := by
  -- `U.subtype` is the inclusion `U →ₗ[K] V`, and it is injective.
  have h_inj : Function.Injective (U.subtype : U →ₗ[K] V) :=
    U.subtype_injective


  simpa using
    (LinearMap.finrank_le_finrank_of_injective h_inj)


Conclusion
"
The only possible basis for the zero space is the empty set, so its dimension is zero.
"
