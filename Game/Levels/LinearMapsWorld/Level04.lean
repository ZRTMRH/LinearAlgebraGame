import Game.Levels.LinearMapsWorld.Level03

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 4

Title "Dimension of a Subspace ≤ Dimension of the Ambient Space"

Introduction "
Now that we have the notion of `Module.finrank` (the dimension of a finite-dimensional space), let's prove a fundamental fact: any subspace has dimension at most that of the whole space. If `V` is a finite-dimensional vector space and `U` is a submodule of `V` (think: a subspace of `V`), it is intuitively clear that `dim U ≤ dim V`.

**Intuition:** Take a basis of the subspace `U` and extend it to a basis of the entire space `V`. The extended basis of `V` has at least as many vectors as the basis of `U`, so the number of basis vectors of `U` (the dimension of `U`) cannot exceed the number of basis vectors of `V` (the dimension of `V`).

**Plan in Lean:** We can capture the above intuition using a linear map. The inclusion map from `U` into `V` (denoted `U.subtype`) is a linear map that is injective (no new collisions when we view elements of `U` inside `V`). Lean provides a lemma `LinearMap.finrank_le_finrank_of_injective` which says that if we have an injective linear map between two finite-dimensional spaces, then the dimension of the domain is ≤ the dimension of the codomain. So our goal is to apply this lemma to `U.subtype`. We'll proceed by:
1. Noting that `U.subtype` is indeed injective (which we can justify with `U.subtype_injective`).
2. Applying `LinearMap.finrank_le_finrank_of_injective` to get the inequality on finranks.

Armed with these ideas, let's carry out the proof!
"

TheoremDoc LinearAlgebraGame.submodule_finrank_le_explicit_aux as "Subspace Dimension ≤ Space Dimension" in "Bases"

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/--
This theorem states that in a finite-dimensional ambient space `V`, any submodule `U` of `V` has `finrank K U ≤ finrank K V`. In other words, a subspace cannot have a higher dimension than the whole space.

**Proof hint:** Consider the inclusion map `U.subtype : U →ₗ[K] V`. This linear map is injective (use `U.subtype_injective` to prove that formally). Once you know it's injective, apply the lemma `LinearMap.finrank_le_finrank_of_injective` to conclude the proof.
-/
Statement submodule_finrank_le_explicit_aux
    [FiniteDimensional K V] (U : Submodule K V) :
    FiniteDimensional.finrank K U ≤ FiniteDimensional.finrank K V := by
  apply LinearMap.finrank_le_finrank_of_injective
  exact Submodule.injective_subtype U

Conclusion "
**Subspace dimension cannot exceed ambient dimension.** We used the injectivity of the inclusion map `U.subtype` to apply a general result about linear maps, yielding `finrank K U ≤ finrank K V`. This formal proof mirrors the intuitive idea that you can extend a basis of `U` to a basis of `V`, so you can never have more basis vectors in `U` than in `V`.

Congratulations on formalizing this classic linear algebra result! By connecting an injective linear map with the concept of basis extension, we've solidified the fact that any subspace's dimension is at most the dimension of the entire space.
"

end LinearAlgebraGame