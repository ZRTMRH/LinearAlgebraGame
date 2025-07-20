import Game.Levels.LinearMapsWorld.Level01

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 2

Title "Finding a Minimal Spanning Set"

Introduction "
## Finding a Minimal Spanning Set

Sometimes you start with a big spanning set that includes lots of redundant vectors.
Like cleaning out a closet, you want to keep only the essentials.
This level proves you can always extract a subset that is a basis.
"

open Submodule
variable (K V : Type) [Field K] [AddCommGroup V] [Module K V]

/--
Given a spanning set, you can extract a subset that is a basis.
This demonstrates that every vector space has a basis.
-/
TheoremDoc LinearAlgebraGame.exists_basis_sub_set as "exists_basis_sub_set" in "BasisWorld"
Statement exists_basis_sub_set (S : Set V) (hS : Submodule.span K S = ⊤) :
  ∃ (B : Set V), B ⊆ S ∧ LinearIndependent K (fun v : B => (v : V)) ∧ Submodule.span K B = ⊤ := by
  Hint "Use `exists_linearIndependent` to get a maximal independent subset."
  obtain ⟨B, hBsub, hBspan, hBlin⟩ := exists_linearIndependent K S
  Hint "Since `span B = span S` and `span S = ⊤`, get `span B = ⊤` by substitution."
  have hBspan_top : Submodule.span K B = ⊤ := by
    rw [hBspan, hS]
  Hint "Collect everything for the answer."
  exact ⟨B, hBsub, hBlin, hBspan_top⟩

Conclusion
"
Any spanning set contains a basis—you can always trim down to something just right!
"

end LinearAlgebraGame
