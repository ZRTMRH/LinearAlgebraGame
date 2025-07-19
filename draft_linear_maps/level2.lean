import Game.Levels.LinearMapsWorld.Level01
World "LinearMapsWorld"
Level 2

Title "Finding a Minimal Spanning Set"

/--
## Summary
Sometimes your spanning set is too big and messy. Can you always extract a basis? Yes!
This is called \"Basis Extraction.\"  
We'll use the existence of a maximal linearly independent subset.

## Key idea
- Start with a spanning set S.
- Use Lean's `exists_linearIndependent` to grab a maximal linearly independent subset `B`.
- Show that `B` is still spanning, since `span B = span S` and `S` was spanning.

The result: every spanning set contains a basis!
-/

Introduction "
## Finding a Minimal Spanning Set

Sometimes you start with a big spanning set that includes lots of redundant vectors.  
Like cleaning out a closet, you want to keep only the essentials.  
This level proves you can always extract a subset that is a basis.
"

TheoremDoc exists_basis_sub_set as "Extracting a Basis" in "BasisWorld"

/--
Given a spanning set, you can extract a subset that is a basis.
-/
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
