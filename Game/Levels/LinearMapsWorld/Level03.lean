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
If every vector in `V` is zero, then `dim K V = 0`.
-/
Statement dim_zero_space (hV : ∀ v : V, v = 0) : dim K V = 0 := by
  Hint "Unfold `dim` to see the definition."
  unfold dim
  Hint "Split into cases: does there exist a finite basis?"
  split_ifs with h
  · let B := Classical.choose h
    let hBasis := (Classical.choose_spec h).1
    by_cases Bempty : B = ∅
    · change Set.ncard B = 0
      rw [Bempty, Set.ncard_empty]
    · have B_nonempty : B.Nonempty := Set.nonempty_iff_ne_empty.mpr Bempty
      obtain ⟨b, hb⟩ := B_nonempty
      have lin := hBasis.1
      specialize lin {b} (fun _ => 1) (by simp [hb])
      have sum1 : Finset.sum {b} (fun v => 1 • v) = 1 • b := by simp
      rw [sum1, hV b, one_smul] at lin
      have h1 : 1 = 0 := lin rfl 0 (Finset.mem_singleton_self 0)
      exact False.elim (one_ne_zero h1)
  · rfl

Conclusion
"
The only possible basis for the zero space is the empty set, so its dimension is zero.
"
