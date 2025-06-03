import Game.Levels.VectorSpaceWorld.Level04

World "VectorSpaceWorld"
Level 5

Title "Negatives in Subspace"

Introduction "
The last theorem we will prove in Vector Space World is that subspaces contain the additive inverses
of each of their elements. The proof is very similar to the previous level. You can try to solve it
completely on your own, and if you get stuck, you can always press the \"Show more help!\" button to
get the next step.
"

/--
This is a proof that if a subspace contains a vector `x`, it also contains `-x`.
-/
TheoremDoc subspace_neg as "subspace_neg" in "Vector Spaces"

Statement subspace_neg (fk : Field K) (acg : AddCommGroup V) (vs : VectorSpace K V) {W : Set V} (hW : isSubspace (K := K) (V := V) W) : ∀ (x : V), x ∈ W → (-x) ∈ W := by
  Hint (hidden := true) "Try `obtain ⟨h1, h2, h3⟩ := hW`"
  Branch
    intros _x _hx
    Hint (hidden := true) "Try `obtain ⟨h1, h2, h3⟩ := hW`"
  obtain ⟨_h1, _h2, h3⟩ := hW
  Hint (hidden := true) "Try `intros x hx`"
  intros x hx
  Hint (hidden := true) "Try `rw [(neg_one_smul_v fk acg vs {x}).symm]`"
  rw [(neg_one_smul_v fk acg vs x).symm]
  Hint (hidden := true) "Try `apply {h3}`"
  apply h3
  Hint (hidden := true) "Try `exact {hx}`"
  exact hx

Conclusion "You have now completed Vector Space World! The theorems proven here will be very helpful
in future worlds. You can now move on to World 2: Linear Independence and Span World!"
