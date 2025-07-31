import Game.Levels.VectorSpaceWorld.Level05

namespace LinearAlgebraGame

World "VectorSpaceWorld"
Level 6

Title "Negatives in Subspace"

Introduction "
The last theorem we will prove in Vector Space World is that subspaces contain the additive inverses of each of their elements. 

## The Mathematical Idea

If x ∈ W and W is a subspace, then -x ∈ W. This follows because -x = (-1) • x, and subspaces are closed under scalar multiplication.

## Proof Strategy

1. Break down the subspace definition using obtain
2. Introduce the universal quantifier (∀) using intros
3. Rewrite -x as (-1) • x using the theorem from Level 3
4. Apply scalar multiplication closure

The proof combines ideas from the previous level with our theorem about -1 scaling.
"

/--
This is a proof that if a subspace contains a vector `x`, it also contains `-x`.
-/
TheoremDoc LinearAlgebraGame.subspace_neg as "subspace_neg" in "Vector Spaces"

DisabledTactic simp linarith

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

Statement subspace_neg {W : Set V} (hW : isSubspace (K := K) (V := V) W) : ∀ (x : V), x ∈ W → (-x) ∈ W := by
  Hint "First, break down the subspace definition to access the closure properties."
  Hint (hidden := true) "Try `obtain ⟨h1, h2, h3⟩ := hW`"
  obtain ⟨_h1, _h2, h3⟩ := hW
  Hint "Introduce the universal quantifier: we need to show this holds for any x and any proof that x ∈ W."
  Hint (hidden := true) "Try `intros x hx`"
  intros x hx
  Hint "Rewrite -x as (-1) • x using our theorem from Level 3. This connects negation to scalar multiplication."
  Hint (hidden := true) "Try `rw [(neg_one_smul_v K V x).symm]`"
  rw [(neg_one_smul_v K V x).symm]
  Hint "Apply the scalar multiplication closure property h3. Since x ∈ W, we have (-1) • x ∈ W."
  Hint (hidden := true) "Try `apply h3`"
  apply h3
  Hint "Provide the proof that x ∈ W, which is our hypothesis hx."
  Hint (hidden := true) "Try `exact hx`"
  exact hx

-- Add set theory theorems needed by LinearIndependenceSpanWorld
NewTheorem Set.union_subset Finset.subset_union_left Finset.subset_union_right

Conclusion "You have now completed Vector Space World! The theorems proven here will be very helpful
in future worlds. You can now move on to World 2: Linear Independence and Span World!"
