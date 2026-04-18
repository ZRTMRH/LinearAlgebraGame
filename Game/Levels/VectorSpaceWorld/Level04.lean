import Game.Levels.VectorSpaceWorld.Level03

namespace LinearAlgebraGame

World "VectorSpaceWorld"
Level 4

Title "Zero must belong"

Introduction "Now that we understand more about vector spaces, let's define what a subspace is.
Intuitively, a subspace is a subset of a vector space that can be considered as a vector space itself.
We define this as a subset `W : Set V` that is nonempty, is closed under addition, and is closed under scalar multiplication.

### The `obtain` tactic
A new tactic will help us solve problems with subspaces. While not necessary, and this tactic can
even be completely replaced by the `cases'` tactic, it will simplify your proofs greatly. The `obtain`
tactic essentially acts as repeating `cases'`. In this level, it has two main uses. First, if `hw : isSubspace W`
is a hypothesis, then `obtain ⟨h1, h2, h3⟩ := hW` will split the definition into the three parts,
labeled h1, h2, and h3. The other important use for `obtain` is if you have a hypothesis `hW : W.Nonempty`,
then `obtain ⟨w, hw⟩ := hW` will give you a `w : V`, and a hypothesis `hw : w ∈ W`. The \"⟨\"
character is written with \"\\langle\", and the \"⟩\" character is written with \"\\rangle\".

### Subspace contains zero
One of the basic properties of a subspace is that it must be nonempty. In fact, every subspace must
contain the zero vector. This is because for any vector in a subspace, you can multiply it by the zero
scalar while still remaining in the subspace, which wil result in the zero vector. In this level, we
formally prove this result.

**Note:** If you see hints appearing multiple times, this is a known issue with the game framework. Simply continue with your proof - the level will work correctly despite any duplicate hints.
"

def isSubspace {K V : Type} [Field K] [AddCommGroup V] [VectorSpace K V] (W : Set V) : Prop :=
  W.Nonempty ∧ (∀ (x y : V), x ∈ W → y ∈ W → x + y ∈ W) ∧ (∀ (a : K) (x : V), x ∈ W → a • x ∈ W)

/--
A subspace is a subset of a vector space that acts similarly to a vector space itself. It has three
main properties:
- Nonempty: a subspace cannot be empty
- Closure under addition: adding any two elements of a subspace should remain in that subspace
- Closure under scalar multiplication: scaling any vector in a subspace should remanin in that subspace

Subspaces are formalized by having the `isSubspace` proposition, which simply combines the three
properties into one proposition.
-/
DefinitionDoc isSubspace as "isSubspace"

NewDefinition isSubspace

/--
## Summary
The `obtain` tactic works very similar to repeating the `cases'` tactic. The `obtain` tactic splits a
statement into cases, and allows you to name each case. Instead of splitting into two cases, like the
`cases'` tactic, `obtain` can split into as many cases as necessary. The syntax looks like
`obtain ⟨h1, h2, h3⟩ := h`.

## Example
If `hw : isSubspace W` is a hypothesis, then `obtain ⟨h1, h2, h3⟩ := hW` will split the definition
into three parts, labeled h1, h2, and h3.

## Example
If you have a hypothesis `hW : W.Nonempty`, where `W : Set V` is a subset of `V`, then
`obtain ⟨w, hw⟩ := hW` will give you a `w : V`, and a hypothesis `hw : w ∈ W`
-/
TacticDoc obtain

NewTactic obtain

/--
This is a proof that any subspace contains the zero vector.
-/
TheoremDoc LinearAlgebraGame.subspace_contains_zero as "subspace_contains_zero" in "Vector Spaces"

DisabledTactic simp linarith

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]

/--
This is a proof that any subspace contains the zero vector.
-/
Statement subspace_contains_zero {W : Set V} (hW : isSubspace (K := K) (V := V) W) : (0 : V) ∈ W := by
  Hint "Start by expanding the subspace definition using obtain. This will give you the three properties: nonempty, closed under addition, and closed under scalar multiplication."
  Hint (hidden := true) "Try `obtain ⟨h1, h2, h3⟩ := hW`"
  obtain ⟨h1, _h2, h3⟩ := hW
  Hint "The nonempty property {h1} means there exists some element in W. Use obtain to extract this element."
  Hint (hidden := true) "Try `obtain ⟨w, hw⟩ := h1`"
  obtain ⟨w, hw⟩ := h1
  Hint "We want to show 0 ∈ W, but we know that 0 = 0 • w (from Level 1). Rewrite the goal using this fact."
  Hint (hidden := true) "Try `rw [(zero_smul_v K V w).symm]`"
  rw [(zero_smul_v K V w).symm]
  Hint "Now apply the scalar multiplication closure property h3. Since w ∈ W and subspaces are closed under scalar multiplication, 0 • w ∈ W."
  Hint (hidden := true) "Try `apply {h3}`"
  apply h3
  Hint "Finally, provide the proof that w ∈ W, which we have from our obtain step."
  Hint (hidden := true) "Try `exact hw`"
  exact hw
