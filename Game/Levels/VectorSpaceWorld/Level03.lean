import Game.Levels.VectorSpaceWorld.Level02

namespace LinearAlgebraGame

World "VectorSpaceWorld"
Level 3

Title "Multiplying by the zero vector"

Introduction "We just proved that multiplying by the zero scalar gives the zero vector. Now, we will show that multiplying by the zero vector also gives the zero vector.

## The Mathematical Idea

This proof mirrors the previous level but uses the other distributivity property (smul_add instead of add_smul).

## Proof Strategy

The forward proof would be: a • 0 = a • (0 + 0) = a • 0 + a • 0, then cancel a • 0 from both sides.
The backward proof: add a • 0 to both sides, then use distributivity in reverse, then simplify.

## Tactics Needed

The proof is very similar to the last level, and requires no new tactics. You can look at the previous level for inspiration and syntax help."

/--
This is a proof that `a • 0 = 0`, or that scaling the zero vector by any scalar gives the zero vector.

It is called "smul_zero_v", since you perform scalar multiplication by the zero vector. The "v" means that it is
scalar multiplication of a vector.
-/
TheoremDoc LinearAlgebraGame.smul_zero_v as "smul_zero_v" in "Vector Spaces"

DisabledTactic simp linarith

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--
In any vector space V over K, any scalar a multiplied by the zero vector gives the zero vector.
-/
Statement smul_zero_v (a : K) : a • (0 : V) = (0 : V) := by
  Hint "Start by adding a • 0 to both sides using add_right_cancel, just like in the previous level."
  Hint (hidden := true) "Try `apply add_right_cancel (b := a • (0 : V))`"
  apply add_right_cancel (b := a • (0 : V))
  Hint "Use smul_add in reverse to write a • (0 + 0) as a • 0 + a • 0. This is the distributivity of scalar multiplication over vector addition."
  Hint (hidden := true) "Try `rw[(smul_add a (0 : V) (0 : V)).symm]`"
  rw[(smul_add a (0 : V) (0 : V)).symm]
  Hint "Simplify 0 + 0 = 0 in the argument to the scalar multiplication."
  Hint (hidden := true) "Try `rw[zero_add]`"
  rw[zero_add]
  Hint "Finally, simplify the right side: 0 + a • 0 = a • 0."
  Hint (hidden := true) "Try `rw[zero_add]`"
  rw[zero_add]
