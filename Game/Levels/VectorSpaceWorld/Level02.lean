import Game.Levels.VectorSpaceWorld.Level01

namespace LinearAlgebraGame

World "VectorSpaceWorld"
Level 2

Title "Multiplying by the zero vector"

Introduction "We just proved that multiplying by the zero scalar gives the zero vector. Now, we will
show that multiplying by the zero vector also gives the zero vector.

The proof is very similar to the last level, and requires no new tactics.

Again, first think out the proof yourself (pencil and paper may help), then reverse the proof and
write it in lean. You can also look at the previous level for inspiration and syntax help."

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
  Hint (hidden := true) "Try `apply add_right_cancel (b := a • (0 : V))`"
  apply add_right_cancel (b := a • (0 : V))
  Hint (hidden := true) "Try `rw[(smul_add a (0 : V) (0 : V)).symm]`"
  rw[(smul_add a (0 : V) (0 : V)).symm]
  Hint (hidden := true) "Try `rw[zero_add]`"
  rw[zero_add]
  Hint (hidden := true) "Try `rw[zero_add]`"
  rw[zero_add]
