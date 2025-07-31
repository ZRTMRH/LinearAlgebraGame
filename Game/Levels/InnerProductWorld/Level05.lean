import Game.Levels.InnerProductWorld.Level04

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 5

Title "Pythagorean Theorem"

Introduction "
## The Goal
This level has you prove the Pythagorean Theorem. In an abstract vector space, this theorem is a proof
that given any two orthogonal vectors, `u, v`, then `‖u + v‖^2 = ‖u‖^2 + ‖v‖^2`. The idea behind the
proof is quite simple. Since all the norms are squared, we can remove the square roots, and then simplify
using the axioms of inner products.
"

/--
This is the Pythagorean Theorem. If you have vectors `u v`, and `h : orthogonal u v`, then
`pythagorean u v h` is a proof that `‖u + v‖^2 = ‖u‖^2 + ‖v‖^2`.
-/
TheoremDoc LinearAlgebraGame.pythagorean as "pythagorean" in "Inner Product"


variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

Statement pythagorean (u v : V) (h : orthogonal u v) : ‖u + v‖^2 = ‖u‖^2 + ‖v‖^2 := by
  Hint "First, try to remove the squares."
  Hint (hidden := true) "Try `repeat rw[norm_sq_eq]`"
  repeat rw[norm_sq_eq]

  Hint "Now, try to expand `⟪u + v, u + v⟫` with our additivity properties."
  Hint (hidden := true) "Try `rw[inner_add_left u v (u + v)]`"
  rw[inner_add_left u v (u + v)]
  Hint (hidden := true) "Try `rw [inner_add_right_v u u v]`"
  rw [inner_add_right_v u u v]
  Hint (hidden := true) "Try `rw [inner_add_right_v v u v]`"
  rw [inner_add_right_v v u v]

  Hint "Keep simplifying!"
  Hint (hidden := true) "Try `rw[inner_conj_symm v u]`"
  rw[inner_conj_symm v u]
  Hint (hidden := true) "Try `unfold orthogonal at h`"
  unfold orthogonal at h
  Hint (hidden := true) "Try `rw[h]`"
  rw[h]
  Hint (hidden := true) "Try `simp`"
  simp

end LinearAlgebraGame
