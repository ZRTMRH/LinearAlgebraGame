import Game.Levels.InnerProductWorld

namespace LinearAlgebraGame

World "DummyTestWorld"
Level 1

Title "Test Level Using Pythagorean Theorem"

Introduction "
This test level uses the Pythagorean theorem from InnerProductWorld to create a dependency.
We'll use the pythagorean theorem to test if this makes InnerProductWorld's display break.
"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

/-- A simple test using the Pythagorean theorem from InnerProductWorld -/
Statement test_pythagorean_simple (u v : V) (h : orthogonal u v) : ‖u + v‖^2 = ‖u‖^2 + ‖v‖^2 := by
  Hint "This is just the Pythagorean theorem from InnerProductWorld."
  exact pythagorean u v h

Conclusion "Great! This test confirms we're using the Pythagorean theorem from InnerProductWorld."

end LinearAlgebraGame