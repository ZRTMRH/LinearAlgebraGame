import Game.Levels.InnerProductWorld.Level01

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 2

Title "Zero Norm if and only if Zero Vector"

Introduction "
## The Goal
In this level, we prove that the norm of a vector is zero if and only if it is the zero vector. The
idea of the proof is to use the `inner_self_eq_zero` axiom, which requires cancelling out the square
roots.

## The `apply_fun` tactic
The `apply_fun` tactic is used to apply functions to both sides of an equality. This only works in your
hypotheses, not in the goal. The syntax is `apply_fun (fun x => f x) at h`. If `h : a = b` is a proof,
then this will change `h` to `h : f a = f b`. This tactic can be very helpful, as squaring a square root
cancels out the operation.
"

/--
## Summary
`apply_fun` allows you to apply functions to both sides of an equality in the hypothesis. This can also
be done simply with a `have`, `rw`, and `rfl` statement, but it is nice to be able to do that in one line.

## Example
If you have `h : sqrt x = 0`, using `apply_fun (fun v => v ^ 2) at h` will change `h` to `h : (sqrt x) ^ 2 = 0 ^ 2`.
-/
TacticDoc apply_fun

/--
`sq_sqrt` is a proof that if `0 ≤ x`, then `(sqrt x) ^ 2 = x`. It allows you to cancel out square roots.
-/
TheoremDoc Real.sq_sqrt as "sq_sqrt" in "ℝ"

/--
`Complex.ext` allows you to split complex numbers into their real and imaginary parts. If your goal is
of the form `a = b`, where `(a b : ℂ)`, then `apply Complex.ext` will create two goals, one `a.re = b.re`,
and the other `a.im = b.im`.
-/
TheoremDoc Complex.ext as "Complex.ext" in "ℂ"

/--
`norm_zero_v` is a proof that `‖v‖ = 0 ↔ v = 0`, or that the only vector with norm zero is the zero vector.
-/
TheoremDoc LinearAlgebraGame.norm_zero_v as "norm_zero_v" in "Inner Product"

NewTactic apply_fun

NewTheorem Real.sq_sqrt Complex.ext

TheoremTab "ℂ"

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [DecidableEq V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex

Statement norm_zero_v (v: V): norm_v v = 0 ↔ v = 0 := by
  Hint "Try unfolding and using constructor to split the `↔`"
  Hint (hidden := true) "Try `unfold norm_v`"
  unfold norm_v
  Hint (hidden := true) "Try `constructor`"
  constructor
  Hint (hidden := true) "Try `intro h`"
  intro h

  Hint "Now, try to remove the square root"
  Hint (hidden := true) "Try `apply_fun (fun x => x^2) at {h}`"
  apply_fun (fun x => x^2) at h
  Hint (hidden := true) "Try `rw[sq_sqrt (inner_self_nonneg v)] at {h}`"
  rw[sq_sqrt (inner_self_nonneg v)] at h
  Hint (hidden := true) "Try `simp at h`"
  simp at h

  Hint "Now, try to use some of the theorems we know"
  Hint (hidden := true) "Try `apply (inner_self_eq_zero v).1`"
  apply (inner_self_eq_zero v).1
  Hint (hidden := true) "Try `apply Complex.ext`"
  apply Complex.ext
  Hint (hidden := true) "Try `exact {h}`"
  exact h
  Hint (hidden := true) "Try `exact inner_self_im_zero v`"
  exact inner_self_im_zero v

  Hint (hidden := true) "Try `intro h`"
  intro h
  Hint (hidden := true) "Try `rw [{h}]`"
  rw [h]
  Hint (hidden := true) "Try `rw [(inner_self_eq_zero 0).2]`"
  rw [(inner_self_eq_zero 0).2]
  Hint (hidden := true) "Try `simp`"
  simp
  Hint (hidden := true) "Try `rfl`"
  rfl

end LinearAlgebraGame
