import Game.Levels.InnerProductWorld.Level02

namespace LinearAlgebraGame

World "InnerProductWorld"
Level 3

Title "Norm of a Scaled Vector"

Introduction "
## The Goal
In this level, we show that you can take scalar multiples out from the norm of a vector, as long as
you multiply by the complex norm of the scalar. The proof here takes multiple steps. The first idea
is to square each side, getting rid of the square roots. Then, you can use multiple theorems to rewrite
the goal to be solved by an exact statement.

**Note:** This level may experience a hint display issue where hints repeat. If you see the same hint multiple times, the level is still working correctly - just continue with your proof as normal.

## The `ring` tactic
`ring` again acts very similar to `linarith`, but it works for equations using rings. Rings are basically
objects where you can multiply and divide, for example, the complex numbers.

## The `←` character
The `←` character acts similarly to `.symm`, but you often do not need to specify the exact details
of what you are rewriting, as you need to do with `.symm` The syntax looks like `← thm` instead of `thm.symm`

## Note on `InnerProductSpace_v`
Some of the axioms and theorems you have share names with other theorems. If you run into a bug saying
\"Ambiguous, possible interpretations\", try specifying the exact name of your theorem by putting `InnerProductSpace_v.`
in front of the theorem name (e.g., `InnerProductSpace_v.inner_smul_left`).
"

/--
## Summary
`ring` acts very similar to `simp` and `linarith` in that it will attempt to solve the goal for you.
`ring` works best with rings, which are objects where you can add and multiply. The most common rings
you will see are the real and complex numbers.

## Example
If you have a goal `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^2`, `ring` will solve the goal.
-/
TacticDoc ring

/--
`norm_nonneg` is very similar to the vector space theorem `norm_nonneg_v`. The theorem shows that any
complex number has nonnegative norm.
-/
TheoremDoc norm_nonneg as "norm_nonneg" in "ℂ"

/--
`Left.mul_nonneg` is a proof that multiplying two nonnegative numbers will give a nonnegative value.
If you have hypotheses `h1 : 0 ≤ a`, `h2 : 0 ≤ b`, then `Left.mul_nonneg h1 h2` is a proof that `0 ≤ a * b`.
-/
TheoremDoc Left.mul_nonneg as "Left.mul_nonneg" in "ℂ"

/--
`sq_eq_sq` is a proof that if `a` and `b` are nonnegative, `a^2 = b^2` if and only if `a = b`. If you
have hypotheses `h1 : 0 ≤ a`, `h2 : 0 ≤ b`, then `sq_eq_sq h1 h2` is a proof that `a ^ 2 = b ^ 2 ↔ a = b`.
-/
TheoremDoc sq_eq_sq as "sq_eq_sq" in "ℝ"

/--
`mul_assoc` is a proof that multiplication is associative. That is, that if you have `a, b, c`, then
`a * (b * c) = (a * b) * c`.
-/
TheoremDoc mul_assoc as "mul_assoc" in "Groups"

/--
`mul_conj` is a proof that `z * conj z = ↑(normSq z)`
-/
TheoremDoc Complex.mul_conj as "mul_conj" in "ℂ"

/--
`normSq_eq_norm_sq` is a proof that `normSq z = ‖z‖ ^ 2`. It essentially unfolds the `normSq` definition.
-/
TheoremDoc Complex.normSq_eq_norm_sq as "normSq_eq_norm_sq" in "ℂ"

/--
`re_ofReal_mul` is a proof that `(↑r * z).re = r * z.re`. It is helpful when working with both real and
complex numbers at the same time.
-/
TheoremDoc Complex.re_ofReal_mul as "re_ofReal_mul" in "ℂ"

/--
The norm of a scalar multiple: `‖a • v‖= ‖a‖ * ‖v‖`.
This fundamental property shows how norms interact with scalar multiplication.
-/
TheoremDoc LinearAlgebraGame.sca_mul as "sca_mul" in "Inner Product"

/--
The square of the norm equals the real part of the inner product with itself:
`‖v‖ ^ 2 = ⟪v, v⟫.re`. This connects the geometric notion of length with the algebraic inner product.
-/
TheoremDoc LinearAlgebraGame.norm_sq_eq as "norm_sq_eq" in "Inner Product"

NewTactic ring

LemmaDoc Complex.add_re as "Complex.add_re" in "Complex Numbers"
LemmaDoc Complex.conj_re as "Complex.conj_re" in "Complex Numbers"
LemmaDoc add_nonneg as "add_nonneg" in "Real Numbers"
LemmaDoc le_trans as "le_trans" in "Inequalities"
LemmaDoc mul_nonneg as "mul_nonneg" in "Real Numbers"
LemmaDoc add_sq as "add_sq" in "Algebra"
LemmaDoc Real.sqrt_pos as "Real.sqrt_pos" in "Real Numbers"

NewTheorem norm_nonneg Left.mul_nonneg sq_eq_sq mul_assoc Complex.mul_conj Complex.normSq_eq_norm_sq Complex.re_ofReal_mul Complex.add_re Complex.conj_re add_nonneg le_trans mul_nonneg add_sq Real.sqrt_pos

variable {V : Type} [AddCommGroup V] [VectorSpace ℂ V] [InnerProductSpace_v V]
open Function Set VectorSpace Real InnerProductSpace_v Complex


Statement sca_mul (a : ℂ) (v: V) : ‖a • v‖= ‖a‖ * ‖v‖ := by
  Hint "First, establish non-negativity of the norms to use the square equality theorem."
  Hint (hidden := true) "Try `have h1 := norm_nonneg a`"
  have h1 := norm_nonneg a
  Hint (hidden := true) "Try `have h2 := norm_nonneg_v v`"
  have h2 := norm_nonneg_v v
  
  Hint "Combine these to get non-negativity of the product."
  Hint (hidden := true) "Try `have g1 := Left.mul_nonneg h1 h2`"
  have g1 := Left.mul_nonneg h1 h2
  
  Hint "Also get non-negativity of the left side."
  Hint (hidden := true) "Try `have g2 := norm_nonneg_v (a • v)`"
  have g2 := norm_nonneg_v (a • v)
  
  Hint "Now apply the square equality theorem to reduce to proving the squared version."
  Hint (hidden := true) "Try `apply (sq_eq_sq g2 g1).1`"
  apply (sq_eq_sq g2 g1).1

  Hint "Use `ring_nf` to simplify the goal"
  Hint (hidden := true) "Try `ring_nf`"
  ring_nf

  Hint "Use our theorems to simplify the goal. Also, remember the `exact?`
  tactic can help you find when to use `exact`."
  Hint (hidden := true) "Try `repeat rw[norm_sq_eq]`"
  repeat rw[norm_sq_eq]
  Hint (hidden := true) "Try `rw [InnerProductSpace_v.inner_smul_left]`"
  rw [InnerProductSpace_v.inner_smul_left]
  Hint (hidden := true) "Try `rw [inner_smul_right_v]`"
  rw [inner_smul_right_v]
  Hint (hidden := true) "Try `rw[← mul_assoc]`"
  rw[← mul_assoc]
  Hint (hidden := true) "Try `rw[mul_conj]`"
  rw[mul_conj]
  Hint (hidden := true) "Try `rw[normSq_eq_norm_sq]`"
  rw[normSq_eq_norm_sq]
  Hint (hidden := true) "Try `exact re_ofReal_mul (‖a‖ ^ 2) ⟪v,v⟫`"
  exact re_ofReal_mul (‖a‖ ^ 2) ⟪v,v⟫

end LinearAlgebraGame
