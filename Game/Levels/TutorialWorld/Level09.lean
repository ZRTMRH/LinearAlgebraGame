import Game.Metadata.Metadata

World "TutorialWorld"
Level 9
Title "The `use` tactic and your first theorem"

/--
## Summary

The `use` tactic makes progress with goals which claim something *exists*.
If the goal claims that some `x` exists with some property, and you know
that `x = 37` will work, then `use 37` will make progress.

Because `a ≤ b` is notation for \"there exists `c` such that `b = a + c`\",
you can make progress on goals of the form `a ≤ b` by `use`ing the
number which is morally `b - a` (i.e. `use b - a`)

Any of the following examples is possible assuming the type of the argument passed to the `use` function is accurate:

- `use 37`
- `use a`
- `use a * a + 1`
-/
TacticDoc use

/--
le_iff_exists_add is a proof that `a ≤ b ↔ ∃ (c : ℕ), a = b + c`.

The reason for the name is that two numbers are less than or equal to each other if and only if
there exists a number that you can add to the smaller one to make them equal.
-/
TheoremDoc le_iff_exists_add as "le_iff_exists_add" in "ℕ"

NewTactic use
NewTheorem le_iff_exists_add

Introduction "
In this level, the goal is to prove `x ≤ 1 + x`. This requires understanding how to prove statements
about inequalities. We can define the `≤` symbol so that `a ≤ b` means `∃ (c : ℕ), b = a + c`. In
other words, a is less than or equal to b if and only if there exists a natural number c where
b = a + c. In this level, we have decided to use the natural numbers, although the statement is
clearly also true when working with real numbers. This is because the theorem \"le_iff_exists_add\"
does not work with the real numbers, so the proof would be slightly different.

We have this statment as a theorem, \"le_iff_exists_add\".

However, note that this theorem will rewrite the goal to have a `∃` symbol. In this case, we have to
find a number that satisfies a certain property. Once you find such a number, you can use the `use`
tactic.

`use c` changes the goal from the form `∃ x, Property(x)` to `Property(c)`. This allows you to solve
`∃` goals, but you need to first find a valid example, which may take some planing ahead.
"


Statement (x : Nat) : x ≤ 1 + x := by
  Hint "Try using the new theorem! Since it is a proof of `↔`, the rewrite tactic should work!"
  Hint (hidden := true) "Try `rw[le_iff_exists_add]`"
  rw[le_iff_exists_add]
  Hint "What number should you use here to make the statement true?"
  Hint (hidden := true) "Try `use 1`"
  use 1
  Hint "You now have a simple linear equation. What tactic can solve linear equations and prove
  equalities?"
  Hint (hidden := true) "Try `linarith`"
  linarith

TheoremTab "ℕ"

Conclusion "
Now on to the last level in the tutorial world!
"
