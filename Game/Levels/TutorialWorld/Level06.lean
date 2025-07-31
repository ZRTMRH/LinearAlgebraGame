import Game.Metadata.Metadata

World "TutorialWorld"
Level 6
Title "The `cases'` and `exfalso` tactics"

/--
## Summary

If `h` is a proof (for example a hypothesis), then `cases' h with...` will break the
proof up into the pieces used to prove it.

## Example

If `h : P ∨ Q` is a hypothesis, then `cases' h with hp hq` will turn one goal
into two goals, one with a hypothesis `hp : P` and the other with a
hypothesis `hq : Q`.

## Example

If `h : False` is a hypothesis, then `cases' h` will turn one goal into no goals,
because there are no ways to make a proof of `False`! And if you have no goals left,
you have finished the level.


## Example

If `h : ∃ (a : ℝ), a * a = 0` is a hypothesis, thatn `cases' h with a ha` will create a variable
`a : Nat` and a hypothesis `ha : a * a = 0`

-/
TacticDoc cases'

/--
## Summary

`exfalso` changes any goal to `False` this works because proving `False` is a contradiction and can
thus prove anything else. Mathematically, this means that for any proposition `P`, `False → P`.

## Example

If you have a hypothesis `h: False`, and a goal `Q`, `exfalso; exact h` will solve the goal`
-/
TacticDoc exfalso

NewTactic cases' exfalso


Introduction "
This level introduces the `cases'` and `exfalso` tactics. The goal of this level is to prove `(P ∧ ¬ P) → Q`.
This proof is similar to a proof by contradiction. The first part of the implication, `P ∧ ¬ P`, is
a contradiction, so it can prove any proposition `Q`.

### Cases'
The `cases'` tactic is very important in Lean. It allows you to split any object or hypothesis into
cases. In this level, we will eventually have an and statement as a hypothesis. If we have `h: P ∧ Q`,
`cases' h with hL hR` will create two hypotheses: `hL: P`, and `hR: Q`. If you have an object `x` that
can be split into cases, `cases' x with c1 c2` will split `x` into cases called `c1` and `c2`.

### Exfalso
The `exfalso` tactic is also useful in this level. It simply changes the goal to `False`. This works
because if you can prove `False`, you have a contradiction, and can thus prove any statements. For
example, if you have a hypothesis `h: False`, and a goal `Q`, `exfalso; exact h` will solve the goal.
"

Statement (P Q : Prop) : (P ∧ ¬ P) → Q := by
  Hint "You have two main options here. Note that you have a statement of the form `P → Q`, so there
  is a tactic we know that can simplify the goal. Also, we have a `¬` character, so unfolding that
  could also be helpful"
  Hint (hidden := true) "Try `intro h`"
  intro h
  Hint "Since the `¬` symbol is in a hypothesis now, instead of the goal, in order to unfold it you
  need to do `unfold Not at h`, where you replace `h` with the name of your hypothesis. `unfold Not
  at *` will also unfold it everywhere."
  Hint (hidden := true) "Try `unfold Not at h`"
  unfold Not at h
  Hint "Now, use the `cases'` tactic to split up your and statement hypothesis."
  Hint (hidden := true) "Try `cases' h with h1 h2`"
  cases' h with h1 h2
  Hint (strict := true) "It would be nice if our goal was `False` here."
  Hint (hidden := true) "Try `exfalso`"
  exfalso
  Hint (hidden := true) "Try `apply h2`"
  apply h2
  Hint (hidden := true) "Try `exact h1`"
  exact h1

Conclusion "
You now know most of the basics for working with logic in Lean! The remaining levels in the tutorial
world will move away from pure logic, but many of the tactics used already will still be essential.
"
