import Game.Metadata.Metadata

World "TutorialWorld"
Level 3
Title "The `intro` and `exact` tactics"

/--
## Summary

Intro introduces a new hypothesis and changes your goal. If you have a goal of the form `P → Q`,
`intro h` will change the goal to `Q` and create a new hypothesis `h : P`.

## Example

If your goal is `x = 1 → x + x = 2`, `intro h` will create the hypothesis `h: x = 1`, and change the
goal to `x + x = 2`.

## Other usage

The `intro` tactic also works with goals using `∀` (\"for all\"). If your goal is of the form `∀ x : T, P`,
`intro x` will create a new variable `x : T`, and change the goal to `P`.

## Example

If your goal is `∀ x : Nat, x ≥ 0`, `intro x` will create a variable `x : Nat`, and change the goal
to `x ≥ 0`.
-/
TacticDoc intro

/--
## Summary

If the goal is a statement `P`, then `exact h` will solve the goal if `h` is a proof of `P`.

## Example

If your goal is `x + 5 = 10`, and you have a hypothesis `h: x + 5 = 10`, then `exact h` will solve
the goal.

## Example

If your goal is `x ⬝ y = 0 ↔ x ⟂ y`, and you have a theorem `dot_zero_iff_perp` that states the same
thing, `exact dot_zero_iff_perp` will solve the goal.

## exact? tactic

`exact` has a variation, `exact?`, that is very useful. If your goal seems very obvious, and if you
believe that there is a theorem or hypothesis that is exactly the same as your goal, `exact?` will
attempt to fill in an `exact` tactic. This way, you don't have to memorize the exact statement of
every theorem in order to finish a proof.
However, with great power comes great responsibility, and using `exact?` too often can obscure how
a proof actually works, and can lead you to being more confused than when you started.
-/
TacticDoc exact

NewTactic intro exact

Introduction "
In this level, we will introduce two tactics: `intro`, and `exact`
Our goal is to prove that for any proposition (a True/False statement) `P`, we know that `P → P`.
This means that `P` implies `P`.

To explain what implication means more rigorously, if we know that `P → Q`, whenever `P` is True, we
now know that `Q` must also be True. A computer scientist can consider a proof that `P → Q` as a function
taking proofs of `P` to proofs of `Q`. In Lean, this means that we take an arbitrary proof of `P`,
say `h: P` and we must construct a proof of `Q` from it.

### Intro
This idea is exatly what the `intro` tactic does. If the goal is of the form `P → Q`, `intro h` will
create a new hypothesis `h: P`, and change the goal into `Q`.

### Exact
The exact tactic is the other tactic you will need to solve this level. If you have a hypothesis that
is exactly the same as the goal, the exact tactic will solve the goal. For example, if your goal is
`P`, and you have a hypothesis `h: P`, `exact h` will solve the goal."

Statement (P : Prop) : P → P := by
  Hint "First use `intro` to give yourself a new assumption and simplify the goal"
  Hint (hidden := true) "Try `intro h`"
  intro h
  Hint "Now use `exact` to solve the goal"
  Hint (hidden := true) "Try `exact h`"
  exact h

Conclusion "
You now know how to use the `intro` and `exact` tactics!
"
