import Game.Metadata.Metadata

World "TutorialWorld"
Level 5
Title "The `unfold` and `apply` tactics"

/--
## Summary

If we have some object or function with some definition, `unfold object` will rewrite the object
with its definition everywhere. Lean often unfolds terms automatically, but some tactics and definitions
are not unfolded automatically. The `unfold` tactic also helps make it easier to take the next steps.

## Example:

If you have a goal `(P → Q) → (¬ Q → ¬ P)`, with `¬ P` (\"Not\" P) being defined as `P → False`,
using `unfold Not` will change the goal to `(P → Q) → ((Q → False) → (P → False))`
-/
TacticDoc unfold

/--
## Summary

If `t : P → Q` is a proof that $P \implies Q$, and `h : P` is a proof of `P`,
then `apply t at h` will change `h` to a proof of `Q`. The idea is that if
you know `P` is true, then you can deduce from `t` that `Q` is true.

If the *goal* is `Q`, then `apply t` will \"argue backwards\" and change the
goal to `P`. The idea here is that if you want to prove `Q`, then by `t`
it suffices to prove `P`, so you can reduce the goal to proving `P`.

### Example:

`succ_inj x y` is a proof that `succ x = succ y → x = y`.

So if you have a hypothesis `h : succ (a + 37) = succ (b + 42)`
then `apply succ_inj at h` will change `h` to `a + 37 = b + 42`.
You could write `apply succ_inj (a + 37) (b + 42) at h`
but Lean is smart enough to figure out the inputs to `succ_inj`.

### Example

If the goal is `a * b = 7`, then `apply succ_inj` will turn the
goal into `succ (a * b) = succ 7`.
-/
TacticDoc apply

/--
## Summary

`intros` acts very similar to the `intro` tactic, except it allows you to introduce many new
hypotheses/variables at once. `intros h1 h2 h3` essentially acts as `intro h1; intro h2; intro h3;`.

## Example

If your goal is `P → Q → (∀ x : Nat, R → (x = 5))`, `intros p q x r` will create hypotheses `p: P`,
`q: Q`, `r: R`, and a variable `x: Nat`, and change the goal to `x = 5`.
-/
TacticDoc intros

/--
## Summary

`Not` is the logical negation. In Lean, `¬ P` is defined as `P → False`.
When you see `¬ P` in a goal or hypothesis, you can use `unfold Not` to
replace it with `P → False`.

## Example

If you have a goal `¬ P`, using `unfold Not` will change it to `P → False`.
This often makes it easier to work with using `intro` and other tactics.
-/
TacticDoc Not

NewTactic unfold apply Not

NewHiddenTactic intros

Introduction "
In this level, we will learn the `unfold` and `apply` tactics. Our goal is to prove `(P → Q) → (¬ Q → ¬ P)`,
which looks very messy and difficult, but it can be slowly unfolded and broken down into simple steps.

The first tactic we will need is `unfold`. You may notice the `¬` symbol appearing multiple times in
the goal. This symbol means \"Not\", so `¬P` means \"not P\", or that P is false. In Lean, this is
encoded as `P → False`.

### Unfold
The `unfold` tactic will unfold definitions. Think of it as a big `rw` tactic that rewrites something
with it's definition everywhere. In this level, `unfold Not` will replace all the `¬ P`s with `P → False`.

We know how to deal with statements of the form `P → Q` in the goal, but what happens if we have them
as hypotheses? In this case, we will need the `apply` tactic.

### Apply
The `apply` tactic applies a hypothesis of the form `P → Q` to the goal. If your goal is `Q`, and
you have a hypothesis `h: P → Q`, `apply h` will change the goal to `P`.

### Combining hypotheses
Another way to use `h: P → Q` hypotheses is that if you also have another hypothesis  `h2: P`,
`h h2` will be a proof of `Q`. So, if you have these two hypotheses, and your goal is `Q`, `exact h h2`
will solve the goal.
"

Statement (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  Hint "Try using `unfold Not` to unfold the definition of `¬`."
  Branch
    intro h1
    intro h2
    Hint "Now, since there is a hypothesis also with a `¬` symbol, `unfold Not at *` will unfold
    everywhere!"
  Hint (hidden := true) "Try `unfold Not`"
  unfold Not
  Hint "Now, since you goal is of the form `P → Q`, the `intro` tactic may help."
  Hint (hidden := true) "Try `intro h1`"
  intro h1
  Hint "You can still use the `intro` tactic because the goal is still of the form `P → Q`"
  Hint (hidden := true) "Try `intro h2`"
  intro h2
  Hint (hidden := true) "Try `intro h3`"
  intro h3
  Hint "Now, try the `apply` tactic. Remember that if your goal is `Q`, you can use `apply h` when
  h is a hypothesis or proof that `P → Q`. You can also solve the level with one carefully worded
  `exact` statement if you combine your hypotheses."
  Hint (hidden := true) "Try `apply h2`"
  apply h2
  Hint "Again, try the `apply` tactic to change the goal. You can also solve the level with one carefully worded
  `exact` statement if you combine your hypotheses."
  Hint (hidden := true) "Try `apply h1`"
  apply h1
  Hint (hidden := true) "Try `exact h3`"
  exact h3

Conclusion "
This theorem shows that a statement `P → Q` implies its contrapositive `¬Q → ¬P`. In fact, these
two statements are the same, and you can prove `(P → Q) ↔ (¬ Q → ¬ P)`

Also, instead of writing intro three times, you can write `intros h1 h2 h3`, and that will be the
same as `intro h1; intro h2; intro h3`.
"
