import Game.Metadata

World "TutorialWorld"
Level 10
Title "The `induction` tactic"

/--
## Summary

If `n : ℕ` is an object, and the goal mentions `n`, then `induction n with | zero => ... | succ n h => ...`
attempts to prove the goal by induction on `n`, with the base case being `zero`
and the inductive case being `succ n` with hypothesis `h`.

### Example:
If the goal is
```
0 + n = n
```

then

`induction n with | zero => ... | succ n h => ...`

will turn it into two goals. The first is `0 + 0 = 0`;
the second has an assumption `h : 0 + n = n` and goal
`0 + succ n = succ n`.

Note that you must prove the first
goal before you can access the second one.
-/
TacticDoc induction

NewTactic induction

Introduction "
The `induction` tactic is a powerful tool to help you to prove statements involving natural numbers.
It splits a proof into two cases: a base case and an inductive step. The base case is the smallest
natural number you need to prove the proof for. The inductive step proves the theorem for all other
numbers. In the inductive step, you can assume the theorem holds for some value `n`, and must then
prove that it holds for `n + 1`, also written as `Nat.succ n`, the successor of `n`. Induction can
also be used to prove theorems about objects indexed by natural numbers, such as vectors whose
dimension can be described by a natural number.

The syntax for the `induction` tactic in Lean 4 is `induction n with | zero => ... | succ n h => ...`.
As long as `n` is an arbitrary natural number in the proof, this will do induction on `n`, where
`zero` handles the base case, `succ n` is the successor case, and `h` is the induction hypothesis.

**Note:** If you see hints appearing multiple times, this is a known issue with the game framework. Simply continue with your proof - the level will work correctly despite any duplicate hints.
"

Statement (n : Nat) : 0 + n = n := by
  Hint "First, perform induction on `n`."
  Hint (hidden := true) "Try `induction n`"
  induction n
  Hint "Base case: prove 0 + 0 = 0."
  Hint (hidden := true) "Try `rfl`"
  rfl
  Hint "Inductive step: prove 0 + (n_1 + 1) = n_1 + 1."
  Hint (hidden := true) "Try `linarith`"
  linarith



Conclusion "
## Summary
You have now finished Tutorial World! Now, you can move on to Vector Space world.

The future worlds will be more challenging than this one, and will use less hints. However, if you're
stuck on how a tactic or theorem works, you can always read what they do on the right, or return to
Tutorial World for more review!

Click \"Leave World\" to return to the main menu.
"
