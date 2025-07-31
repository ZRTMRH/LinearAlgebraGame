import Game.Metadata.Metadata

World "TutorialWorld"
Level 10
Title "The `induction'` tactic"

/--
## Summary

If `n : ℕ` is an object, and the goal mentions `n`, then `induction' n with d hd`
attempts to prove the goal by induction on `n`, with the inductive
variable in the successor case being `d`, and the inductive hypothesis being `hd`.

### Example:
If the goal is
```
0 + n = n
```

then

`induction' n with d hd`

will turn it into two goals. The first is `0 + 0 = 0`;
the second has an assumption `hd : 0 + d = d` and goal
`0 + succ d = succ d`.

Note that you must prove the first
goal before you can access the second one.
-/
TacticDoc induction'

/--
'add_succ' is a proof that `n + Nat.succ m = Nat.succ (n + m)`.

The reason for the name is that the theorem proves that adding the successor of a number is equal to
the successor of addind that number.
-/
TheoremDoc Nat.add_succ as "add_succ" in "ℕ"

NewTactic induction'
NewTheorem Nat.add_succ

Introduction "
The `induction'` tactic is a powerful tool to help you to prove statments involving natural numbers.
It splits a proof into two cases: a base case and an inductive step. The base case is the smallest
natural number you need to prove the proof for. The inductive step proves the theorem for all other
numbers. In the inductive step, you can assume the theorem holds for some value `d`, and must then
prove that it holds for `d + 1`, also written as `Nat.succ d`, the successor of `d`. Induction can
also be used to prove theorems about objects indexed my natural numbers, such as vectors whose
dimension can be described by a natural number.

The syntax for the `induction'` tactic is `induction' n with d hd`. As long as `n` is an arbirtary
natural number in the proof, this will do induction on `n`, where `d` is the number you assume the
theorem holds for in the inductive step, and `hd` is the induction hypothesis you will get.

This level also uses a new theorem: `add_succ`. `add_succ` is a proof that
`n + Nat.succ m = Nat.succ (n + m)`, for any `n, m : ℕ`.
"

Statement (n : Nat) : 0 + n = n := by
  Hint "First, perform induction on `n`."
  Hint (hidden := true) "Try `induction' n with n h`"
  induction' n with n h
  Hint "Base case: prove 0 + 0 = 0."
  Hint (hidden := true) "Try `simp`"
  simp
  Hint "Inductive step: use add_succ and the induction hypothesis."
  Hint (hidden := true) "Try `simp [Nat.add_succ, h]`"
  simp [Nat.add_succ, h]


Conclusion "
## Summary
You have now finished Tutorial World! Now, you can move on to Vector Space world.

The future worlds will be more challenging than this one, and will use less hints. However, if you're
stuck on how a tactic or theorem works, you can always read what they do on the right, or return to
Tutorial World for more review!

Click \"Leave World\" to return to the main menu.
"
