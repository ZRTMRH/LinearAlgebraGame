import Game.Metadata.Metadata

World "TutorialWorld"
Level 1
Title "The rfl tactic"

/--
## Summary

`rfl` proves goals of the form `X = X`.

In other words, the `rfl` tactic will close any goal of the
form `A = B` if `A` and `B` are *identical*.

`rfl` is short for \"reflexivity (of equality)\".

## Example:

If the goal looks like this:

```
x + 37 = x + 37
```

then `rfl` will close it. But if it looks like `0 + x = x` then `rfl` won't work, because even
though $0+x$ and $x$ are always equal as *numbers*, they are not equal as *terms*.
The only term which is identical to `0 + x` is `0 + x`.

## Details

`rfl` is short for \"reflexivity of equality\".
-/
TacticDoc rfl

NewTactic rfl

Introduction "
Most levels in this game will require you to prove a mathematical theorem. In the middle of the
screen, you will see your \"Active Goal\", which includes \"Objects:\" `x: ℝ` and a \"Goal\" `x=x`.
In later levels, you may also get a \"Assumptions\" line. Your objects and assumptions are what you
have to work with. In this case, we know that `x` is in  `ℝ`, which means `x` is a real number.
From this, we have to prove our goal, that `x=x`.

The first tactic we will use is the `rfl` tactic. `rfl` stands for \"reflexivity\". `rfl` will solve
goals when the left side of an equation is the same as the right side, at least up to definitions.
"

Statement (x : ℝ) : x = x := by
  Hint "Try typing 'rfl' into the text box below, then hit \"Execute\". This should finish the proof."
  Hint (hidden := true) "Try `rfl`"
  rfl

Conclusion "
You have now finished your first proof in Lean 4! In future levels, you can also use the 'rfl' tactic.
You can click on the 'rfl' box on the right side to learn more about the 'rfl' tactic.

Click on \"Next\" to go to the next level.
"
