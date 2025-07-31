import Game.Metadata.Metadata

World "TutorialWorld"
Level 8

Title "The `simp` tactic"

/--
### Summary

The `simp` tactic tries to simplify the goal, and will solve it if possible. It acts similar to the
`rw` tactic, although it is able to rewrite with many different statements many times in order to
simplify the goal. `simp` will try to use all the theorems available if not told explicitly what
theorems to use.

Using `simp only [tactic1, tactic2, ...]` will simplify only using the theorems listed.

### Example

If your goal is something simple like `0 + 0 = 0`, `simp` will know enough about the natural numbers
to solve the goal.

### Example

If your goal is `(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h`, which seems
complicated, but you only need to use associativity and commutativity of addition,
`simp only [add_assoc, add_left_comm, add_comm]` will solve the goal.
-/
TacticDoc simp

NewTactic simp

Introduction "
The `simp` tactic aims to simplify your goal. Often if a goal seems very complicated, or uses
definitions that need to be unfolded, the `simp` tactic will make progress.

`simp` is not a flawless tool, and there are many simple statements it cannot prove, although when
used correctly, it can be very useful.

In this level, your goal is to prove an equality about certain elements in a \"Group\". A group is a
mathematical object where elements in a group can be multiplied together in a way that \"makes sense\".
Examples of groups involve the real numbers, integers, invertible square matrices of a specific size,
and many more. `simp` knows many theorems about groups, and is able to simplify and solve most
simple statements about them.

In this level, `a b c` are all elements of G, `1` is the multiplicative identity of G, and `a⁻¹` is
the multiplicative inverse of `a`. You can see that both sides of the equation will cancel out to `b`,
but there is an easy way to prove that they are equal.
"

Statement (G : Type) (hg : Group G) (a b c : G)  : a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  Hint "Just typing `simp` will solve the goal"
  Hint (hidden := true) "Try `simp`"
  simp

Conclusion "`simp` will be very useful when solving simple equations in future worlds. You can always
read more about it by clicking on it on the right."
