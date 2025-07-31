import Game.Levels.LinearIndependenceSpanWorld.Level06

namespace LinearAlgebraGame

World "LinearIndependenceSpanWorld"
Level 7

Title "Supersets Span the Whole Space"

Introduction "
Now that we know some properties of subsets, we can work on a property of supersets. This level is a
proof that if `A` spans the whole space, then any `B ⊇ A` also spans the whole space

### The Goal
We have three sets, and three hypotheses. We have sets `A` and `B`, which are the set and superset we
are working with. We also have the set `T`, which is the entire space `V`. The reason we are using `T`
instead of `V` is that `T` is an object of the type `Set V`, which is the same type as `span K V A` or
`span K V B`. We can't compare these spans with `V`, but we can compare them with `T`. This also means
we need a hypothesis  (hT : ∀ (x : V), x ∈ T), which means that any element of `V` is also in `T`.
The other two hypotheses simply state that `B` is a superset of `A`, and that the span of `A` is `T`.
The goal is to prove that the span of `B` is also `T`.

### `Set.eq_of_subset_of_subset`
When working with sets, a very useful theorem is `Set.eq_of_subset_of_subset`. This theorem shows that
two sets are equal if and only if they are subsets of each other. So, if you have a goal of the form
`A = B`, `apply Set.eq_of_subset_of_subset` will change the goal into two goals: `A ⊆ B`, and `B ⊆ A`.
"

/--
`superset_span_full` is a proof that if a set `A` spans the whole space `V`, then any superset of `A`
also spans `V`. The syntax requires a set `T : Set V` with the property `hT: ∀ (x : V), x ∈ T`, so that
`T` is a subset that is actually the entire space. With other hypotheses `hA : T = span K V A`, and
`hAsubB : A ⊆ B`, then `superset_span_full` is a proof that `T = span K V B`.
-/
TheoremDoc LinearAlgebraGame.superset_span_full as "superset_span_full" in "Vector Spaces"

/--
`Set.eq_of_subset_of_subset` is a proof that `A = B` if and only if `A ⊆ B` and `B ⊆ A`. If you have
a goal of the form `A = B`, `apply Set.eq_of_subset_of_subset` will change the goal into two goals:
`A ⊆ B`, and `B ⊆ A`.
-/
TheoremDoc Set.eq_of_subset_of_subset as "eq_of_subset_of_subset" in "Sets"

NewTheorem Set.eq_of_subset_of_subset

open VectorSpace Set
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/-- If a set $A$ spans the whole space $V$, then any superset of $A$ also spans $V`.-/
Statement superset_span_full {A B T: Set V} (hT: ∀ (x : V), x ∈ T)(hA : T = span K V A) (hAsubB : A ⊆ B) :
    T = span K V B := by
  Hint (hidden := true) "Try `apply Set.eq_of_subset_of_subset`"
  apply eq_of_subset_of_subset
  Hint (hidden := true) "Try `rw [hA]`"
  rw [hA]
  Hint (hidden := true) "Try `exact span_mono K V hAsubB`"
  exact span_mono K V hAsubB
  Hint (hidden := true) "Try `intros x _ssg`"
  intros x _ssg
  Hint (hidden := true) "Try `exact hT x`"
  exact hT x

Conclusion "The next three levels in this world will be much more difficult. The next level can be
thought of as a \"boss level\", and the last two levels can be extra optional challenges. Try to plan
out your proofs before writing them."
