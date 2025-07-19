import Game.Levels.LinearIndependenceSpanWorld.Level08
World "LinearMapsWorld"
Level 1

Title "Definition of a Basis"

Introduction "
In this level, we introduce the precise mathematical definition of a **basis** for a vector space.

Given a vector space $V$ over a field $K$, a set $B \\subseteq V$ is called a basis of $V$ if it satisfies **two key properties**:

1. **Linear Independence:** No nontrivial linear combination of elements of $B$ gives zero.  
   That is, if a finite sum $\\sum_{i} \\alpha_i b_i = 0$ with $b_i \\in B$ and scalars $\\alpha_i$ implies all $\\alpha_i = 0$.

2. **Spanning:** Every vector $v \\in V$ can be written as a finite linear combination of elements of $B$.

In Lean, we formalize this as follows:

def isBasis (B : Set V) : Prop :=
  linear_independent K V B ∧ span K V B = ⊤


### The Goal
Prove that the definition above is equivalent to saying $B$ is linearly independent and spans $V$.
"


/--
`isBasis K V B` means $B$ is a basis: linearly independent and spans $V$.
-/
def isBasis (B : Set V) : Prop :=
  linear_independent K V B ∧ span K V B = ⊤

/--
The definition of a basis is just linear independence and spanning.
-/
Statement basis_iff_independent_and_spanning (B : Set V) :
    isBasis K V B ↔ (linear_independent K V B ∧ span K V B = ⊤) := by
  Hint "Try `unfold isBasis` to see the definition directly."
  unfold isBasis
  exact Iff.rfl

Conclusion "
You have formalized the mathematical definition of a basis for a vector space.

In the next levels, you will use this definition to explore fundamental theorems about bases, dimension, and coordinate representations.
"
