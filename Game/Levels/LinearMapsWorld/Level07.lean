import Game.Levels.LinearMapsWorld.Level06

namespace LinearAlgebraGame

World "LinearMapsWorld"
Level 7

Title "Coordinates Representation"

Introduction "
## Coordinates with Respect to a Basis

In linear algebra, a **basis** of a vector space allows us to represent every vector in the space as a combination of the basis vectors. Imagine we have chosen a specific basis `B : Fin n → V` for an `n`-dimensional vector space `V`. How can we describe an arbitrary vector `v` in `V` in terms of this basis? By listing its **coordinates** relative to `B` — essentially, how much of each basis vector is needed to reconstruct `v`. 

In this level, we introduce a formal coordinate map that takes any vector to its coordinate tuple, and we prove that these coordinates provide a unique representation of the vector.

## Summary
**Coordinates with Respect to a Basis:** We prove that once a basis `B` of `V` is fixed, every vector `v` in `V` can be expressed *uniquely* as a linear combination of the basis vectors. We formalize this by defining the function `coord`, which returns the coefficients of `v` with respect to `B`. The main theorem, `coord_representation`, then states that `v` equals the sum of its coordinates times the corresponding basis elements. This confirms that coordinates give a one-to-one correspondence between vectors in `V` and their coordinate tuples.

## Key idea
- We obtain the coordinate function `coord` by using the basis's `repr` function. This gives each vector `v` a tuple of `n` scalars corresponding to its components along the basis vectors in `B`.
- Because `B` spans `V`, every vector can be expressed as a sum of basis elements with appropriate coefficients. In fact, the library lemma `B.sum_repr` states that `∑ i, coord v i • B i = v`, directly reconstructing `v` from its coordinates.
- The representation is *unique* because `B` is linearly independent. If two different coordinate lists produced the same vector `v`, their difference would give a nonzero linear combination of basis vectors equal to zero — contradicting linear independence. Hence, no vector has two distinct sets of coordinates.
"

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {n : ℕ} (B : Basis (Fin n) K V)

TheoremDoc LinearAlgebraGame.coord_representation as "Coordinate Representation" in "Bases"

/--
The coordinate map (unique coordinates for each v ∈ V)
-/
noncomputable def coord (v : V) : Fin n → K := B.repr v

/--
Every vector equals the sum of its coordinates times the corresponding basis elements.
-/
Statement coord_representation (v : V) : v = Finset.univ.sum (fun i => coord K V B v i • B i) := by
  rw [coord]
  exact (B.sum_repr v).symm

Conclusion "
By choosing a basis for `V`, we've established that any vector can be captured by a finite list of scalars — its coordinates. In other words, every vector corresponds to a unique tuple of coordinates (and vice versa) with respect to the chosen basis. This underpins the idea of coordinate systems in linear algebra, allowing us to seamlessly move between abstract vectors and their concrete representations.
"

end LinearAlgebraGame