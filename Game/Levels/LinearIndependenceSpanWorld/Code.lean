import Game.Levels.LinearIndependenceSpanWorld.VectorSpaceThms

variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--  Linear Combination**
A vector $x$ is called a **linear combination** of a set $S$ if it can be expressed as a finite sum of elements of $S$ scaled by scalars in the field. Here we formalize this concept. ∑ v in s, f v • v-/
def is_linear_combination (S : Set V) (x : V) : Prop :=
∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (∀ v ∉ s, f v = 0) ∧ (x = Finset.sum s (fun v => f v • v))

theorem linear_combination_of_mem {S : Set V} {v : V} (hv : v ∈ S) : is_linear_combination K V S v := by
  unfold is_linear_combination
  use {v}
  use (λ w => if w = v then (1 : K) else 0)
  simp
  exact hv

/-- **Level 7: Span**
The **span** of a set $S$ is the set of all linear combinations of elements of $S`. It is the smallest subspace containing $S`. -/
def span (S : Set V) : Set V :=
  { x : V | is_linear_combination K V S x }

theorem mem_span_of_mem {S : Set V} {v : V} (hv : v ∈ S) : v ∈ span K V S := by
  unfold span
  exact linear_combination_of_mem K V hv

/-- **Level 8: Monotonicity of Span**
If $A \subseteq B$ are sets of vectors, then `span A ⊆ span B`. In other words, a larger set of vectors can only have a larger (or equal) span. -/
theorem span_mono {K V :Type} [Field K] [AddCommGroup V][VectorSpace K V]{A B : Set V} (hAB : A ⊆ B) : span K V A ⊆ span K V B := by
  intro x hxA
  unfold span at *
  unfold is_linear_combination at *
  simp at *
  obtain ⟨s, hsA, f, h1, h2⟩ := hxA
  use s
  constructor
  exact hsA.trans hAB
  use f

/-- Linear Independence**
A set of vectors $S$ is **linearly independent** if no vector in $S$ can be written as a linear combination of the others. Equivalently, the only solution to a linear combination of elements of $S$ equaling zero is the trivial solution (all coefficients zero). Here we formalize this condition. -/
def linear_independent_v (S : Set V) : Prop :=
∀ (s : Finset V) (f : V → K),
(↑s ⊆ S) → (Finset.sum s (fun v ↦ f v • v) = 0) → (∀ v ∈ s, f v = 0)

/-- Independence of Empty Set and Singletons**
Proposition 2.6(a): The empty set is linearly independent (vacuously, since there are no vectors to depend on). -/
theorem linear_independent_empty (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V] : linear_independent_v K V (∅ : Set V) := by
  unfold linear_independent_v
  intros _s f hs _sum_zero v hv
  exfalso
  exact hs hv

/--  Independence of Subsets**
**Proposition 2.7(a):** Any subset of a linearly independent set is also linearly independent. -/
theorem subset_linear_independents [Field K] [AddCommGroup V][VectorSpace K V] {A B : Set V} (hBsubA : B ⊆ A) (hA : linear_independent_v K V A) :
    linear_independent_v K V B := by
  unfold linear_independent_v at *
  intros s f hsB sum_zero v hv
  have hsA : ↑s ⊆ A := hsB.trans hBsubA
  exact hA s f hsA sum_zero v hv


/-- **Proposition 2.7(b):** If a set $A$ spans the whole space $V$, then any superset of $A$ also spans $V`. Adding more vectors can't reduce the span. -/
theorem superset_span_full {A B T: Set V} (hT: ∀ (x: V), x ∈ T)(hA : T = span K V A) (hAsubB : A ⊆ B) :
    T = span K V B := by
  -- `span A = T` means A is a spanning set for V (the entire space).
  -- We want to show `span B = V` as well.
  apply Set.eq_of_subset_of_subset
  rw [hA]
  exact span_mono hAsubB
  intros x _ssg
  exact hT x

theorem help (f g : V → K): (fun v => (f - g) v • v) = (fun v => (f v - g v) • v) := by
  rfl

theorem help2 (f g : V → K) : (fun v => ((f v) - (g v)) • v) = (fun (v : V) => ((f v) • v) - ((g v) • v)) := by
  funext v
  exact sub_smul (f v) (g v) v

theorem linear_combination_unique
{S : Set V} (hS : linear_independent_v K V S)
(s t : Finset V) (hs : ↑s ⊆ S) (ht : ↑t ⊆ S)
(f g : V → K) (hf0 : ∀ v ∉ s, f v = 0) (hg0 : ∀ v ∉ t, g v = 0)
(heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)) :
∀ (v : V), f v = g v := by
  intro v
  cases' Decidable.em (v ∈ (s ∪ t)) with hIn hOut
  unfold linear_independent_v at hS
  specialize hS (s ∪ t) (f - g)
  rw[Finset.coe_union] at hS
  specialize hS (Set.union_subset hs ht)
  have hShyp : (Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0 := by
    rw[help, help2, Finset.sum_sub_distrib]
    have hfprod0 : ∀ v ∉ s, f v • v = 0 := by
      intros v hv
      rw[hf0 v hv]
      exact zero_smul K v
    have hgprod0 : ∀ v ∉ t, g v • v = 0 := by
      intros v hv
      rw[hg0 v hv]
      exact zero_smul K v
    rw [(Finset.sum_subset (f := fun x => f x • x) (Finset.subset_union_left s t) (by intro x _hx; exact hfprod0 x)).symm]
    rw [(Finset.sum_subset (f := fun x => g x • x) (Finset.subset_union_right s t) (by intro x _hx; exact hgprod0 x)).symm]
    rw[heq]
    simp
  specialize hS hShyp v hIn
  exact sub_eq_zero.1 hS
  rw[Finset.not_mem_union] at hOut
  cases' hOut with hS hT
  rw[hf0 v hS, hg0 v hT]
