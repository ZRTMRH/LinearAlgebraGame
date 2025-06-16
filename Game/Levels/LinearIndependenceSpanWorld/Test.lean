import Mathlib
open Function Set

#print preimage -- notated ⁻¹'

#print image -- notated ''



-- class VectorSpace (K V : Type) [Field K] [AddCommGroup V] extends SMul K V where
-- smul_add : ∀ (a : K) (x y : V), a • (x + y) = a • x + a • y -- distributivity of scalar over vector addition
-- add_smul : ∀ (a b : K) (x : V), (a + b) • x = a • x + b • x -- distributivity of scalar addition
-- mul_smul : ∀ (a b : K) (x : V), (a * b) • x = a • (b • x) -- compatibility of scalar multiplication
-- one_smul : ∀ (x : V), (1 : K) • x = x -- identity scalar acts as identity
class VectorSpace (K V : Type) [Field K] [AddCommGroup V] extends Module K V where

smul_add_explicit : ∀ (a : K) (x y : V), a • (x + y) = a • x + a • y := smul_add
add_smul_explicit : ∀ (a b : K) (x : V), (a + b) • x = a • x + b • x := add_smul
mul_smul_explicit : ∀ (a b : K) (x : V), (a * b) • x = a • (b • x) := mul_smul
one_smul_explicit : ∀ (x : V), (1 : K) • x = x := one_smul


variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]


def isSubspace (W : Set V) : Prop :=
W.Nonempty ∧ (∀ (x y : V), x ∈ W → y ∈ W → x + y ∈ W) ∧ (∀ (a : K) (x : V), x ∈ W → a • x ∈ W)

#check add_right_cancel

#check Finset.sum
#check singleton_subset_iff

variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]


/--  Linear Combination**
A vector $x$ is called a **linear combination** of a set $S$ if it can be expressed as a finite sum of elements of $S$ scaled by scalars in the field. Here we formalize this concept. ∑ v in s, f v • v-/
def is_linear_combination (S : Set V) (x : V) : Prop :=
∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (∀ v ∉ s, f v = 0) ∧ (x = Finset.sum s (fun v => f v • v))

/-- Any vector in $S$ is trivially a linear combination of $S$. -/
theorem linear_combination_of_mem {S : Set V} {v : V} [DecidableEq V] (hv : v ∈ S) : is_linear_combination K V S v := by
  use {v}, (λ w => if w = v then (1 : K) else 0)
  simp only [Finset.coe_singleton, Finset.singleton_subset_iff]
  constructor
  · exact singleton_subset_iff.mpr hv
  constructor
  · intro w hw
    simp only [Finset.mem_singleton] at hw
    simp [hw]
  · simp only [Finset.sum_singleton]
    simp [one_smul]






/--  Span
The **span** of a set $S$ is the set of all linear combinations of elements of $S. It is the smallest subspace containing $S. -/
def span (S : Set V) : Set V :=
{ x : V | is_linear_combination K V S x }

variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/-- Every element of $S$ lies in span S (since it can be expressed as a trivial linear combination of itself). -/
theorem mem_span_of_mem {S : Set V} {v : V} (hv : v ∈ S) : v ∈ span K V S := by
unfold span
have hg: is_linear_combination K V S v:= by exact linear_combination_of_mem K V hv
exact hg






/--  Monotonicity of Span
If $A \subseteq B$ are sets of vectors, then span A ⊆ span B. In other words, a larger set of vectors can only have a larger (or equal) span. -/
theorem span_mono {K V :Type} [Field K] [AddCommGroup V][VectorSpace K V]{A B : Set V} (hAB : A ⊆ B) : span K V A ⊆ span K V B := by
intro x hxA
obtain ⟨s, f, hsA, hf0, rfl⟩ := hxA
have hsB : ↑s ⊆ B := hsA.trans hAB
exact ⟨s, f, hsB, hf0, rfl⟩


/-- Linear Independence**
A set of vectors $S$ is **linearly independent** if no vector in $S$ can be written as a linear combination of the others. Equivalently, the only solution to a linear combination of elements of $S$ equaling zero is the trivial solution (all coefficients zero). Here we formalize this condition. -/
def linear_independent_1 (S : Set V) : Prop :=
∀ (s : Finset V) (f : V → K),
(↑s ⊆ S) → (Finset.sum s (fun v ↦ f v • v) = 0) → (∀ v ∈ s, f v = 0)



/-- Independence of Empty Set and Singletons**
Proposition 2.6(a): The empty set is linearly independent (vacuously, since there are no vectors to depend on). -/
theorem linear_independent_empty (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V] :
linear_independent_1 K V (∅ : Set V) := by
intros _s f hs _sum_zero v hv
exact False.elim (hs hv)



/--  Independence of Subsets**
**Proposition 2.7(a):** Any subset of a linearly independent set is also linearly independent. -/
theorem subset_linear_independents [Field K] [AddCommGroup V][VectorSpace K V] {A B : Set V} (hBsubA : B ⊆ A) (hA : linear_independent_1 K V A) :
    linear_independent_1 K V B := by
  intros s f hsB sum_zero v hv
  have hsA : ↑s ⊆ A := hsB.trans hBsubA
  exact hA s f hsA sum_zero v hv
  /-- **Proposition 2.7(b):** If a set $A$ spans the whole space $V$, then any superset of $A$ also spans $V`. Adding more vectors can't reduce the span. -/
theorem superset_span_full {A B T: Set V} (hT: ∀ (x: V), x∈ T)(hA : T = span K V A) (hAsubB : A ⊆ B) :
    T = span K V B := by
  -- `span A = T` means A is a spanning set for V (the entire space).
  -- We want to show `span B = V` as well.
  have h1 : span K V B ⊆  T:= by
    intro x
    intro _ssg
    exact hT x
  have h2: T⊆ span K V B := by
    rw [hA]
    exact span_mono hAsubB
  exact Subset.antisymm h2 h1


/-- Uniqueness of Representation (Proposition 2.8)**
If $S$ is linearly independent, then any vector in the span of $S$ has a unique expression as a linear combination of elements of $S$. In particular, if
$$\sum_{i} a_i u_i = \sum_{j} b_j w_j,$$
with all $u_i, w_j ∈ S$, then $a_i = b_j$ for each corresponding vector in $S$. We prove that the coefficient functions must coincide. -/
theorem linear_combination_unique
{S : Set V} (hS : linear_independent_1 K V S)
(s t : Finset V) (hs : ↑s ⊆ S) (ht : ↑t ⊆ S)
(f g : V → K) (hf0 : ∀ v ∉ s, f v = 0) (hg0 : ∀ v ∉ t, g v = 0)
(heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)) :
∀ (v : V), f v = g v := by
-- Consider the combined set of all vectors involved in both sums.
  let u := s ∪ t
  have huS : ↑u ⊆ S := by
    rw [Finset.coe_union]
    exact Set.union_subset hs ht
  -- Define a new coefficient function h for u as the difference of f and g.
  let h := (λ v => f v - g v)
  have _h0 : ∀ v ∉ u, h v = 0 := by
    intro v hv
    simp only [h]
    rw [hf0 v (λ h'↦ hv (Finset.mem_union_left t h')),
        hg0 v (λ h' ↦ hv (Finset.mem_union_right s h'))]
    simp
  -- Now sum over u using h; this equals the difference of the two sums, which is zero.
  have sum_h : Finset.sum u (fun v => h v • v) = 0 := by
    have expand_h : Finset.sum u (fun v => h v • v) =
                   Finset.sum u (fun v => (f v - g v) • v) := by
      simp only [h]
    have use_sub_smul : Finset.sum u (fun v => (f v - g v) • v) =
                       Finset.sum u (fun v => f v • v - g v • v) := by
      apply Finset.sum_congr rfl
      intro v _a
      exact sub_smul (f v) (g v) v
    have sub_dist : Finset.sum u (fun v => f v • v - g v • v) =
                   Finset.sum u (fun v => f v • v) - Finset.sum u (fun v => g v • v) := by
      exact Finset.sum_sub_distrib
    have sum_f_eq : Finset.sum u (fun v => f v • v) = Finset.sum s (fun v => f v • v) := by
      symm
      apply Finset.sum_subset
      exact Finset.subset_union_left s t
      intro v _hv_u hv_not_s
      rw [hf0 v hv_not_s]
      simp
    have sum_g_eq : Finset.sum u (fun v => g v • v) = Finset.sum t (fun v => g v • v) := by
      symm
      apply Finset.sum_subset
      exact Finset.subset_union_right s t
      intro v _hv_u hv_not_t
      rw [hg0 v hv_not_t]
      simp

    rw [expand_h, use_sub_smul, sub_dist, sum_f_eq, sum_g_eq, heq, sub_self]
  -- By linear independence of S (applied to u ⊆ S), all coefficients h v must be zero.
  have coeff_zero := hS u h huS sum_h
  intro v
  -- For each v (especially v ∈ u), h v = 0, so f v = g v.
  by_cases hv : v ∈ u
  · exact sub_eq_zero.1 (coeff_zero v hv) -- h v = 0 implies f v - g v = 0, so f v = g v.
  · -- If v ∉ u, then neither f v nor g v appeared in the sums, hence both are 0 by the support conditions.
    rw [hf0 v (λ hv' => hv (Finset.mem_union_left t hv')),
        hg0 v (λ hv' => hv (Finset.mem_union_right s hv'))]
#check sub_smul
