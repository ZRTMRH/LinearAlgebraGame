import Game.Levels.LinearIndependenceSpanWorld.VectorSpaceThms

variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--  Linear Combination**
A vector $x$ is called a **linear combination** of a set $S$ if it can be expressed as a finite sum of elements of $S$ scaled by scalars in the field. Here we formalize this concept. ∑ v in s, f v • v-/
def is_linear_combination (S : Set V) (x : V) : Prop :=
∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (x = Finset.sum s (fun v => f v • v))

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

theorem linear_combination_unique
{S : Set V} (hS : linear_independent_v K V S)
(s t : Finset V) (hs : ↑s ⊆ S) (ht : ↑t ⊆ S)
(f g : V → K) (hf0 : ∀ v ∉ s, f v = 0) (hg0 : ∀ v ∉ t, g v = 0)
(heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)) :
∀ (v : V), f v = g v := by
  -- First, remove the ∀ symbol
  intro v
  -- Now, we can split into cases where either v ∈ (s ∪ t) or not.
  cases' Decidable.em (v ∈ (s ∪ t)) with hIn hOut
  unfold linear_independent_v at hS
  -- Think about the forwards proof. What set and function are we summing over when applying the
  -- linear independence of S?
  specialize hS (s ∪ t) (f - g)
  -- This line simply fixes some issues with type casting
  rw[Finset.coe_union] at hS
  -- Set.union_subset is a proof that if s ⊆ S and t ⊆ S, s ∪ t ⊆ S
  -- This solves the first requirement in hS
  specialize hS (Set.union_subset hs ht)
  -- Now, we want to prove the second requirement in hS
  specialize hS (by
    -- This allows us to simplify the function we are summing, and eventuall split it into two sums
    have fun_dist : (fun v => (f - g) v • v) = (fun (v : V) => ((f v) • v) - ((g v) • v)) := by
      -- funext allows us to change a goal of the form f = g to ∀ x, f x = g x
      funext v
      exact sub_smul (f v) (g v) v
    -- Now, we can split the sum in two
    rw[fun_dist, Finset.sum_sub_distrib]
    -- This shows our first function is 0 outside of s
    have hfprod0 : ∀ v ∈ s ∪ t,  v ∉ s → f v • v = 0 := by
      intros v _hv1 hv2
      rw[hf0 v hv2]
      exact zero_smul K v
    -- This shows our second function is 0 outside of t
    have hgprod0 : ∀ v ∈ s ∪ t,  v ∉ t → g v • v = 0 := by
      intros v _hv1 hv2
      rw[hg0 v hv2]
      exact zero_smul K v
    -- Now, since we know our functions are 0 outside s and t respectively, we can consider the sum
    -- Over s ∪ t as a sum over s and a sum over t, since everything else adds to 0
    rw [(Finset.sum_subset (f := fun v => f v • v) (Finset.subset_union_left s t) hfprod0).symm]
    rw [(Finset.sum_subset (f := fun v => g v • v) (Finset.subset_union_right s t) hgprod0).symm]
    -- Now, we use the fact that the two sums are equal to finish the proof
    rw[heq]
    simp)
  --Now, we chang ethe form of hS to fit our goal
  specialize hS v hIn
  -- We know now from hS that f v - g v = 0, so it is simple to show f v = g v
  exact sub_eq_zero.1 hS
  -- Finset.not_mem_union shows that if v ∉ s ∪ t, then v ∉ s and v ∉ t
  rw[Finset.not_mem_union] at hOut
  cases' hOut with hS hT
  -- Now, we use hf0 and hg0 to show both sides of the equation are 0
  rw[hf0 v hS, hg0 v hT]

/-- Main theorem: If v ∉ span S and S is linearly independent,
    then S ∪ {v} is linearly independent -/
theorem linear_independent_insert_of_not_in_span
  {S : Set V} {v : V}
  (hS : linear_independent_v K V S)
  (hv_not_span : v ∉ span K V S):
  linear_independent_v K V (S ∪ {v}) := by
    intros B f hB hf w hw
    cases' Decidable.em (v ∈ B) with hIn hOut

    have lemma_fv_zero : f v = 0 := by
      -- Proof by contradiction
      by_contra hfv_ne_zero

      -- Since f v ≠ 0, we can solve for v from the linear combination
      -- From sum_zero: ∑ u ∈ s, f u • u = 0
      -- This can be written as: f v • v + ∑ u ∈ s.erase v, f u • u = 0
      set g : V → V := fun u => f u • u
      have sum_split : f v • v + (B.erase v).sum (fun u => f u • u) = 0 := by
        rw[Finset.add_sum_erase B g hIn]
        exact hf

      -- Therefore: f v • v = -∑ u ∈ s.erase v, f u • u
      have v_expr : f v • v = -((B.erase v).sum (fun u => f u • u)) := by
        exact Eq.symm (neg_eq_of_add_eq_zero_left sum_split)

      -- Since f v ≠ 0, we can multiply both sides by (f v)⁻¹ to get v in terms of other vectors
      have v_as_combination : v = (-(f v)⁻¹) • ((B.erase v).sum (fun u => f u • u)) := by
        -- Apply (f v)⁻¹ to both sides of v_expr
        have step1 : (f v)⁻¹ • (f v • v) = (f v)⁻¹ • (-((B.erase v).sum (fun u => f u • u))) := by
          rw [v_expr]
        -- Left side simplifies to v
        have step2 : (f v)⁻¹ • (f v • v) = v := by

          rw [← mul_smul]
          rw [inv_mul_cancel]
          exact one_smul K v
          exact hfv_ne_zero
          -- Right side has the negation factored out
        have step3 : (f v)⁻¹ • (-((B.erase v).sum (fun u => f u • u))) =
                     -(f v)⁻¹ • ((B.erase v).sum (fun u => f u • u)) := by
          rw [smul_neg]
          exact (neg_smul (f v)⁻¹ (Finset.sum (Finset.erase B v) fun u => f u • u)).symm

        nth_rw 1 [← step2]
        rw[step1]
        rw[step3]

      -- Show that s.erase v ⊆ S
      have B_erase_v_subset_S : ↑(B.erase v) ⊆ S := by
        intro u hu_in_erase
        have hu_in_B : u ∈ B := Finset.mem_of_mem_erase hu_in_erase
        have hu_ne_v : u ≠ v := Finset.ne_of_mem_erase hu_in_erase
        have hu_in_union : u ∈ S ∪ {v} := hB hu_in_B
        cases' hu_in_union with hu_in_S hu_eq_v
        · exact hu_in_S
        · simp at hu_eq_v; contradiction

      -- This shows v is a linear combination of elements from S
      have v_in_span_S : v ∈ span K V S := by
        unfold span
        simp
        unfold is_linear_combination
        use B.erase v, fun u => -(f v)⁻¹ * f u
        constructor
        · exact B_erase_v_subset_S
        · nth_rw 1  [v_as_combination]
          rw [Finset.smul_sum]
          congr 1
          ext u
          exact smul_smul (-(f v)⁻¹) (f u) u

      -- This contradicts v ∉ span S
      exact hv_not_span v_in_span_S

    -- Now using the lemma, prove f w = 0 for any w ∈ s
    by_cases hw_eq_v : w = v
    · -- If w = v, then f w = f v = 0 by our lemma
      rw [hw_eq_v]; exact lemma_fv_zero
    · -- If w ≠ v, then w ∈ S, and we can apply linear independence of S

      -- Since f v = 0, the sum becomes just the sum over s.erase v
      let B' := B.erase v
      have B'_subset_S : ↑B' ⊆ S := by
        intro u hu_in_B'
        have hu_in_B : u ∈ B := Finset.mem_of_mem_erase hu_in_B'
        have hu_ne_v : u ≠ v := Finset.ne_of_mem_erase hu_in_B'
        have hu_in_union : u ∈ S ∪ {v} := hB hu_in_B
        cases' hu_in_union with hu_in_S hu_eq_v
        · exact hu_in_S
        · simp at hu_eq_v; contradiction

      have sum_B'_zero : B'.sum (fun u => f u • u) = 0 := by
        -- From our earlier sum_split and lemma_fv_zero
        let g : V → V := fun u => f u • u
        have sum_split : f v • v + B'.sum (fun u => f u • u) = 0 := by
          rw [← Finset.add_sum_erase B g hIn] at hf
          exact hf
        --#check VectorSpace.zero_smul
        rw [lemma_fv_zero, zero_smul_v, zero_add] at sum_split
        exact sum_split

      have hw_in_B' : w ∈ B' := by
        rw [Finset.mem_erase]; exact ⟨hw_eq_v, hw⟩

      -- Apply linear independence of S
      exact hS B' f B'_subset_S sum_B'_zero w hw_in_B'

    -- Then s ⊆ S, so we can directly apply linear independence of S
    have B_subset_S : ↑B ⊆ S := by
      intro u hu_in_B
      have hu_in_union : u ∈ S ∪ {v} := hB hu_in_B
      cases' hu_in_union with hu_in_S hu_eq_v
      · exact hu_in_S
      · simp at hu_eq_v
        rw [hu_eq_v] at hu_in_B
        contradiction

    exact hS B f B_subset_S hf w hw

/-- **Level 18: Removing a Redundant Vector (Theorem 2.10)**
If a vector $w$ in set $S$ is a linear combination of the other vectors in $S$, then removing $w$ from $S$ does not change the span. In symbols, if $w ∈ S$ and $w ∈ \span(S \setminus \{w\})$, then $\span(S) = \span(S \setminus \{w\})`. -/
theorem remove_redundant_span {S : Set V} {w : V}
  (hwS : w ∈ S) (hcomb : w ∈ span (S \ {w})) :
  span S = span (S \ {w}) := by
  -- First, `S \ {w} ⊆ S`, so span(S \ {w}) ⊆ span(S) by monotonicity.
  apply Set.eq_of_subset_of_subset (span_mono (Set.diff_subset _ _))
  · intro x hx
    -- x is in span S, so x is some linear combination of S.
    obtain ⟨t, f, htS, hf0, rfl⟩ := hx  -- x = ∑_{v ∈ t} f v • v with t ⊆ S.
    -- If w ∉ t, then actually x is a combination of S\{w} already.
    by_cases hw : w ∈ t
    -- Case 1: w ∉ t. Then t ⊆ S \ {w}, so x ∈ span(S \ {w}) directly.**
    · have : ↑t ⊆ S \ {w} := Set.subset_diff_singleton htS hw
      exact ⟨t, f, this, hf0, rfl⟩
    -- Case 2: w ∈ t. Replace w by its combination from hcomb.**
    · -- Let t' = t \ {w}. Note t' ⊆ S \ {w}.
      let t' := t.erase w
      have ht'S : ↑t' ⊆ S \ {w} := Set.subset_diff_singleton (htS) hw
      -- Obtain a combination of S\{w} that equals w (since w ∈ span(S\{w})).
      obtain ⟨u, g, hu, hg0, hw_sum⟩ := hcomb  -- w = ∑_{y ∈ u} g y • y, with u ⊆ S\{w}.
      -- Now express x, substituting the contribution of w.
      calc
        x = f w • w + t'.sum (fun v => f v • v)                   := by rw [Finset.sum_insert (Finset.not_mem_erase w t), Finset.erase_insert hw]
        _ = f w • (u.sum (fun y => g y • y)) + t'.sum (fun v => f v • v)  := by rw [hw_sum]  -- substitute w
        _ = u.sum (fun y => f w * g y) • y + t'.sum (fun v => f v • v)  := by rw [Finset.smul_sum, smul_assoc]
        _ = (u ∪ t').sum (fun z => h z • z)                       := by
            -- Define combined coefficients h for z in the union of u and t'.
            let h := (λ z => (if z ∈ u then f w * g z else 0) + (if z ∈ t' then f z else 0))
            have hz0 : ∀ z ∉ u ∪ t', h z = 0 := λ z hz => by simp [hz]
            -- Both u and t' are finite and subsets of S\{w}, so their union is too.
            have huv : ↑(u ∪ t') ⊆ S \ {w} := Set.union_subset hu ht'S
            -- The above sum is exactly ∑_{z ∈ u ∪ t'} h z • z by construction of h.
            exact (⟨u ∪ t', h, huv, hz0, rfl⟩ : ∃ (H : Finset V) (h : V → K), ↑H ⊆ S \ {w} ∧ (∀ z ∉ H, h z = 0) ∧ _)
      -- Thus x is expressed as a linear combination of S \ {w}.
      exact ⟨u ∪ t', h, huv, hz0, rfl⟩
