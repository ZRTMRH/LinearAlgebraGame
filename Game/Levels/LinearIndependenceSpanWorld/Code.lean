import Game.Levels.VectorSpaceWorld.Level05

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--  Linear Combination**
A vector $x$ is called a **linear combination** of a set $S$ if it can be expressed as a finite sum of elements of $S$ scaled by scalars in the field. Here we formalize this concept. ∑ v in s, f v • v-/
def is_linear_combination (S : Set V) (x : V) : Prop :=
  ∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (x = Finset.sum s (fun v => f v • v))

theorem linear_combination_of_mem {S : Set V} {v : V} (hv : v ∈ S) : is_linear_combination K V S v := by
  unfold is_linear_combination
  use {v}
  use (fun w => if w = v then (1 : K) else 0)
  simp
  exact hv

/-- **Level 7: Span**
The **span** of a set $S$ is the set of all linear combinations of elements of $S`. It is the smallest subspace containing $S`. -/
def span (S : Set V) : Set V :=
  { x : V | is_linear_combination K V S x }

theorem mem_span_of_mem {S : Set V} {v : V} (hv : v ∈ S) : v ∈ span K V S := by
  unfold span
  simp
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
  exact subset_trans hsA hAB
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
theorem subset_linear_independent [Field K] [AddCommGroup V][VectorSpace K V] {A B : Set V} (hBsubA : B ⊆ A) (hA : linear_independent_v K V A) :
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
  by_cases h : v ∈ (s ∪ t)
  unfold linear_independent_v at hS

  -- Think about the forwards proof. What set and function are we summing over when applying the
  -- linear independence of S?
  specialize hS (s ∪ t) (f - g)

  -- This line simply fixes some issues with type casting
  rw[Finset.coe_union] at hS

  -- Set.union_subset is a proof that if s ⊆ S and t ⊆ S, s ∪ t ⊆ S
  -- This solves the first requirement in hS
  specialize hS (Set.union_subset hs ht)

  have lemmaSumDiffEqZero : (Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0 := by
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
    simp

  -- Now, we want to prove the second requirement in hS
  specialize hS lemmaSumDiffEqZero

  --Now, we change the form of hS to fit our goal
  specialize hS v h

  -- We know now from hS that f v - g v = 0, so it is simple to show f v = g v
  exact sub_eq_zero.1 hS

  -- Finset.not_mem_union shows that if v ∉ s ∪ t, then v ∉ s and v ∉ t
  rw[Finset.not_mem_union] at h
  cases' h with hS hT

  -- Now, we use hf0 and hg0 to show both sides of the equation are 0
  rw[hf0 v hS, hg0 v hT]

theorem linear_independent_insert_of_not_in_span
  {S : Set V} {v : V}
  (hS : linear_independent_v K V S)
  (hv_not_span : v ∉ span K V S):
  linear_independent_v K V (S ∪ {v}) := by
    -- First, unfold the definitions, intro the variables and hypotheses we need, and simp where nescessary
    unfold linear_independent_v at *
    intros s f hs hf w hw
    unfold span at *
    unfold is_linear_combination at *
    simp at hv_not_span

    -- We want to prove two seperate cases: v ∈ s and v ∉ s. If v ∉ s, then we know s ⊆ S, so since S
    -- is linearly independent, so is s. If v ∈ s, then we have more work to do.
    by_cases hvIns : v ∈ s

    -- Case 1: v ∈ s
    -- Here, we remove v from the sum on s, to get a sum over s \ {v} ⊆ S.
    rw [Finset.sum_eq_sum_diff_singleton_add hvIns] at hf

    -- Here, we want to show that ↑(s \ {v}) ⊆ S. This helps us use our hypotheses on sums over s \ {v}
    -- We start by introducing an arbitrary x ∈ ↑(s \ {v}), then simp to turn the statement into pure logic
    -- From there, as long as we remember how to solve logic problems and simp wherever nescessary, the proof is simple
    have subset : ↑(s \ {v}) ⊆ S := by
      intros x hx
      simp at hx
      cases' hx with xs xNev
      have xInUnion := hs xs
      simp at xInUnion
      cases' xInUnion with xEqv xInS
      exfalso
      exact xNev xEqv
      exact xInS

    -- This is our important lemma. If we know f(v) = 0, then we know that the sum over s \ {v} is also
    -- equal to 0, which by the linear independence of S means that f(w) = 0 for w ∈ s \ {v}, which will finish the proof
    have lemma_fv_zero : f v = 0 := by
      -- We use the by_contra tactic here, which assumes the opposite of the goal, and changes the goal to False
      by_contra hfv_ne_zero

      -- If f(v) ≠ 0, we can represent v as a linear combination of s \ {v}. This is not possible since
      -- v ∉ span S, completing our contradiction
      have hvLinearCombo : v = (s \ {v}).sum (fun x => (-(f v)⁻¹ * (f x)) • x) := by
        -- This simp only tactic allows us to rewrite using theorems inside a function, which cannot be done with just rw
        simp only [mul_smul]

        -- We now factor out a term of -(f v)⁻¹ from the sum, and rewrite using hf
        rw[(Finset.smul_sum (r := -(f v)⁻¹) (f := fun x => f x • x) (s := (s \ {v}))).symm]
        rw [(neg_add_self ((f v) • v)).symm] at hf
        rw[add_right_cancel hf]

        -- Now, this is a simple algebra problem, which needs simp and some simple theorems
        simp
        rw[(mul_smul (f v)⁻¹ (f v) v).symm]
        rw[inv_mul_cancel hfv_ne_zero, one_smul]

      -- Now, we are able to use the fact that v ∉ span S to find our contradiction
      specialize hv_not_span (s \ {v})
      specialize hv_not_span subset (fun x => -(f v)⁻¹ * (f x))
      exact hv_not_span hvLinearCombo

    -- We now consider two cases: w = v or w ≠ v. If w = v, our lemma is our goal. If w ≠ v, we need
    -- to use the linear independence of S
    by_cases hw2 : w = v
    rw[hw2]
    exact lemma_fv_zero

    -- We can use our lemma to show that the sum over s \ {v} is equal to 0
    rw[lemma_fv_zero] at hf
    simp at hf

    -- Since our linear independence of S will only show that f is 0 on s \ {v}, we need to show that
    -- w ∈ s \ {v}. This only requires simp and our previously known hypotheses
    have hwInS : w ∈ s \ {v} := by
      simp
      constructor
      exact hw
      exact hw2

    -- Now, we can apply all of our hypotheses to close the goal
    exact hS (s \ {v}) f subset hf w hwInS

    -- Case 2: v ∉ s
    -- We now need to show that s ⊆ S, and we can use the linear independence of S to show s is linearly independent
    have s_subset_S : ↑s ⊆ S := by
      -- First, we introduce an arbitrary u ∈ s
      intro u hu_in_s

      -- Since u ∈ s ⊆ S ∪ {v}, either u ∈ S or u ∈ {v}. We solve these cases seperately
      cases' hs hu_in_s with hu_in_S hu_eq_v

      -- If u ∈ S, our goal is done
      exact hu_in_S

      -- If u ∈ {v}, simp will change the hypothesis to u = v, which then creates a contradiction
      simp at hu_eq_v
      rw [hu_eq_v] at hu_in_s
      exfalso
      exact hvIns hu_in_s

    -- Now, we can use the linear independence of S to finish the proof
    exact hS s f s_subset_S hf w hw

theorem remove_redundant_span
  {S : Set V} {w : V} (hcomb : w ∈ span K V (S \ {w})) :
  span K V S = span K V (S \ {w}) := by
  -- We will prove this result by showing the two sets are subsets of each other, which means they are equal.
  apply Set.eq_of_subset_of_subset

  -- First subset : span K V S ⊆ span K V (S \ {w}). This is the hard step
  -- The broad idea here is that for any linear combination of S, we take any copies of w and replace them with the
  -- way we are able to express w as a linear combination of elements of (S \ {w}). This is now a linear
  -- combination of S \ {w}

  -- First, we introduce a random element of span K V S, x, and unfold and simp our definitions
  intro x hx
  unfold span at *
  unfold is_linear_combination at *
  simp at *

  -- Now, we obtain from our two statements, getting two sets and functions on those sets summing to
  -- x and w respectively.
  obtain ⟨sw, hsw, fw, hfw⟩ := hcomb
  obtain ⟨sx, hsx, fx, hfx⟩ := hx

  -- We now prove it by cases of whether w is included in the liner combination to get x. If it is,
  -- the proof continues. If not, then the linear combination to get x doesn't include w, so is already in S \ {w}
  by_cases hw : w ∈ sx

  -- First case : w ∈ sx
  -- The set we are summing over is the union of the sets the two functions are defined on, excluding w.
  use sw ∪ (sx \ {w})

  -- Our goal is an and statement, so constructor splits it into two goals
  constructor

  -- Here, we only need to prove each set we are unioning is a subset of S \ {w}. Both of these steps
  -- are simple, and only need simp and exact?
  rw[Finset.coe_union]
  apply Set.union_subset hsw
  simp
  exact subset_trans hsx (Set.subset_insert w S)

  -- Now, in order to simplify the set we are summing over, we want to prove sw ∪ (sx \ {w}) = (sw ∪ sx) \ {w}
  -- This will allow us to more easily manipulate the sums in the future.
  have set_eq : sw ∪ (sx \ {w}) = (sw ∪ sx) \ {w} := by
    -- This acts similarly to Set.eq_of_subset_of_subset, but works on Finsets instead of Sets
    apply Finset.Subset.antisymm_iff.2
    constructor

    -- Case 1 : Proving sw ∪ sx \ {w} ⊆ (sw ∪ sx) \ {w}
    -- intro to get an arbitrary element in sw ∪ sx \ {w}
    intro x hx

    -- The two simp statements change the "\ {w}" into logic which is easier to work with than set notation
    simp
    simp at hx

    -- Constructor splits the and statement, and tauto solves the first goal, since it can be proven entirely by logic
    constructor
    tauto

    -- Now, we split hx into the two cases using cases'.
    cases' hx with hInsw hInsx

    -- Case 1a: x ∈ sw
    -- We need to prove x ≠ w, so we assume x = w, then by the definition of subsets, we can get w ∈ S \ {w}
    -- Simp at hContra will relize that we have a contradiction and solve the goal
    intro hEqW
    rw[hEqW] at hInsw
    have hContra := hsw hInsw
    simp at hContra

    -- Case 1b: x ∈ sx \ {w}
    -- Since x ∈ sx \ {w}, clearly x ≠ w
    exact hInsx.2

    -- Case 2: Proving (sw ∪ sx) \ {w} ⊆ sw ∪ sx \ {w}
    -- Again, we intro an arbirtary x and simp
    intro x hx
    simp
    simp at hx

    -- We now use cases' on our and andor statements
    cases' hx with hl hr
    cases' hl with hInsw hInsx

    -- `left` lets us prove only the left side of an or goal. This is exactly one of out hypotheses
    left
    exact hInsw

    -- `right` acts similarly to `left`. We need to now split the goal to prove it, but it is still two exact statements
    right
    constructor
    exact hInsx
    exact hr

  -- Now that we have our proof of the set equality, we can work on defining the function we will use
  -- We need to first adapt the first function, fx in order to have it be 0 everywhere where it is not
  -- needed. This allows us to sum on a larger set than it was originally made for without causing problems
  let fx' := fun v => (if v ∈ sx then fx v else 0)
  have hfx' : fx' = (fun v => (if v ∈ sx then fx v else 0)) := rfl

  -- We want to prove that summing fx' v • v gives us the value we want.
  have fx'_sum : x - (fx w • w) = (sw ∪ (sx \ {w})).sum (fun v => fx' v • v) := by

    -- To get rid of the {w}, we use the set equality we proved earlier
    rw[set_eq]

    -- Also, we want to move the fx w • w to the other side. This allows us to use a theorem later
    apply add_right_cancel (b := fx w • w)
    simp

    -- We also want the term fx w to be fx' w to match the function we are summing.
    -- This just needs our definition of fx' and some simp statments, along with our proof that w ∈ sx
    have hfx'w : fx w = fx' w := by
      rw[hfx']
      simp only [hw]
      simp

    -- We can now rewrite using this theorem and now use Finset.sum_eq_sum_diff_singleton_add. This theorem
    -- states that we can remove an element we are summing over and add it on to the end, which allows
    -- us to remove the {w} from sx. It does need a proof that {w} ∈ (sw ∪ sx), which is what Finset.mem_union_right is doing
    -- After this, some rws, simp and exact will finish the proof
    rw[hfx'w]
    rw[(Finset.sum_eq_sum_diff_singleton_add (Finset.mem_union_right sw hw) (fun v => fx' v • v)).symm]
    rw[hfx']
    simp
    exact hfx

  -- Now, we create the second important function, fw', which is fx w * fw on sw, and 0 everywhere else
  let fw' := fun v => if v ∈ sw then fx w * fw v else 0
  have hfw' : fw' = (fun v => if v ∈ sw then fx w * fw v else 0) := rfl

  -- We want to show that summing over this function will get fx w • w
  have fw'_sum : fx w • w = (sw ∪ (sx \ {w})).sum (fun v => fw' v • v) := by
    -- We rewrite with the definition of fw', and simp is able to clean up a lot
    rw[hfw']
    simp
    simp only [mul_smul]

    -- We factor out the term of fx w, and the proof is done
    rw[(Finset.smul_sum (r := fx w) (s := sw) (f := fun v => fw v • v)).symm]
    rw[hfw]

  -- Now, we combine the two functions to get our linear combination for x
  use fun v => fx' v + fw' v

  -- simp is able to distribute out into two sums, which can be split apart by Finset.sum_add_distrib
  -- Then, we rewrite with the values we obtained for the two sums, and simp finishes the proof
  simp only [add_smul]
  rw[Finset.sum_add_distrib, fx'_sum.symm, fw'_sum.symm]
  simp

  -- Now, we are on the second case, that w ∉ sx. We simply use the same s and f we used for x, since
  use sx
  constructor
  exact Set.subset_diff_singleton hsx hw
  use fx

  -- Now, we are on the second part of the proof, showing that span K V (S \ {w}) ⊆ span K V S
  -- We already have span_mono, which along with proving S \ {w} ⊆ S, finishes the proof
  apply span_mono
  exact Set.diff_subset S {w}
