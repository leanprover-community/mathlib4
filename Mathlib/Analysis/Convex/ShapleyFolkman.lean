import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped Pointwise BigOperators
open Set Finset

variable {ι : Type*}
variable {E : Type*}

section SetSums

variable [AddCommMonoid E]

#check Set.mem_add
#check Set.mem_zero
#check Finset.sum_insert
#check Finset.sum_eq_zero
#check Finset.induction_on
#check Caratheodory.minCardFinsetOfMemConvexHull
#check Caratheodory.minCardFinsetOfMemConvexHull_subseteq
#check Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull
#check Caratheodory.mem_minCardFinsetOfMemConvexHull
#check convexHull_eq_union
#check eq_pos_convex_span_of_mem_convexHull

example (A B : Set E) (x y : E) (hx : x ∈ A) (hy : y ∈ B) :
    x + y ∈ A + B := by
  exact ⟨x, hx, y, hy, rfl⟩

example (A B : Set E) (z : E) (hz : z ∈ A + B) :
    ∃ x ∈ A, ∃ y ∈ B, x + y = z := by
  simpa [Set.mem_add] using hz

lemma mem_finset_sum_sets_of_forall
    (s : Finset ι) (A : ι → Set E) (x : ι → E)
    (hx : ∀ i ∈ s, x i ∈ A i) :
    (∑ i ∈ s, x i) ∈ (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      rw [Finset.sum_insert has]
      exact ⟨x a, hx a (by simp), ∑ i ∈ s, x i,
        ih (fun i hi => hx i (by simp [hi])), rfl⟩

lemma mem_finset_sum_sets_exists
    (s : Finset ι) (A : ι → Set E) (z : E)
    (hz : z ∈ (∑ i ∈ s, A i)) :
    ∃ x : ι → E,
      (∀ i ∈ s, x i ∈ A i) ∧
      ∑ i ∈ s, x i = z := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i hi
        simp at hi
      · simpa using hz.symm

  | insert a s has ih =>
      rw [Finset.sum_insert has] at hz
      rcases hz with ⟨xa, hxa, ys, hys, hsum⟩
      rcases ih ys hys with ⟨x, hx, hxsum⟩

      refine ⟨Function.update x a xa, ?_, ?_⟩

      · intro i hi
        by_cases hia : i = a
        · subst hia
          simp [Function.update, hxa]
        · have his : i ∈ s := by
            simpa [hia] using hi
          simp [Function.update, hia, hx i his]

      · rw [Finset.sum_insert has]

        have hsum_update :
            ∑ i ∈ s, Function.update x a xa i = ∑ i ∈ s, x i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hia : i ≠ a := by
            intro h
            exact has (h ▸ hi)
          simp [Function.update, hia]

        calc
          Function.update x a xa a + ∑ i ∈ s, Function.update x a xa i
              = xa + ∑ i ∈ s, x i := by
                  rw [hsum_update]
                  simp [Function.update]
          _ = xa + ys := by
                  rw [hxsum]
          _ = z := by
                  simpa using hsum

end SetSums
lemma shapley_folkman_mem_of_choice
    {ι E : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    (S : ι → Set E)
    (x : E)
    (y : ι → E)
    (bad : Finset ι)
    (hy_conv : ∀ i ∈ bad, y i ∈ convexHull ℝ (S i))
    (hy_good : ∀ i ∈ (Finset.univ \ bad), y i ∈ S i)
    (hysum : ∑ i ∈ (Finset.univ : Finset ι), y i = x) :
    x ∈
      (∑ i ∈ bad, convexHull ℝ (S i)) +
      (∑ i ∈ (Finset.univ \ bad), S i) := by
  classical
  rw [Set.mem_add]
  refine ⟨
    ∑ i ∈ bad, y i,
    ?_,
    ∑ i ∈ (Finset.univ \ bad), y i,
    ?_,
    ?_
  ⟩
  · apply mem_finset_sum_sets_of_forall
    intro i hi
    exact hy_conv i hi
  · apply mem_finset_sum_sets_of_forall
    intro i hi
    exact hy_good i hi
  · have hbad_subset : bad ⊆ (Finset.univ : Finset ι) := by
      intro i hi
      simp
    have hsum_sdiff :
        ∑ i ∈ ((Finset.univ : Finset ι) \ bad), y i =
          (∑ i ∈ (Finset.univ : Finset ι), y i) - ∑ i ∈ bad, y i := by
      simpa using
        (Finset.sum_sdiff
          (s := (Finset.univ : Finset ι))
          (t := bad)
          (f := y)
          hbad_subset)
    rw [hsum_sdiff]
    rw [hysum]
    simp [sub_eq_add_neg, add_left_comm]

lemma exists_caratheodory_finset
    {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (S : Set E)
    (x : E)
    (hx : x ∈ convexHull ℝ S) :
    ∃ T : Finset E,
      ↑T ⊆ S ∧
      x ∈ convexHull ℝ (T : Set E) ∧
      AffineIndependent ℝ (fun p : T => (p : E)) := by
  classical
  refine ⟨Caratheodory.minCardFinsetOfMemConvexHull hx, ?_, ?_, ?_⟩
  · exact Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  · exact Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  · simpa using Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx

lemma shapley_folkman_exists_choice
    {ι E : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : ι → Set E)
    (x : E)
    (hx : x ∈ (∑ i ∈ (Finset.univ : Finset ι), convexHull ℝ (S i))) :
    ∃ y : ι → E,
    ∃ bad : Finset ι,
      bad.card ≤ Module.finrank ℝ E ∧
      (∀ i ∈ bad, y i ∈ convexHull ℝ (S i)) ∧
      (∀ i ∈ (Finset.univ \ bad), y i ∈ S i) ∧
      ∑ i ∈ (Finset.univ : Finset ι), y i = x := by
  classical
  rcases mem_finset_sum_sets_exists
      (Finset.univ : Finset ι)
      (fun i => convexHull ℝ (S i))
      x
      hx with
    ⟨y₀, hy₀, hy₀sum⟩

  have hy₀_all : ∀ i : ι, y₀ i ∈ convexHull ℝ (S i) := by
    intro i
    exact hy₀ i (Finset.mem_univ i)

  have hcar : ∀ i : ι,
      ∃ T : Finset E,
        ↑T ⊆ S i ∧
        y₀ i ∈ convexHull ℝ (T : Set E) ∧
        AffineIndependent ℝ (fun p : T => (p : E)) := by
    intro i
    exact exists_caratheodory_finset (S i) (y₀ i) (hy₀_all i)

  let T : ι → Finset E := fun i => Classical.choose (hcar i)

  have hT_subset : ∀ i : ι, ↑(T i) ⊆ S i := by
    intro i
    exact (Classical.choose_spec (hcar i)).1

  have hy₀_mem_T : ∀ i : ι, y₀ i ∈ convexHull ℝ (T i : Set E) := by
    intro i
    exact (Classical.choose_spec (hcar i)).2.1

  have hT_affineIndependent :
      ∀ i : ι, AffineIndependent ℝ (fun p : T i => (p : E)) := by
    intro i
    exact (Classical.choose_spec (hcar i)).2.2

  -- Checkpoint:
  -- For every index `i`, we now have a finite Carathéodory set `T i`.
  --
  -- Next mathematical step:
  -- convert `hy₀_mem_T i` into positive convex coefficients over `T i`,
  -- then set up the minimization / perturbation argument.
  sorry

theorem shapley_folkman
    {ι E : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : ι → Set E)
    (x : E)
    (hx : x ∈ (∑ i ∈ (Finset.univ : Finset ι), convexHull ℝ (S i))) :
    ∃ t : Finset ι,
      t.card ≤ Module.finrank ℝ E ∧
      x ∈
        (∑ i ∈ t, convexHull ℝ (S i)) +
        (∑ i ∈ (Finset.univ \ t), S i) := by
  classical
  rcases shapley_folkman_exists_choice S x hx with
    ⟨y, bad, hbad_card, hy_bad, hy_good, hysum⟩
  refine ⟨bad, hbad_card, ?_⟩
  exact shapley_folkman_mem_of_choice S x y bad hy_bad hy_good hysum
