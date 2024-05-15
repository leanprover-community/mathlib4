import KolmogorovExtension4.CompactSystem
import KolmogorovExtension4.AdditiveOfContinuous

open scoped ENNReal BigOperators

namespace MeasureTheory

variable {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}

-- `innerRegular` is defined only for a measure, hence we expand the definition to use it with a
-- content
lemma tendsto_zero_of_regular_addContent [Nonempty α] (hR : SetRing R) (m : AddContent R)
    (hs : ∀ n, s n ∈ R) (hs_anti : Antitone s) (hs_Inter : (⋂ n, s n) = ∅)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A (_ : A ∈ R) (ε : ℝ≥0∞) (_ : 0 < ε), ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε) :
    Filter.Tendsto (fun n ↦ m (s n)) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := ENNReal.exists_seq_pos_lt ε hε
  have h_reg' : ∀ n, ∃ K ∈ C, K ⊆ s n ∧ m (s n \ K) ≤ δ n :=
    fun n ↦ h_reg (s n) (hs n) (δ n) (hδ_pos n)
  choose t ht_mem_C ht_subset ht using h_reg'
  rw [Filter.eventually_atTop]
  have ht_empty : ⋂ n, t n = ∅ := Set.subset_eq_empty (Set.iInter_mono ht_subset) hs_Inter
  let S := hC.support ht_mem_C ht_empty
  have hS := hC.iInter_eq_empty ht_mem_C ht_empty
  have hS_nonempty : Finset.Nonempty S := by
    by_contra h
    simp only [S, Finset.not_nonempty_iff_eq_empty] at h
    simp only [h, Finset.not_mem_empty, Set.iInter_of_empty, Set.iInter_univ,
      Set.univ_eq_empty_iff, not_isEmpty_of_nonempty] at hS
  let N := Finset.max' S hS_nonempty
  have ht_empty' : ∀ n, N ≤ n → ⋂ i ≤ n, t i = ∅ := by
    intro n hn
    refine Set.subset_eq_empty ?_ hS
    simp only [Set.subset_iInter_iff]
    intro i hi
    refine Set.biInter_subset_of_mem ?_
    exact (Finset.le_max' S i hi).trans hn
  refine ⟨N, fun n hn ↦ ?_⟩
  calc m (s n) = m (⋂ i ≤ n, s i) := by
        congr
        exact le_antisymm (le_iInf₂ fun i hi ↦ hs_anti hi)
          (iInf₂_le (κ := fun i ↦ i ≤ n) (f := fun i _ ↦ s i) n le_rfl)
    _ = m ((⋂ i ≤ n, s i) \ (⋂ i ≤ n, t i)) := by
        suffices ⋂ i ≤ n, t i = ∅ by
          simp only [this, Set.diff_empty]
        exact ht_empty' n hn
    _ ≤ m (⋃ i ≤ n, (s i \ t i)) := by
        refine AddContent.mono m hR.setSemiring ?_ ?_ ?_
        · exact hR.diff_mem (hR.iInter_le_mem hs n) (hR.iInter_le_mem (fun i ↦ hCR (ht_mem_C i)) n)
        · exact hR.iUnion_le_mem (fun i ↦ hR.diff_mem (hs i) (hCR (ht_mem_C i))) n
        · rw [Set.diff_iInter]
          refine Set.iUnion_mono (fun i ↦ ?_)
          by_cases hin : i ≤ n
          · simp only [hin, Set.iInter_true, Set.iUnion_true]
            refine Set.diff_subset_diff ?_ subset_rfl
            exact Set.biInter_subset_of_mem hin
          · simp only [hin, Set.iInter_of_empty, Set.diff_univ, Set.iUnion_of_empty,
              Set.empty_subset]
    _ ≤ ∑ i in Finset.range (n + 1), m (s i \ t i) :=
        addContent_iUnion_le m hR (fun i ↦ hR.diff_mem (hs i) (hCR (ht_mem_C i))) n
    _ ≤ ∑ i in Finset.range (n + 1), δ i := Finset.sum_le_sum (fun i _ ↦ ht i)
    _ ≤ ∑' i, δ i := ENNReal.sum_le_tsum _
    _ ≤ ε := hδ_sum.le

lemma AddContent.sigma_additive_of_regular [Nonempty α] (hR : SetRing R) (m : AddContent R)
    (hm_ne_top : ∀ {s} (_ : s ∈ R), m s ≠ ∞)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A (_ : A ∈ R) (ε : ℝ≥0∞) (_ : 0 < ε), ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε)
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ R) (hUf : (⋃ i, f i) ∈ R) (h_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine sigma_additive_addContent_of_tendsto_zero hR m hm_ne_top ?_ hf hUf h_disj
  intro s hs hs_anti hs_iInter
  exact tendsto_zero_of_regular_addContent hR m hs hs_anti hs_iInter hC hCR h_reg

end MeasureTheory
