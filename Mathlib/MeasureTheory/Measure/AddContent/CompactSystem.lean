/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.Topology.Compactness.CompactSystem

/-!
# σ-additivity of inner regular contents

An additive content on a ring of sets which is inner regular with respect to a compact system
contained in the ring is σ-additive.

## Main statements

* `tendsto_zero_of_innerRegular_addContent`: such a content is continuous at `∅`.
* `addContent_iUnion_eq_sum_of_innerRegular`: such a content is σ-additive, if it takes finite
  values.
-/

public section

open Filter Set

open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}

/-- Let `m` be an additive content on a ring of sets `R`, inner regular with respect to a compact
system `C ⊆ R`: every set of `R` can be approximated from inside by sets of `C`. Then `m` is
continuous at `∅`: if `s` is a decreasing sequence of sets of `R` with empty intersection, then
`m (s n)` tends to `0`. -/
lemma tendsto_zero_of_innerRegular_addContent (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hs : ∀ n, s n ∈ R) (hs_anti : Antitone s) (hs_iInter : ⋂ n, s n = ∅)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A ∈ R, ∀ ε, 0 < ε → ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε) :
    Tendsto (fun n ↦ m (s n)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose t ht_mem_C ht_subset ht using fun n ↦ h_reg (s n) (hs n) (δ n) (mod_cast hδ_pos n)
  have ht_mem n : t n ∈ R := hCR (ht_mem_C n)
  -- the sets `t n` have empty intersection, hence finitely many of them already do
  obtain ⟨N, hN⟩ := hC t ht_mem_C (subset_eq_empty (iInter_mono ht_subset) hs_iInter)
  refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  have hs_eq : dissipate s n = s n :=
    Subset.antisymm (dissipate_subset le_rfl) (subset_iInter₂ fun i hi ↦ hs_anti hi)
  calc m (s n) = m (dissipate s n \ dissipate t n) := by
        rw [subset_eq_empty (antitone_dissipate hn) hN, sdiff_empty, hs_eq]
    _ ≤ m (⋃ i ≤ n, (s i \ t i)) := by
        refine addContent_mono hR.isSetSemiring
          (hR.sdiff_mem (hR.iInter_le_mem hs n) (hR.iInter_le_mem ht_mem n))
          (hR.iUnion_le_mem (fun i ↦ hR.sdiff_mem (hs i) (ht_mem i)) n) ?_
        rintro x ⟨hxs, hxt⟩
        simp only [mem_dissipate, not_forall, mem_iUnion, Set.mem_sdiff] at hxs hxt ⊢
        grind
    _ = m (⋃ i ∈ Finset.range (n + 1), (s i \ t i)) := by simp only [Finset.mem_range_succ_iff]
    _ ≤ ∑ i ∈ Finset.range (n + 1), m (s i \ t i) :=
        addContent_biUnion_le hR fun i _ ↦ hR.sdiff_mem (hs i) (ht_mem i)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (δ i : ℝ≥0∞) := Finset.sum_le_sum fun i _ ↦ ht i
    _ ≤ ∑' i, (δ i : ℝ≥0∞) := ENNReal.sum_le_tsum _
    _ ≤ ε := hδ_sum.le

/-- An additive content with finite values on a ring of sets `R`, which is inner regular with
respect to a compact system `C ⊆ R`, is σ-additive. -/
lemma addContent_iUnion_eq_sum_of_innerRegular (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hm_ne_top : ∀ s ∈ R, m s ≠ ∞)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A ∈ R, ∀ ε, 0 < ε → ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε)
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ R) (hUf : (⋃ i, f i) ∈ R)
    (h_disj : Pairwise (Function.onFun Disjoint f)) :
    m (⋃ i, f i) = ∑' i, m (f i) :=
  addContent_iUnion_eq_sum_of_tendsto_zero hR m hm_ne_top
    (fun _ hs hs_anti hs_iInter ↦
      tendsto_zero_of_innerRegular_addContent hR m hs hs_anti hs_iInter hC hCR h_reg)
    hf hUf h_disj

end MeasureTheory
