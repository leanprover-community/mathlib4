/-
Copyright (c) 2025 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.Set.Card

/-!
# Sum of restrictions of measures

In this file we prove an upper bound on a sum of restrictions of a measure `μ`. This can be used
to compare `∫ x ∈ X, f x ∂μ` with `∑ i, ∫ x ∈ (s i), f x ∂μ`, where `s` is a cover of `X`.
-/

open Set Finset

lemma MeasureTheory.Measure.sum_restrict_le {α : Type*} [MeasurableSpace α] {ι : Type*}
    {μ : Measure α} (s : ι → Set α) {M : ℕ} (hs_meas : ∀ i, MeasurableSet (s i))
    (hs : ∀ y, {i | y ∈ s i}.encard ≤ M) :
    Measure.sum (fun i ↦ μ.restrict (s i)) ≤ M • μ.restrict (⋃ i, s i) := by
  classical
  refine le_iff.mpr (fun t ht ↦ ?_)
  rw [sum_apply _ ht]
  refine ENNReal.summable.tsum_le_of_sum_le (fun F ↦ ?_)
  have : Fintype (𝒫 (F : Set ι)) := F.finite_toSet.powerset.fintype
  -- `P` is a partition of `⋃ i ∈ F, s i` indexed by `C ∈ Cs` (nonempty subsets of `F`).
  -- `P` is a partition of `s i` when restricted to `C ∈ G i` (subsets of `F` containing `i`).
  let P (C : Set ι) := (⋂ i ∈ C, s i) ∩ (⋂ i ∈ ((F : Set ι) \ C), (s i)ᶜ)
  let Cs := (𝒫 (F : Set ι) \ {∅}).toFinset
  let G (i : ι) := { C | C ∈ 𝒫 F ∧ i ∈ C }
  have subset_F (C : Cs) : (C : Set ι) ⊆ F := (mem_toFinset.mp (Subtype.coe_prop C)).1
  have P_meas (C : Cs) : MeasurableSet (P C) :=
    MeasurableSet.biInter (F.countable_toSet.mono (subset_F C)) (fun i _ ↦ hs_meas i) |>.inter <|
      MeasurableSet.biInter (F.countable_toSet.mono diff_subset) (fun i _ ↦ (hs_meas i).compl)
  have P_cover {i : ι} (hi : i ∈ F) : s i ⊆ ⋃ C ∈ G i, P C :=
    fun x hx ↦ Set.mem_biUnion ⟨sep_subset _ (x ∈ s ·), ⟨hi, hx⟩⟩ <| by
      simp_rw [P, mem_diff, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_compl_iff]; tauto
  have iUnion_P : ⋃ C ∈ Cs, P C ⊆ ⋃ i, s i := by
    intro x hx
    simp_rw [Cs, toFinset_diff, toFinset_singleton, mem_sdiff, mem_iUnion] at hx
    have ⟨C, ⟨_, C_nonempty⟩, hxC⟩ := hx
    have ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr <| Finset.notMem_singleton.mp C_nonempty
    exact ⟨s i, ⟨i, rfl⟩, hxC.1 (s i) ⟨i, by simp [hi]⟩⟩
  have P_subset_s {i : ι} (hi : i ∈ F) {C : Set ι} (hiC : i ∈ C) : P C ⊆ s i := by
    intro x hx; simp only [mem_inter_iff, mem_iInter, P] at hx; exact hx.1 i hiC
  have mem_C {i : ι} (hi : i ∈ F) {C : Set ι} {x : α} (hx : x ∈ P C) (hxs : x ∈ s i) : i ∈ C := by
    rw [mem_inter_iff, mem_iInter₂, mem_iInter₂] at hx; exact of_not_not (hx.2 i ⟨hi, ·⟩ hxs)
  have C_subset_C {C₁ C₂ : Cs} {x : α} (hx : x ∈ P C₁ ∩ P C₂) : (C₁ : Set ι) ⊆ (C₂ : Set ι) :=
    fun i hi ↦ mem_C ((subset_F C₁) hi) hx.2 <| P_subset_s ((subset_F C₁) hi) hi hx.1
  calc ∑ i ∈ F, (μ.restrict (s i)) t
    _ ≤ ∑ i ∈ F, Measure.sum (fun (C : G i) ↦ μ.restrict (P C)) t :=
      F.sum_le_sum fun i hi ↦
        le_trans (restrict_mono_set μ (P_cover hi) t) (restrict_biUnion_le (G i) t)
    _ = ∑ i ∈ F, ∑' (C : G i), μ.restrict (P C) t := by simp_rw [Measure.sum_apply _ ht]
    _ = ∑' C, ∑ i ∈ F, (G i).indicator (fun C ↦ μ.restrict (P C) t) C := by
      rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]; simp_rw [← tsum_subtype (G _)]
    _ = ∑ C ∈ Cs, ∑ i ∈ F, C.indicator (fun _ ↦ (μ.restrict (P C)) t) i := by
      rw [sum_eq_tsum_indicator]
      congr with C; by_cases hC : C ∈ 𝒫 F <;> by_cases hC' : C = ∅ <;>
        simp [hC, hC', Cs, G, indicator, -mem_powerset_iff]
    _ = ∑ C ∈ Cs, {a ∈ F | a ∈ C}.card • μ.restrict (P C) t := by simp [indicator, ← sum_filter]
    _ ≤ ∑ C ∈ Cs, M • μ.restrict (P C) t := by
      refine sum_le_sum fun C hC ↦ ?_
      by_cases hPC : P C = ∅
      · simp [hPC]
      have hCM : C.encard ≤ M :=
        have ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hPC
        le_trans (encard_mono (mem_iInter₂.mp hx.1)) (hs x)
      have hC : C.Finite := finite_of_encard_le_coe hCM
      exact nsmul_le_nsmul_left (zero_le _) <| calc {a ∈ F | a ∈ C}.card
        _ ≤ hC.toFinset.card := card_mono <| fun i hi ↦ hC.mem_toFinset.mpr (F.mem_filter.mp hi).2
        _ = C.ncard          := ncard_eq_toFinset_card C hC |>.symm
        _ ≤ M                := ENat.toNat_le_of_le_coe hCM
    _ = M • (μ.restrict (⋃ C ∈ Cs, (P C)) t) := by
      have : ⋃ C ∈ Cs, P C = ⋃ (C : Cs), P C := Set.biUnion_eq_iUnion _ _
      rw [← smul_sum, this, μ.restrict_iUnion _ P_meas]
      · rw [Measure.sum_apply _ ht, Finset.tsum_subtype (f := fun i ↦ μ.restrict (P i) t)]
      · refine fun C₁ C₂ hC ↦ Set.disjoint_iff.mpr (fun x hx ↦ hC (Subtype.eq ?_))
        exact subset_antisymm (C_subset_C hx) (C_subset_C (Set.inter_comm _ _ ▸ hx))
    _ ≤ (M • μ.restrict (⋃ i, s i)) t := by
      rw [Measure.smul_apply]; exact nsmul_le_nsmul_right (μ.restrict_mono_set iUnion_P t) M
