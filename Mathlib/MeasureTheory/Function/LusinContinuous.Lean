/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Lusin's theorem

There are many different versions of Lusin's theorem. All of them roughly say that a measurable
function is continuous on nearly all its domain. Different versions of Lusin's theorem can be
classified into roughly two types:

1. The first type considers measures that can be approximated (from inside) by closed/compact
sets and relies on Egoroff's theorem. In most classical textbooks, the codomain usually satisfies
some countability conditions. We relax this condition by showing that the image of an AEMeasurable
functions taking values in a pseudometrizable space is always contained in some separable space.

2. The second type considers measures that can be approximated by open sets and the proof does
not rely on Egoroff's theorem (see and). To prove this type of results, we introduce the concept of
smooth measures, which in particular are satisfied by outer regular sigma finite measures.

## Main results

## References
* https://www.jstor.org/stable/2320466
* On the continuity of measurable functions in Neighborhood Spaces by HM Schaerf

-/

@[expose] public section


noncomputable section

open scoped symmDiff

open MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace α]
  [TopologicalSpace β]

/-! ### Lusin's Theorem for InnerRegularWRT Measures -/

theorem SimpleFunc.exists_continuous_restrict [T2Space α] {ε : ℝ≥0∞} (hε : ε < μ univ)
    [μ.InnerRegular] (f : SimpleFunc α β) :
    ∃ s, IsCompact s ∧ (ε < μ s) ∧ ContinuousOn f s := by
  sorry

theorem StronglyMeasurable.exists_continuous_restrict [T2Space α] [PseudoEMetricSpace β]
    {ε : ℝ≥0∞} (hε : ε < μ univ) (hμ : μ.InnerRegularWRT IsCompact MeasurableSet) {f : α → β}
    (hf : StronglyMeasurable f) :
    ∃ s, IsCompact s ∧ (ε < μ s) ∧ ContinuousOn f s := by
  obtain ⟨g, hg⟩ := hf
  sorry

theorem NullMeasurable.exists_continuous_restrict {p : Set α → Prop}
    (hp : ∀ {ι} [Finite ι] {t : ι → Set α}, (∀ i : ι, p (t i)) → p (⋃ i, t i)) {ε : ℝ} (hε : 0 < ε)
    (hμ : μ.InnerRegularWRT p MeasurableSet) {f : α → β} [MeasurableSpace β]
    (hf : NullMeasurable f μ) :
    ∃ s, p s ∧ (μ sᶜ ≤ ENNReal.ofReal ε) ∧ ContinuousOn f s := by
  sorry


/-! ### Lusin's Theorem for Smooth Measures -/

theorem _root_.Set.iInter_eq_empty_of_eq_empty {i : ι} {f : ι → Set β} (h : f i = ∅) :
    ⋂ j, f j = ∅ :=
  subset_eq_empty (iInter_subset _ i) h

class Measure.Smooth (μ : Measure α) : Prop where
  smooth : ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r, 0 < r → ∃ U, IsOpen U ∧ μ (U ∆ A) ≤ r

instance [μ.OuterRegular] [SigmaFinite μ] : μ.Smooth where
  smooth A hA r hr := by
    have (n : ℕ) : ∃ U ⊇ spanningSets μ n ∩ A, IsOpen U ∧
        μ (U \ ((spanningSets μ n) ∩ A)) ≤ r * 2 ^ (-1 - n : ℤ) := by
      have hp : μ ((spanningSets μ n) ∩ A) ≠ ⊤ :=
        measure_ne_top_of_subset inter_subset_left (measure_spanningSets_lt_top μ n).ne
      have hq : r * 2 ^ (-1 - n : ℤ) ≠ 0 :=
        (ENNReal.mul_pos hr.ne.symm (ENNReal.zpow_pos (by simp) (by simp) (-1 - n)).ne.symm).ne.symm
      have hm := (measurableSet_spanningSets μ n).inter hA
      obtain ⟨U, hU⟩ := hm.exists_isOpen_diff_lt hp hq
      exact ⟨U, hU.1, hU.2.1, hU.2.2.2.le⟩
    choose U hsub ho hle using this
    refine ⟨⋃ n, U n, isOpen_iUnion ho, ?_⟩
    calc
    _ = μ ((⋃ n, U n) \ A) := by
      suffices ⋃ i, (spanningSets μ i) ∩ A ⊆ ⋃ i, U i from by simp_all [← iUnion_inter, symmDiff]
      exact iUnion_mono'' hsub
    _ ≤ ∑' n, μ (U n \ A) := by simp [iUnion_diff, measure_iUnion_le]
    _ ≤ ∑' n, μ (U n \ (((spanningSets μ n) ∩ A))) := by gcongr; exact inter_subset_right
    _ ≤ ∑' (n : ℕ), r * 2 ^ (-1 - n : ℤ) := by gcongr; apply hle
    _ = _ := by simp [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one]

@[simp]
lemma isTopologicalBasis_empty : IsTopologicalBasis {(∅ : Set α)} ↔ IsEmpty α where
  mp h := by simpa using h.diff_empty
  mpr h := ⟨by simp, by simp [Set.univ_eq_empty_iff.2], Subsingleton.elim ..⟩

theorem _root_.TopologicalSpace.exists_seq_basis (β) [TopologicalSpace β]
    [SecondCountableTopology β] :
    ∃ b : ℕ → Set β, IsTopologicalBasis (range b) := by
  obtain ⟨t, ht⟩ :=  TopologicalSpace.exists_countable_basis β
  by_cases! hn : t.Nonempty
  · obtain ⟨b, rfl⟩ := ht.1.exists_eq_range hn
    exact ⟨b, ht.2.2⟩
  · exact ⟨fun n => ∅, by simp_all⟩

theorem _root_.TopologicalSpace.IsTopologicalBasis.continuousOn_iff {b : Set (Set β)}
    (hb : IsTopologicalBasis b) (f : α → β) (s : Set α) :
    ContinuousOn f s ↔ ∀ t ∈ b, ∃ u, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  rw [continuousOn_iff']
  refine ⟨fun h t ht => h t (hb.isOpen ht), fun h t ht => ?_⟩
  obtain ⟨ι, g, rfl, hg⟩ := hb.open_eq_iUnion ht
  choose v hv he using (fun i => h (g i) (hg i))
  exact ⟨⋃ i, v i, isOpen_iUnion hv, by simp_all [iUnion_inter]⟩

theorem Measurable.exists_continuous_restrict_of_secondCountableTopology (μ : Measure α) [μ.Smooth]
    {f : α → β} [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : Measurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s, MeasurableSet s ∧ (μ sᶜ ≤ ε) ∧ ContinuousOn f s := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis β
  have hm (n : ℕ) := (hb.isOpen (mem_range_self n)).measurableSet.preimage hf
  have (n : ℕ) : ∃ U, IsOpen U ∧
    μ (U ∆ (f ⁻¹' (b n))) ≤ ε * 2 ^ (-1 - n : ℤ) := by
    refine Measure.Smooth.smooth (hm n) _ ?_
    exact ENNReal.mul_pos hε.ne.symm (ENNReal.zpow_pos (by simp) (by simp) (-1 - n)).ne.symm
  choose g ho hg using this
  refine ⟨(⋃ n, (g n ∆ (f ⁻¹' (b n))))ᶜ, (MeasurableSet.iUnion fun n => ?_).compl, ?_, ?_⟩
  · exact (ho n).measurableSet.symmDiff (hm n)
  · rw [compl_compl]
    calc
    _ ≤ ∑' n, μ (g n ∆ (f ⁻¹' (b n))) := measure_iUnion_le _
    _ ≤ ∑' (n : ℕ), ε * 2 ^ (-1 - n : ℤ) := ENNReal.tsum_le_tsum fun n => hg n
    _ = _ := by simp [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one]
  · rw [hb.continuousOn_iff]
    rintro - ⟨n, rfl⟩
    refine ⟨g n, ho n, subset_antisymm ?_ ?_⟩
    <;> rw [← diff_eq_empty, ← inter_diff_distrib_right, compl_iUnion, inter_iInter]
    <;> apply iInter_eq_empty_of_eq_empty (i := n)
    · simp [symmDiff, ← inter_left_comm]
    · simp [symmDiff, ← inter_assoc]

theorem AEMeasurable.exists_continuous_restrict_of_secondCountableTopology [μ.Smooth] {f : α → β}
    [SecondCountableTopology β] [MeasurableSpace β] [MeasurableEq β] [OpensMeasurableSpace α]
    [OpensMeasurableSpace β] (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s, NullMeasurableSet s μ ∧ (μ sᶜ ≤ ε) ∧ ContinuousOn f s := by
  have := hf
  obtain ⟨g, hg⟩ := hf
  obtain ⟨s, hs, hle, hc⟩ := hg.1.exists_continuous_restrict_of_secondCountableTopology μ hε
  refine ⟨s ∩ {x | f x = g x}, ?_, ?_, ?_⟩
  · exact hs.nullMeasurableSet.inter (nullMeasurableSet_eq_fun this hg.1.aemeasurable)
  · calc
    _ ≤ μ sᶜ + μ {x | f x = g x}ᶜ := by grw [compl_inter, measure_union_le]
    _ ≤ ε := by
      suffices μ {x | f x = g x}ᶜ = 0 from by simp_all
      simpa [EventuallyEq, ae_iff, ← compl_setOf] using hg.2
  · exact (hc.mono inter_subset_left).congr fun x hx => hx.2

end MeasureTheory
