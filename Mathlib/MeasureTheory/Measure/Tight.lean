/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# (Pre-)tight measures

## Main definitions

* `IsPretight`: A measure `μ` is pre-tight if for all `0 < ε`, there exists `K` totally bounded such
  that `μ Kᶜ ≤ ε`.
* `IsTight`: A measure `μ` is tight if for all `0 < ε`, there exists `K` compact such that
  `μ Kᶜ ≤ ε`.
* `IsTightSet`: A set of measures `S` is tight if for all `0 < ε`, there exists `K` compact such
  that for all `μ` in `S`, `μ Kᶜ ≤ ε`.

## Main statements

*

## Notation


## Implementation details


-/
open Topology Filter Uniformity Uniform MeasureTheory Set

namespace MeasureTheory

variable {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}

lemma aux1 [IsFiniteMeasure μ] (K : ℕ → Set α) (h : μ (⋃ n, K n) = μ Set.univ) :
    ∀ ε > 0, ∃ n, μ (Set.Accumulate K n) ≥ μ Set.univ - ε := by
  rintro ε hε
  have : Filter.Tendsto (μ ∘ Set.Accumulate K) Filter.atTop (nhds (μ (⋃ n, Set.Accumulate K n))) :=
    MeasureTheory.tendsto_measure_iUnion Set.monotone_accumulate
  rw [ENNReal.tendsto_atTop] at this
  have hLε : ∀ ε > 0, ∃ n, μ (Set.Accumulate K n) ≥ μ (⋃ n, Set.Accumulate K n) - ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := this ε hε
    use n
    simp_all only [Function.comp_apply, Set.mem_Icc, tsub_le_iff_right, le_refl]
  obtain ⟨n, hn⟩ := hLε ε hε
  use n
  · rw [← h, ← Set.iUnion_accumulate]
    exact hn
  · rw [Set.iUnion_accumulate, h]
    exact measure_ne_top μ Set.univ

lemma aux2 [IsFiniteMeasure μ] [TopologicalSpace α] [OpensMeasurableSpace α]
    (K : ℕ → Set α) (hKclosed : ∀ n, IsClosed (K n)) (h : μ (⋃ n, K n) = μ Set.univ) :
    ∀ ε > 0, ∃ n, μ ((Set.Accumulate K n)ᶜ) ≤ ε := by
  rintro ε hε
  obtain ⟨n, hn⟩ := aux1 K h ε hε
  use n
  have hK2 : IsClosed (Set.Accumulate K n) :=
      Set.Finite.isClosed_biUnion instFiniteSubtypeLeToLE (fun i _ => hKclosed i)
  rw [measure_compl hK2.measurableSet (measure_ne_top μ _)]
  exact tsub_le_iff_tsub_le.mp hn

/-- A measure `μ` is separable if there is a separable set `S` such that `μ S = μ Set.univ`. -/
 def IsSeparable [TopologicalSpace α] (μ : Measure α) : Prop :=
   ∃ S : Set α, TopologicalSpace.IsSeparable S ∧ μ S = μ Set.univ

/-- A measure `μ` is tight if for all `0 < ε`, there exists `K` compact such that `μ Kᶜ ≤ ε`.
This is formulated in terms of filters for simplicity, and proven equivalent to the usual definition
in `iff_compact_sets`. -/
def IsTight (μ : Measure α) : Prop := Tendsto μ (cocompact α).smallSets (𝓝 0)

namespace IsTight

lemma iff_compact_sets {μ : Measure α} :
    IsTight μ ↔ ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) ≤ ε := by
  simp only [IsTight, ne_eq, ENNReal.zero_ne_top, not_false_eq_true, ENNReal.tendsto_nhds,
    zero_le, tsub_eq_zero_of_le, zero_add, mem_Icc, true_and,
    eventually_smallSets, mem_cocompact]
  apply forall₂_congr ; rintro ε - ; constructor
  · rintro ⟨A, ⟨K, h1, h2⟩, hA⟩
    exact ⟨K, h1, hA Kᶜ h2⟩
  · rintro ⟨K, h1, h2⟩
    refine ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA => μ.mono hA |>.trans h2⟩

lemma of_le_isTight {μ ν : Measure α} (h : μ ≤ ν) (hν : IsTight ν) : IsTight μ := by
  rw [iff_compact_sets] at *
  intro ε hε
  obtain ⟨K, hK, hKc⟩ := hν ε hε
  exact ⟨K, hK, le_trans (h Kᶜ) hKc⟩

lemma of_restrict_isTight {μ : Measure α} {U : Set α} (hν : IsTight μ) :
    IsTight (μ.restrict U) := by
  rw [iff_compact_sets] at *
  intro ε hε
  obtain ⟨K, hK, hKc⟩ := hν ε hε
  exact ⟨K, hK, le_trans (μ.restrict_le_self _) hKc⟩

lemma add {μ ν : Measure α} (hμ : IsTight μ) (hν : IsTight ν) : IsTight (μ + ν) := by
  have := Filter.Tendsto.add hμ hν
  simp only [add_zero] at this
  exact this

lemma const_mul {μ : Measure α} (c : NNReal) (hμ : IsTight μ) : IsTight (c • μ) := by
  rw [iff_compact_sets] at *
  intro ε hε
  have hεc : ε / c > 0 := by
    simp only [ENNReal.div_pos_iff, ne_eq, ENNReal.coe_ne_top, not_false_eq_true,
      and_true, hε.ne']
  obtain ⟨K, hK, hKc⟩ := hμ (ε / c) hεc
  exact ⟨K, hK, ENNReal.mul_le_of_le_div' hKc⟩

instance [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α] [hk: IsFiniteMeasureOnCompacts μ]
    [h : Fact (IsTight μ)] : IsFiniteMeasure μ := by
  obtain ⟨_, hK, hμ⟩ := (iff_compact_sets.mp h.out) 1 (zero_lt_one)
  have := (MeasureTheory.measure_add_measure_compl (μ := μ) hK.isClosed.measurableSet).symm
  have : μ Set.univ < ⊤ := by
    rw [this, WithTop.add_lt_top]
    exact ⟨hk.lt_top_of_isCompact hK, lt_of_le_of_lt hμ ENNReal.one_lt_top⟩
  exact ⟨this⟩

lemma has_compact_nat [TopologicalSpace α] (h : IsTight μ) :
    ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n := by
  intro n
  rw [iff_compact_sets] at h
  apply h
  simp

lemma of_compact_nat [TopologicalSpace α] (h : ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n) :
    IsTight μ:= by
  rw [iff_compact_sets]
  intro ε hε
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  obtain ⟨K, hK, hKe⟩ := h n
  refine ⟨K, hK, le_trans hKe (le_trans ?_ hn.le)⟩
  rw [one_div, ENNReal.inv_le_inv]

lemma iff_compact_nat [TopologicalSpace α] :
    IsTight μ ↔ ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n :=
  ⟨has_compact_nat, of_compact_nat⟩

lemma of_innerRegular [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [μ.InnerRegular] : IsTight μ := by
  rw [iff_compact_sets]
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    rw [hμ]
    refine fun _ _ ↦ ⟨∅, isCompact_empty, ?_⟩
    simp
  | inr hμ =>
    let r := μ Set.univ
    have hr : 0 < r := NeZero.pos r
    intro ε hε
    cases lt_or_ge ε r with
    | inl hεr =>
      have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hr.ne' hε.ne'
      obtain ⟨K, _, hK_compact, hKμ⟩ :=
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set α)).exists_lt_isCompact hεr'
      refine ⟨K, hK_compact, ?_⟩
      rw [measure_compl hK_compact.isClosed.measurableSet (measure_ne_top μ _),
        tsub_le_iff_right]
      rw [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hεr) hεr.le, add_comm] at hKμ
      exact hKμ.le
    | inr hεr =>
      refine ⟨∅, isCompact_empty, ?_⟩
      rw [Set.compl_empty]
      exact hεr

lemma Ulam_tightness [TopologicalSpace.SeparableSpace α] [MetricSpace α]
    [CompleteSpace α] [OpensMeasurableSpace α] [IsFiniteMeasure μ] : IsTight μ := by
  sorry

lemma countable_compact_cover [TopologicalSpace α] (h : IsTight μ) :
    ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ := by
  choose! K hK using h.has_compact_nat
  use ⋃ n, K n
  constructor
  · apply isSigmaCompact_iUnion_of_isCompact
    intro _
    simp_all only [one_div,
      ENNReal.le_inv_iff_mul_le]
  · rw [measure_congr]
    rw [ae_eq_univ, Set.compl_iUnion, ← le_zero_iff]
    refine le_of_forall_lt' (fun ε hε ↦ ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne.symm
    exact lt_of_le_of_lt ((measure_mono <| Set.iInter_subset _ n).trans <|
      (inv_eq_one_div (n : ENNReal)).symm ▸ (hK n).2) hn

lemma of_countable_compact_cover [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] (h : ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ) : IsTight μ := by
  rw [iff_compact_sets]
  rintro ε hε
  rcases h with ⟨M, hM, hMμ⟩
  unfold IsSigmaCompact at hM
  rcases hM with ⟨K, hK, rfl⟩
  have hAKc : ∀ n, IsCompact (Set.Accumulate K n) := fun n ↦ isCompact_accumulate hK n
  obtain ⟨n, hn⟩ := aux2 K (fun n => (hK n).isClosed) hMμ ε hε
  exact ⟨Set.Accumulate K n, hAKc n, hn⟩

lemma iff_countable_compact_cover [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] : IsTight μ ↔ ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ :=
  ⟨countable_compact_cover, of_countable_compact_cover⟩

end IsTight

end MeasureTheory
