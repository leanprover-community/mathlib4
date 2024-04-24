/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.Regular

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

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

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

/-- A measure `μ` is pre-tight if for all `0 < ε`, there exists `K` totally bounded such that
  `μ Kᶜ ≤ ε`. -/
def IsPretight [UniformSpace α] (μ : Measure α) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ ε

/-- A measure `μ` is tight if for all `0 < ε`, there exists `K` compact such that `μ Kᶜ ≤ ε`. -/
def IsTight [TopologicalSpace α] (μ : Measure α) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ ε

instance [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α] [hk: IsFiniteMeasureOnCompacts μ]
    [h : Fact (IsTight μ)] : IsFiniteMeasure μ := by
  obtain ⟨K, hK, hμ⟩ := h.out 1 (zero_lt_one)
  have := (MeasureTheory.measure_add_measure_compl (μ := μ) hK.isClosed.measurableSet).symm
  have : μ Set.univ < ∞ := by
    rw [this, WithTop.add_lt_top]
    exact ⟨hk.lt_top_of_isCompact hK, lt_of_le_of_lt hμ ENNReal.one_lt_top⟩
  exact ⟨this⟩

/-- Every tight measure is pre-tight-/
lemma Tight.of_pretight [UniformSpace α] (h : IsTight μ) : IsPretight μ := by
  intro ε hε
  obtain ⟨K, hK_compact, hKμ⟩ := h ε hε
  use K
  refine ⟨hK_compact.totallyBounded, hKμ⟩

variable [TopologicalSpace α]

namespace IsTight

lemma has_compact_nat [TopologicalSpace α] (h : IsTight μ) :
    ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n := by
  intro n
  apply h
  simp

lemma of_compact_nat [TopologicalSpace α] (h : ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n) :
    IsTight μ:= by
  intro ε hε
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  obtain ⟨K, hK, hKe⟩ := h n
  refine ⟨K, hK, ?_⟩
  apply le_trans hKe (le_trans ?_ hn.le)
  rw [one_div, ENNReal.inv_le_inv]

lemma compact_nat_iff [TopologicalSpace α] :
    IsTight μ ↔ ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n :=
  ⟨has_compact_nat, of_compact_nat⟩

lemma of_innerRegular [T2Space α] [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [μ.InnerRegular] :
    IsTight μ := by
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

lemma countable_compact_cover (h : IsTight μ) :
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
      (inv_eq_one_div (n : ℝ≥0∞)).symm ▸ (hK n).2) hn

lemma of_countable_compact_cover [IsFiniteMeasure μ] [T2Space α] [OpensMeasurableSpace α]
    (h : ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ) : IsTight μ := by
  rintro ε hε
  rcases h with ⟨M, hM, hMμ⟩
  unfold IsSigmaCompact at hM
  rcases hM with ⟨K, hK, rfl⟩
  have hAKc : ∀ n, IsCompact (Set.Accumulate K n) := fun n ↦ isCompact_accumulate hK n
  obtain ⟨n, hn⟩ := aux2 K (fun n => (hK n).isClosed) hMμ ε hε
  exact ⟨Set.Accumulate K n, hAKc n, hn⟩

lemma countable_compact_cover_iff [IsFiniteMeasure μ] [T2Space α] [OpensMeasurableSpace α]:
    IsTight μ ↔ ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ :=
  ⟨countable_compact_cover, of_countable_compact_cover⟩

end IsTight

/-- A set `S` of measures is tight if for all `0 < ε`, there exists `K` compact such that for all
`μ` in `S`, `μ Kᶜ ≤ ε`. -/
def IsTightSet (S : Set (Measure α)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set α, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε

lemma tight_singleton [T2Space α] [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [μ.InnerRegular] :IsTightSet {μ} := by
  unfold IsTightSet
  intro ε hε
  simp_all only [IsTight.of_innerRegular μ ε hε, Set.mem_singleton_iff, forall_eq]

end MeasureTheory
