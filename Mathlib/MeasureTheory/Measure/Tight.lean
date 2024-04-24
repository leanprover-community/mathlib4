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

lemma aux3 {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (h : TotallyBounded s) : TopologicalSpace.IsSeparable s:= by
  rw [Metric.totallyBounded_iff] at h
  have := fun n : ℕ => h (1/(n+1)) Nat.one_div_pos_of_nat
  choose! f hf hfb using this
  use ⋃ n, f n
  constructor
  · apply Set.countable_iUnion
    exact fun i => (hf i).countable
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have := hfb n hx
    have : ∃ b ∈ f n, dist x b < ε := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
      simp only [one_div, Set.mem_iUnion, Metric.mem_ball, exists_prop] at hi
      use i, hi.1
      apply lt_trans hi.2 ?_
      rw [inv_eq_one_div]
      exact hn
    aesop

/-- A measure `μ` is separable if there is a separable set `S` such that `μ S = μ Set.univ`. -/
 def IsSeparable [TopologicalSpace α] (μ : Measure α) : Prop :=
   ∃ S : Set α, TopologicalSpace.IsSeparable S ∧ μ S = μ Set.univ

/-- A measure `μ` is pre-tight if for all `0 < ε`, there exists `K` totally bounded such that
  `μ Kᶜ ≤ ε`. -/
def IsPretight [UniformSpace α] (μ : Measure α) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ ε

namespace IsPretight

lemma has_totally_bounded_nat [UniformSpace α] (h : IsPretight μ) :
    ∀ n : ℕ, ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n := by
  intro n
  apply h
  simp

lemma of_totally_bounded_nat [UniformSpace α] (h : ∀ n : ℕ, ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n) :
    IsPretight μ:= by
  intro ε hε
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  obtain ⟨K, hK, hKe⟩ := h n
  refine ⟨K, hK, ?_⟩
  apply le_trans hKe (le_trans ?_ hn.le)
  rw [one_div, ENNReal.inv_le_inv]

lemma totally_bounded_nat_iff [UniformSpace α] :
    IsPretight μ ↔ ∀ n : ℕ, ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n :=
  ⟨has_totally_bounded_nat, of_totally_bounded_nat⟩

lemma has_countable_totally_bounded_union [UniformSpace α] [OpensMeasurableSpace α]
    (h : IsPretight μ):
    ∃ K : ℕ → Set α, (∀ n, TotallyBounded (K n)) ∧ μ (⋃ n, K n) = μ Set.univ := by
  choose! K hKa hKb using h.has_totally_bounded_nat
  use K, hKa
  rw [← Set.iUnion_accumulate, measure_congr]
  rw [ae_eq_univ, Set.compl_iUnion, ← le_zero_iff]
  refine le_of_forall_lt' (fun ε hε ↦ ?_)
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne.symm
  rw [← one_div] at hn
  have : μ ((Set.Accumulate K n)ᶜ) ≤ μ ((K n)ᶜ) := by
    apply measure_mono
    rw [Set.compl_subset_compl]
    exact Set.subset_accumulate
  have : μ ((Set.Accumulate K n)ᶜ) < ε := by
    apply lt_of_le_of_lt this (lt_of_le_of_lt (hKb n) hn)
  exact lt_of_le_of_lt (measure_mono <| Set.iInter_subset _ n) this

lemma to_separable_on_metric [PseudoMetricSpace α] [OpensMeasurableSpace α] (h : IsPretight μ) :
    IsSeparable μ := by
  obtain ⟨K, hKa, hKb⟩ := has_countable_totally_bounded_union h
  use ⋃ n, K n, ?_, hKb
  rw [TopologicalSpace.isSeparable_iUnion]
  exact fun i => aux3 (hKa i)

--lemma of_separable_on_metric [Nonempty α] [UniformSpace α] [OpensMeasurableSpace α]
--    (h : IsSeparable μ) : IsPretight μ := by
--  obtain ⟨S, hSa, hSb⟩ := h
--  let S₀ := closure S
--  have : Nonempty S := by sorry
--  have : Nonempty S₀ := by sorry
--  have hS₀a := TopologicalSpace.IsSeparable.closure hSa
--  have : TopologicalSpace.SeparableSpace S₀ := by sorry
--  obtain ⟨n, hn⟩ := TopologicalSpace.exists_countable_dense S₀
--  sorry
end IsPretight

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
