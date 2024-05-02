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
open scoped ENNReal

namespace MeasureTheory

variable {α ι : Type*}

lemma aux1 [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] (K : ℕ → Set α)
    (h : μ (⋃ n, K n) = μ Set.univ) : ∀ ε > 0, ∃ n, μ (Set.Accumulate K n) ≥ μ Set.univ - ε := by
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

lemma aux2 [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (K : ℕ → Set α) (hKclosed : ∀ n, IsClosed (K n))
    (h : μ (⋃ n, K n) = μ Set.univ) : ∀ ε > 0, ∃ n, μ ((Set.Accumulate K n)ᶜ) ≤ ε := by
  rintro ε hε
  obtain ⟨n, hn⟩ := aux1 K h ε hε
  use n
  have hK2 : IsClosed (Set.Accumulate K n) :=
      Set.Finite.isClosed_biUnion instFiniteSubtypeLeToLE (fun i _ => hKclosed i)
  rw [measure_compl hK2.measurableSet (measure_ne_top μ _)]
  exact tsub_le_iff_tsub_le.mp hn

lemma aux3 [UniformSpace α] [i : IsCountablyGenerated (𝓤 α)] {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s:= by
  letI := UniformSpace.pseudoMetricSpace (X := α)
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

variable [MeasurableSpace α] {μ : Measure α}

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

lemma of_totally_bounded_nat [UniformSpace α]
    (h : ∀ n : ℕ, ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n) : IsPretight μ := by
  intro ε hε
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  obtain ⟨K, hK, hKe⟩ := h n
  refine ⟨K, hK, ?_⟩
  apply le_trans hKe (le_trans ?_ hn.le)
  rw [one_div, ENNReal.inv_le_inv]

lemma totally_bounded_nat_iff [UniformSpace α] :
    IsPretight μ ↔ ∀ n : ℕ, ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n :=
  ⟨has_totally_bounded_nat, of_totally_bounded_nat⟩

lemma has_countable_totally_bounded_union [UniformSpace α] (h : IsPretight μ):
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

lemma to_isSeparable_on_countable_generated_uniform [UniformSpace α]
    [i : IsCountablyGenerated (𝓤 α)] (h : IsPretight μ) : IsSeparable μ := by
  obtain ⟨K, hKa, hKb⟩ := has_countable_totally_bounded_union h
  use ⋃ n, K n, ?_, hKb
  rw [TopologicalSpace.isSeparable_iUnion]
  exact fun i => aux3 (hKa i)

lemma aux_sep_1 [PseudoMetricSpace α] [TopologicalSpace.SeparableSpace α] [Nonempty α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    ∃ K : ℕ → α, DenseRange K ∧ ∀ η > 0, ∀ δ > 0, ∃ N : ℕ, μ (⋃ i ≤ N, Metric.ball (K i) δ) ≥ μ (Set.univ) - η := by
  obtain ⟨K, hK⟩ := TopologicalSpace.exists_dense_seq α
  rw [DenseRange] at hK
  have ball_cover : ∀ δ > 0, μ (⋃ i, Metric.ball (K i) δ) = μ (Set.univ) := by
    intro δ hδ
    apply le_antisymm (measure_mono fun ⦃a⦄ _ ↦ trivial)
    apply measure_mono
    exact fun y _ => Set.mem_iUnion.mpr (DenseRange.exists_dist_lt hK y hδ)
  have cover : ∀ η > 0, ∀ δ > 0, ∃ N : ℕ, μ (⋃ i ≤ N, Metric.ball (K i) δ) ≥ μ (Set.univ) - η := by
    intro η hη δ hδ
    exact aux1 (fun y ↦ Metric.ball (K y) δ) (ball_cover δ hδ) η hη
  exact ⟨K, hK, cover⟩

lemma aux_sep_2 [PseudoMetricSpace α] [TopologicalSpace.SeparableSpace α] [Nonempty α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {ε : ENNReal} (hε : 0 < ε) :
    ∃ K : ℕ → α, DenseRange K ∧ ∀ j : ℕ, ∃ N : ℕ, μ ((⋃ i ≤ N, Metric.ball (K i) (1/(j+1)))ᶜ) ≤ ε/2^(j+1) := by
  obtain ⟨K, hK, cover⟩ := aux_sep_1 μ
  have hεj_pos : ∀ j : ℕ, ε/(2^(j+1)) > 0 := by
    exact fun j => ENNReal.div_pos hε.ne' (Ne.symm (ne_of_beq_false rfl))
  have hj_pos : ∀ j : ℕ, (1/(j+1) : ℝ) > 0 := by
    exact fun j ↦ Nat.one_div_pos_of_nat
  use K, hK
  intro j
  obtain ⟨N, hN⟩ := cover (ε/(2^(j+1))) (hεj_pos j) (1/(j+1)) (hj_pos j)
  use N
  have meas : MeasurableSet (⋃ i ≤ N, Metric.ball (K i) (1 / (j + 1))) := by
    measurability
  calc
    _ = μ (Set.univ) - μ (⋃ i, ⋃ (_ : i ≤ N), Metric.ball (K i) (1 / (↑j + 1))) := by
      refine measure_compl meas ?h_fin
      apply measure_ne_top μ (⋃ i, ⋃ (_ : i ≤ N), Metric.ball (K i) (1 / (↑j + 1)))
    _ ≤ _ := by
      exact tsub_le_iff_tsub_le.mp hN

theorem ENNReal.tsum_geometric_add_one (r : ℝ≥0∞) : ∑' n : ℕ, r ^ (n + 1) = r * (1 - r)⁻¹ := by
   calc ∑' n : ℕ, r ^ (n + 1)
   _ = ∑' n : ℕ, r * r ^ (n) := by
         congr with n
         exact pow_succ' r n
   _ = r * ∑' n : ℕ, r ^ n := by rw [ENNReal.tsum_mul_left]
   _ = r * (1 - r)⁻¹ := by rw [ENNReal.tsum_geometric r]

lemma of_separableSpace_on_metric [PseudoMetricSpace α] [TopologicalSpace.SeparableSpace α]
    [OpensMeasurableSpace α] [IsFiniteMeasure μ] : IsPretight μ := by
  by_cases hμ : μ (Set.univ) = 0
  · intro ε hε
    use ∅, totallyBounded_empty
    rw [Set.compl_empty, hμ]
    exact hε.le
  · have : Nonempty α := by
      have : μ (Set.univ) > 0 := by
        rw [Measure.measure_univ_eq_zero] at hμ
        exact Measure.measure_univ_pos.mpr hμ
      exact nonempty_of_exists (MeasureTheory.nonempty_of_measure_ne_zero this.ne')
    intro ε hε
    obtain ⟨x, _, cover⟩ := aux_sep_2 μ hε
    choose G hG using cover
    use ⋂ j, ⋃ i ≤ G j, Metric.ball (x i) (1/(j+1))
    constructor
    · rw [Metric.totallyBounded_iff]
      intro η hη
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
      use ⋃ i ≤ G k, {x i}, Set.toFinite (⋃ i ≤ G k, {x i})
      apply subset_trans ?_ (Set.iUnion₂_mono fun i j ↦ Metric.ball_subset_ball hk.le)
      apply subset_trans (Set.iInter_subset _ k)
      apply Set.iUnion_subset
      intro i
      simp only [one_div, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Set.iUnion_exists,
        Set.biUnion_and', Set.iUnion_iUnion_eq_left, Set.iUnion_subset_iff]
      intro hi
      apply Set.subset_iUnion₂_of_subset i
      · exact le_rfl
      · exact hi
    · simp only [one_div, Set.compl_iInter, Set.compl_iUnion]
      apply le_trans (MeasureTheory.measure_iUnion_le _)
      have : ∀ i, μ (⋂ j, ⋂ (_ : j ≤ G i), (Metric.ball (x j) (↑i + 1)⁻¹)ᶜ) ≤ ε / 2 ^ (i + 1) := by
        intro i
        have := hG i
        simp only [one_div, Set.compl_iUnion] at this
        exact this
      apply le_trans (ENNReal.tsum_le_tsum this)
      calc ∑' (a : ℕ), ε / (2 ^ (a + 1))
        _ = ε * ∑' (a : ℕ), 2⁻¹ ^ (a + 1) := by
          simp only [div_eq_mul_inv, ENNReal.inv_pow, ENNReal.tsum_mul_left]
        _ = ε * (2⁻¹ * 2) := by simp [ENNReal.tsum_geometric_add_one]
        _ ≤ ε := by rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.two_ne_top, mul_one]

lemma of_isSeparable_on_metric [PseudoMetricSpace α] [OpensMeasurableSpace α]
    (h : IsSeparable μ) [IsFiniteMeasure μ] : IsPretight μ := by
  obtain ⟨S, hS, hSμ⟩ := h
  have : TopologicalSpace.PseudoMetrizableSpace (closure S) := by
    infer_instance
  have : TopologicalSpace.SeparableSpace (closure S) := by
    have hSc := TopologicalSpace.IsSeparable.closure hS
    have : closure S = Set.univ (α := closure S) := by
      exact (Subtype.coe_image_univ (closure S)).symm
    rw [this] at hSc
    sorry
  have := of_separableSpace_on_metric (α := closure S) -- fails

end IsPretight

/-- A measure `μ` is tight if for all `0 < ε`, there exists `K` compact such that `μ Kᶜ ≤ ε`.
This is formulated in terms of filters for simplicity, and proven equivalent to the usual definition
in `iff_compact_sets`. -/
def IsTight [TopologicalSpace α] (μ : Measure α) : Prop := Tendsto μ (cocompact α).smallSets (𝓝 0)

namespace IsTight

lemma iff_compact_sets [TopologicalSpace α] {μ : Measure α} :
    IsTight μ ↔ ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) ≤ ε := by
  simp only [IsTight, ne_eq, ENNReal.zero_ne_top, not_false_eq_true, ENNReal.tendsto_nhds,
    zero_le, tsub_eq_zero_of_le, zero_add, mem_Icc, true_and,
    eventually_smallSets, mem_cocompact]
  apply forall₂_congr ; rintro ε - ; constructor
  · rintro ⟨A, ⟨K, h1, h2⟩, hA⟩
    exact ⟨K, h1, hA Kᶜ h2⟩
  · rintro ⟨K, h1, h2⟩
    refine ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA => μ.mono hA |>.trans h2⟩

/-- Every tight measure is pre-tight -/
lemma IsPretight.of_isTight [UniformSpace α] (h : IsTight μ) : IsPretight μ := by
  rw [iff_compact_sets] at h
  intro ε hε
  obtain ⟨K, hK_compact, hKμ⟩ := h ε hε
  use K
  refine ⟨hK_compact.totallyBounded, hKμ⟩

/-- On complete uniform spaces, every pre-tight measure is tight -/
lemma of_isPretight_complete [UniformSpace α] [CompleteSpace α] (h : IsPretight μ) : IsTight μ := by
  rw [iff_compact_sets]
  intro ε hε
  obtain ⟨K, hK, hKe⟩ := h ε hε
  refine ⟨closure K, isCompact_of_totallyBounded_isClosed hK.closure isClosed_closure, ?_⟩
  have : μ (closure K)ᶜ ≤ μ Kᶜ := by
    apply μ.mono
    simp only [Set.compl_subset_compl, subset_closure]
  exact le_trans this hKe

lemma isPretight_iff_uniform_complete [UniformSpace α] [CompleteSpace α] :
    IsTight μ ↔ IsPretight μ := ⟨IsPretight.of_isTight, of_isPretight_complete⟩

/-- Ulam's tightness theorem -/
lemma of_isSeparable_complete_uniform [UniformSpace α] [i : IsCountablyGenerated (𝓤 α)]
    [TopologicalSpace.SeparableSpace α] [CompleteSpace α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] : IsTight μ := by
  letI := UniformSpace.pseudoMetricSpace (X := α)
  apply of_isPretight_complete
  exact IsPretight.of_separableSpace_on_metric

lemma of_le_isTight [TopologicalSpace α] {μ ν : Measure α} (h : μ ≤ ν) (hν : IsTight ν) :
    IsTight μ := by
  rw [iff_compact_sets] at *
  intro ε hε
  obtain ⟨K, hK, hKc⟩ := hν ε hε
  exact ⟨K, hK, le_trans (h Kᶜ) hKc⟩

lemma of_restrict_isTight [TopologicalSpace α] {μ : Measure α} {U : Set α} (hν : IsTight μ) :
    IsTight (μ.restrict U) := by
  rw [iff_compact_sets] at *
  intro ε hε
  obtain ⟨K, hK, hKc⟩ := hν ε hε
  exact ⟨K, hK, le_trans (μ.restrict_le_self _) hKc⟩

lemma add [TopologicalSpace α] {μ ν : Measure α} (hμ : IsTight μ) (hν : IsTight ν) :
    IsTight (μ + ν) := by
  have := Filter.Tendsto.add hμ hν
  simp only [add_zero] at this
  exact this

lemma const_mul [TopologicalSpace α] {μ : Measure α} (c : NNReal) (hμ : IsTight μ) :
    IsTight (c • μ) := by
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
