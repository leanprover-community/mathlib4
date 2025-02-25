/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Uniformity

/-!
# (Pre-)tight measures
The key definition of interest here is that of tight measures, `IsTight`. We first introduce two
weaker notions, `IsSeparablySupported` and `IsPretight`, which are equivalent on complete metric
spaces. We provide some basic API for these notions and prove Ulam's tightness theorem
(`of_isSeparableSpace_completeSpace`) and its strengthening `of_isSeparablySupported_completeSpace`.

## Main definitions
* `MeasureTheory.Measure.IsSeparablySupported`: A measure `μ` is separably supported if there is a
  separable set `S` such that `μ Sᶜ = 0`.
* `MeasureTheory.Measure.IsPretight`: A measure `μ` is pre-tight if for all `0 < ε`, there exists
  `K` totally bounded such that `μ Kᶜ ≤ ε`.
* `MeasureTheory.Measure.IsTight`: A measure `μ` is tight if for all `0 < ε`, there exists `K`
  compact such that `μ Kᶜ ≤ ε`. This is defined in terms of filters.
  `iff_exists_isCompact_measure_compl_le` establishes equivalence with the usual definition.

## Main statements

* `of_isSeparableSpace_completeSpace`: Ulam's tightness theorem: a finite measure on a complete
  separable metric space is tight.
* `of_isSeparablySupported_completeSpace`: A strengthening of Ulam's tightness theorem: a finite,
  separably supported measure on a complete metric space is tight.
* `of_innerRegular`: Every finite, inner-regular measure on a T2 space is tight.

## Notation


## Implementation details


-/
open Topology Filter Uniformity Uniform MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For a finite measure `μ`, we can extract from a countable cover that has full measure, a finite
cover of accumulated sets that has `ε`-almost full measure. -/
lemma exists_sub_le_measure_accumulate [IsFiniteMeasure μ] (K : ℕ → Set α)
    (h : μ (⋃ n, K n) = μ Set.univ) {ε : ENNReal} (hε : 0 < ε) :
    ∃ n, μ Set.univ - ε ≤ μ (Set.Accumulate K n) := by
  have : Filter.Tendsto (μ ∘ Set.Accumulate K) Filter.atTop (nhds (μ (⋃ n, Set.Accumulate K n))) :=
    MeasureTheory.tendsto_measure_iUnion_atTop Set.monotone_accumulate
  rw [ENNReal.tendsto_atTop (measure_ne_top μ (⋃ n, Accumulate K n)), Set.iUnion_accumulate] at this
  obtain ⟨N, hN⟩ := this ε hε
  use N
  simp_all only [Function.comp_apply, mem_Icc, le_refl]

/-- For a finite measure `μ`, we can extract from a countable cover that has full measure, a finite
cover of accumulated sets that has `ε`-almost full measure. -/
lemma exists_sub_le_measure_accumulate2 [IsFiniteMeasure μ] (K : ℕ → Set α)
    (h : μ (⋃ n, K n)ᶜ = 0) {ε : ENNReal} (hε : 0 < ε) :
    ∀ᶠ n in atTop, μ (Accumulate K n)ᶜ ≤ ε := by
  rw [Filter.eventually_atTop]
  have : Filter.Tendsto (μ ∘ (Accumulate K)ᶜ) Filter.atTop (𝓝 (μ (⋂ n, (Accumulate K n)ᶜ))) := by
    apply MeasureTheory.tendsto_measure_iInter_atTop
    · sorry
    · sorry
    · exact ⟨0, measure_ne_top _ _⟩
  rw [ENNReal.tendsto_atTop (measure_ne_top _ _), ← compl_iUnion, iUnion_accumulate] at this
  obtain ⟨N, hN⟩ := this ε hε
  use N
  intro b hb
  have := hN b hb
  simp at this
  sorry

/-- For a finite measure `μ`, we can extract from a countable cover that has full measure, a finite
cover of accumulated sets for which the complement has measure below `ε`. -/
lemma exists_sub_le_measure_accumulate_compl [IsFiniteMeasure μ] (K : ℕ → Set α)
    (hKmeas : ∀ n, MeasurableSet (K n)) (h : μ (⋃ n, K n) = μ Set.univ) {ε : ENNReal} (hε : 0 < ε) :
    ∃ n, μ ((Set.Accumulate K n)ᶜ) ≤ ε := by
  obtain ⟨n, hn⟩ := exists_sub_le_measure_accumulate K h hε
  use n
  have hK2 : MeasurableSet (Set.Accumulate K n) := by
    rw [Set.Accumulate]
    measurability
  rw [measure_compl hK2 (measure_ne_top μ _)]
  exact tsub_le_iff_tsub_le.mp hn

/-- For a finite measure `μ`, we can construct a dense sequence such that for any radius, we can
cover all but a set of measure below `ε`. -/
lemma exists_denseRange_sub_le_measure_univ_of_separableSpace [PseudoMetricSpace α]
    [TopologicalSpace.SeparableSpace α] [Nonempty α] (μ : Measure α) [IsFiniteMeasure μ] :
    ∃ u : ℕ → α, DenseRange u ∧
    ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, μ (Set.univ) - ε ≤ μ (⋃ i ≤ N, Metric.ball (u i) δ) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq α
  use u, hu
  intro ε hε δ hδ
  apply exists_sub_le_measure_accumulate (fun y ↦ Metric.ball (u y) δ) (?_) hε
  apply le_antisymm (measure_mono fun ⦃a⦄ _ ↦ trivial)
  exact measure_mono <| fun y _ => Set.mem_iUnion.mpr (DenseRange.exists_dist_lt hu y hδ)

/-- For a finite measure `μ`, we can construct a dense sequence such that for any radius, we can
find a `N` such that the measure of the complement of the first `N` balls of radius `1/(j+1)` is
at most `ε/2^(j+1)`. -/
lemma exists_denseRange_sub_le_measure_univ_of_separableSpace_compl [PseudoMetricSpace α]
    [TopologicalSpace.SeparableSpace α] [Nonempty α] [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {ε : ENNReal} (hε : 0 < ε) : ∃ u : ℕ → α, DenseRange u ∧
    ∀ j : ℕ, ∃ N : ℕ, μ ((⋃ i ≤ N, Metric.ball (u i) (1/(j+1)))ᶜ) ≤ ε/2^(j+1) := by
  obtain ⟨u, hu, cover⟩ := exists_denseRange_sub_le_measure_univ_of_separableSpace μ
  have hεj_pos : ∀ j : ℕ, ε/(2^(j+1)) > 0 :=
    fun j => ENNReal.div_pos hε.ne' (Ne.symm (ne_of_beq_false rfl))
  use u, hu
  intro j
  obtain ⟨N, hN⟩ := cover (ε/(2^(j+1))) (hεj_pos j) (1/(j+1)) (Nat.one_div_pos_of_nat)
  use N
  rw [measure_compl (by measurability) (measure_ne_top μ _)]
  exact tsub_le_iff_tsub_le.mp hN

/-- A measure `μ` is separable if there is a separable set `S` such that `μ S = μ Set.univ`. -/
 def IsSeparablySupported [TopologicalSpace α] (μ : Measure α) : Prop :=
  ∃ S : Set α, TopologicalSpace.IsSeparable S ∧ μ (Sᶜ) = 0

namespace IsSeparablySupported

lemma of_separableSpace [TopologicalSpace α] [TopologicalSpace.SeparableSpace α] :
    IsSeparablySupported μ := by
  refine ⟨Set.univ, TopologicalSpace.isSeparable_univ_iff.mpr ‹_›, ?_⟩
  rw [Set.compl_univ, measure_empty]

lemma separablySupported_nat_iff [TopologicalSpace α] :
    IsSeparablySupported μ ↔ ∀ n : ℕ, ∃ S : Set α, TopologicalSpace.IsSeparable S ∧ μ Sᶜ ≤ 1/n := by
  constructor
  · rintro ⟨S, hS, hSc⟩ n
    use S, hS
    simp_all only [zero_le]
  · intro h
    choose S hsep hmeas using h
    use ⋃ n, S n, TopologicalSpace.isSeparable_iUnion.mpr hsep
    rw [← le_zero_iff]
    apply le_of_forall_lt'
    intro _ hc
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hc.ne.symm
    apply lt_of_le_of_lt ?_ hn
    have : μ (S n)ᶜ ≤ (↑n)⁻¹ := by
      simp_all only [one_div,
        ENNReal.le_inv_iff_mul_le]
    apply le_trans ?_ this
    apply measure_mono
    rw [Set.compl_subset_compl]
    exact subset_iUnion_of_subset n fun ⦃a⦄ a ↦ a

end IsSeparablySupported

section IsPretight

variable [UniformSpace α]

/-- A measure `μ` is pre-tight if for all `0 < ε`, there exists `K` totally bounded such that
  `μ Kᶜ ≤ ε`. -/
def IsPretight (μ : Measure α) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ ε

namespace IsPretight

lemma of_totallyBounded (h : TotallyBounded (Set.univ : Set α)) : IsPretight μ := by
  intro ε hε
  use Set.univ, h
  rw [Set.compl_univ, measure_empty]
  exact hε.le

lemma exists_totallyBounded_nat (h : IsPretight μ) (n : ℕ):
    ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n := by
  apply h
  simp only [one_div, ENNReal.inv_pos, ne_eq, ENNReal.natCast_ne_top, not_false_eq_true]

/-- It suffices to check totally boundedness along countably many `ε`. -/
lemma of_totallyBounded_nat (h : ∀ n : ℕ, ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n) :
    IsPretight μ := by
  intro ε hε
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  obtain ⟨K, hK, hKe⟩ := h n
  refine ⟨K, hK, ?_⟩
  apply le_trans hKe (le_trans ?_ hn.le)
  rw [one_div, ENNReal.inv_le_inv]

lemma totallyBounded_nat_iff : IsPretight μ ↔ ∀ n : ℕ, ∃ K : Set α, TotallyBounded K ∧ μ Kᶜ ≤ 1/n :=
  ⟨exists_totallyBounded_nat, of_totallyBounded_nat⟩

/-- If a measure `μ` is pretight, we can cover `μ`-almost all of the space by a countable sequence
of totally bounded sets. -/
lemma exists_countable_totallyBounded_union (h : IsPretight μ):
    ∃ K : ℕ → Set α, (∀ n, TotallyBounded (K n)) ∧ μ (⋃ n, K n)ᶜ = 0 := by
  choose! K hKa hKb using h.exists_totallyBounded_nat
  use K, hKa
  rw [← le_zero_iff]
  apply le_of_forall_lt'
  intro _ hc
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hc.ne.symm
  apply lt_of_le_of_lt ?_ hn
  have : μ (K n)ᶜ ≤ (↑n)⁻¹ := by
    simp_all only [one_div,
      ENNReal.le_inv_iff_mul_le]
  apply le_trans ?_ this
  apply measure_mono
  rw [Set.compl_subset_compl]
  exact subset_iUnion_of_subset n fun ⦃a⦄ a ↦ a

/-- Every pretight measure on a countably generated uniform space is separably supported. -/
lemma to_isSeparablySupported_on_countably_generated_uniformSpace [IsCountablyGenerated (𝓤 α)]
    (h : IsPretight μ) : IsSeparablySupported μ := by
  obtain ⟨K, hKa, hKb⟩ := exists_countable_totallyBounded_union h
  use ⋃ n, K n, ?_, hKb
  rw [TopologicalSpace.isSeparable_iUnion]
  exact fun i => TotallyBounded.isSeparable (hKa i)

/-- Every finite measure on a countably generated, separable, uniform space is pretight.-/
lemma of_separableSpace_on_countablyGenerated_uniformSpace [IsCountablyGenerated (𝓤 α)]
    [TopologicalSpace.SeparableSpace α] [OpensMeasurableSpace α] [IsFiniteMeasure μ] :
    IsPretight μ := by
  letI := UniformSpace.pseudoMetricSpace (X := α)
  by_cases hμ : μ (Set.univ) = 0
  · intro ε hε
    use ∅, totallyBounded_empty
    rw [Set.compl_empty, hμ]
    exact hε.le
  · have : Nonempty α := by
      have : 0 < μ (Set.univ) := by
        rw [Measure.measure_univ_eq_zero] at hμ
        exact Measure.measure_univ_pos.mpr hμ
      exact nonempty_of_exists (MeasureTheory.nonempty_of_measure_ne_zero this.ne')
    intro ε hε
    obtain ⟨x, _, cover⟩ := exists_denseRange_sub_le_measure_univ_of_separableSpace_compl μ hε
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
        simp_all only [Measure.measure_univ_eq_zero, one_div, compl_iUnion]
      apply le_trans (ENNReal.tsum_le_tsum this)
      calc ∑' (a : ℕ), ε / (2 ^ (a + 1))
        _ = ε * ∑' (a : ℕ), 2⁻¹ ^ (a + 1) := by
          simp only [div_eq_mul_inv, ENNReal.inv_pow, ENNReal.tsum_mul_left]
        _ = ε * (2⁻¹ * 2) := by simp [ENNReal.tsum_geometric_add_one]
        _ ≤ ε := by rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-- Every finite, separably supported measure on a countably generated, uniform space is pretight.-/
lemma of_isSeparablySupported_on_countablyGenerated_uniformSpace [IsCountablyGenerated (𝓤 α)]
    [OpensMeasurableSpace α] (h : IsSeparablySupported μ) [IsFiniteMeasure μ] : IsPretight μ := by
  letI := UniformSpace.pseudoMetricSpace (X := α)
  obtain ⟨S, hS, hSμ⟩ := h
  have : TopologicalSpace.SeparableSpace (closure S) :=
    TopologicalSpace.IsSeparable.separableSpace <| TopologicalSpace.IsSeparable.closure hS
  letI mα : MeasureSpace α := ⟨μ⟩
  letI mS : MeasureSpace (closure S) := Measure.Subtype.measureSpace
  have : IsFiniteMeasure mS.volume := by
    constructor
    rw [Measure.Subtype.volume_univ (MeasurableSet.nullMeasurableSet measurableSet_closure)]
    exact measure_lt_top volume (closure S)
  have := of_separableSpace_on_countablyGenerated_uniformSpace (μ := mS.volume)
  intro ε hε
  obtain ⟨K, hK, hKe⟩ := this ε hε
  have hSμ_co : μ (closure S)ᶜ = 0 := by
    rw [← le_zero_iff] at *
    apply le_trans ?_ hSμ
    apply measure_mono
    rw [Set.compl_subset_compl]
    exact subset_closure
  use (closure K)
  constructor
  · apply TotallyBounded.closure
    rw [Metric.totallyBounded_iff] at *
    intro δ hδ
    obtain ⟨N, hN⟩ := hK δ hδ
    use N, Finite.image Subtype.val hN.1
    simp_all only [iUnion_coe_set, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      iUnion_exists, image_subset_iff, preimage_iUnion]
    exact hN.right
  · have hKe : volume (closure K)ᶜ ≤ ε := by
      apply le_trans ?_ hKe
      apply measure_mono
      rw [Set.compl_subset_compl]
      exact subset_closure
    apply le_trans ?_ hKe
    rw [Measure.Subtype.volume_def, MeasureTheory.Measure.comap_apply _ Subtype.val_injective]
    · rw [← MeasureTheory.measure_inter_add_diff₀ (t := closure S),
        ← MeasureTheory.measure_inter_add_diff₀ (μ := volume) (t := closure S), volume]
      · apply add_le_add
        · apply measure_mono
          intro x hx
          simp only [mem_inter_iff, mem_image, mem_compl_iff, closure_subtype, Subtype.exists,
            exists_and_left, exists_prop, exists_eq_right_right, and_self_right]
          constructor <;> simp_all only [mem_inter_iff, mem_compl_iff, not_false_eq_true]
        · have : μ ((closure (Subtype.val '' K))ᶜ \ closure S) = 0 := by
            rw [← nonpos_iff_eq_zero, ← hSμ_co]
            apply measure_mono
            intro x hx
            simp_all only [mem_diff, mem_compl_iff, not_false_eq_true]
          rw [this]
          exact zero_le _
      · apply MeasurableSet.nullMeasurableSet
        measurability
      · apply MeasurableSet.nullMeasurableSet
        measurability
    · exact fun s hs ↦ MeasurableSet.subtype_image measurableSet_closure hs
    · measurability

end IsPretight

end IsPretight

/-- A measure `μ` is tight if for all `0 < ε`, there exists `K` compact such that `μ Kᶜ ≤ ε`.
This is formulated in terms of filters for simplicity, and proven equivalent to the usual definition
in `iff_exists_isCompact_measure_compl_le`. -/
def IsTight [TopologicalSpace α] (μ : Measure α) : Prop := Tendsto μ (cocompact α).smallSets (𝓝 0)

namespace IsTight

/-- The usual definition of tightness is equivalent to the filter definition. -/
lemma iff_exists_isCompact_measure_compl_le [TopologicalSpace α] :
    IsTight μ ↔ ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) ≤ ε := by
  simp only [IsTight, ne_eq, ENNReal.zero_ne_top, not_false_eq_true, ENNReal.tendsto_nhds,
    zero_le, tsub_eq_zero_of_le, zero_add, mem_Icc, true_and,
    eventually_smallSets, mem_cocompact]
  apply forall₂_congr; rintro ε -; constructor
  · rintro ⟨A, ⟨K, h1, h2⟩, hA⟩
    exact ⟨K, h1, hA Kᶜ h2⟩
  · rintro ⟨K, h1, h2⟩
    refine ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA => μ.mono hA |>.trans h2⟩

lemma of_compactSpace [TopologicalSpace α] [CompactSpace α] : IsTight μ := by
  rw [iff_exists_isCompact_measure_compl_le]
  intro ε hε
  use Set.univ, CompactSpace.isCompact_univ
  rw [Set.compl_univ, measure_empty]
  exact hε.le

lemma exists_isCompact_nat [TopologicalSpace α] (h : IsTight μ) (n : ℕ) :
    ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n := by
  rw [iff_exists_isCompact_measure_compl_le] at h
  apply h
  simp

lemma of_isCompact_nat [TopologicalSpace α] (h : ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n) :
    IsTight μ:= by
  rw [iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  obtain ⟨K, hK, hKe⟩ := h n
  refine ⟨K, hK, le_trans hKe (le_trans ?_ hn.le)⟩
  rw [one_div, ENNReal.inv_le_inv]

lemma iff_isCompact_nat [TopologicalSpace α] :
    IsTight μ ↔ ∀ n : ℕ, ∃ K : Set α, IsCompact K ∧ μ Kᶜ ≤ 1/n :=
  ⟨exists_isCompact_nat, of_isCompact_nat⟩

lemma exists_countable_isSigmaCompact_cover [TopologicalSpace α] (h : IsTight μ) :
    ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ := by
  choose! K hK using h.exists_isCompact_nat
  use ⋃ n, K n, isSigmaCompact_iUnion_of_isCompact _ (fun _ => (hK _).1 )
  rw [measure_congr]
  rw [ae_eq_univ, Set.compl_iUnion, ← le_zero_iff]
  refine le_of_forall_lt' (fun ε hε ↦ ?_)
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne.symm
  exact lt_of_le_of_lt ((measure_mono <| Set.iInter_subset _ n).trans <|
    (inv_eq_one_div (n : ENNReal)).symm ▸ (hK n).2) hn

lemma of_countable_isSigmaCompact_cover [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] (h : ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ) : IsTight μ := by
  rw [iff_exists_isCompact_measure_compl_le]
  rintro ε hε
  rcases h with ⟨M, hM, hMμ⟩
  rcases hM with ⟨K, hK, rfl⟩
  have hAKc : ∀ n, IsCompact (Set.Accumulate K n) := fun n ↦ isCompact_accumulate hK n
  obtain ⟨n, hn⟩ := exists_sub_le_measure_accumulate_compl K (fun n => (hK n).measurableSet) hMμ hε
  exact ⟨Set.Accumulate K n, hAKc n, hn⟩

lemma iff_countable_isSigmaCompact_cover [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] : IsTight μ ↔ ∃ M, IsSigmaCompact M ∧ μ M = μ Set.univ :=
  ⟨exists_countable_isSigmaCompact_cover, of_countable_isSigmaCompact_cover⟩

lemma of_le_isTight [TopologicalSpace α] {μ ν : Measure α} (h : μ ≤ ν) (hν : IsTight ν) :
    IsTight μ := by
  rw [iff_exists_isCompact_measure_compl_le] at *
  intro ε hε
  obtain ⟨K, hK, hKc⟩ := hν ε hε
  exact ⟨K, hK, le_trans (h Kᶜ) hKc⟩

lemma of_restrict_isTight [TopologicalSpace α] {U : Set α} (hμ : IsTight μ) :
    IsTight (μ.restrict U) := by
  rw [iff_exists_isCompact_measure_compl_le] at *
  intro ε hε
  obtain ⟨K, hK, hKc⟩ := hμ ε hε
  exact ⟨K, hK, le_trans (μ.restrict_le_self _) hKc⟩

lemma add [TopologicalSpace α] {μ ν : Measure α} (hμ : IsTight μ) (hν : IsTight ν) :
    IsTight (μ + ν) := by
  simpa only [add_zero] using Filter.Tendsto.add hμ hν

lemma const_mul [TopologicalSpace α] (c : NNReal) (hμ : IsTight μ) : IsTight (c • μ) := by
  rw [iff_exists_isCompact_measure_compl_le] at *
  intro ε hε
  have hεc : 0 < ε / c := by
    simp only [ENNReal.div_pos_iff, ne_eq, ENNReal.coe_ne_top, not_false_eq_true,
      and_true, hε.ne']
  obtain ⟨K, hK, hKc⟩ := hμ (ε / c) hεc
  exact ⟨K, hK, ENNReal.mul_le_of_le_div' hKc⟩

/-- Every tight measure is pre-tight -/
lemma IsPretight.of_isTight [UniformSpace α] (h : IsTight μ) : IsPretight μ := by
  rw [iff_exists_isCompact_measure_compl_le] at h
  intro ε hε
  obtain ⟨K, hK_compact, hKμ⟩ := h ε hε
  use K
  exact ⟨hK_compact.totallyBounded, hKμ⟩

/-- On complete uniform spaces, every pre-tight measure is tight -/
lemma of_isPretight_completeSpace [UniformSpace α] [CompleteSpace α] (h : IsPretight μ) :
    IsTight μ := by
  rw [iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K, hK, hKe⟩ := h ε hε
  refine ⟨closure K, isCompact_of_totallyBounded_isClosed hK.closure isClosed_closure, ?_⟩
  exact le_trans (subset_closure |> compl_subset_compl.mpr |> μ.mono) hKe

lemma isPretight_iff_completeSpace [UniformSpace α] [CompleteSpace α] :
    IsTight μ ↔ IsPretight μ := ⟨IsPretight.of_isTight, of_isPretight_completeSpace⟩

/-- Ulam's tightness theorem. -/
lemma of_isSeparableSpace_completeSpace [UniformSpace α] [IsCountablyGenerated (𝓤 α)]
    [TopologicalSpace.SeparableSpace α] [CompleteSpace α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] : IsTight μ := by
  letI := UniformSpace.pseudoMetricSpace (X := α)
  apply of_isPretight_completeSpace
  exact IsPretight.of_separableSpace_on_countablyGenerated_uniformSpace

/-- A strengthened version of Ulam's tightness theorem. -/
lemma of_isSeparablySupported_completeSpace [UniformSpace α] [IsCountablyGenerated (𝓤 α)]
    [CompleteSpace α] [OpensMeasurableSpace α] (h : IsSeparablySupported μ) [IsFiniteMeasure μ] :
    IsTight μ := by
  letI := UniformSpace.pseudoMetricSpace (X := α)
  apply of_isPretight_completeSpace
  exact IsPretight.of_isSeparablySupported_on_countablyGenerated_uniformSpace h

/-- Tight measures on T2 spaces that assign finite measure to compact sets are finite. -/
instance [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α] [hk: IsFiniteMeasureOnCompacts μ]
    [h : Fact (IsTight μ)] : IsFiniteMeasure μ := by
  obtain ⟨_, hK, hμ⟩ := (iff_exists_isCompact_measure_compl_le.mp h.out) 1 (zero_lt_one)
  have : μ Set.univ < ⊤ := by
    rw [← (MeasureTheory.measure_add_measure_compl hK.measurableSet), WithTop.add_lt_top]
    exact ⟨hk.lt_top_of_isCompact hK, lt_of_le_of_lt hμ ENNReal.one_lt_top⟩
  exact ⟨this⟩

/-- Inner regular finite measures on T2 spaces are tight. -/
lemma of_innerRegular [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] [μ.InnerRegular] : IsTight μ := by
  rw [iff_exists_isCompact_measure_compl_le]
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    rw [hμ]
    exact fun _ i ↦ ⟨∅, isCompact_empty, le_of_lt i⟩
  | inr hμ =>
    let r := μ Set.univ
    have hr := NeZero.pos r
    intro ε hε
    cases lt_or_ge ε r with
    | inl hεr =>
      have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hr.ne' hε.ne'
      obtain ⟨K, _, hK_compact, hKμ⟩ :=
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set α)).exists_lt_isCompact hεr'
      refine ⟨K, hK_compact, ?_⟩
      rw [measure_compl hK_compact.measurableSet (measure_ne_top μ _),
        tsub_le_iff_right]
      rw [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hεr) hεr.le, add_comm] at hKμ
      exact hKμ.le
    | inr hεr =>
      refine ⟨∅, isCompact_empty, ?_⟩
      rw [Set.compl_empty]
      exact hεr

end IsTight

end MeasureTheory.Measure
