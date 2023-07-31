/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Results about indicator functions and measures

## Main results

The section "IndicatorConstMeasurable" contains simple results showing that if the indicator
function of a set is a pointwise limit (resp. a.e.-limit) of indicators of measurable
(resp. null-measurable) sets, then the set itself is measurable (resp. null-measurable).

The section "Limits of measures of sets from limits of indicators" contains simple results showing
that the pointwise convergence of indicator functions of sets implies the convergence of measures:
limᵢ Aᵢ.indicator = A.indicator implies limᵢ μ(Aᵢ) = μ(A).

## Tags

indicator function, measure, dominated convergence

-/

/-
Where should these results live? Should they be put in different files or should a new file
devoted to measure-theoretic lemmas about indicators be created?

I believe those in section IndicatorConstMeasurable only have prerequisites
 * `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`
 * `Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic`
   (for the ones using `AEStronglyMeasurable`)

Those in section TendstoMeasureOfTendstoIndicator (except to the extent they rely on measurability)
only have prerequisites
 * `Mathlib.MeasureTheory.Integral.Lebesgue`
 -/

open MeasureTheory Set Filter Topology ENNReal NNReal BigOperators

section IndicatorConstMeasurable

-- I didn't find the following lemma, the closest variants were around `indicator_const_preimage`.
--#check indicator_const_preimage

/-- A characterization of the measurability of the indicator function which takes a constant
value `b` on a set `A` and `0` elsewhere. (This version requires the measurability of the singleton
`{0}` as an explicit input, see `measurable_indicator_const_iff` for a version with typeclass
inference.) -/
lemma measurable_indicator_const_iff' [MeasurableSpace α] (A : Set α) [Zero β] [MeasurableSpace β]
  (h0 : MeasurableSet ({0} : Set β)) (b : β) :
    Measurable (A.indicator (fun _ ↦ b)) ↔ (b = 0 ∨ MeasurableSet A) := by
  constructor <;> intro h
  · by_cases hb : b = 0 <;> simp only [hb, true_or, false_or]
    convert h h0.compl
    ext a
    simp [hb]
  · by_cases hb : b = 0
    · simp only [hb, indicator_zero, measurable_const]
    · have A_mble : MeasurableSet A := by simpa only [hb, false_or] using h
      intro B _
      rcases indicator_const_preimage A B b with ⟨hB⟩ | ⟨hB | ⟨hB | hB⟩⟩
      · simp only [hB, MeasurableSet.univ]
      · simp only [hB, A_mble]
      · simp only [hB, MeasurableSet.compl_iff, A_mble]
      · simp only [mem_singleton_iff] at hB
        simp only [hB, MeasurableSet.empty]

--#find_home measurable_indicator_const_iff'
-- Gives: `Mathlib.MeasureTheory.Integral.Indicator`, i.e., this file itself...
-- But why? Could be in `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`!

/-- A characterization of the measurability of the indicator function which takes a constant
value `b` on a set `A` and `0` elsewhere. -/
lemma measurable_indicator_const_iff [MeasurableSpace α] (A : Set α) [Zero β] [MeasurableSpace β]
  [MeasurableSingletonClass β] (b : β) :
    Measurable (A.indicator (fun _ ↦ b)) ↔ (b = 0 ∨ MeasurableSet A) :=
  measurable_indicator_const_iff' A (MeasurableSet.singleton 0) b

/-- A characterization of the a.e.-measurability of the indicator function which takes a constant
value `b` on a set `A` and `0` elsewhere. (This version requires the measurability of the singleton
`{0}` as an explicit input, see `measurable_indicator_const_iff` for a version with typeclass
inference.) -/
lemma aeMeasurable_indicator_const_iff' [MeasurableSpace α] (A : Set α) [DecidableEq β]
  [Zero β] [MeasurableSpace β] [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
  [BorelSpace β]
  [TopologicalSpace.SecondCountableTopology β] [OpensMeasurableSpace β] (μ : Measure α)
  (h0 : MeasurableSet ({0} : Set β)) (b : β) :
    AEStronglyMeasurable (A.indicator (fun _ ↦ b)) μ ↔ (b = 0 ∨ NullMeasurableSet A μ) := by
  constructor <;> intro h
  · by_cases hb : b = 0 <;> simp only [hb, true_or, false_or]
    obtain ⟨f, ⟨f_mble, f_eq⟩⟩ := h
    have A_eq := @indicator_const_preimage_eq_union α β _ A {0}ᶜ b _ _
    simp only [preimage_compl, mem_compl_iff, mem_singleton_iff, hb, not_false_eq_true,
               ite_true, not_true, ite_false, union_empty] at A_eq
    rw [←A_eq]
    refine @NullMeasurableSet.congr α ‹MeasurableSpace α›
            μ (f ⁻¹' {(0 : β)})ᶜ ((indicator A fun _ ↦ b) ⁻¹' {(0 : β)})ᶜ ?_ ?_
    · apply NullMeasurableSet.compl
      apply MeasurableSet.nullMeasurableSet
      measurability
    · exact EventuallyEq.compl (EventuallyEq.preimage (id (EventuallyEq.symm f_eq)) {0})
  · by_cases hb : b = 0
    · simp only [hb, indicator_zero]
      exact Measurable.aestronglyMeasurable measurable_const
    · simp only [hb, false_or] at h
      obtain ⟨A', ⟨mble_A', eq_A'⟩⟩ := h
      refine @AEStronglyMeasurable.congr α β ‹MeasurableSpace α›
              μ _ (A'.indicator (fun _ ↦ b)) (A.indicator (fun _ ↦ b)) ?_ ?_
      · apply Measurable.aestronglyMeasurable
        apply measurable_const.indicator
        exact mble_A'
      · filter_upwards [eq_A'] with a ha
        have same : a ∈ A ↔ a ∈ A' := Iff.of_eq ha
        by_cases haA : a ∈ A
        · simp [haA, same.mp haA]
        · simp [haA, (not_iff_not.mpr same).mp haA]

end IndicatorConstMeasurable

section TendstoMeasureOfTendstoIndicator
/-!
### Limits of measures of sets from limits of indicators

This section contains results showing that the pointwise convergence of indicator functions of
sets implies the convergence of measures: limᵢ Aᵢ.indicator = A.indicator implies
limᵢ μ(Aᵢ) = μ(A).
-/

variable {α : Type _} [MeasurableSpace α] {A : Set α}
variable {ι : Type _} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicator functions of measurable sets `Aᵢ` converge to the indicator function of
a set `A` along a nontrivial countably generated filter, then `A` is also measurable. -/
lemma measurableSet_of_tendsto_indicator [NeBot L] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    MeasurableSet A := by
  have obs := measurable_indicator_const_iff A (1 : ℝ≥0∞)
  simp only [one_ne_zero, false_or] at obs
  rw [←obs]
  apply @measurable_of_tendsto_ennreal' α _ ι (fun i x ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
    (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) L _ _
  · intro i
    simp only [measurable_indicator_const_iff, one_ne_zero, As_mble i, or_true]
  · simpa [tendsto_pi_nhds] using h_lim

/-- If the indicator functions of a.e.-measurable sets `Aᵢ` converge a.e. to the indicator function
of a set `A` along a nontrivial countably generated filter, then `A` is also a.e.-measurable. -/
lemma nullMeasurableSet_of_tendsto_indicator [NeBot L] (μ : Measure α)
    (As_mble : ∀ i, NullMeasurableSet (As i) μ)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    NullMeasurableSet A μ := by
  have obs := @aeMeasurable_indicator_const_iff' α ℝ≥0∞ _ A _ _ _ _ _ _ _ _ μ
                (MeasurableSet.singleton 0) 1
  simp only [one_ne_zero, false_or] at obs
  rw [←obs]
  refine aestronglyMeasurable_of_tendsto_ae (μ := μ) (u := L)
            (f := (fun i x ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x))
            (g := A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ?_ h_lim
  intro i
  simp [aeMeasurable_indicator_const_iff', As_mble i]

/-- If the indicators of measurable sets `Aᵢ` tend pointwise almost everywhere to the indicator
of a measurable set `A` and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then
the measures of `Aᵢ` tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator' (μ : Measure α) (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (fun _ ↦ (1 : ℝ≥0∞)))
          (eventually_of_forall ?_) ?_ ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact eventually_of_forall (fun x ↦ indicator_le_indicator_of_subset hi (by simp) x)
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas

--#find_home tendsto_measure_of_tendsto_indicator'
-- Gives: `Mathlib.MeasureTheory.Integral.Lebesgue`.

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise
almost everywhere to the indicator of a measurable set `A`, then the measures `μ Aᵢ` tend to
the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure' [IsCountablyGenerated L]
    (μ : Measure α) [IsFiniteMeasure μ] (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_tendsto_indicator' L μ A_mble As_mble MeasurableSet.univ
    (measure_ne_top μ univ) (eventually_of_forall (fun i ↦ subset_univ (As i))) h_lim

/-- If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a set `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the measures of `Aᵢ`
tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator [NeBot L] (μ : Measure α)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_tendsto_indicator' L μ ?_ As_mble B_mble B_finmeas As_le_B
  · apply eventually_of_forall
    simpa only [tendsto_pi_nhds] using h_lim
  · exact @measurableSet_of_tendsto_indicator α _ A ι L _ As _ As_mble h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure [NeBot L]
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure' L μ ?_ As_mble
  · apply eventually_of_forall
    simpa only [tendsto_pi_nhds] using h_lim
  · exact @measurableSet_of_tendsto_indicator α _ A ι L _ As _ As_mble h_lim

end TendstoMeasureOfTendstoIndicator
