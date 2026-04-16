/-
Copyright (c) 2026 Michal Swietek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Swietek
-/

module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Bases
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lusin's theorem

This file proves Lusin's theorem: if `f` is a measurable function from a topological space `X`
(equipped with an outer-regular Borel measure) to a second-countable topological space `Y`, then for
every measurable set `A` of finite measure and every `ε > 0`, there exists a compact subset `K ⊆ A`
with `μ(A \ K) < ε` such that `f` is continuous on `K`.

## Main results

* `MeasureTheory.Measurable.exists_measurableSet_continuousOn`: measurable-set version, producing
  a measurable set on which `f` is continuous. Only requires `OuterRegular μ`.
* `MeasureTheory.Measurable.exists_isClosed_continuousOn`: closed-set version (the standard
  textbook statement), producing a closed set on which `f` is continuous. Requires `WeaklyRegular μ`.
* `MeasureTheory.Measurable.exists_isCompact_continuousOn`: compact-set version, producing a
  compact set on which `f` is continuous. Requires `InnerRegularCompactLTTop μ` and `T2Space X`.

## References

* [D.L. Cohn, *Measure Theory*][cohn2013measure], Proposition 7.5.2

## Tags

Lusin, measurable function, continuous restriction
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace ENNReal

namespace MeasureTheory

variable {X Y : Type*}

/-- **Lusin's theorem** (measurable set version). For a measurable function `f` into a
second-countable space, any measurable set of finite measure contains a measurable subset on which
`f` is continuous, with arbitrarily small complement. -/
theorem Measurable.exists_measurableSet_continuousOn
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {μ : Measure X} [μ.OuterRegular]
    {f : X → Y} (hf : Measurable f)
    {A : Set X} (hA : MeasurableSet A) (hAμ : μ A ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K ⊆ A, MeasurableSet K ∧ ContinuousOn f K ∧ μ (A \ K) < ε := by
  have hBasis := isBasis_countableBasis Y
  have hmeas_pre : ∀ V ∈ countableBasis Y, MeasurableSet (f ⁻¹' V) := fun V hV ↦
    hf (hBasis.isOpen hV).measurableSet
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' (countableBasis Y)
  -- For each basis element, approximate f ⁻¹' V ∩ A from outside by an open set
  choose U hU_sup hU_open _ hU_diff using fun (b : countableBasis Y) ↦
    MeasurableSet.exists_isOpen_diff_lt ((hmeas_pre b.1 b.2).inter hA)
      (ne_top_of_le_ne_top hAμ (measure_mono inter_subset_right)) (hδ_pos _).ne'
  -- Define the "good" set K₀ by removing all "bad" parts
  set K₀ := A \ ⋃ b, U b \ (f ⁻¹' ↑b ∩ A)
  refine ⟨K₀, diff_subset, ?measurableSet, ?continuousOn, ?measure⟩
  case measurableSet =>
    exact hA.diff (.iUnion fun b ↦
      (hU_open b).measurableSet.diff ((hmeas_pre b.1 b.2).inter hA))
  case continuousOn =>
    rw [continuousOn_iff_continuous_restrict, hBasis.continuous_iff]
    intro V hV
    -- On K₀, membership in f ⁻¹' V agrees with membership in the open set U ⟨V, hV⟩
    suffices h : Set.restrict K₀ f ⁻¹' V = Subtype.val ⁻¹' U ⟨V, hV⟩ by
      rw [h]; exact (hU_open ⟨V, hV⟩).preimage continuous_subtype_val
    ext ⟨x, hx⟩
    simp only [Set.restrict, mem_preimage]
    exact ⟨fun hfV ↦ hU_sup ⟨V, hV⟩ ⟨hfV, hx.1⟩,
      fun hxU ↦ by_contra fun hfV ↦ hx.2 (mem_iUnion.2 ⟨⟨V, hV⟩, hxU, fun h ↦ hfV h.1⟩)⟩
  case measure =>
    calc μ (A \ K₀)
        ≤ μ (⋃ b, U b \ (f ⁻¹' ↑b ∩ A)) := measure_mono sdiff_sdiff_le
      _ ≤ ∑' b, μ (U b \ (f ⁻¹' ↑b ∩ A)) := measure_iUnion_le _
      _ ≤ ∑' b, δ b := ENNReal.tsum_le_tsum fun b ↦ (hU_diff b).le
      _ < ε := hδ_sum

/-- **Lusin's theorem** (closed set version). For a measurable function `f` into a second-countable
space with a weakly regular measure, any measurable set of finite measure contains a closed subset
on which `f` is continuous, with arbitrarily small complement. -/
theorem Measurable.exists_isClosed_continuousOn
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {μ : Measure X} [μ.OuterRegular] [μ.WeaklyRegular]
    {f : X → Y} (hf : Measurable f)
    {A : Set X} (hA : MeasurableSet A) (hAμ : μ A ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K ⊆ A, IsClosed K ∧ ContinuousOn f K ∧ μ (A \ K) < ε := by
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' ofNat_ne_top
  obtain ⟨K₀, hK₀A, hK₀_meas, hK₀_cont, hK₀_diff⟩ :=
    hf.exists_measurableSet_continuousOn hA hAμ hε2
  obtain ⟨K, hKK₀, hK_closed, hK_diff⟩ :=
    hK₀_meas.exists_isClosed_diff_lt
      (ne_top_of_le_ne_top hAμ (measure_mono hK₀A)) hε2.ne'
  refine ⟨K, hKK₀.trans hK₀A, hK_closed, hK₀_cont.mono hKK₀, ?_⟩
  calc μ (A \ K)
      ≤ μ (A \ K₀) + μ (K₀ \ K) :=
        (measure_mono (sdiff_triangle A K₀ K)).trans (measure_union_le _ _)
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hK₀_diff hK_diff
    _ = ε := ENNReal.add_halves ε

/-- **Lusin's theorem** (compact set version). For a measurable function `f` into a second-countable
space, any measurable set of finite measure contains a compact subset on which `f` is continuous,
with arbitrarily small complement. -/
theorem Measurable.exists_isCompact_continuousOn
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {μ : Measure X} [μ.OuterRegular] [μ.InnerRegularCompactLTTop]
    {f : X → Y} (hf : Measurable f)
    {A : Set X} (hA : MeasurableSet A) (hAμ : μ A ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K ⊆ A, IsCompact K ∧ ContinuousOn f K ∧ μ (A \ K) < ε := by
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' ofNat_ne_top
  obtain ⟨K₀, hK₀A, hK₀_meas, hK₀_cont, hK₀_diff⟩ :=
    hf.exists_measurableSet_continuousOn hA hAμ hε2
  obtain ⟨K, hKK₀, hK_compact, hK_diff⟩ :=
    hK₀_meas.exists_isCompact_diff_lt
      (ne_top_of_le_ne_top hAμ (measure_mono hK₀A)) hε2.ne'
  refine ⟨K, hKK₀.trans hK₀A, hK_compact, hK₀_cont.mono hKK₀, ?_⟩
  calc μ (A \ K)
      ≤ μ (A \ K₀) + μ (K₀ \ K) :=
        (measure_mono (sdiff_triangle A K₀ K)).trans (measure_union_le _ _)
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hK₀_diff hK_diff
    _ = ε := ENNReal.add_halves ε

end MeasureTheory
