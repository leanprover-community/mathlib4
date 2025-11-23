/-
Copyright (c) 2025 Stefano Rocca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Stefano Rocca
-/
module

public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Følner filters - definitions and properties

This file defines Følner filters for measurable spaces acted on by a group.

## Definitions

* `IsFoelner G μ l F` : A Følner sequence with respect to some group `G` acting on
  a measure space `X` is a sequence of sets `F` such that:
    1. Each `s` in `l` is eventually measurable with finite non-zero measure,
    2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`.

* `maxFoelner G μ` : The maximal Følner filter with respect to some group `G` acting on a
  measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s` on measurable
  sets of finite non-zero measure.

## Main results

* `IsFoelner.amenable` : If there exists a non-trivial Følner filter with respect to some
  group `G` acting on a measure space `X`, then it exists a `G`-invariant finitely additive
  probability measure on `X`.

* `isFoelner_iff_tendsto` : A sequence of sets is Følner if and only if it tends to the
  maximal Følner filter.
  The terminology maximal of the latter comes from the direct implication of this theorem :
  if `IsFoelner G μ l F` then the push-forward filter `(l.map F) ≤ maxFoelner G μ`.

* `amenable_of_maximalFoelner_ne_bot` : If the maximal Følner filter is non-trivial,
  then there exists a `G`-invariant finitely additive probability measure on `X`.

## Tags

Følner filter, amenability, amenable group
-/

@[expose] public section


open MeasureTheory Filter Set
open scoped ENNReal Pointwise symmDiff Topology Filter

variable {G ι X : Type*} [MeasurableSpace X] [Group G] [MulAction G X] {l : Filter ι}
  {F : ι → Set X} {μ : Measure X}

namespace Filter

variable (G μ) in
/-- A Følner sequence with respect to some group `G` acting on a measure space `X`
is a sequence of sets `F` such that:
    1. Each `s` in `l` is eventually measurable with finite non-zero measure,
    2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`. -/
structure IsFoelner (l : Filter ι) (F : ι → Set X) : Prop where
  eventually_measurableSet : ∀ᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : ∀ᶠ i in l, μ (F i) ≠ 0
  eventually_meas_ne_top : ∀ᶠ i in l, μ (F i) ≠ ∞
  tendsto_meas_symmDiff (g : G) : Tendsto (fun i ↦ μ ((g • (F i)) ∆ (F i)) / μ (F i)) l (𝓝 0)

/-- The constant sequence `X` is Følner if `X` has finite measure. -/
theorem IsFoelner.univ_of_isFiniteMeasure [NeZero μ] [IsFiniteMeasure μ] :
    IsFoelner G μ l (fun _ ↦ .univ) where
  eventually_measurableSet := by simp
  eventually_meas_ne_zero := by simp [NeZero.ne]
  eventually_meas_ne_top := by simp
  tendsto_meas_symmDiff := by simp [tendsto_const_nhds]

lemma IsFoelner.limUnder_univ_of_ultrafilter_le {l : Filter ι} (hfoel : IsFoelner G μ l F)
    {u : Ultrafilter ι} (hle : u ≤ l) :
    limUnder u (fun i ↦ μ (.univ ∩ (F i)) / μ (F i)) = 1 := by
  refine Tendsto.limUnder_eq <| Tendsto.mono_left (tendsto_congr' ?_|>.mp tendsto_const_nhds) hle
  exact Eventually.mono
    (hfoel.eventually_meas_ne_zero.and hfoel.eventually_meas_ne_top)
    (fun _ hi ↦ by simp [ENNReal.div_self hi.1 hi.2])

lemma IsFoelner.limUnder_add_of_ultrafilter_le {l : Filter ι} (hfoel : IsFoelner G μ l F)
    {u : Ultrafilter ι} (hle : u ≤ l) :
    ∀ s t, MeasurableSet t → Disjoint s t →
      limUnder u (fun i ↦ μ ((s ∪ t) ∩ (F i)) / μ (F i))  =
        limUnder u (fun i ↦ μ (s ∩ (F i)) / μ (F i)) +
          limUnder u (fun i ↦ μ (t ∩ (F i)) / μ (F i)) := by
  intro s t ht hdisj
  have subset_Icc : ∀ s, ∀ᶠ i in u, μ (s ∩ (F i)) / μ (F i) ∈ Icc 0 1 :=
    fun s ↦ Eventually.mono (
        (Eventually.filter_mono hle hfoel.eventually_meas_ne_zero).and
        (Eventually.filter_mono hle hfoel.eventually_meas_ne_top))
      (fun i hi ↦ by simp [ENNReal.div_le_iff hi.1 hi.2]; exact μ.mono inter_subset_right)
  obtain ⟨_, _, h₁⟩ := u.tendsto_of_eventually_mem_isCompact isCompact_Icc (subset_Icc s)
  obtain ⟨_, _, h₂⟩ := u.tendsto_of_eventually_mem_isCompact isCompact_Icc (subset_Icc t)
  rw [Tendsto.limUnder_eq h₁, Tendsto.limUnder_eq h₂]
  simp [union_inter_distrib_right]
  refine Tendsto.limUnder_eq <| Filter.Tendsto.congr' ?_ (Tendsto.add h₁ h₂)
  refine Eventually.mono (Eventually.filter_mono hle (hfoel.eventually_measurableSet)) ?_
  intro i hi
  simp [← ENNReal.add_div]
  rw [← measure_union
      (Disjoint.mono (inter_subset_left) (inter_subset_left) hdisj)
      (MeasurableSet.inter ht hi)]

lemma IsFoelner.limUnder_smul_of_ultrafilter_le [SMulInvariantMeasure G X μ]
    {l : Filter ι} (hfoel : IsFoelner G μ l F) {u : Ultrafilter ι} (hle : u ≤ l) :
    ∀ (g : G) (s : Set X),
      limUnder u (fun i ↦ μ ((g • s) ∩ (F i)) / μ (F i)) =
        limUnder u (fun i ↦ μ (s ∩ (F i)) / μ (F i)) := by
  let m := fun t ↦ limUnder u (fun i ↦ μ (t ∩ (F i)) / μ (F i))
  intro g t
  suffices h_le : ∀ (h h' : G), m (h • t) ≤ m (h' • t) by
    simpa [one_smul] using le_antisymm (h_le g 1) (h_le 1 g)
  intro h h'
  have tendsto₀ : Tendsto (fun i ↦ μ ((h⁻¹ • (F i)) ∆ (h'⁻¹ • (F i))) / μ (F i)) u (𝓝 0) := by
    simpa [← smul_smul, measure_smul_symmDiff _ h'] using
      Tendsto.mono_left (hfoel.tendsto_meas_symmDiff (h' * h⁻¹)) hle
  have h_le_add : ∀ i,
      μ (h • t ∩ (F i)) ≤ μ (h' • t ∩ (F i)) + μ ((h⁻¹ • (F i)) ∆ (h'⁻¹ • (F i))) := by
    intro i
    simp_all [measure_smul_inter]
    set A := t ∩ h⁻¹ • F i
    set B := t ∩ h'⁻¹ • F i
    calc
      μ A ≤ μ B + μ (A \ B) := by simpa [Set.inter_union_diff] using
        (measure_union_le (A ∩ B) (A \ B)).trans <| add_le_add_left (measure_mono (by simp)) _
      _ ≤ μ B + μ ((h⁻¹ • (F i)) ∆ (h'⁻¹ • (F i))) :=
        add_le_add_right (by
          rw [← inter_diff_distrib_left]
          apply measure_mono
          exact inter_subset_right.trans (by simp [symmDiff_def])) _
  have subset_Icc : ∀ t, ∀ᶠ i in u, μ (t ∩ (F i)) / μ (F i) ∈ Icc 0 1 :=
    fun t ↦ Eventually.mono (
        (Eventually.filter_mono hle hfoel.eventually_meas_ne_zero).and
        (Eventually.filter_mono hle hfoel.eventually_meas_ne_top))
      (fun i hi ↦ by simp [ENNReal.div_le_iff hi.1 hi.2]; exact μ.mono inter_subset_right)
  obtain ⟨w₁, _, h₁⟩ := u.tendsto_of_eventually_mem_isCompact isCompact_Icc (subset_Icc (h • t))
  obtain ⟨w₂, _, h₂⟩ := u.tendsto_of_eventually_mem_isCompact isCompact_Icc (subset_Icc (h' • t))
  simp [m]
  rw [Tendsto.limUnder_eq h₁, Tendsto.limUnder_eq h₂, ← add_zero w₂]
  refine le_of_tendsto_of_tendsto' h₁ (Tendsto.add h₂ tendsto₀) ?_
  simp [← ENNReal.add_div]
  exact fun i ↦ by gcongr; exact h_le_add i

/-- If there exists a non-trivial Følner filter with respect to some group `G` acting on a measure
space `X`, then it exists a `G`-invariant finitely additive probability measure on `X`. -/
theorem IsFoelner.amenable [SMulInvariantMeasure G X μ]
    {l : Filter ι} [NeBot l] (hfoel : IsFoelner G μ l F) :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
      ∀ (g : G) (s : Set X), m (g • s) = m s := by
  use fun t ↦ limUnder (Ultrafilter.of l) (fun i ↦ μ (t ∩ (F i)) / μ (F i))
  refine ⟨?_, ?_, ?_⟩
  · exact IsFoelner.limUnder_univ_of_ultrafilter_le hfoel (Ultrafilter.of_le l)
  · exact IsFoelner.limUnder_add_of_ultrafilter_le hfoel (Ultrafilter.of_le l)
  · exact IsFoelner.limUnder_smul_of_ultrafilter_le hfoel (Ultrafilter.of_le l)

variable (G μ) in
/-- The maximal Følner filter with respect to some group `G` acting on a
measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s`
on measurable sets of finite non-zero measure. -/
def maxFoelner : Filter (Set X) :=
  𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
  ⨅ (g : G), (comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0))

theorem isFoelner_iff_tendsto {ι : Type*} (l : Filter ι) (F : ι → Set X) :
    IsFoelner G μ l F ↔ Tendsto F l (maxFoelner G μ) := by
  simp_all [maxFoelner, tendsto_inf]
  constructor
  all_goals intro h
  · refine ⟨⟨h.eventually_measurableSet, h.eventually_meas_ne_zero, h.eventually_meas_ne_top⟩, ?_⟩
    exact h.tendsto_meas_symmDiff
  · exact {
      eventually_measurableSet := h.1.1
      eventually_meas_ne_zero := h.1.2.1,
      eventually_meas_ne_top := h.1.2.2,
      tendsto_meas_symmDiff := h.2 }

theorem amenable_of_maximalFoelner_ne_bot
    [SMulInvariantMeasure G X μ] (h : NeBot (maxFoelner G μ)) :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
      ∀ (g : G) (s : Set X), m (g • s) = m s :=
  IsFoelner.amenable <| (isFoelner_iff_tendsto _ _).2 <| @tendsto_id _ (maxFoelner G μ)

end Filter
