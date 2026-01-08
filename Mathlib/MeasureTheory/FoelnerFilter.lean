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

* `IsFoelner.mean μ u F s` : The limit along an ultrafilter `u` of the density of a set `s`
  with respect to a Følner sequence `F` in the measure space `X`.

* `maxFoelner G μ` : The maximal Følner filter with respect to some group `G` acting on a
  measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s` over measurable
  sets of finite non-zero measure.

## Main results

* `IsFoelner.amenable` : If there exists a non-trivial Følner filter with respect to some
  group `G` acting on a measure space `X`, then it exists a `G`-invariant finitely additive
  probability measure on `X`.

* `isFoelner_iff_tendsto` : A sequence of sets is Følner if and only if it tends to the
  maximal Følner filter.
  The attribute "maximal" of the latter comes from the direct implication of this theorem :
  if `IsFoelner G μ l F` then the push-forward filter `(l.map F) ≤ maxFoelner G μ`.

* `amenable_of_maxFoelner_ne_bot` : If the maximal Følner filter is non-trivial,
  then there exists a `G`-invariant finitely additive probability measure on `X`.

## Tags

Foelner, Følner filter, amenability, amenable group
-/

@[expose] public section


open MeasureTheory Filter Set Tendsto
open scoped ENNReal Pointwise symmDiff Topology Filter

variable {G X : Type*} [MeasurableSpace X] {μ : Measure X} [Group G] [MulAction G X]
variable {ι : Type*} {l : Filter ι} {u : Ultrafilter ι} {F : ι → Set X}

namespace Filter


variable (G μ l F) in
/-- A Følner sequence with respect to some group `G` acting on a measure space `X`
    is a sequence of sets `F` such that:
      1. Each `s` in `l` is eventually measurable with finite non-zero measure,
      2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`. -/
@[mk_iff]
structure IsFoelner : Prop where
  eventually_measurableSet : ∀ᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : ∀ᶠ i in l, μ (F i) ≠ 0
  eventually_meas_ne_top : ∀ᶠ i in l, μ (F i) ≠ ∞
  tendsto_meas_symmDiff (g : G) : Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)

/-- The constant sequence `X` is Følner if `X` has finite measure. -/
theorem IsFoelner.univ_of_isFiniteMeasure [NeZero μ] [IsFiniteMeasure μ] :
    IsFoelner G μ l (fun _ ↦ .univ) where
  eventually_measurableSet := by simp
  eventually_meas_ne_zero := by simp [NeZero.ne]
  eventually_meas_ne_top := by simp
  tendsto_meas_symmDiff := by simp [tendsto_const_nhds]

theorem IsFoelner.mono {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : l' ≤ l) :
    IsFoelner G μ l' F where
  eventually_measurableSet := hfoel.eventually_measurableSet.filter_mono hle
  eventually_meas_ne_zero := hfoel.eventually_meas_ne_zero.filter_mono hle
  eventually_meas_ne_top := hfoel.eventually_meas_ne_top.filter_mono hle
  tendsto_meas_symmDiff (g : G) := Tendsto.mono_left (hfoel.tendsto_meas_symmDiff g) hle

variable (μ u F) in
/-- The limit along an ultrafilter of the density of a set with respect to a
    Følner sequence in `X`. -/
noncomputable def IsFoelner.mean (s : Set X) :=
  limUnder u (fun i ↦ μ (s ∩ F i) / μ (F i))

theorem IsFoelner.tendsto_nhds_mean (hfoel : IsFoelner G μ u F) (s : Set X) :
    Tendsto (fun i ↦ μ (s ∩ F i) / μ (F i)) u (𝓝 (IsFoelner.mean μ u F s)) := by
  have mem_Icc : ∀ᶠ i in u, μ (s ∩ F i) / μ (F i) ∈ Icc 0 1 := by
    filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
    simpa [ENNReal.div_le_iff hi hi'] using μ.mono inter_subset_right
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (u.map (fun i ↦ μ (s ∩ F i) / μ (F i))) (mem_map.1 mem_Icc)
  exact tendsto_nhds_limUnder (by use x; exact hx.2)

theorem IsFoelner.mean_univ_eq_one (hfoel : IsFoelner G μ u F) :
    IsFoelner.mean μ u F .univ = 1 := by
  refine tendsto_nhds_unique_of_eventuallyEq (hfoel.tendsto_nhds_mean _) tendsto_const_nhds ?_
  filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
  simp [ENNReal.div_self hi hi']

theorem IsFoelner.mean_union_eq_add_of_disjoint (hfoel : IsFoelner G μ u F)
    (s t : Set X) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    IsFoelner.mean μ u F (s ∪ t) = IsFoelner.mean μ u F s + IsFoelner.mean μ u F t := by
  refine tendsto_nhds_unique_of_eventuallyEq
    (hfoel.tendsto_nhds_mean _) ((hfoel.tendsto_nhds_mean _).add (hfoel.tendsto_nhds_mean _)) ?_
  filter_upwards [hfoel.eventually_measurableSet] with i hi
  rw [union_inter_distrib_right,
    measure_union (hdisj.inter_left _ |>.inter_right _) (ht.inter hi), ENNReal.add_div]

theorem IsFoelner.mean_smul_eq_mean [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g : G) (s : Set X) :
    IsFoelner.mean μ u F (g • s) = IsFoelner.mean μ u F s := by
  suffices h_le : ∀ h h', IsFoelner.mean μ u F (h • s) ≤ IsFoelner.mean μ u F (h' • s) by
    simpa [one_smul] using le_antisymm (h_le g 1) (h_le 1 g)
  intro h h'
  have tendsto₀ : Tendsto (fun i ↦ μ ((h⁻¹ • F i) ∆ (h'⁻¹ • F i)) / μ (F i)) u (𝓝 0) := by
    simpa [← smul_smul] using hfoel.tendsto_meas_symmDiff (h' * h⁻¹)
  have h_le_add (i : ι) : μ (h • s ∩ F i) ≤ μ (h' • s ∩ F i) + μ ((h⁻¹ • F i) ∆ (h'⁻¹ • F i)) := by
    simp_rw [← measure_inter_inv_smul]
    set A := s ∩ h⁻¹ • F i
    set B := s ∩ h'⁻¹ • F i
    calc
      μ A ≤ μ B + μ (A \ B) := by
        simpa [Set.inter_union_diff] using
          (measure_union_le (A ∩ B) (A \ B)).trans <| add_le_add_left (measure_mono (by simp)) _
      _ ≤ μ B + μ ((h⁻¹ • F i) ∆ (h'⁻¹ • F i)) :=
        add_le_add_right (by
          rw [← inter_diff_distrib_left]
          apply measure_mono
          exact inter_subset_right.trans <| by simp [symmDiff_def]) _
  rw [← add_zero <| mean μ u F (h' • s)]
  exact le_of_tendsto_of_tendsto'
    (hfoel.tendsto_nhds_mean _)
    ((hfoel.tendsto_nhds_mean _).add tendsto₀)
    (by simp only [← ENNReal.add_div]; exact fun i ↦ by gcongr; exact h_le_add i)

/-- If there exists a non-trivial Følner filter with respect to some group `G` acting on a measure
    space `X`, then it exists a `G`-invariant finitely additive probability measure on `X`. -/
theorem IsFoelner.amenable [SMulInvariantMeasure G X μ] [NeBot l] (hfoel : IsFoelner G μ l F) :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
        ∀ (g : G) (s : Set X), m (g • s) = m s := by
  use IsFoelner.mean μ (Ultrafilter.of l) F
  refine ⟨?_, ?_, ?_⟩
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_univ_eq_one
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_union_eq_add_of_disjoint
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_smul_eq_mean

variable (G μ) in
/-- The maximal Følner filter with respect to some group `G` acting on a
    measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s`
    on measurable sets of finite non-zero measure. -/
def maxFoelner : Filter (Set X) :=
  𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
  ⨅ (g : G), (comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0))

variable (l F) in
theorem isFoelner_iff_tendsto : IsFoelner G μ l F ↔ Tendsto F l (maxFoelner G μ) := by
  simp [maxFoelner, tendsto_inf, tendsto_iInf, isFoelner_iff, Function.comp_def, and_assoc]

theorem amenable_of_maxFoelner_ne_bot [SMulInvariantMeasure G X μ] (h : NeBot (maxFoelner G μ)) :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
        ∀ (g : G) (s : Set X), m (g • s) = m s :=
  IsFoelner.amenable <| (isFoelner_iff_tendsto _ _).2 <| @tendsto_id _ (maxFoelner G μ)

end Filter
