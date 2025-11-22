/-
Copyright (c) 2025 Stefano Rocca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Stefano Rocca
-/
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Følner filters - definitions and properties

This file defines Følner filters for measurable spaces acted on by a group.

## Definitions

* `IsFoelner G μ l` : A Følner filter on a measurable `G`-space `X` with measure `μ`
  (a measurable space with an action of `G`) is a filter `l` on `Set X` such that:
    1. Each `s in l` is eventually measurable with finite non-zero measure,
    2. For all `g : G`, `μ (g • s ∆ s) / μ (s)` tends to `0`.

* `MaximalFoelner G μ` : The maximal Følner filter for a measurable `G`-space `X`
  with measure `μ` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s` on measurable
  sets of finite non-zero measure.

-/

open MeasureTheory Filter Set
open scoped ENNReal Pointwise symmDiff Topology Filter

variable {G X : Type*} [MeasurableSpace X] [Group G] [MulAction G X] {μ : Measure X}

namespace Filter

variable (G μ) in
/-- A Følner filter on a measurable `G`-space `X` with measure `μ`
(a measurable space with an action of `G`) is a filter `l` on `Set X` such that:
    1. Each `s in l` is eventually measurable with finite non-zero measure,
    2. For all `g : G`, `μ (g • s ∆ s) / μ (s)` tends to `0`. -/
structure IsFoelner (l : Filter (Set X)) : Prop where
  meas_set : ∀ᶠ s in l, MeasurableSet s
  meas_ne_zero : ∀ᶠ s in l, μ s ≠ 0
  meas_ne_top : ∀ᶠ s in l, μ s ≠ ∞
  tendsto_meas_symmDiff (g : G) : Tendsto (fun s ↦ μ ((g • s) ∆ s) / μ s) l (𝓝 0)

/-- The constant filter `X` is Følner if `X` has finite measure. -/
lemma IsFoelner.pure_of_isFiniteMeasure [NeZero μ] [IsFiniteMeasure μ] :
    IsFoelner G μ (pure .univ) where
  meas_set := by simp
  meas_ne_zero := by simp [NeZero.ne]
  meas_ne_top := by simp
  tendsto_meas_symmDiff (g : G) := by
    simpa using tendsto_pure_nhds (fun s ↦ μ ((g • s) ∆ s) / μ s) .univ

/-- If there exists a non-trivial Følner filter on the measurable `G`-space `X`,
then it exists a `G`-invariant finitely additive probability measure on `X`. -/
lemma IsFoelner.amenable [SMulInvariantMeasure G X μ] {l : Filter (Set X)} [NeBot l]
    (hfoel : IsFoelner G μ l) : ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
    (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
    ∀ (g : G) (s : Set X), m (g • s) = m s := by
  set u := Ultrafilter.of l
  set m := fun t ↦ limUnder u (fun s ↦ μ (t ∩ s) / μ s)
  have compact_Icc := @isCompact_Icc ℝ≥0∞ _ _ _ 0 1
  have subset_Icc : ∀ t, ∀ᶠ s in u, μ (t ∩ s) / μ s ∈ Icc 0 1 := fun t ↦
    Eventually.mono (
      (Eventually.filter_mono (Ultrafilter.of_le l) hfoel.meas_ne_zero).and
      (Eventually.filter_mono (Ultrafilter.of_le l) hfoel.meas_ne_top))
    (fun i hi ↦ by simp [ENNReal.div_le_iff (hi.1) (hi.2)]; exact μ.mono (inter_subset_right))
  use m
  refine ⟨?_, ?_, ?_⟩
  · refine limUnder_mono (tendsto_congr' ?_|>.mp tendsto_const_nhds) (Ultrafilter.of_le l)
    exact Eventually.mono
      (hfoel.meas_ne_zero.and hfoel.meas_ne_top)
      (fun _ hi ↦ by simp [ENNReal.div_self (hi.1) (hi.2)])
  · intro s t ht hdisj
    obtain ⟨_, _, h₁⟩ := u.tendsto_of_eventually_mem_compact compact_Icc (subset_Icc s)
    obtain ⟨_, _, h₂⟩ := u.tendsto_of_eventually_mem_compact compact_Icc (subset_Icc t)
    simp[m, ← limUnder_add h₁ h₂, union_inter_distrib_right, ← ENNReal.add_div]
    refine limUnder_congr' (Eventually.mono
      (Eventually.filter_mono (Ultrafilter.of_le l) hfoel.meas_set)
      (fun i hi ↦ ?_))
    simp[measure_union
      (Disjoint.mono (inter_subset_left) (inter_subset_left) hdisj)
      (MeasurableSet.inter ht hi)]
  · intro g t
    suffices h_le : ∀ (h h' : G), m (h • t) ≤ m (h' • t) by
      simpa [one_smul] using le_antisymm (h_le g 1) (h_le 1 g)
    intro h h'
    have tendsto₀ : Tendsto (fun s ↦ μ ((h⁻¹ • s) ∆ (h'⁻¹ • s)) / μ s) u (𝓝 0) := by
      simpa [u, ← smul_smul, measure_smul_symmDiff _ h'] using
        Tendsto.mono_left (hfoel.tendsto_meas_symmDiff (h' * h⁻¹)) (Ultrafilter.of_le l)
    have h_le : ∀ s, μ (h • t ∩ s) ≤ μ (h' • t ∩ s) + μ ((h⁻¹ • s) ∆ (h'⁻¹ • s)) := by
      intro s
      simp_all [measure_smul_inter]
      set A := t ∩ h⁻¹ • s
      set B := t ∩ h'⁻¹ • s
      calc
        μ A ≤ μ B + μ (A \ B) := by simpa [Set.inter_union_diff] using
          (measure_union_le (A ∩ B) (A \ B)).trans <| add_le_add_right (measure_mono (by simp)) _
        _ ≤ μ B + μ ((h⁻¹ • s) ∆ (h'⁻¹ • s)) :=
          add_le_add_left (by
            rw [← inter_diff_distrib_left]
            apply measure_mono
            exact inter_subset_right.trans (by simp[symmDiff_def])) _
    have := fun s ↦ (by simpa [ENNReal.add_div] using ENNReal.div_le_div_right (h_le s) (μ s))
    obtain ⟨_, _, h₁⟩ := u.tendsto_of_eventually_mem_compact compact_Icc (subset_Icc (h • t))
    obtain ⟨_, _, h₂⟩ := u.tendsto_of_eventually_mem_compact compact_Icc (subset_Icc (h' • t))
    simpa [m, limUnder_add h₂ tendsto₀, Tendsto.limUnder_eq tendsto₀] using
      limUnder_le_of_tendsto_of_tendsto' h₁ (Tendsto.add h₂ tendsto₀) this

variable (G μ) in
/-- The maximal Følner filter for the measurable `G`-space `X` with measure `μ` is the pullback
of `𝓝 0` along the map `S ↦ μ (g • S) / μ S` on measurable sets of finite non-zero measure. -/
def MaximalFoelner : Filter (Set X) :=
  𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
  ⨅ (g : G), (comap (fun s => μ ((g • s) ∆ s) / μ s) (𝓝 0))

theorem isFoelner_iff_le (l : Filter (Set X)) :
    IsFoelner G μ l ↔ l ≤ MaximalFoelner G μ := by
  simp_all [MaximalFoelner, ← eventually_iff, eventually_and]
  constructor
  all_goals intro h
  · exact ⟨⟨h.meas_set, h.meas_ne_zero, h.meas_ne_top⟩,
      fun g ↦ tendsto_iff_comap.1 (h.tendsto_meas_symmDiff g)⟩
  · exact ⟨h.1.1, h.1.2.1, h.1.2.2, fun g ↦ tendsto_iff_comap.2 (h.2 g)⟩

theorem isFoelner_map_iff_tendsto {ι : Type*} (l : Filter ι) (F : ι → Set X) :
    IsFoelner G μ (l.map F) ↔ Tendsto F l (MaximalFoelner G μ) := isFoelner_iff_le (l.map F)

theorem amenable_of_maximalFoelner_ne_bot
    [SMulInvariantMeasure G X μ] (h : NeBot (MaximalFoelner G μ)) :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
    (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
    ∀ (g : G) (s : Set X), m (g • s) = m s :=
  IsFoelner.amenable <|
    (isFoelner_map_iff_tendsto _ _).2 <| @tendsto_id _ (MaximalFoelner G μ)

end Filter
