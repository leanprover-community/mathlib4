/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Sub

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Results about subtraction of finite measures

The content of this file is not placed in `MeasureTheory.Measure.Sub` because it uses tools that are
not imported in the other file: the Hahn decomposition of finite measures and measures built with
`withDensity`.

## Main statements

* `sub_le_iff_le_add`: for `μ` and `ν` finite measures, `μ - ν ≤ ξ ↔ μ ≤ ξ + ν`. See also
  `sub_le_iff_le_add_of_le` for the case where only `ν` is finite, with the additional hypothesis
  `ν ≤ μ`.
* `withDensity_sub`: If `μ.withDensity g` is finite, then
  `μ.withDensity (f - g) = μ.withDensity f - μ.withDensity g`.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ξ : Measure α}

lemma sub_le_iff_le_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ - ν ≤ ξ ↔ μ ≤ ξ + ν := by
  refine ⟨fun h ↦ ?_, sub_le_of_le_add⟩
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h_le_s : μ.restrict s ≤ ξ.restrict s + ν.restrict s :=
    hs.le_on.trans (Measure.le_add_left le_rfl)
  have h_le_s_compl : μ.restrict sᶜ ≤ ξ.restrict sᶜ + ν.restrict sᶜ := by
    refine (sub_le_iff_le_add_of_le hs.ge_on_compl).mp ?_
    rw [← restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl]
    exact restrict_mono subset_rfl h
  rw [← restrict_add_restrict_compl (μ := μ) hs.measurableSet,
    ← restrict_add_restrict_compl (μ := ξ) hs.measurableSet,
    ← restrict_add_restrict_compl (μ := ν) hs.measurableSet]
  suffices μ.restrict s + μ.restrict sᶜ
    ≤ ξ.restrict s + ν.restrict s + (ξ.restrict sᶜ + ν.restrict sᶜ) from this.trans_eq (by abel)
  gcongr

lemma withDensity_sub_of_le {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hg : Measurable g) (hgf : g ≤ᵐ[μ] f) :
    μ.withDensity (f - g) = μ.withDensity f - μ.withDensity g := by
  ext s hs
  rw [sub_apply hs (withDensity_mono hgf), withDensity_apply _ hs, withDensity_apply _ hs,
    withDensity_apply _ hs, ← lintegral_sub hg _ (ae_restrict_of_ae hgf)]
  · simp
  · simp [← withDensity_apply _ hs]

lemma withDensity_sub {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity (f - g) = μ.withDensity f - μ.withDensity g := by
  refine le_antisymm ?_ ?_
  · let t := {x | f x ≤ g x}
    have ht : MeasurableSet t := measurableSet_le hf hg
    rw [← restrict_add_restrict_compl (μ := μ.withDensity (f - g)) ht,
      ← restrict_add_restrict_compl (μ := μ.withDensity f - μ.withDensity g) ht]
    have h_zero : (μ.withDensity (f - g)).restrict t = 0 := by
      simp only [restrict_eq_zero]
      rw [withDensity_apply _ ht, lintegral_eq_zero_iff (by fun_prop)]
      refine ae_restrict_of_forall_mem ht fun x hx ↦ ?_
      simpa [tsub_eq_zero_iff_le]
    rw [h_zero, zero_add]
    suffices (μ.withDensity (f - g)).restrict tᶜ
      ≤ (μ.withDensity f - μ.withDensity g).restrict tᶜ from this.trans (Measure.le_add_left le_rfl)
    rw [restrict_sub_eq_restrict_sub_restrict ht.compl]
    simp_rw [restrict_withDensity ht.compl]
    have : IsFiniteMeasure ((μ.restrict tᶜ).withDensity g) := by
      rw [← restrict_withDensity ht.compl]
      infer_instance
    rw [withDensity_sub_of_le hg]
    refine ae_restrict_of_forall_mem ht.compl fun x hx ↦ ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, t] at hx
    exact hx.le
  · refine sub_le_of_le_add ?_
    rw [← withDensity_add_right _ hg]
    exact withDensity_mono (ae_of_all _ fun x ↦ le_tsub_add)

end MeasureTheory.Measure
