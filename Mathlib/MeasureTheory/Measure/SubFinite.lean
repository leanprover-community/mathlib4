/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne. All rights reserved.
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Results about subtraction of finite measures

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ξ : Measure α}

lemma sub_le_iff_le_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ - ν ≤ ξ ↔ μ ≤ ξ + ν := by
  refine ⟨fun h ↦ ?_, sub_le_of_le_add⟩
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  suffices μ.restrict s ≤ ξ.restrict s + ν.restrict s
      ∧ μ.restrict sᶜ ≤ ξ.restrict sᶜ + ν.restrict sᶜ by
    have h_eq_restrict (μ : Measure α) : μ = μ.restrict s + μ.restrict sᶜ := by
      rw [restrict_add_restrict_compl hs.measurableSet]
    rw [h_eq_restrict μ, h_eq_restrict ξ, h_eq_restrict ν]
    suffices μ.restrict s + μ.restrict sᶜ
        ≤ ξ.restrict s + ν.restrict s + (ξ.restrict sᶜ + ν.restrict sᶜ) by
      refine this.trans_eq ?_
      abel
    gcongr
    · exact this.1
    · exact this.2
  constructor
  · have h_le := hs.le_on
    refine h_le.trans ?_
    exact Measure.le_add_left le_rfl
  · have h_le := hs.ge_on_compl
    have h' : μ.restrict sᶜ - ν.restrict sᶜ ≤ ξ.restrict sᶜ := by
      rw [← restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl]
      exact restrict_mono subset_rfl h
    exact (sub_le_iff_le_add_of_le h_le).mp h'

lemma add_sub_of_mutuallySingular (h : μ ⟂ₘ ξ) : μ + (ν - ξ) = μ + ν - ξ := by
  let s := h.nullSet
  have hs : MeasurableSet s := h.measurableSet_nullSet
  suffices μ.restrict s + (ν - ξ).restrict s = μ.restrict s + ν.restrict s - ξ.restrict s
      ∧ μ.restrict sᶜ + (ν - ξ).restrict sᶜ = μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ by
    calc μ + (ν - ξ)
    _ = μ.restrict s + μ.restrict sᶜ + (ν - ξ).restrict s + (ν - ξ).restrict sᶜ := by
      rw [restrict_add_restrict_compl hs, add_assoc, restrict_add_restrict_compl hs]
    _ = μ.restrict s + (ν - ξ).restrict s + (μ.restrict sᶜ + (ν - ξ).restrict sᶜ) := by abel
    _ = (μ.restrict s + ν.restrict s - ξ.restrict s) +
        (μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ) := by rw [this.1, this.2]
    _ = (μ + ν - ξ).restrict s + (μ + ν - ξ).restrict sᶜ := by
        simp [restrict_sub_eq_restrict_sub_restrict hs,
          restrict_sub_eq_restrict_sub_restrict hs.compl]
    _ = μ + ν - ξ := by rw [restrict_add_restrict_compl hs]
  constructor
  · rw [h.restrict_nullSet, restrict_sub_eq_restrict_sub_restrict hs]
    simp
  · rw [restrict_sub_eq_restrict_sub_restrict hs.compl, h.restrict_compl_nullSet]
    simp

/-- Auxiliary lemma for `withDensity_sub`. -/
private lemma withDensity_sub_aux {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hg : Measurable g) (hgf : g ≤ᵐ[μ] f) :
    (μ.withDensity f - μ.withDensity g) = μ.withDensity (f - g) := by
  refine le_antisymm ?_ ?_
  · refine sub_le_of_le_add ?_
    rw [← withDensity_add_right _ hg]
    refine withDensity_mono (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    exact le_tsub_add
  · rw [sub_def, le_sInf_iff]
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ
    rw [le_iff] at hξ ⊢
    intro s hs
    specialize hξ s hs
    simp only [coe_add, Pi.add_apply] at hξ
    simp_rw [withDensity_apply _ hs] at hξ ⊢
    simp only [Pi.sub_apply]
    rw [lintegral_sub hg]
    · rwa [tsub_le_iff_right]
    · rw [← withDensity_apply _ hs]
      simp
    · exact ae_restrict_of_ae hgf

lemma withDensity_sub {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity f - μ.withDensity g) = μ.withDensity (f - g) := by
  refine le_antisymm ?_ ?_
  · refine sub_le_of_le_add ?_
    rw [← withDensity_add_right _ hg]
    refine withDensity_mono (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    exact le_tsub_add
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
        ≤ (μ.withDensity f - μ.withDensity g).restrict tᶜ by
      refine this.trans ?_
      exact Measure.le_add_left le_rfl
    rw [restrict_sub_eq_restrict_sub_restrict ht.compl]
    simp_rw [restrict_withDensity ht.compl]
    have : IsFiniteMeasure ((μ.restrict tᶜ).withDensity g) := by
      rw [← restrict_withDensity ht.compl]
      infer_instance
    rw [withDensity_sub_aux hg]
    refine ae_restrict_of_forall_mem ht.compl fun x hx ↦ ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, t] at hx
    exact hx.le

lemma sub_apply_eq_rnDeriv_add_singularPart [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α) :
    (μ - ν) s = ν.withDensity (fun a ↦ μ.rnDeriv ν a - 1) s + μ.singularPart ν s := by
  have hμ : μ = ν.withDensity (fun a ↦ μ.rnDeriv ν a) + μ.singularPart ν := by
    rw [rnDeriv_add_singularPart]
  have hν : ν = ν.withDensity 1 := by rw [withDensity_one]
  conv_lhs => rw [hν, hμ, add_comm _ (μ.singularPart ν)]
  rw [← add_sub_of_mutuallySingular]
  swap; · simpa only [withDensity_one] using mutuallySingular_singularPart μ ν
  simp only [coe_add, Pi.add_apply]
  have : IsFiniteMeasure (ν.withDensity 1) := by simp only [withDensity_one]; infer_instance
  rw [add_comm, withDensity_sub (by fun_prop) (by fun_prop)]
  congr

end MeasureTheory.Measure
