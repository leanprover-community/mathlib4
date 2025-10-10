/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Basic

/-!
# Bochner integrals of kernels

-/

open MeasureTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : β → E} {a : α}

namespace Kernel

lemma IsFiniteKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x ↦ (κ x).real s) μ := by
  refine Integrable.mono' (integrable_const κ.bound.toReal)
    ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact ENNReal.toReal_mono (Kernel.bound_ne_top _) (Kernel.measure_le_bound _ _ _)

lemma IsMarkovKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x).real s) μ :=
  IsFiniteKernel.integrable μ κ hs

lemma integral_congr_ae₂ {f g : α → β → E} {μ : Measure α} (h : ∀ᵐ a ∂μ, f a =ᵐ[κ a] g a) :
    ∫ a, ∫ b, f a b ∂(κ a) ∂μ = ∫ a, ∫ b, g a b ∂(κ a) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

lemma integral_indicator₂ (f : α → β → E) (s : Set α) (a : α) :
    ∫ y, s.indicator (f · y) a ∂κ a = s.indicator (fun x ↦ ∫ y, f x y ∂κ x) a := by
  by_cases ha : a ∈ s <;> simp [ha]

section Deterministic

variable [CompleteSpace E] {g : α → β}

theorem integral_deterministic' (hg : Measurable g) (hf : StronglyMeasurable f) :
    ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, integral_dirac' _ _ hf]

@[simp]
theorem integral_deterministic [MeasurableSingletonClass β] (hg : Measurable g) :
    ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, integral_dirac _ (g a)]

theorem setIntegral_deterministic' (hg : Measurable g)
    (hf : StronglyMeasurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setIntegral_dirac' hf _ hs]

@[simp]
theorem setIntegral_deterministic [MeasurableSingletonClass β] (hg : Measurable g)
    (s : Set β) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setIntegral_dirac f _ s]

end Deterministic

section Const

@[simp]
theorem integral_const {μ : Measure β} : ∫ x, f x ∂const α μ a = ∫ x, f x ∂μ := by
  rw [const_apply]

@[simp]
theorem setIntegral_const {μ : Measure β} {s : Set β} :
    ∫ x in s, f x ∂const α μ a = ∫ x in s, f x ∂μ := by rw [const_apply]

end Const

section Restrict

variable {s : Set β}

@[simp]
theorem integral_restrict (hs : MeasurableSet s) :
    ∫ x, f x ∂κ.restrict hs a = ∫ x in s, f x ∂κ a := by
  rw [restrict_apply]

@[simp]
theorem setIntegral_restrict (hs : MeasurableSet s) (t : Set β) :
    ∫ x in t, f x ∂κ.restrict hs a = ∫ x in t ∩ s, f x ∂κ a := by
  rw [restrict_apply, Measure.restrict_restrict' hs]

end Restrict

section Piecewise

variable {η : Kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· ∈ s)]

theorem integral_piecewise (a : α) (g : β → E) :
    ∫ b, g b ∂piecewise hs κ η a = if a ∈ s then ∫ b, g b ∂κ a else ∫ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

theorem setIntegral_piecewise (a : α) (g : β → E) (t : Set β) :
    ∫ b in t, g b ∂piecewise hs κ η a =
      if a ∈ s then ∫ b in t, g b ∂κ a else ∫ b in t, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

end Piecewise

end Kernel
end ProbabilityTheory
