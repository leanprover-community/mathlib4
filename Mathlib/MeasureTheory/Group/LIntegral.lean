/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Group.Measure

/-!
# Lebesgue Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about Lebesgue integration.
-/

assert_not_exists NormedSpace

namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {G : Type*} [MeasurableSpace G] {μ : Measure G} {g : G}

section MeasurableMul

variable [Group G] [MeasurableMul G]

/-- Translating a function by left-multiplication does not change its Lebesgue integral
with respect to a left-invariant measure. -/
@[to_additive
      "Translating a function by left-addition does not change its Lebesgue integral with
      respect to a left-invariant measure."]
theorem lintegral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]
#align measure_theory.lintegral_mul_left_eq_self MeasureTheory.lintegral_mul_left_eq_self
#align measure_theory.lintegral_add_left_eq_self MeasureTheory.lintegral_add_left_eq_self

/-- Translating a function by right-multiplication does not change its Lebesgue integral
with respect to a right-invariant measure. -/
@[to_additive
      "Translating a function by right-addition does not change its Lebesgue integral with
      respect to a right-invariant measure."]
theorem lintegral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (x * g) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert (lintegral_map_equiv f <| MeasurableEquiv.mulRight g).symm using 1
  simp [map_mul_right_eq_self μ g]
#align measure_theory.lintegral_mul_right_eq_self MeasureTheory.lintegral_mul_right_eq_self
#align measure_theory.lintegral_add_right_eq_self MeasureTheory.lintegral_add_right_eq_self

@[to_additive] -- Porting note: was `@[simp]`
theorem lintegral_div_right_eq_self [IsMulRightInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (x / g) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_mul_right_eq_self f g⁻¹]
#align measure_theory.lintegral_div_right_eq_self MeasureTheory.lintegral_div_right_eq_self
#align measure_theory.lintegral_sub_right_eq_self MeasureTheory.lintegral_sub_right_eq_self

end MeasurableMul

section TopologicalGroup

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] [BorelSpace G] [IsMulLeftInvariant μ]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive
      "For nonzero regular left invariant measures, the integral of a continuous nonnegative
      function `f` is 0 iff `f` is 0."]
theorem lintegral_eq_zero_of_isMulLeftInvariant [Regular μ] [NeZero μ] {f : G → ℝ≥0∞}
    (hf : Continuous f) : ∫⁻ x, f x ∂μ = 0 ↔ f = 0 := by
  rw [lintegral_eq_zero_iff hf.measurable, hf.ae_eq_iff_eq μ continuous_zero]
#align measure_theory.lintegral_eq_zero_of_is_mul_left_invariant MeasureTheory.lintegral_eq_zero_of_isMulLeftInvariant
#align measure_theory.lintegral_eq_zero_of_is_add_left_invariant MeasureTheory.lintegral_eq_zero_of_isAddLeftInvariant

end TopologicalGroup

end MeasureTheory
