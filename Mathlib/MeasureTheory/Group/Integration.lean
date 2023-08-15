/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Group.Measure

#align_import measure_theory.group.integration from "leanprover-community/mathlib"@"ec247d43814751ffceb33b758e8820df2372bf6f"

/-!
# Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about integrability, Lebesgue integration and Bochner integration.
-/


namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {𝕜 M α G E F : Type*} [MeasurableSpace G]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]

variable {μ : Measure G} {f : G → E} {g : G}

section MeasurableInv

variable [Group G] [MeasurableInv G]

@[to_additive]
theorem Integrable.comp_inv [IsInvInvariant μ] {f : G → F} (hf : Integrable f μ) :
    Integrable (fun t => f t⁻¹) μ :=
  (hf.mono_measure (map_inv_eq_self μ).le).comp_measurable measurable_inv
#align measure_theory.integrable.comp_inv MeasureTheory.Integrable.comp_inv
#align measure_theory.integrable.comp_neg MeasureTheory.Integrable.comp_neg

@[to_additive]
theorem integral_inv_eq_self (f : G → E) (μ : Measure G) [IsInvInvariant μ] :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : G => x⁻¹ := (MeasurableEquiv.inv G).measurableEmbedding
  rw [← h.integral_map, map_inv_eq_self]
#align measure_theory.integral_inv_eq_self MeasureTheory.integral_inv_eq_self
#align measure_theory.integral_neg_eq_self MeasureTheory.integral_neg_eq_self

end MeasurableInv

section MeasurableMul

variable [Group G] [MeasurableMul G]

/-- Translating a function by left-multiplication does not change its `MeasureTheory.lintegral`
with respect to a left-invariant measure. -/
@[to_additive
      "Translating a function by left-addition does not change its `MeasureTheory.lintegral` with
      respect to a left-invariant measure."]
theorem lintegral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]
#align measure_theory.lintegral_mul_left_eq_self MeasureTheory.lintegral_mul_left_eq_self
#align measure_theory.lintegral_add_left_eq_self MeasureTheory.lintegral_add_left_eq_self

/-- Translating a function by right-multiplication does not change its `MeasureTheory.lintegral`
with respect to a right-invariant measure. -/
@[to_additive
      "Translating a function by right-addition does not change its `MeasureTheory.lintegral` with
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
  simp_rw [div_eq_mul_inv]
  -- Porting note: was `simp_rw`
  rw [lintegral_mul_right_eq_self f g⁻¹]
#align measure_theory.lintegral_div_right_eq_self MeasureTheory.lintegral_div_right_eq_self
#align measure_theory.lintegral_sub_right_eq_self MeasureTheory.lintegral_sub_right_eq_self

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[to_additive
      "Translating a function by left-addition does not change its integral with respect to a
      left-invariant measure."] -- Porting note: was `@[simp]`
theorem integral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => g * x := (MeasurableEquiv.mulLeft g).measurableEmbedding
  rw [← h_mul.integral_map, map_mul_left_eq_self]
#align measure_theory.integral_mul_left_eq_self MeasureTheory.integral_mul_left_eq_self
#align measure_theory.integral_add_left_eq_self MeasureTheory.integral_add_left_eq_self

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[to_additive
      "Translating a function by right-addition does not change its integral with respect to a
      right-invariant measure."] -- Porting note: was `@[simp]`
theorem integral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => x * g :=
    (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← h_mul.integral_map, map_mul_right_eq_self]
#align measure_theory.integral_mul_right_eq_self MeasureTheory.integral_mul_right_eq_self
#align measure_theory.integral_add_right_eq_self MeasureTheory.integral_add_right_eq_self

@[to_additive] -- Porting note: was `@[simp]`
theorem integral_div_right_eq_self [IsMulRightInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (x / g) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv]
  -- Porting note: was `simp_rw`
  rw [integral_mul_right_eq_self f g⁻¹]
#align measure_theory.integral_div_right_eq_self MeasureTheory.integral_div_right_eq_self
#align measure_theory.integral_sub_right_eq_self MeasureTheory.integral_sub_right_eq_self

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive
      "If some left-translate of a function negates it, then the integral of the function with
      respect to a left-invariant measure is 0."]
theorem integral_eq_zero_of_mul_left_eq_neg [IsMulLeftInvariant μ] (hf' : ∀ x, f (g * x) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_left_eq_self]
#align measure_theory.integral_eq_zero_of_mul_left_eq_neg MeasureTheory.integral_eq_zero_of_mul_left_eq_neg
#align measure_theory.integral_eq_zero_of_add_left_eq_neg MeasureTheory.integral_eq_zero_of_add_left_eq_neg

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive
      "If some right-translate of a function negates it, then the integral of the function with
      respect to a right-invariant measure is 0."]
theorem integral_eq_zero_of_mul_right_eq_neg [IsMulRightInvariant μ] (hf' : ∀ x, f (x * g) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_right_eq_self]
#align measure_theory.integral_eq_zero_of_mul_right_eq_neg MeasureTheory.integral_eq_zero_of_mul_right_eq_neg
#align measure_theory.integral_eq_zero_of_add_right_eq_neg MeasureTheory.integral_eq_zero_of_add_right_eq_neg

@[to_additive]
theorem Integrable.comp_mul_left {f : G → F} [IsMulLeftInvariant μ] (hf : Integrable f μ) (g : G) :
    Integrable (fun t => f (g * t)) μ :=
  (hf.mono_measure (map_mul_left_eq_self μ g).le).comp_measurable <| measurable_const_mul g
#align measure_theory.integrable.comp_mul_left MeasureTheory.Integrable.comp_mul_left
#align measure_theory.integrable.comp_add_left MeasureTheory.Integrable.comp_add_left

@[to_additive]
theorem Integrable.comp_mul_right {f : G → F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t => f (t * g)) μ :=
  (hf.mono_measure (map_mul_right_eq_self μ g).le).comp_measurable <| measurable_mul_const g
#align measure_theory.integrable.comp_mul_right MeasureTheory.Integrable.comp_mul_right
#align measure_theory.integrable.comp_add_right MeasureTheory.Integrable.comp_add_right

@[to_additive]
theorem Integrable.comp_div_right {f : G → F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t => f (t / g)) μ := by
  simp_rw [div_eq_mul_inv]
  exact hf.comp_mul_right g⁻¹
#align measure_theory.integrable.comp_div_right MeasureTheory.Integrable.comp_div_right
#align measure_theory.integrable.comp_sub_right MeasureTheory.Integrable.comp_sub_right

variable [MeasurableInv G]

@[to_additive]
theorem Integrable.comp_div_left {f : G → F} [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (hf : Integrable f μ) (g : G) : Integrable (fun t => f (g / t)) μ :=
  ((measurePreserving_div_left μ g).integrable_comp hf.aestronglyMeasurable).mpr hf
#align measure_theory.integrable.comp_div_left MeasureTheory.Integrable.comp_div_left
#align measure_theory.integrable.comp_sub_left MeasureTheory.Integrable.comp_sub_left

@[to_additive] -- Porting note: was `@[simp]`
theorem integrable_comp_div_left (f : G → F) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    Integrable (fun t => f (g / t)) μ ↔ Integrable f μ := by
  refine' ⟨fun h => _, fun h => h.comp_div_left g⟩
  convert h.comp_inv.comp_mul_left g⁻¹
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]
#align measure_theory.integrable_comp_div_left MeasureTheory.integrable_comp_div_left
#align measure_theory.integrable_comp_sub_left MeasureTheory.integrable_comp_sub_left

@[to_additive] -- Porting note: was `@[simp]`
theorem integral_div_left_eq_self (f : G → E) (μ : Measure G) [IsInvInvariant μ]
    [IsMulLeftInvariant μ] (x' : G) : (∫ x, f (x' / x) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv]
  -- Porting note: was `simp_rw`
  rw [integral_inv_eq_self (fun x => f (x' * x)) μ, integral_mul_left_eq_self f x']
#align measure_theory.integral_div_left_eq_self MeasureTheory.integral_div_left_eq_self
#align measure_theory.integral_sub_left_eq_self MeasureTheory.integral_sub_left_eq_self

end MeasurableMul

section SMul

variable [Group G] [MeasurableSpace α] [MulAction G α] [MeasurableSMul G α]

@[to_additive] -- Porting note: was `@[simp]`
theorem integral_smul_eq_self {μ : Measure α} [SMulInvariantMeasure G α μ] (f : α → E) {g : G} :
    (∫ x, f (g • x) ∂μ) = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : α => g • x := (MeasurableEquiv.smul g).measurableEmbedding
  rw [← h.integral_map, map_smul]
#align measure_theory.integral_smul_eq_self MeasureTheory.integral_smul_eq_self
#align measure_theory.integral_vadd_eq_self MeasureTheory.integral_vadd_eq_self

end SMul

section TopologicalGroup

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] [BorelSpace G] [IsMulLeftInvariant μ]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive
      "For nonzero regular left invariant measures, the integral of a continuous nonnegative
      function `f` is 0 iff `f` is 0."]
theorem lintegral_eq_zero_of_isMulLeftInvariant [Regular μ] (hμ : μ ≠ 0) {f : G → ℝ≥0∞}
    (hf : Continuous f) : ∫⁻ x, f x ∂μ = 0 ↔ f = 0 := by
  haveI := isOpenPosMeasure_of_mulLeftInvariant_of_regular hμ
  rw [lintegral_eq_zero_iff hf.measurable, hf.ae_eq_iff_eq μ continuous_zero]
#align measure_theory.lintegral_eq_zero_of_is_mul_left_invariant MeasureTheory.lintegral_eq_zero_of_isMulLeftInvariant
#align measure_theory.lintegral_eq_zero_of_is_add_left_invariant MeasureTheory.lintegral_eq_zero_of_isAddLeftInvariant

end TopologicalGroup

end MeasureTheory
