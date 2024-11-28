/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Group.Measure

/-!
# Bochner Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about integrability and Bochner integration.
-/

namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {𝕜 M α G E F : Type*} [MeasurableSpace G]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
variable {μ : Measure G} {f : G → E} {g : G}

section MeasurableInv

variable [Group G] [MeasurableInv G]

@[to_additive]
theorem Integrable.comp_inv [IsInvInvariant μ] {f : G → F} (hf : Integrable f μ) :
    Integrable (fun t ↦ f t⁻¹) μ :=
  (hf.mono_measure (map_inv_eq_self μ).le).comp_measurable measurable_inv

@[to_additive]
theorem integral_inv_eq_self (f : G → E) (μ : Measure G) [IsInvInvariant μ] :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : G => x⁻¹ := (MeasurableEquiv.inv G).measurableEmbedding
  rw [← h.integral_map, map_inv_eq_self]

end MeasurableInv

section MeasurableMul

variable [Group G] [MeasurableMul G]

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[to_additive
      "Translating a function by left-addition does not change its integral with respect to a
      left-invariant measure."] -- Porting note: was `@[simp]`
theorem integral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x ↦ g * x := (MeasurableEquiv.mulLeft g).measurableEmbedding
  rw [← h_mul.integral_map, map_mul_left_eq_self]

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[to_additive
      "Translating a function by right-addition does not change its integral with respect to a
      right-invariant measure."] -- Porting note: was `@[simp]`
theorem integral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x ↦ x * g :=
    (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← h_mul.integral_map, map_mul_right_eq_self]

@[to_additive] -- Porting note: was `@[simp]`
theorem integral_div_right_eq_self [IsMulRightInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (x / g) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f g⁻¹]

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive
      "If some left-translate of a function negates it, then the integral of the function with
      respect to a left-invariant measure is 0."]
theorem integral_eq_zero_of_mul_left_eq_neg [IsMulLeftInvariant μ] (hf' : ∀ x, f (g * x) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_left_eq_self]

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive
      "If some right-translate of a function negates it, then the integral of the function with
      respect to a right-invariant measure is 0."]
theorem integral_eq_zero_of_mul_right_eq_neg [IsMulRightInvariant μ] (hf' : ∀ x, f (x * g) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_right_eq_self]

@[to_additive]
theorem Integrable.comp_mul_left {f : G → F} [IsMulLeftInvariant μ] (hf : Integrable f μ) (g : G) :
    Integrable (fun t ↦ f (g * t)) μ :=
  (hf.mono_measure (map_mul_left_eq_self μ g).le).comp_measurable <| measurable_const_mul g

@[to_additive]
theorem Integrable.comp_mul_right {f : G → F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t ↦ f (t * g)) μ :=
  (hf.mono_measure (map_mul_right_eq_self μ g).le).comp_measurable <| measurable_mul_const g

@[to_additive]
theorem Integrable.comp_div_right {f : G → F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t ↦ f (t / g)) μ := by
  simp_rw [div_eq_mul_inv]
  exact hf.comp_mul_right g⁻¹

variable [MeasurableInv G]

@[to_additive]
theorem Integrable.comp_div_left {f : G → F} [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (hf : Integrable f μ) (g : G) : Integrable (fun t ↦ f (g / t)) μ :=
  ((measurePreserving_div_left μ g).integrable_comp hf.aestronglyMeasurable).mpr hf

@[to_additive] -- Porting note: was `@[simp]`
theorem integrable_comp_div_left (f : G → F) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    Integrable (fun t ↦ f (g / t)) μ ↔ Integrable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_div_left g⟩
  convert h.comp_inv.comp_mul_left g⁻¹
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]

@[to_additive] -- Porting note: was `@[simp]`
theorem integral_div_left_eq_self (f : G → E) (μ : Measure G) [IsInvInvariant μ]
    [IsMulLeftInvariant μ] (x' : G) : (∫ x, f (x' / x) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, integral_inv_eq_self (fun x ↦ f (x' * x)) μ,
    integral_mul_left_eq_self f x']

end MeasurableMul

section SMul

variable [Group G] [MeasurableSpace α] [MulAction G α] [MeasurableSMul G α]

@[to_additive] -- Porting note: was `@[simp]`
theorem integral_smul_eq_self {μ : Measure α} [SMulInvariantMeasure G α μ] (f : α → E) {g : G} :
    (∫ x, f (g • x) ∂μ) = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : α => g • x := (MeasurableEquiv.smul g).measurableEmbedding
  rw [← h.integral_map, map_smul]

end SMul

end MeasureTheory
