/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle Averages

For a function `f` on the complex plane, this file introduces the definition
`Real.circleAverage f c R` as a shorthand for the average of `f` on the circle with center `c` and
radius `R`, equipped with the rotation-invariant measure of total volume one. Like
`IntervalAverage`, this notion exists as a convenience. It avoids notationally inconvenient
compositions of `f` with `circleMap` and avoids the need to manually eliminate `2 * π` every time
an average is computed.

Note: Like the interval average defined in `Mathlib/MeasureTheory/Integral/IntervalAverage.lean`,
the `circleAverage` defined here is a purely measure-theoretic average. It should not be confused
with `circleIntegral`, which is the path integral over the circle path. The relevant integrability
property `circleAverage` is `CircleIntegrable`, as defined in
`Mathlib/MeasureTheory/Integral/CircleIntegral.lean`.

Implementation Note: Like `circleMap`, `circleAverage`s are defined for negative radii. The theorem
`circleAverage_congr_negRadius` shows that the average is independent of the radius' sign.
-/

open Complex Filter Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  {f f₁ f₂ : ℂ → E} {c : ℂ} {R : ℝ} {a : 𝕜}

namespace Real

/-!
# Definition
-/

variable (f c R) in
/--
Define `circleAverage f c R` as the average value of `f` on the circle with center `c` and radius
`R`. This is a real notion, which should not be confused with the complex path integral notion
defined in `circleIntegral` (integrating with respect to `dz`).
-/
noncomputable def circleAverage : E :=
  (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)

lemma circleAverage_def :
    circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := rfl

/-- Expression of `circleAverage´ in terms of interval averages. -/
lemma circleAverage_eq_intervalAverage :
    circleAverage f c R = ⨍ θ in 0..2 * π, f (circleMap c R θ) := by
  simp [circleAverage, interval_average_eq]

/-- Interval averages for zero radii equal values at the center point. -/
@[simp] lemma circleAverage_zero [CompleteSpace E] :
    circleAverage f c 0 = f c := by
  rw [circleAverage]
  simp only [circleMap_zero_radius, Function.const_apply,
    intervalIntegral.integral_const, sub_zero,
    ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero),
    one_smul]

/--
Expression of `circleAverage´ with arbitrary center in terms of `circleAverage` with center zero.
-/
lemma circleAverage_fun_add :
    circleAverage (fun z ↦ f (z + c)) 0 R = circleAverage f c R := by
  unfold circleAverage circleMap
  congr
  ext θ
  simp only [zero_add]
  congr 1
  ring

/--
Expression of the `circleAverage` in terms of a `circleIntegral`.
-/
theorem circleAverage_eq_circleIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} (h : R ≠ 0) :
    circleAverage f c R = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z) := by
  calc circleAverage f c R
  _ = (↑(2 * π) : ℂ)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := by
    simp [circleAverage, ← coe_smul]
  _ = (2 * π * I)⁻¹ • ∫ θ in 0..2 * π, I • f (circleMap c R θ) := by
    rw [intervalIntegral.integral_smul, mul_inv_rev, smul_smul]
    match_scalars
    field_simp
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z) := by
    unfold circleIntegral
    congr with θ
    simp [deriv_circleMap, circleMap_sub_center, smul_smul]
    field_simp [circleMap_ne_center h]

/-!
## Congruence Lemmata
-/

/-- Circle averages do not change when shifting the angle. -/
lemma circleAverage_eq_integral_add (η : ℝ) :
    circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R (θ + η)) := by
  rw [intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap c R θ))]
  have t₀ : (fun θ ↦ f (circleMap c R θ)).Periodic (2 * π) :=
    fun x ↦ by simp [periodic_circleMap c R x]
  have := t₀.intervalIntegral_add_eq 0 η
  rw [zero_add, add_comm] at this
  rw [zero_add]
  simp only [circleAverage, mul_inv_rev]
  congr

/-- Circle averages do not change when replacing the radius by its negative. -/
@[simp] theorem circleAverage_neg_radius :
    circleAverage f c (-R) = circleAverage f c R := by
  unfold circleAverage
  simp_rw [circleMap_neg_radius, ← circleAverage_def, circleAverage_eq_integral_add π]

/-- Circle averages do not change when replacing the radius by its absolute value. -/
@[simp] theorem circleAverage_abs_radius :
    circleAverage f c |R| = circleAverage f c R := by
  by_cases hR : 0 ≤ R
  · rw [abs_of_nonneg hR]
  · rw [abs_of_neg (not_le.1 hR), circleAverage_neg_radius]

/-- If two functions agree outside of a discrete set in the circle, then their averages agree. -/
theorem circleAverage_congr_codiscreteWithin
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R ≠ 0) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin.mono (by tauto) (circleMap_preimage_codiscrete hR hf)

/-- If two functions agree on the circle, then their circle averages agree. -/
theorem circleAverage_congr_sphere {f₁ f₂ : ℂ → E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  exact intervalIntegral.integral_congr (fun x ↦ by simp [hf (circleMap_mem_sphere' c R x)])

/--
Express the circle average over an arbitrary circle as a circle average over the unit circle.
-/
theorem circleAverage_eq_circleAverage_zero_one :
    circleAverage f c R = (circleAverage (fun z ↦ f (R * z + c)) 0 1) := by
  unfold circleAverage circleMap
  congr with θ
  ring_nf
  simp

/--
The circle average of a function `f` on the unit sphere equals the circle average of the function
`z ↦ f z⁻¹`.
-/
@[simp]
theorem circleAverage_zero_one_congr_inv {f : ℂ → E} :
    circleAverage (f ·⁻¹) 0 1 = circleAverage f 0 1 := by
  unfold circleAverage
  congr 1
  calc ∫ θ in 0..2 * π, f (circleMap 0 1 θ)⁻¹
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 (-θ)) := by
    simp [circleMap_zero_inv]
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 θ) := by
    rw [intervalIntegral.integral_comp_neg (fun w ↦ f (circleMap 0 1 w))]
    have t₀ : Function.Periodic (fun w ↦ f (circleMap 0 1 w)) (2 * π) :=
      fun x ↦ by simp [periodic_circleMap 0 1 x]
    simpa using (t₀.intervalIntegral_add_eq_of_pos two_pi_pos (-(2 * π)) 0)

/-!
## Constant Functions
-/

/--
The circle average of a constant function equals the constant.
-/
theorem circleAverage_const [CompleteSpace E] (a : E) (c : ℂ) (R : ℝ) :
    circleAverage (fun _ ↦ a) c R = a := by
  simp only [circleAverage, intervalIntegral.integral_const, ← smul_assoc, sub_zero, smul_eq_mul]
  ring_nf
  simp

/--
If `f x` equals `a` on for every point of the circle, then the circle average of `f` equals `a`.
-/
theorem circleAverage_const_on_circle [CompleteSpace E] {a : E}
    (hf : ∀ x ∈ Metric.sphere c |R|, f x = a) :
    circleAverage f c R = a := by
  rw [circleAverage]
  conv =>
    left; arg 2; arg 1
    intro θ
    rw [hf (circleMap c R θ) (circleMap_mem_sphere' c R θ)]
  apply circleAverage_const a c R

/-!
## Inequalities
-/

/--
If `f x` is smaller than `a` on for every point of the circle, then the circle average of `f` is
smaller than `a`.
-/
theorem circleAverage_mono_on_of_le_circle {f : ℂ → ℝ} {a : ℝ} (hf : CircleIntegrable f c R)
    (h₂f : ∀ x ∈ Metric.sphere c |R|, f x ≤ a) :
    circleAverage f c R ≤ a := by
  rw [← circleAverage_const a c |R|, circleAverage, circleAverage, smul_eq_mul, smul_eq_mul,
    mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf
    intervalIntegrable_const (fun θ _ ↦ h₂f (circleMap c R θ) (circleMap_mem_sphere' c R θ))

/--
Analogue of `intervalIntegral.abs_integral_le_integral_abs`: The absolute value of a circle average
is less than or equal to the circle average of the absolute value of the function.
-/
theorem abs_circleAverage_le_circleAverage_abs {f : ℂ → ℝ} :
    |circleAverage f c R| ≤ circleAverage |f| c R := by
  rw [circleAverage, circleAverage, smul_eq_mul, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.2 two_pi_pos), mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt two_pi_pos)

/-!
## Commutativity with Linear Maps
-/

/-- Circle averages commute with continuous linear maps. -/
theorem _root_.ContinuousLinearMap.circleAverage_comp_comm [CompleteSpace E] (L : E →L[ℝ] F)
    {f : ℂ → E} (hf : CircleIntegrable f c R) :
    circleAverage (L ∘ f) c R = L (circleAverage f c R) := by
  unfold circleAverage
  rw [map_smul]
  congr
  exact L.intervalIntegral_comp_comm hf

/-!
## Behaviour with Respect to Arithmetic Operations
-/

/-- Circle averages commute with scalar multiplication. -/
theorem circleAverage_smul :
    circleAverage (a • f) c R = a • circleAverage f c R := by
  unfold circleAverage
  have := SMulCommClass.symm ℝ 𝕜 E
  rw [smul_comm]
  simp [intervalIntegral.integral_smul]

/-- Circle averages commute with scalar multiplication. -/
theorem circleAverage_fun_smul :
    circleAverage (fun z ↦ a • f z) c R = a • circleAverage f c R :=
  circleAverage_smul

/-- Circle averages commute with addition. -/
theorem circleAverage_add (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (f₁ + f₂) c R = circleAverage f₁ c R + circleAverage f₂ c R := by
  rw [circleAverage, circleAverage, circleAverage, ← smul_add]
  congr
  apply intervalIntegral.integral_add hf₁ hf₂

/-- Circle averages commute with sums. -/
theorem circleAverage_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    circleAverage (∑ i ∈ s, f i) c R = ∑ i ∈ s, circleAverage (f i) c R := by
  unfold circleAverage
  simp [← Finset.smul_sum, intervalIntegral.integral_finset_sum h]

/-- Circle averages commute with subtraction. -/
theorem circleAverage_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (f₁ - f₂) c R = circleAverage f₁ c R - circleAverage f₂ c R := by
  rw [circleAverage, circleAverage, circleAverage, ← smul_sub]
  congr
  apply intervalIntegral.integral_sub hf₁ hf₂


end Real
