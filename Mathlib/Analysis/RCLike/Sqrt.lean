/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Square root of RCLike

This file contains the definitions `Complex.sqrt` and `RCLike.sqrt`.
-/

public section

/-- The square root of a complex number. -/
noncomputable abbrev Complex.sqrt (a : ℂ) : ℂ := a ^ (2⁻¹ : ℂ)

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The square root of `RCLike`. -/
noncomputable def RCLike.sqrt (a : 𝕜) : 𝕜 :=
  if h : im (I : 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt
  else (re a).sqrt

theorem Complex.re_sqrt_ofReal (a : ℝ) :
    (sqrt (a : ℂ)).re = a.sqrt := by
  simp only [sqrt, cpow_inv_two_re, norm_real, Real.norm_eq_abs, ofReal_re]
  grind

theorem RCLike.re_sqrt_ofReal (a : ℝ) :
    re (sqrt (a : 𝕜)) = a.sqrt := by
  aesop (add simp [sqrt, Complex.re_sqrt_ofReal])

@[simp] theorem RCLike.sqrt_real (a : ℝ) :
    sqrt a = a.sqrt := by simp [← re_sqrt_ofReal (𝕜 := ℝ)]

@[simp] theorem RCLike.sqrt_complex (a : ℂ) :
    sqrt a = a.sqrt := by simp [sqrt]

open ComplexOrder

theorem Complex.sqrt_of_nonneg {a : ℂ} (ha : 0 ≤ a) :
    a.sqrt = a.re.sqrt := by
  obtain ⟨α : ℝ, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (α : ℂ).sqrt, re_sqrt_ofReal]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]

theorem RCLike.sqrt_symm_complexRingEquiv {a : ℂ} (h : im (I : 𝕜) = 1) :
    sqrt ((complexRingEquiv h).symm a) = (complexRingEquiv h).symm a.sqrt := by
  aesop (add simp [sqrt])

open RCLike in
theorem Complex.sqrt_complexRingEquiv {a : 𝕜} (h : RCLike.im (RCLike.I : 𝕜) = 1) :
    (complexRingEquiv h a).sqrt = complexRingEquiv h (RCLike.sqrt a) := by
  aesop (add simp [RCLike.sqrt])

attribute [local grind =] RCLike.complexRingEquiv_nonneg_iff

theorem RCLike.sqrt_of_nonneg {a : 𝕜} (ha : 0 ≤ a) :
    sqrt a = sqrt (re a) := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt]
  apply_fun complexRingEquiv h
  rw [← Complex.sqrt_complexRingEquiv h, Complex.sqrt_of_nonneg (by grind)]
  simp

theorem Complex.sqrt_neg_of_nonneg {a : ℂ} (ha : 0 ≤ a) :
    (-a).sqrt = I * a.sqrt := by
  obtain ⟨α, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  rw [Complex.sqrt_of_nonneg ha]
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (-(α : ℂ)).sqrt]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα, cpow_inv_two_re, mul_comm]

theorem RCLike.sqrt_neg_of_nonneg {a : 𝕜} (ha : 0 ≤ a) :
    sqrt (-a) = I * sqrt a := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt, Real.sqrt_eq_zero', nonneg_iff.mp ha]
  apply_fun complexRingEquiv h
  rw [← Complex.sqrt_complexRingEquiv h, map_neg, Complex.sqrt_neg_of_nonneg (by grind),
    map_mul, ← Complex.sqrt_complexRingEquiv h]
  simp [h]

theorem Complex.sqrt_neg_one : sqrt (-1) = I := by
  simp [sqrt_neg_of_nonneg (a := 1) (by simp)]

theorem RCLike.sqrt_neg_one : sqrt (-1) = (I : 𝕜) := by
  rw [sqrt_neg_of_nonneg (by simp)]
  simp [sqrt]

theorem Complex.sqrt_I : sqrt (I : ℂ) = √2⁻¹ * (1 + I) := by
  rw [sqrt, ← re_add_im (I ^ 2⁻¹), cpow_inv_two_im_eq_sqrt (by simp), cpow_inv_two_re]
  simp [mul_add]

theorem Complex.sqrt_neg_I : sqrt (-I : ℂ) = √2⁻¹ * (1 - I) := by
  rw [sqrt, ← re_add_im ((-I) ^ 2⁻¹), cpow_inv_two_im_eq_neg_sqrt (by simp), cpow_inv_two_re]
  simp [mul_sub, ← sub_eq_add_neg]
