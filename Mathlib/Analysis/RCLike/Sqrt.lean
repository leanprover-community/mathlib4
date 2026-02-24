/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Square root on `RCLike`

This file contains the definitions `Complex.sqrt` and `RCLike.sqrt` and builds basic API.
-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]

open ComplexOrder

/-- The square root of a complex number. -/
noncomputable def Complex.sqrt (a : ℂ) : ℂ := a ^ (2⁻¹ : ℂ)

@[simp] theorem Complex.sqrt_zero : (0 : ℂ).sqrt = 0 := by simp [sqrt]
@[simp] theorem Complex.sqrt_one : (1 : ℂ).sqrt = 1 := by simp [sqrt]

theorem Complex.sqrt_eq_real_add_ite {a : ℂ} :
    a.sqrt = √((‖a‖ + a.re) / 2) + (if 0 ≤ a.im then 1 else -1) * √((‖a‖ - a.re) / 2) * I := by
  rw [← cpow_inv_two_re, sqrt]
  by_cases! h : 0 ≤ a.im
  · simp [← cpow_inv_two_im_eq_sqrt h, h]
  simp only [re_add_im, ↓reduceIte, h.not_ge, neg_one_mul, ← ofReal_neg,
    ← cpow_inv_two_im_eq_neg_sqrt h]

/-- The square root on `RCLike`. -/
noncomputable def RCLike.sqrt (a : 𝕜) : 𝕜 := map ℂ 𝕜 (map 𝕜 ℂ a).sqrt

theorem RCLike.sqrt_eq_ite {a : 𝕜} :
    sqrt a = if h : im (I : 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt
      else √(re a) := by
  rw [sqrt, eq_comm]
  split_ifs with h
  · simp
  have : (I : 𝕜) = 0 := by grind [I_eq_zero_or_im_I_eq_one]
  simp_all only [Complex.sqrt, im_eq_zero this, map_apply, add_zero, re_to_complex, im_to_complex,
    mul_zero, algebraMap.coe_inj, Complex.cpow_inv_two_re]
  by_cases! ha' : 0 ≤ re a
  · simp [abs_of_nonneg ha', ← two_mul]
  simp [abs_of_nonpos ha'.le, Real.sqrt_eq_zero', ha'.le]

theorem RCLike.sqrt_eq_real_add_ite {a : 𝕜} :
    sqrt a = √((‖a‖ + re a) / 2) + (if 0 ≤ im a then 1 else -1) * √((‖a‖ - re a) / 2) * I := by
  rw [sqrt, Complex.sqrt_eq_real_add_ite]
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← re_add_im a]
    simp [h, im_eq_zero]
  aesop

@[simp] theorem RCLike.sqrt_zero : sqrt (0 : 𝕜) = 0 := by simp [sqrt]
@[simp] theorem RCLike.sqrt_one : sqrt (1 : 𝕜) = 1 := by simp [sqrt]

theorem Complex.re_sqrt_ofReal {a : ℝ} :
    (sqrt (a : ℂ)).re = √a := by
  simp only [cpow_inv_two_re, norm_real, Real.norm_eq_abs, ofReal_re, Complex.sqrt]
  grind

theorem RCLike.re_sqrt_ofReal {a : ℝ} :
    re (sqrt (a : 𝕜)) = √a := by
  aesop (add simp [sqrt, Complex.re_sqrt_ofReal])

@[simp] theorem RCLike.sqrt_real {a : ℝ} :
    sqrt a = √a := by simp [← re_sqrt_ofReal (𝕜 := ℝ)]

@[simp] theorem RCLike.sqrt_complex {a : ℂ} :
    sqrt a = a.sqrt := by simp [sqrt]

theorem Complex.sqrt_of_nonneg {a : ℂ} (ha : 0 ≤ a) :
    a.sqrt = √a.re := by
  obtain ⟨α : ℝ, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (α : ℂ).sqrt, re_sqrt_ofReal]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]

theorem RCLike.sqrt_map {𝕜' : Type*} [RCLike 𝕜'] {a : 𝕜} (h : im (I : 𝕜) = im (I : 𝕜')) :
    sqrt (map 𝕜 𝕜' a) = map 𝕜 𝕜' (sqrt a) := by
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜')
  aesop (add simp [RCLike.sqrt, im_eq_zero])

theorem Complex.sqrt_map {a : 𝕜} (h : RCLike.im (RCLike.I : 𝕜) = 1) :
    (RCLike.map 𝕜 ℂ a).sqrt = RCLike.map 𝕜 ℂ (RCLike.sqrt a) := by
  aesop (add simp [RCLike.sqrt])

theorem RCLike.sqrt_of_nonneg {a : 𝕜} (ha : 0 ≤ a) :
    sqrt a = √(re a) := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite]
  rw [sqrt_eq_ite, dif_pos h, RingEquiv.symm_apply_eq, Complex.sqrt_of_nonneg (by simpa)]
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
  · simp [h, sqrt_eq_ite, Real.sqrt_eq_zero', nonneg_iff.mp ha]
  rw [sqrt_eq_ite, dif_pos h, RingEquiv.symm_apply_eq, map_neg,
    Complex.sqrt_neg_of_nonneg (by simpa)]
  simp [h, sqrt, map_mul]

theorem Complex.sqrt_neg_one : sqrt (-1) = I := by
  simp [sqrt_neg_of_nonneg (a := 1) (by simp)]

theorem RCLike.sqrt_neg_one : sqrt (-1) = (I : 𝕜) := by
  simp [sqrt_neg_of_nonneg (a := (1 : 𝕜)) (by simp)]

theorem Complex.sqrt_I : sqrt (I : ℂ) = √2⁻¹ * (1 + I) := by
  rw [sqrt, ← re_add_im (I ^ 2⁻¹), cpow_inv_two_im_eq_sqrt (by simp), cpow_inv_two_re]
  simp [mul_add]

theorem Complex.sqrt_neg_I : sqrt (-I : ℂ) = √2⁻¹ * (1 - I) := by
  rw [sqrt, ← re_add_im ((-I) ^ 2⁻¹), cpow_inv_two_im_eq_neg_sqrt (by simp), cpow_inv_two_re]
  simp [mul_sub, ← sub_eq_add_neg]

theorem RCLike.sqrt_I : sqrt (I : 𝕜) = √2⁻¹ * (1 - I) * I := by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, mul_add, add_comm, Complex.sqrt_I, add_mul]
  grind [I_eq_zero_or_im_I_eq_one]

theorem RCLike.sqrt_neg_I : sqrt (-I : 𝕜) = √2⁻¹ * (1 + I) * -I := by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, add_comm, Complex.sqrt_neg_I, neg_mul, mul_add, add_mul, mul_sub,
      mul_comm Complex.I, ← sub_eq_add_neg]
  grind [I_eq_zero_or_im_I_eq_one]
