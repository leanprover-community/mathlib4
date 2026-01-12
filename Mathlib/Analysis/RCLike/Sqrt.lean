/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Square root on `RCLike`

This file contains the definitions `Complex.sqrt` and `RCLike.sqrt` and builds basic API.
-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]

open ComplexOrder

/-- The square root of a complex number. -/
noncomputable abbrev Complex.sqrt (a : ℂ) : ℂ := a ^ (2⁻¹ : ℂ)

theorem Complex.sqrt_def (a : ℂ) :
    a.sqrt = √((‖a‖ + a.re) / 2) + (if a.im < 0 then -1 else 1) * √((‖a‖ - a.re) / 2) * I := by
  rw [← cpow_inv_two_re]
  by_cases! h : 0 ≤ a.im
  · simp [← cpow_inv_two_im_eq_sqrt h, h.not_gt]
  simp only [re_add_im, ↓reduceIte, h, neg_one_mul, ← ofReal_neg, ← cpow_inv_two_im_eq_neg_sqrt h]

/-- The square root on `RCLike`. -/
noncomputable def RCLike.sqrt (a : 𝕜) : 𝕜 :=
  if h : im (I : 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt
  else √(re a)

theorem RCLike.re_sqrt (a : 𝕜) : re (sqrt a) = √((‖a‖ + re a) / 2) := by
  rw [sqrt]
  split_ifs with h
  · convert Complex.cpow_inv_two_re (complexRingEquiv h a)
    · simp
    · simpa [eq_comm] using norm_to_complex h a
    simp
  rw [← show re a = a by grind [I_eq_zero_or_im_I_eq_one, re_add_im]]
  by_cases! ha' : 0 ≤ re a
  · simp [abs_of_nonneg ha']
  simp [abs_of_nonpos ha'.le, Real.sqrt_eq_zero', ha'.le]

theorem RCLike.sqrt_def (a : 𝕜) :
    sqrt a = √((‖a‖ + re a) / 2) + (if im a < 0 then -1 else 1) * √((‖a‖ - re a) / 2) * I := by
  rw [← re_sqrt]
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt]
  by_cases! ha : 0 ≤ im a
  · simp only [sqrt, h, ↓reduceDIte, complexRingEquiv_apply, complexRingEquiv_symm_apply, map_add,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, mul_one, sub_self, add_zero, ha.not_gt,
      ↓reduceIte, Nat.ofNat_nonneg, Real.sqrt_div', map_div₀, one_mul, add_right_inj,
      mul_eq_mul_right_iff]
    rw [Complex.cpow_inv_two_im_eq_sqrt (by simpa)]
    simp [h]
  simp only [ha, ↓reduceIte, sqrt, h, ↓reduceDIte, complexRingEquiv_apply,
    complexRingEquiv_symm_apply, map_add, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, mul_one,
    sub_self, add_zero, Nat.ofNat_nonneg, Real.sqrt_div', map_div₀, neg_mul, add_right_inj]
  rw [Complex.cpow_inv_two_im_eq_neg_sqrt (by simpa)]
  simp [h]

theorem Complex.re_sqrt_ofReal (a : ℝ) :
    (sqrt (a : ℂ)).re = √a := by
  simp only [cpow_inv_two_re, norm_real, Real.norm_eq_abs, ofReal_re]
  grind

theorem RCLike.re_sqrt_ofReal (a : ℝ) :
    re (sqrt (a : 𝕜)) = √a := by
  aesop (add simp [sqrt, Complex.re_sqrt_ofReal])

@[simp] theorem RCLike.sqrt_real (a : ℝ) :
    sqrt a = √a := by simp [← re_sqrt_ofReal (𝕜 := ℝ)]

@[simp] theorem RCLike.sqrt_complex (a : ℂ) :
    sqrt a = a.sqrt := by simp [sqrt]

theorem Complex.sqrt_of_nonneg {a : ℂ} (ha : 0 ≤ a) :
    a.sqrt = √a.re := by
  obtain ⟨α : ℝ, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (α : ℂ).sqrt, re_sqrt_ofReal]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]

theorem RCLike.sqrt_symm_complexRingEquiv {a : ℂ} (h : im (I : 𝕜) = 1) :
    sqrt ((complexRingEquiv h).symm a) = (complexRingEquiv h).symm a.sqrt := by
  aesop (add simp [sqrt])

theorem RCLike.sqrt_complexRingEquiv {a : 𝕜} (h : im (I : 𝕜) = 1) :
    (complexRingEquiv h a).sqrt = complexRingEquiv h (sqrt a) := by
  aesop (add simp [sqrt])

theorem RCLike.sqrt_of_nonneg {a : 𝕜} (ha : 0 ≤ a) :
    sqrt a = √(re a) := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt]
  apply_fun complexRingEquiv h
  rw [← sqrt_complexRingEquiv h, Complex.sqrt_of_nonneg (by simpa)]
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
  rw [← sqrt_complexRingEquiv h, map_neg, Complex.sqrt_neg_of_nonneg (by simpa),
    map_mul, ← sqrt_complexRingEquiv h]
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
