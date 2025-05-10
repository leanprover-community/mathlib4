/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Monotone.Monovary

/-!
# Schur's inequality

This file proves a number of forms of Schur's inequality.
The proofs are adapted from https://www.cip.ifi.lmu.de/~grinberg/VornicuS.pdf
-/

lemma vornicu_schur_mildorf {α : Type*} [PartialOrder α] [CommRing α] [IsOrderedRing α]
    {a b c x y z : α}
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hcb : c ≤ b) (hba : b ≤ a)
    (hyxz : y ≤ x + z) :
    0 ≤ x * (a - b) * (a - c) + y * (b - a) * (b - c) + z * (c - a) * (c - b) := by
  have h₁ : 0 ≤ a - b := by linear_combination hba
  have h₂ : 0 ≤ b - c := by linear_combination hcb
  have h₃ : 0 ≤ x + z - y := by linear_combination hyxz
  have h₄ : 0 ≤ x * (a - b) := mul_nonneg hx h₁
  calc
    _ ≤ (x + z - y) * (b - c) * (a - b) := mul_nonneg (mul_nonneg h₃ h₂) h₁
    _ = x * (a - b) * (b - c) + y * (b - a) * (b - c) + z * (a - b) * (b - c) := by ring
    _ ≤ x * (a - b) * (a - c) + y * (b - a) * (b - c) + z * (a - c) * (b - c) := by gcongr
    _ = x * (a - b) * (a - c) + y * (b - a) * (b - c) + z * (c - a) * (c - b) := by ring

lemma generalized_schur {α : Type*} [LinearOrder α] [CommRing α] [IsOrderedRing α]
    {a b c x y z : α}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : Monovary ![a, b, c] ![x, y, z]) :
    0 ≤ x * (a - b) * (a - c) + y * (b - a) * (b - c) + z * (c - a) * (c - b) := by
  wlog hcb : c < b generalizing a b c x y z
  case inr =>
    simp only [not_lt] at hcb
    have h' : Monovary ![a, c, b] ![x, z, y] := by
      convert h.comp_right ![0, 2, 1]
      all_goals ext i; fin_cases i <;> simp
    obtain rfl | hcb' := eq_or_lt_of_le hcb
    · simp [mul_assoc, hx, mul_self_nonneg, mul_nonneg]
    linear_combination this hx hz hy h' hcb'
  wlog hba : b < a generalizing a b c x y z
  case inr =>
    rcases lt_trichotomy a c with hac | rfl | hca
    next =>
      have h' : Monovary ![b, c, a] ![y, z, x] := by
        convert h.comp_right ![1, 2, 0]
        all_goals ext i; fin_cases i <;> simp
      linear_combination this hy hz hx h' hac hcb
    next => simp [mul_assoc, hy, mul_nonneg, mul_self_nonneg]
    next =>
      simp only [not_lt] at hba
      have h' : Monovary ![b, a, c] ![y, x, z] := by
        convert h.comp_right ![1, 0, 2]
        all_goals ext i; fin_cases i <;> simp
      obtain rfl | hba' := eq_or_lt_of_le hba
      · simp [mul_assoc, hz, mul_self_nonneg, mul_nonneg]
      linear_combination this hy hx hz h' hca (by order)
  have hyx : y ≤ x := h.symm (i := 1) (j := 0) hba
  exact vornicu_schur_mildorf hx hz hcb.le hba.le (by linear_combination hz + hyx)

lemma generalized_schur_antivary {α : Type*} [LinearOrder α] [CommRing α] [IsOrderedRing α]
    {a b c x y z : α}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : Antivary ![a, b, c] ![x, y, z]) :
    0 ≤ x * (a - b) * (a - c) + y * (b - a) * (b - c) + z * (c - a) * (c - b) := by
  wlog hcb : c < b generalizing a b c x y z
  case inr =>
    simp only [not_lt] at hcb
    have h' : Antivary ![a, c, b] ![x, z, y] := by
      convert h.comp_right ![0, 2, 1]
      all_goals ext i; fin_cases i <;> simp
    obtain rfl | hcb' := eq_or_lt_of_le hcb
    case inl => simp [mul_assoc, hx, mul_self_nonneg, mul_nonneg]
    linear_combination this hx hz hy h' hcb'
  wlog hba : b < a generalizing a b c x y z
  case inr =>
    rcases lt_trichotomy a c with hac | rfl | hca
    next =>
      have h' : Antivary ![b, c, a] ![y, z, x] := by
        convert h.comp_right ![1, 2, 0]
        all_goals ext i; fin_cases i <;> simp
      linear_combination this hy hz hx h' hac hcb
    next => simp [mul_assoc, hy, mul_nonneg, mul_self_nonneg]
    next =>
      simp only [not_lt] at hba
      have h' : Antivary ![b, a, c] ![y, x, z] := by
        convert h.comp_right ![1, 0, 2]
        all_goals ext i; fin_cases i <;> simp
      obtain rfl | hba' := eq_or_lt_of_le hba
      case inl => simp [mul_assoc, hz, mul_self_nonneg, mul_nonneg]
      linear_combination this hy hx hz h' hca (by order)
  have hyz : y ≤ z := h.symm (i := 2) (j := 1) hcb
  exact vornicu_schur_mildorf hx hz hcb.le hba.le (by linear_combination hx + hyz)

lemma sq_le_sq_of_nonpos {α : Type*} [LinearOrder α] [CommRing α] [IsOrderedRing α]
    {a b : α} (hab : a ≤ b) (hb : b ≤ 0) : b ^ 2 ≤ a ^ 2 := by
  rw [sq, sq]
  exact mul_le_mul_of_nonpos_of_nonpos hab hab (hab.trans hb) hb

lemma pow_le_pow_left_of_nonpos₀ {α : Type*} [LinearOrder α] [CommRing α] [IsOrderedRing α]
    {a b : α} {n : ℕ} (hab : a ≤ b) (hb : b ≤ 0)
    (hn : Even n) : b ^ n ≤ a ^ n := by
  obtain ⟨n, rfl⟩ := hn
  rw [← two_mul, pow_mul, pow_mul]
  apply pow_le_pow_left₀ (sq_nonneg _)
  exact sq_le_sq_of_nonpos hab hb

lemma schur {a b c r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    0 ≤ a ^ r * (a - b) * (a - c) + b ^ r * (b - a) * (b - c) + c ^ r * (c - a) * (c - b) := by
  wlog hcb : c ≤ b generalizing a b c
  next => linear_combination this ha hc hb (le_of_not_le hcb)
  wlog hba : b ≤ a generalizing a b c
  next =>
    obtain hac | hca := le_total a c
    case inl => linear_combination this hb hc ha hac hcb
    case inr => linear_combination this hb ha hc hca (le_of_not_le hba)
  refine vornicu_schur_mildorf (Real.rpow_nonneg ha _) (Real.rpow_nonneg hc _) hcb hba ?_
  linear_combination Real.rpow_le_rpow hb hba hr + Real.rpow_nonneg hc r

lemma schur_pos {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ a ^ r * (a - b) * (a - c) + b ^ r * (b - a) * (b - c) + c ^ r * (c - a) * (c - b) := by
  wlog hcb : c ≤ b generalizing a b c
  next => linear_combination this ha hc hb (le_of_not_le hcb)
  wlog hba : b ≤ a generalizing a b c
  next =>
    obtain hac | hca := le_total a c
    case inl => linear_combination this hb hc ha hac hcb
    case inr => linear_combination this hb ha hc hca (le_of_not_le hba)
  refine vornicu_schur_mildorf (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hc.le _) hcb hba ?_
  obtain hr₀ | hr₀ := le_or_lt 0 r
  · linear_combination Real.rpow_le_rpow hb.le hba hr₀ + Real.rpow_nonneg hc.le r
  · linear_combination Real.rpow_le_rpow_of_nonpos hc hcb hr₀.le + Real.rpow_nonneg ha.le r

lemma schur_even {α : Type*} [LinearOrder α] [CommRing α] [IsStrictOrderedRing α]
    (a b c : α) (r : ℕ) (hr : Even r) :
    0 ≤ a ^ r * (a - b) * (a - c) + b ^ r * (b - a) * (b - c) + c ^ r * (c - a) * (c - b) := by
  wlog hcb : c ≤ b generalizing a b c
  next => linear_combination this a c b (le_of_not_le hcb)
  wlog hba : b ≤ a generalizing a b c
  next =>
    obtain hac | hca := le_total a c
    case inl => linear_combination this b c a hac hcb
    case inr => linear_combination this b a c hca (le_of_not_le hba)
  refine vornicu_schur_mildorf (hr.pow_nonneg _) (hr.pow_nonneg _) hcb hba ?_
  obtain hb | hb := le_total 0 b
  case inl => linear_combination pow_le_pow_left₀ hb hba r + hr.pow_nonneg c
  case inr => linear_combination pow_le_pow_left_of_nonpos₀ hcb hb hr + hr.pow_nonneg a
