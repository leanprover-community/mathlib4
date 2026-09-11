/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic

/-!
# A finite trigonometric dimension equation

For natural d at least two, cos squared of pi over d plus one equals (d - 1) / 4
exactly when d is two or three.
-/

@[expose] public section

open Real
namespace Real
theorem cos_sq_pi_div_nat_add_one_lt (d : ℕ) (hd : 5 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 < (d - 1 : ℝ) / 4 := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hx_pos : 0 < π / ((d : ℝ) + 1) := by positivity
  have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hcos_lt : Real.cos (π / (d + 1)) < 1 := by
    have hy : π / ((d : ℝ) + 1) ≤ π := by
      rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hy hx_pos
    simpa using h
  have hcos_nonneg : 0 ≤ Real.cos (π / ((d : ℝ) + 1)) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos]
    · rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
  have hcos_le : Real.cos (π / (d + 1)) ^ 2 < 1 := by
    nlinarith [hcos_nonneg, hcos_lt]
  have hfloor : (1 : ℝ) ≤ ((d : ℝ) - 1) / 4 := by
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  linarith

theorem cos_sq_pi_div_three : Real.cos (π / 3) ^ 2 = 1 / 4 := by
  rw [Real.cos_pi_div_three]; norm_num

theorem cos_sq_pi_div_four : Real.cos (π / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four]
  rw [div_pow, sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  norm_num

theorem cos_sq_pi_div_five_ne_three_div_four : Real.cos (π / 5) ^ 2 ≠ 3 / 4 := by
  rw [Real.cos_pi_div_five]
  intro h
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs, hnn, h]

theorem cos_sq_pi_div_nat_add_one_eq_iff (d : ℕ) (hd : 2 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨h2, h3⟩ := hne
    rcases Nat.lt_or_ge d 5 with h5 | h5
    · have hd4 : d = 4 := by omega
      subst hd4
      have hc : ((4 : ℕ) : ℝ) + 1 = 5 := by norm_num
      rw [hc] at h
      have h34 : (((4 : ℕ) : ℝ) - 1) / 4 = 3 / 4 := by norm_num
      rw [h34] at h
      exact cos_sq_pi_div_five_ne_three_div_four h
    · exact absurd h (ne_of_lt (cos_sq_pi_div_nat_add_one_lt d h5))
  · rintro (rfl | rfl)
    · have hc : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
      rw [hc, cos_sq_pi_div_three]; norm_num
    · have hc : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
      rw [hc, cos_sq_pi_div_four]; norm_num

theorem cos_sq_pi_div_nat_add_one_ne_of_four_le (d : ℕ) (hd : 4 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4 := by
  intro h
  have hsem : d = 2 ∨ d = 3 := (cos_sq_pi_div_nat_add_one_eq_iff d (by omega)).mp h
  omega

end Real
