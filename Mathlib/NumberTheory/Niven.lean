/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Peel
import Mathlib.Tactic.Rify

/-! # Niven's Theorem

This file proves Niven's theorem, stating that the only rational angles _in degrees_ which
also have rational cosines, are 0, 30 degrees, and 90 degrees - up to reflection and shifts
by π. Equivalently, the only rational numbers that occur as `cos(π * p / q)` are the five
values `{-1, -1/2, 0, 1/2, 1}`.
-/

namespace IsIntegral

variable {α R : Type*} [DivisionRing α] [CharZero α] {q : ℚ} {x : α}

@[simp]
theorem ratCast_iff : IsIntegral ℤ (q : α) ↔ IsIntegral ℤ q :=
  isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ α)

theorem exists_int_iff_exists_rat (h₁ : IsIntegral ℤ x) : (∃ q : ℚ, x = q) ↔ ∃ k : ℤ, x = k := by
  refine ⟨?_, fun ⟨w, h⟩ ↦ ⟨w, by simp [h]⟩⟩
  rintro ⟨q, rfl⟩
  rw [ratCast_iff] at h₁
  peel IsIntegrallyClosed.algebraMap_eq_of_integral h₁ with h
  simp [← h]

end IsIntegral

variable {θ : ℝ}

open Real

theorem isIntegral_two_mul_cos_rat_mul_pi (r : ℚ) :
    IsIntegral ℤ (2 * cos (r * π)) := by
  let z : ℂ := .exp (.I * r * π)
  obtain ⟨p, q, hq_pos, rfl⟩ : ∃ (p : ℤ) (q : ℕ), q ≠ 0 ∧ r = p / q :=
    ⟨r.num, r.den, r.den_ne_zero, r.num_div_den.symm⟩
  -- Let `z = e ^ (i * π * p / q)`, which is a root of unity.
  have hz_root : z ^ (2 * q) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    use p
    push_cast
    field_simp [hq_pos]
  -- Since z is a root of unity, `2 cos θ = z` and `z⁻¹` are algebraic integers, and their sum.
  have h_cos_eq : 2 * cos (p / q * π) = z + z⁻¹ := by
    simpa [Complex.cos, Complex.exp_neg, z] using by ring_nf
  obtain ⟨f, hf₁, hf₂⟩ : IsIntegral ℤ (z + z⁻¹) := by apply IsIntegral.add <;>
      exact ⟨.X ^ (2 * q) - 1, Polynomial.monic_X_pow_sub_C _ (by positivity), by simp [hz_root]⟩
  use f, hf₁
  simp_all [Polynomial.eval₂_eq_sum_range, ← Complex.ofReal_inj]

/-- **Niven's theorem**: The only rational values of `cos` that occur at rational multiples of π
are `{-1, -1/2, 0, 1/2, 1}`. -/
theorem niven (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q) :
    cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  -- Since `2 cos θ ` is an algebraic integer and rational, it must be an integer.
  -- Hence, `2 cos θ ∈ {-2, -1, 0, 1, 2}`.
  obtain ⟨r, rfl⟩ := hθ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * cos (r * π) = k := by
    rw [← (isIntegral_two_mul_cos_rat_mul_pi r).exists_int_iff_exists_rat]
    exact ⟨2 * hcos.choose, by push_cast; linarith [hcos.choose_spec]⟩
  -- Since k is an integer and `2 * cos (w * pi) = k`, we have $k ∈ {-2, -1, 0, 1, 2}$.
  have hk_values : k ∈ Finset.Icc (-2 : ℤ) 2 := by
    rw [Finset.mem_Icc]
    rify
    constructor <;> linarith [hk, (r * π).neg_one_le_cos, (r * π).cos_le_one]
  rw [show cos (r * π) = k / 2 by grind]
  fin_cases hk_values <;> simp

/-- Niven's theorem, but stated for `sin` instead of `cos`. -/
theorem niven_sin (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, sin θ = q) :
    sin θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  convert ← niven (θ := θ - π/2) ?_ ?_ using 1
  · exact cos_sub_pi_div_two θ
  · exact hθ.imp' (· - 1 / 2) (by intros; push_cast; linarith)
  · simpa [cos_sub_pi_div_two]

/-- Niven's theorem, giving the possible angles for `θ` in the range `0 .. π`. -/
theorem niven_angle_eq (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q)
    (h_bnd : θ ∈ Set.Icc 0 π) : θ ∈ ({0, π / 3, π / 2, π * (2 / 3), π} : Set ℝ) := by
  rcases niven hθ hcos with h | h | h | h | h <;>
  -- define `h₂` appropriately for each proof branch
  [ have h₂ := cos_pi;
    have h₂ : cos (π * (2 / 3)) = -1 / 2 := by
      have := cos_pi_sub (π / 3)
      have := cos_pi_div_three
      grind;;
    have h₂ := cos_pi_div_two;
    have h₂ := cos_pi_div_three;
    have h₂ := cos_zero] <;>
  simp [injOn_cos h_bnd ⟨by positivity, by linarith [pi_nonneg]⟩ (h₂ ▸ h)]
