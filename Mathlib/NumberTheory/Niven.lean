/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Snir Broshi
-/
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

open Real Polynomial

section IsIntegral

/-- `exp(q * πi)` for `q : ℚ` is integral over `ℤ`. -/
theorem Complex.isIntegral_exp_rat_mul_pi_mul_I (q : ℚ) : IsIntegral ℤ <| exp <| q * π * I := by
  refine ⟨X ^ (2 * q.den) - 1, monic_X_pow_sub <| by simp [q.den_pos], ?_⟩
  nth_rw 1 [← q.num_div_den]
  simp [← exp_nat_mul,
    show 2 * q.den * (q.num / q.den * π * I) = q.den / q.den * q.num * (2 * π * I) by ring_nf]

/-- `2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `sin` function. -/
theorem Complex.isIntegral_two_mul_sin_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * sin (q * π) := by
  convert ((isIntegral_exp_rat_mul_pi_mul_I (-q)).sub (isIntegral_exp_rat_mul_pi_mul_I q))
    |>.mul isIntegral_int_I using 1
  unfold sin
  push_cast
  ring_nf

/-- `2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `cos` function. -/
theorem Complex.isIntegral_two_mul_cos_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * cos (q * π) := by
  convert (isIntegral_exp_rat_mul_pi_mul_I q).add (isIntegral_exp_rat_mul_pi_mul_I (-q)) using 1
  unfold cos
  push_cast
  ring_nf

/-- `2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `sin` function. -/
theorem Real.isIntegral_two_mul_sin_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * sin (q * π) :=
  isIntegral_algebraMap_iff (B := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isIntegral_two_mul_sin_rat_mul_pi]

/-- `2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `cos` function. -/
theorem Real.isIntegral_two_mul_cos_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * cos (q * π) :=
  isIntegral_algebraMap_iff (B := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isIntegral_two_mul_cos_rat_mul_pi]

@[deprecated (since := "2025-11-09")]
alias isIntegral_two_mul_cos_rat_mul_pi := Real.isIntegral_two_mul_cos_rat_mul_pi

/-- `sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `sin` function. -/
theorem Complex.isAlgebraic_sin_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| sin <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/-- `cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `cos` function. -/
theorem Complex.isAlgebraic_cos_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| cos <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/-- `sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `sin` function. -/
theorem Real.isAlgebraic_sin_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| sin <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/-- `cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `cos` function. -/
theorem Real.isAlgebraic_cos_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| cos <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/-- `tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `tan` function. -/
theorem Complex.tan_rat_mul_pi_isAlgebraic (q : ℚ) : IsAlgebraic ℤ <| tan <| q * π :=
  (isAlgebraic_sin_rat_mul_pi q).mul (isAlgebraic_cos_rat_mul_pi q).inv

/-- `tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `tan` function. -/
theorem Real.tan_rat_mul_pi_isAlgebraic (q : ℚ) : IsAlgebraic ℤ <| tan <| q * π :=
  isAlgebraic_algebraMap_iff (A := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.tan_rat_mul_pi_isAlgebraic]

end IsIntegral

/-- **Niven's theorem**: The only rational values of `cos` that occur at rational multiples of π
are `{-1, -1/2, 0, 1/2, 1}`. -/
theorem niven (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q) :
    cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  -- Since `2 cos θ ` is an algebraic integer and rational, it must be an integer.
  -- Hence, `2 cos θ ∈ {-2, -1, 0, 1, 2}`.
  obtain ⟨r, rfl⟩ := hθ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * cos (r * π) = k := by
    rw [← (Real.isIntegral_two_mul_cos_rat_mul_pi r).exists_int_iff_exists_rat]
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
