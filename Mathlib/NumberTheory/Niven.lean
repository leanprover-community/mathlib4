/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Snir Broshi
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Field
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Peel
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Rify
import Mathlib.Tactic.SetLike

/-! # Niven's Theorem

This file proves Niven's theorem, stating that the only rational angles _in degrees_ which
also have rational cosines, are 0, 30 degrees, and 90 degrees - up to reflection and shifts
by π. Equivalently, the only rational numbers that occur as `cos(π * p / q)` are the five
values `{-1, -1/2, 0, 1/2, 1}`.
-/

public section

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

section IsIntegral

namespace Complex

lemma exp_rat_mul_pi_mul_I_pow_two_mul_den (q : ℚ) : exp (q * π * I) ^ (2 * q.den) = 1 := by
  nth_rw 1 [← q.num_div_den, ← exp_nat_mul]
  push_cast
  rw [show 2 * q.den * (q.num / q.den * π * I) = q.num * (2 * π * I) by field,
    exp_int_mul_two_pi_mul_I]

/-- `exp(q * π * I)` for `q : ℚ` is integral over `ℤ`. -/
theorem isIntegral_exp_rat_mul_pi_mul_I (q : ℚ) : IsIntegral ℤ <| exp <| q * π * I := by
  refine .of_pow (Nat.mul_pos zero_lt_two q.den_pos) ?_
  exact exp_rat_mul_pi_mul_I_pow_two_mul_den _ ▸ isIntegral_one

/-- `exp(-(q * π) * I)` for `q : ℚ` is integral over `ℤ`. -/
theorem isIntegral_exp_neg_rat_mul_pi_mul_I (q : ℚ) :
    IsIntegral ℤ <| exp <| -(q * π) * I := by
  simpa using isIntegral_exp_rat_mul_pi_mul_I (-q)

/-- `2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `sin` function. -/
theorem isIntegral_two_mul_sin_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * sin (q * π) := by
  rw [sin.eq_1, mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_neg_rat_mul_pi_mul_I q).sub (isIntegral_exp_rat_mul_pi_mul_I q)
    |>.mul isIntegral_int_I

/-- `2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `cos` function. -/
theorem isIntegral_two_mul_cos_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * cos (q * π) := by
  rw [cos.eq_1, mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_rat_mul_pi_mul_I q).add (isIntegral_exp_neg_rat_mul_pi_mul_I q)

/-- `sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `sin` function. -/
theorem isAlgebraic_sin_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| sin <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/-- `cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `cos` function. -/
theorem isAlgebraic_cos_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| cos <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/-- `tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `tan` function. -/
theorem isAlgebraic_tan_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| tan <| q * π :=
  (isAlgebraic_sin_rat_mul_pi q).mul (isAlgebraic_cos_rat_mul_pi q).inv

end Complex

namespace Real

/-- `2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `sin` function. -/
theorem isIntegral_two_mul_sin_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * sin (q * π) :=
  isIntegral_algebraMap_iff (B := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isIntegral_two_mul_sin_rat_mul_pi]

/-- `2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `cos` function. -/
theorem isIntegral_two_mul_cos_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * cos (q * π) :=
  isIntegral_algebraMap_iff (B := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isIntegral_two_mul_cos_rat_mul_pi]

@[deprecated (since := "2025-11-15")]
alias _root_.isIntegral_two_mul_cos_rat_mul_pi := isIntegral_two_mul_cos_rat_mul_pi

/-- `sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `sin` function. -/
theorem isAlgebraic_sin_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| sin <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/-- `cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `cos` function. -/
theorem isAlgebraic_cos_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| cos <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/-- `tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `tan` function. -/
theorem isAlgebraic_tan_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| tan <| q * π :=
  isAlgebraic_algebraMap_iff (A := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isAlgebraic_tan_rat_mul_pi]

end Real

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
  convert ← niven (θ := θ - π / 2) ?_ ?_ using 1
  · exact cos_sub_pi_div_two θ
  · exact hθ.imp' (· - 1 / 2) (by intros; push_cast; linarith)
  · simpa [cos_sub_pi_div_two]

/-- Niven's theorem, giving the possible angles for `θ` in the range `0 .. π`. -/
theorem niven_angle_eq (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q)
    (h_bnd : θ ∈ Set.Icc 0 π) : θ ∈ ({0, π / 3, π / 2, π * (2 / 3), π} : Set ℝ) := by
  rcases niven hθ hcos with h | h | h | h | h <;>
  -- define `h₂` appropriately for each proof branch
  [have h₂ := cos_pi;
    have h₂ : cos (π * (2 / 3)) = -1 / 2 := by
      have := cos_pi_sub (π / 3)
      have := cos_pi_div_three
      grind;;
    have h₂ := cos_pi_div_two;
    have h₂ := cos_pi_div_three;
    have h₂ := cos_zero] <;>
  simp [injOn_cos h_bnd ⟨by positivity, by linarith [pi_nonneg]⟩ (h₂ ▸ h)]

theorem niven_angle_div_pi_eq {r : ℚ} (hcos : ∃ q : ℚ, cos (r * π) = q)
    (h_bnd : r ∈ Set.Icc 0 1) : r ∈ ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set ℚ) := by
  apply smul_left_injective ℚ pi_ne_zero |>.mem_set_image.mp
  replace h_bnd : (r : ℝ) * π ∈ Set.Icc (0 * π) (1 * π) := by
    obtain ⟨hr, hr'⟩ := h_bnd; constructor <;> gcongr <;> norm_cast
  generalize h : (r : ℝ) * π = θ at *
  have := niven_angle_eq ⟨r, h.symm⟩ hcos (by simpa using h_bnd)
  simp_all [Rat.smul_def]
  grind

theorem niven_fract_angle_div_pi_eq {r : ℚ} (hcos : ∃ q : ℚ, cos (r * π) = q) :
    Int.fract r ∈ ({0, 1 / 3, 1 / 2, 2 / 3} : Set ℚ) := by
  suffices Int.fract r ∈ ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set ℚ) by
    grind [ne_of_lt (Int.fract_lt_one r)]
  refine niven_angle_div_pi_eq (r := Int.fract r) ?_ (by simp [le_of_lt <| Int.fract_lt_one r])
  obtain ⟨q, hq⟩ := hcos
  exact ⟨(-1) ^ ⌊r⌋ * q, by rw [Int.fract]; push_cast; rw [sub_mul, cos_sub_int_mul_pi, hq]⟩

theorem irrational_cos_rat_mul_pi {r : ℚ} (hr : 3 < r.den) :
    Irrational (cos (r * π)) := by
  rw [← Rat.den_intFract] at hr
  by_contra! hnz
  rcases niven_fract_angle_div_pi_eq (exists_rat_of_not_irrational hnz) with (hr' | hr' | hr' | hr')
  all_goals (try rw [Set.mem_singleton_iff] at hr'); rw [hr'] at hr; norm_num at hr
