/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Series

import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# `Real.pi` for interval_dyadic_real

This file encloses `Real.pi` for the `interval_dyadic_real` inclusion family, by Machin's formula
`π = 16 * arctan (1 / 5) - 4 * arctan (1 / 239)`.

This file is opt-in so that `dyadic_interval` doesn't import unnecessary theories.
-/

public section

namespace Inclusion.IntervalDyadicReal

/-- An enclosure of `arctan (1 / k)` by the first `n` terms of its series and the remainder bound
of `Real.abs_arctan_sub_sum_range_le`, rounded outward to precision `prec`. The series divided by
its first term `1 / k` has the term ratios `-(2 * j + 1) / ((2 * j + 3) * k ^ 2)`. -/
@[expose]
def arctanInvTaylor (k n prec : ℕ) : Interval Dyadic :=
  let X := hypergeomPartialSum (fun j ↦ -((2 * j + 1 : ℕ) : ℤ)) (fun j ↦ (2 * j + 3) * k ^ 2) 0 n
  ratBall (X.sumNum * ((2 * n + 1) * k ^ (2 * n) : ℕ)) X.den
    (X.den * k * ((2 * n + 1) * k ^ (2 * n))) prec

theorem arctanInvTaylor_mem {k : ℕ} (hk : 1 < k) (n prec : ℕ) :
    Real.arctan (k : ℝ)⁻¹ ∈ arctanInvTaylor k n prec := by
  have h := Real.abs_arctan_sub_sum_range_le (x := (k : ℝ)⁻¹) (by positivity)
    (inv_lt_one_of_one_lt₀ (mod_cast hk)) n
  rw [← hypergeomPartialSum_div (Int.castRingHom ℝ) (fun j ↦ -((2 * j + 1 : ℕ) : ℤ))
    (fun j ↦ (2 * j + 3) * k ^ 2) (fun j ↦ by positivity)
    (fun m ↦ (-1) ^ m * (k : ℝ)⁻¹ ^ (2 * m + 1) / ↑(2 * m + 1))
    (fun j ↦ by push_cast [eq_intCast, inv_pow]; field)] at h
  have hden := (hypergeomPartialSum_spec (fun j ↦ -((2 * j + 1 : ℕ) : ℤ))
    (fun j ↦ (2 * j + 3) * k ^ 2) 0 n).2.1
  rw [arctanInvTaylor]
  generalize hypergeomPartialSum (R := ℤ) _ _ 0 n = X at h hden ⊢
  have hden0 : (X.den : ℝ) ≠ 0 := by
    rw [hden]
    positivity
  refine ratBall_mem ?_ prec
  convert h using 1 <;> push_cast [eq_intCast, inv_pow]
  · field_simp
  · field

/-- An enclosure of `π` by Machin's formula `π = 16 * arctan (1 / 5) - 4 * arctan (1 / 239)`. Each
term of the series gains more than `4` bits for `1 / 5` and more than `15` for `1 / 239`. The `8`
extra bits keep the enclosure before the final rounding narrower than `2 ^ (-prec - 1)`, so the
result has width at most `2 ^ (-prec)`. -/
@[expose]
def pi (prec : ℕ) : Interval Dyadic :=
  let p := prec + 8
  roundOut (((Interval.singleton 16).mul (arctanInvTaylor 5 (p / 4 + 1) p)).sub
    ((Interval.singleton 4).mul (arctanInvTaylor 239 (p / 15 + 1) p))) (prec + 1)

@[inclusion_op interval_dyadic_real]
theorem pi_mem (prec : ℕ) : Real.pi ∈ pi prec := by
  have h : Real.pi = 16 * Real.arctan ((5 : ℕ) : ℝ)⁻¹ - 4 * Real.arctan ((239 : ℕ) : ℝ)⁻¹ := by
    linarith [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
  rw [h]
  refine roundOut_mem (sub_mem (mul_mem (ofNat_mem 16) ?_) (mul_mem (ofNat_mem 4) ?_)) _ <;>
    exact arctanInvTaylor_mem (by norm_num) _ _

end Inclusion.IntervalDyadicReal
