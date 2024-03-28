/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.ZetaFunctions.RiemannZeta

/-!
# Special values of the Riemann zeta function

This file gives the formula for `ζ (2 * k)`, for `k` a non-zero integer, in terms of Bernoulli
numbers.
-/

open Complex Real
open scoped Nat

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ` with `k ≠ 0`: we have
`ζ (2 * k) = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)!`.
Compare `hasSum_zeta_nat` for a version formulated explicitly as a sum, and
`riemannZeta_neg_nat_eq_bernoulli` for values at negative integers (equivalent to the above via
the functional equation). -/
theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  convert congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one]
    · rw [ofReal_tsum]
      norm_num
    · refine one_lt_two.trans_le ?_
      conv_lhs => rw [← mul_one 2]
      rwa [mul_le_mul_left (zero_lt_two' ℕ), Nat.one_le_iff_ne_zero]
  · set_option tactic.skipAssignedInstances false in norm_num
#align riemann_zeta_two_mul_nat riemannZeta_two_mul_nat

theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two, ofReal_tsum]
    norm_num
  · norm_num
#align riemann_zeta_two riemannZeta_two

theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : ℂ) = (4 : ℕ) by norm_num,
      zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < 4), ofReal_tsum]
    norm_num
  · norm_num
#align riemann_zeta_four riemannZeta_four

theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) = (-1 : ℂ) ^ k * bernoulli (k + 1) / (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · cases' m with m m
    ·-- k = 0 : evaluate explicitly
      rw [Nat.zero_eq, mul_zero, Nat.cast_zero, pow_zero, one_mul, zero_add, neg_zero, zero_add,
        div_one, bernoulli_one, riemannZeta_zero]
      norm_num
    · -- k = 2 * (m + 1) : both sides "trivially" zero
      rw [Nat.cast_mul, ← neg_mul, Nat.cast_two, Nat.cast_succ, riemannZeta_neg_two_mul_nat_add_one,
        bernoulli_eq_bernoulli'_of_ne_one]
      swap; · apply ne_of_gt; norm_num
      rw [bernoulli'_odd_eq_zero ⟨m + 1, rfl⟩ (by norm_num), Rat.cast_zero, mul_zero,
        zero_div]
  · -- k = 2 * m + 1 : the interesting case
    rw [Odd.neg_one_pow ⟨m, rfl⟩]
    rw [show -(↑(2 * m + 1) : ℂ) = 1 - (2 * m + 2) by push_cast; ring]
    rw [riemannZeta_one_sub]
    rotate_left
    · intro n
      rw [(by norm_cast : 2 * (m : ℂ) + 2 = ↑(2 * m + 2)), ← Int.cast_neg_natCast, ← Int.cast_ofNat,
        Ne.def, Int.cast_inj]
      apply ne_of_gt
      exact lt_of_le_of_lt
        (by set_option tactic.skipAssignedInstances false in norm_num : (-n : ℤ) ≤ 0)
        (by positivity)
    · rw [(by norm_cast : 2 * (m : ℂ) + 2 = ↑(2 * m + 2)), Ne.def, Nat.cast_eq_one]; norm_num
    -- get rid of cosine term
    rw [show Complex.cos (π * (2 * m + 2) / 2) = -(-1 : ℂ) ^ m by
        rw [(by field_simp; ring : (π : ℂ) * (2 * m + 2) / 2 = (π * m + π))]
        rw [Complex.cos_add_pi, neg_inj]
        rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
        · rw [pow_mul, neg_one_sq, one_pow]
          convert Complex.cos_nat_mul_two_pi t using 2
          push_cast; ring_nf
        · rw [pow_add, pow_one, pow_mul, neg_one_sq, one_pow, one_mul]
          convert Complex.cos_nat_mul_two_pi_add_pi t using 2
          push_cast; ring_nf]
    -- substitute in what we know about zeta values at positive integers
    have step1 := congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat (by norm_num : m + 1 ≠ 0)).tsum_eq
    have step2 := zeta_nat_eq_tsum_of_gt_one (by rw [mul_add]; norm_num : 1 < 2 * (m + 1))
    simp_rw [ofReal_tsum, ofReal_div, ofReal_one, ofReal_pow, ofReal_nat_cast] at step1
    rw [step1, (by norm_cast : (↑(2 * (m + 1)) : ℂ) = 2 * ↑m + 2)] at step2
    rw [step2, mul_div]
    -- now the rest is just a lengthy but elementary rearrangement
    rw [show ((2 * (m + 1))! : ℂ) = Complex.Gamma (2 * m + 2) * (↑(2 * m + 1) + 1) by
        rw [(by push_cast; ring : (2 * m + 2 : ℂ) = ↑(2 * m + 1) + 1),
          Complex.Gamma_nat_eq_factorial, (by ring : 2 * (m + 1) = 2 * m + 1 + 1),
          Nat.factorial_succ, Nat.cast_mul, mul_comm]
        norm_num]
    rw [← div_div, neg_one_mul]
    congr 1
    rw [div_eq_iff (Gamma_ne_zero_of_re_pos _)]
    swap; · rw [(by norm_num : 2 * (m : ℂ) + 2 = ↑(2 * (m : ℝ) + 2)), ofReal_re]; positivity
    simp_rw [ofReal_mul, ← mul_assoc, ofReal_rat_cast, mul_add, Nat.add_assoc, mul_one,
      one_add_one_eq_two, mul_neg, neg_mul, neg_inj]
    conv_rhs => rw [mul_comm]
    congr 1
    rw [ofReal_pow, ofReal_neg, ofReal_one, pow_add, neg_one_sq, mul_one]
    conv_lhs =>
      congr
      congr
      rw [mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [(by simp : (2 : ℂ) * π = ((2 : ℝ) : ℂ) * π), mul_cpow_ofReal_nonneg two_pos.le pi_pos.le,
      ← mul_assoc]
    rw [show (2 : ℂ) * ↑(2 : ℝ) ^ (-(2 * ↑m + 2) : ℂ) = (↑((2 : ℝ) ^ (2 * m + 2 - 1 : ℕ)))⁻¹ by
        rw [ofReal_pow, ← cpow_nat_cast, ← cpow_neg, show (2 : ℝ) = (2 : ℂ) by norm_num]
        rw [Nat.add_sub_assoc one_le_two, Nat.cast_add, Nat.cast_mul, Nat.cast_two,
          (by norm_num : 2 - 1 = 1), Nat.cast_one]
        nth_rewrite 1 [← cpow_one 2]
        rw [← cpow_add _ _ two_ne_zero]
        congr 1
        ring]
    rw [show (π : ℂ) ^ (-(2 * (m : ℂ) + 2)) = (↑(π ^ (2 * m + 2)))⁻¹ by
        rw [ofReal_pow, ← cpow_nat_cast, ← cpow_neg, Nat.cast_add, Nat.cast_mul, Nat.cast_two]]
    rw [(by intros; ring : ∀ a b c d e : ℂ, a * b * c * d * e = a * d * (b * e) * c)]
    rw [inv_mul_cancel (ofReal_ne_zero.mpr <| pow_ne_zero _ pi_ne_zero),
      inv_mul_cancel (ofReal_ne_zero.mpr <| pow_ne_zero _ two_ne_zero), one_mul, one_mul]
#align riemann_zeta_neg_nat_eq_bernoulli riemannZeta_neg_nat_eq_bernoulli
