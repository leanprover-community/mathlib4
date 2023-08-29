/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathlib.Analysis.SpecialFunctions.Integrals

#align_import data.real.pi.wallis from "leanprover-community/mathlib"@"980755c33b9168bc82f774f665eaa27878140fac"

/-! # The Wallis formula for Pi

This file establishes the Wallis product for `π` (`Real.tendsto_prod_pi_div_two`). Our proof is
largely about analyzing the behaviour of the sequence `∫ x in 0..π, sin x ^ n` as `n → ∞`.
See: https://en.wikipedia.org/wiki/Wallis_product

The proof can be broken down into two pieces. The first step (carried out in
`Analysis.SpecialFunctions.Integrals`) is to use repeated integration by parts to obtain an
explicit formula for this integral, which is rational if `n` is odd and a rational multiple of `π`
if `n` is even.

The second step, carried out here, is to estimate the ratio
`∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
it converges to one using the squeeze theorem. The final product for `π` is obtained after some
algebraic manipulation.

## Main statements

* `Real.Wallis.W`: the product of the first `k` terms in Wallis' formula for `π`.
* `Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow`: express `W n` as a ratio of integrals.
* `Real.Wallis.W_le` and `Real.Wallis.le_W`: upper and lower bounds for `W n`.
* `Real.tendsto_prod_pi_div_two`: the Wallis product formula.
 -/


open scoped Real Topology BigOperators Nat

open Filter Finset intervalIntegral

namespace Real

namespace Wallis

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

set_option linter.uppercaseLean3 false

/-- The product of the first `k` terms in Wallis' formula for `π`. -/
noncomputable def W (k : ℕ) : ℝ :=
  ∏ i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))
#align real.wallis.W Real.Wallis.W

theorem W_succ (k : ℕ) :
    W (k + 1) = W k * ((2 * k + 2) / (2 * k + 1) * ((2 * k + 2) / (2 * k + 3))) :=
  prod_range_succ _ _
#align real.wallis.W_succ Real.Wallis.W_succ

theorem W_pos (k : ℕ) : 0 < W k := by
  induction' k with k hk
  -- ⊢ 0 < W Nat.zero
  · unfold W; simp
    -- ⊢ 0 < ∏ i in range Nat.zero, (2 * ↑i + 2) / (2 * ↑i + 1) * ((2 * ↑i + 2) / (2  …
              -- 🎉 no goals
  · rw [W_succ]
    -- ⊢ 0 < W k * ((2 * ↑k + 2) / (2 * ↑k + 1) * ((2 * ↑k + 2) / (2 * ↑k + 3)))
    refine' mul_pos hk (mul_pos (div_pos _ _) (div_pos _ _)) <;> positivity
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
#align real.wallis.W_pos Real.Wallis.W_pos

theorem W_eq_factorial_ratio (n : ℕ) :
    W n = 2 ^ (4 * n) * n ! ^ 4 / ((2 * n)! ^ 2 * (2 * n + 1)) := by
  induction' n with n IH
  -- ⊢ W Nat.zero = ↑(2 ^ (4 * Nat.zero)) * ↑(Nat.zero ! ^ 4) / (↑((2 * Nat.zero)!  …
  · simp only [W, prod_range_zero, Nat.factorial_zero, mul_zero, pow_zero,
      algebraMap.coe_one, one_pow, mul_one, algebraMap.coe_zero, zero_add, div_self, Ne.def,
      one_ne_zero, not_false_iff]
    norm_num
    -- 🎉 no goals
  · unfold W at IH ⊢
    -- ⊢ ∏ i in range (Nat.succ n), (2 * ↑i + 2) / (2 * ↑i + 1) * ((2 * ↑i + 2) / (2  …
    rw [prod_range_succ, IH, _root_.div_mul_div_comm, _root_.div_mul_div_comm]
    -- ⊢ ↑(2 ^ (4 * n)) * ↑(n ! ^ 4) * ((2 * ↑n + 2) * (2 * ↑n + 2)) / (↑((2 * n)! ^  …
    refine' (div_eq_div_iff _ _).mpr _
    any_goals exact ne_of_gt (by positivity)
    -- ⊢ ↑(2 ^ (4 * n)) * ↑(n ! ^ 4) * ((2 * ↑n + 2) * (2 * ↑n + 2)) * (↑((2 * Nat.su …
    simp_rw [Nat.mul_succ, Nat.factorial_succ, pow_succ]
    -- ⊢ ↑(2 ^ (4 * n)) * ↑(n ! * (n ! * (n ! * (n ! * n ! ^ 0)))) * ((2 * ↑n + 2) *  …
    push_cast
    -- ⊢ 2 ^ (4 * n) * (↑n ! * (↑n ! * (↑n ! * (↑n ! * ↑n ! ^ 0)))) * ((2 * ↑n + 2) * …
    ring_nf
    -- 🎉 no goals
#align real.wallis.W_eq_factorial_ratio Real.Wallis.W_eq_factorial_ratio

theorem W_eq_integral_sin_pow_div_integral_sin_pow (k : ℕ) : (π / 2)⁻¹ * W k =
    (∫ x : ℝ in (0)..π, sin x ^ (2 * k + 1)) / ∫ x : ℝ in (0)..π, sin x ^ (2 * k) := by
  rw [integral_sin_pow_even, integral_sin_pow_odd, mul_div_mul_comm, ← prod_div_distrib, inv_div]
  -- ⊢ 2 / π * W k = 2 / π * ∏ x in range k, (2 * ↑x + 2) / (2 * ↑x + 3) / ((2 * ↑x …
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc]
  -- ⊢ 2 / π * W k = 2 / π * ∏ x in range k, (2 * ↑x + 2) / (2 * ↑x + 1) * ((2 * ↑x …
  rfl
  -- 🎉 no goals
#align real.wallis.W_eq_integral_sin_pow_div_integral_sin_pow Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow

theorem W_le (k : ℕ) : W k ≤ π / 2 := by
  rw [← div_le_one pi_div_two_pos, div_eq_inv_mul]
  -- ⊢ (π / 2)⁻¹ * W k ≤ 1
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, div_le_one (integral_sin_pow_pos _)]
  -- ⊢ ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * k + 1) ≤ ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * k)
  apply integral_sin_pow_succ_le
  -- 🎉 no goals
#align real.wallis.W_le Real.Wallis.W_le

theorem le_W (k : ℕ) : ((2 : ℝ) * k + 1) / (2 * k + 2) * (π / 2) ≤ W k := by
  rw [← le_div_iff pi_div_two_pos, div_eq_inv_mul (W k) _]
  -- ⊢ (2 * ↑k + 1) / (2 * ↑k + 2) ≤ (π / 2)⁻¹ * W k
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, le_div_iff (integral_sin_pow_pos _)]
  -- ⊢ (2 * ↑k + 1) / (2 * ↑k + 2) * ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * k) ≤ ∫ (x : ℝ …
  convert integral_sin_pow_succ_le (2 * k + 1)
  -- ⊢ (2 * ↑k + 1) / (2 * ↑k + 2) * ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * k) = ∫ (x : ℝ …
  rw [integral_sin_pow (2 * k)]
  -- ⊢ (2 * ↑k + 1) / (2 * ↑k + 2) * ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * k) = (sin 0 ^ …
  simp only [sin_zero, zero_pow', Ne.def, Nat.succ_ne_zero, zero_mul, sin_pi, tsub_zero, zero_div,
    zero_add]
  norm_cast
  -- 🎉 no goals
#align real.wallis.le_W Real.Wallis.le_W

theorem tendsto_W_nhds_pi_div_two : Tendsto W atTop (𝓝 <| π / 2) := by
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ tendsto_const_nhds le_W W_le
  -- ⊢ Tendsto (fun i => (2 * ↑i + 1) / (2 * ↑i + 2) * (π / 2)) atTop (𝓝 (π / 2))
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)) := by rw [sub_zero, one_mul]
  -- ⊢ Tendsto (fun i => (2 * ↑i + 1) / (2 * ↑i + 2) * (π / 2)) atTop (𝓝 (π / 2))
  rw [this]
  -- ⊢ Tendsto (fun i => (2 * ↑i + 1) / (2 * ↑i + 2) * (π / 2)) atTop (𝓝 ((1 - 0) * …
  refine' Tendsto.mul _ tendsto_const_nhds
  -- ⊢ Tendsto (fun i => (2 * ↑i + 1) / (2 * ↑i + 2)) atTop (𝓝 (1 - 0))
  have h : ∀ n : ℕ, ((2 : ℝ) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2) := by
    intro n
    rw [sub_div' _ _ _ (ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg
      (two_pos : 0 < (2 : ℝ)).le (Nat.cast_nonneg _)) two_pos)), one_mul]
    congr 1; ring
  simp_rw [h]
  -- ⊢ Tendsto (fun i => 1 - 1 / (2 * ↑i + 2)) atTop (𝓝 (1 - 0))
  refine' (tendsto_const_nhds.div_atTop _).const_sub _
  -- ⊢ Tendsto (fun i => 2 * ↑i + 2) atTop atTop
  refine' Tendsto.atTop_add _ tendsto_const_nhds
  -- ⊢ Tendsto (fun i => 2 * ↑i) atTop atTop
  exact tendsto_nat_cast_atTop_atTop.const_mul_atTop two_pos
  -- 🎉 no goals
#align real.wallis.tendsto_W_nhds_pi_div_two Real.Wallis.tendsto_W_nhds_pi_div_two

end Wallis

end Real

/-- Wallis' product formula for `π / 2`. -/
theorem Real.tendsto_prod_pi_div_two :
    Tendsto (fun k => ∏ i in range k, ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3)))
      atTop (𝓝 (π / 2)) :=
  Real.Wallis.tendsto_W_nhds_pi_div_two
#align real.tendsto_prod_pi_div_two Real.tendsto_prod_pi_div_two
