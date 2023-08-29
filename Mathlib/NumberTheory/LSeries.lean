/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.Algebra.InfiniteSum.Basic

#align_import number_theory.l_series from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# L-series

Given an arithmetic function, we define the corresponding L-series.

## Main Definitions
 * `Nat.ArithmeticFunction.LSeries` is the `LSeries` with a given arithmetic function as its
  coefficients. This is not the analytic continuation, just the infinite series.
 * `Nat.ArithmeticFunction.LSeriesSummable` indicates that the `LSeries`
  converges at a given point.

## Main Results
 * `Nat.ArithmeticFunction.LSeriesSummable_of_bounded_of_one_lt_real`: the `LSeries` of a bounded
  arithmetic function converges when `1 < z.re`.
 * `Nat.ArithmeticFunction.zeta_LSeriesSummable_iff_one_lt_re`: the `LSeries` of `ζ`
  (whose analytic continuation is the Riemann ζ) converges iff `1 < z.re`.

-/


noncomputable section

open scoped BigOperators

namespace Nat

namespace ArithmeticFunction

/-- The L-series of an `ArithmeticFunction`. -/
def LSeries (f : ArithmeticFunction ℂ) (z : ℂ) : ℂ :=
  ∑' n, f n / n ^ z
#align nat.arithmetic_function.l_series Nat.ArithmeticFunction.LSeries

/-- `f.LSeriesSummable z` indicates that the L-series of `f` converges at `z`. -/
def LSeriesSummable (f : ArithmeticFunction ℂ) (z : ℂ) : Prop :=
  Summable fun n => f n / n ^ z
#align nat.arithmetic_function.l_series_summable Nat.ArithmeticFunction.LSeriesSummable

theorem LSeries_eq_zero_of_not_LSeriesSummable (f : ArithmeticFunction ℂ) (z : ℂ) :
    ¬f.LSeriesSummable z → f.LSeries z = 0 :=
  tsum_eq_zero_of_not_summable
#align nat.arithmetic_function.l_series_eq_zero_of_not_l_series_summable Nat.ArithmeticFunction.LSeries_eq_zero_of_not_LSeriesSummable

@[simp]
theorem LSeriesSummable_zero {z : ℂ} : LSeriesSummable 0 z := by
  simp [LSeriesSummable, summable_zero]
  -- 🎉 no goals
#align nat.arithmetic_function.l_series_summable_zero Nat.ArithmeticFunction.LSeriesSummable_zero

theorem LSeriesSummable_of_bounded_of_one_lt_real {f : ArithmeticFunction ℂ} {m : ℝ}
    (h : ∀ n : ℕ, Complex.abs (f n) ≤ m) {z : ℝ} (hz : 1 < z) : f.LSeriesSummable z := by
  by_cases h0 : m = 0
  -- ⊢ LSeriesSummable f ↑z
  · subst h0
    -- ⊢ LSeriesSummable f ↑z
    have hf : f = 0 := ArithmeticFunction.ext fun n =>
      Complex.abs.eq_zero.1 (le_antisymm (h n) (Complex.abs.nonneg _))
    simp [hf]
    -- 🎉 no goals
  refine' summable_of_norm_bounded (fun n : ℕ => m / n ^ z) _ _
  -- ⊢ Summable fun n => m / ↑n ^ z
  · simp_rw [div_eq_mul_inv]
    -- ⊢ Summable fun n => m * (↑n ^ z)⁻¹
    exact (summable_mul_left_iff h0).2 (Real.summable_nat_rpow_inv.2 hz)
    -- 🎉 no goals
  · intro n
    -- ⊢ ‖↑f n / ↑n ^ ↑z‖ ≤ (fun n => m / ↑n ^ z) n
    have hm : 0 ≤ m := le_trans (Complex.abs.nonneg _) (h 0)
    -- ⊢ ‖↑f n / ↑n ^ ↑z‖ ≤ (fun n => m / ↑n ^ z) n
    cases' n with n
    -- ⊢ ‖↑f Nat.zero / ↑Nat.zero ^ ↑z‖ ≤ (fun n => m / ↑n ^ z) Nat.zero
    · simp [hm, Real.zero_rpow (_root_.ne_of_gt (lt_trans Real.zero_lt_one hz))]
      -- 🎉 no goals
    simp only [map_div₀, Complex.norm_eq_abs]
    -- ⊢ ↑Complex.abs (↑f (succ n)) / ↑Complex.abs (↑(succ n) ^ ↑z) ≤ m / ↑(succ n) ^ z
    apply div_le_div hm (h _) (Real.rpow_pos_of_pos (Nat.cast_pos.2 n.succ_pos) _) (le_of_eq _)
    -- ⊢ ↑(succ n) ^ z = ↑Complex.abs (↑(succ n) ^ ↑z)
    rw [Complex.abs_cpow_real, Complex.abs_cast_nat]
    -- 🎉 no goals
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_real Nat.ArithmeticFunction.LSeriesSummable_of_bounded_of_one_lt_real

theorem LSeriesSummable_iff_of_re_eq_re {f : ArithmeticFunction ℂ} {w z : ℂ} (h : w.re = z.re) :
    f.LSeriesSummable w ↔ f.LSeriesSummable z := by
  suffices h :
    ∀ n : ℕ, Complex.abs (f n) / Complex.abs (↑n ^ w) = Complex.abs (f n) / Complex.abs (↑n ^ z)
  · simp [LSeriesSummable, ← summable_norm_iff, h, Complex.norm_eq_abs]
    -- 🎉 no goals
  intro n
  -- ⊢ ↑Complex.abs (↑f n) / ↑Complex.abs (↑n ^ w) = ↑Complex.abs (↑f n) / ↑Complex …
  cases' n with n; · simp
  -- ⊢ ↑Complex.abs (↑f Nat.zero) / ↑Complex.abs (↑Nat.zero ^ w) = ↑Complex.abs (↑f …
                     -- 🎉 no goals
  apply congr rfl
  -- ⊢ ↑Complex.abs (↑(succ n) ^ w) = ↑Complex.abs (↑(succ n) ^ z)
  have h0 : (n.succ : ℂ) ≠ 0 := by
    rw [Ne.def, Nat.cast_eq_zero]
    apply n.succ_ne_zero
  rw [Complex.cpow_def, Complex.cpow_def, if_neg h0, if_neg h0, Complex.abs_exp_eq_iff_re_eq]
  -- ⊢ (Complex.log ↑(succ n) * w).re = (Complex.log ↑(succ n) * z).re
  simp only [h, Complex.mul_re, mul_eq_mul_left_iff, sub_right_inj]
  -- ⊢ w.im = z.im ∨ (Complex.log ↑(succ n)).im = 0
  right
  -- ⊢ (Complex.log ↑(succ n)).im = 0
  rw [Complex.log_im, ← Complex.ofReal_nat_cast]
  -- ⊢ Complex.arg ↑↑(succ n) = 0
  exact Complex.arg_ofReal_of_nonneg (le_of_lt (cast_pos.2 n.succ_pos))
  -- 🎉 no goals
#align nat.arithmetic_function.l_series_summable_iff_of_re_eq_re Nat.ArithmeticFunction.LSeriesSummable_iff_of_re_eq_re

theorem LSeriesSummable_of_bounded_of_one_lt_re {f : ArithmeticFunction ℂ} {m : ℝ}
    (h : ∀ n : ℕ, Complex.abs (f n) ≤ m) {z : ℂ} (hz : 1 < z.re) : f.LSeriesSummable z := by
  rw [← LSeriesSummable_iff_of_re_eq_re (Complex.ofReal_re z.re)]
  -- ⊢ LSeriesSummable f ↑z.re
  apply LSeriesSummable_of_bounded_of_one_lt_real h
  -- ⊢ 1 < z.re
  exact hz
  -- 🎉 no goals
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re Nat.ArithmeticFunction.LSeriesSummable_of_bounded_of_one_lt_re

open scoped ArithmeticFunction

theorem zeta_LSeriesSummable_iff_one_lt_re {z : ℂ} : LSeriesSummable ζ z ↔ 1 < z.re := by
  rw [← LSeriesSummable_iff_of_re_eq_re (Complex.ofReal_re z.re), LSeriesSummable, ←
    summable_norm_iff, ← Real.summable_one_div_nat_rpow, iff_iff_eq]
  by_cases h0 : z.re = 0
  -- ⊢ (Summable fun x => ‖↑↑ζ x / ↑x ^ ↑z.re‖) = Summable fun n => 1 / ↑n ^ z.re
  · rw [h0, ← summable_nat_add_iff 1]
    -- ⊢ (Summable fun n => ‖↑↑ζ (n + 1) / ↑(n + 1) ^ ↑0‖) = Summable fun n => 1 / ↑n …
    apply congr rfl
    -- ⊢ (fun n => ‖↑↑ζ (n + 1) / ↑(n + 1) ^ ↑0‖) = fun n => 1 / ↑n ^ 0
    ext n
    -- ⊢ ‖↑↑ζ (n + 1) / ↑(n + 1) ^ ↑0‖ = 1 / ↑n ^ 0
    simp [n.succ_ne_zero]
    -- 🎉 no goals
  · apply congr rfl
    -- ⊢ (fun x => ‖↑↑ζ x / ↑x ^ ↑z.re‖) = fun n => 1 / ↑n ^ z.re
    ext ⟨- | n⟩
    -- ⊢ ‖↑↑ζ Nat.zero / ↑Nat.zero ^ ↑z.re‖ = 1 / ↑Nat.zero ^ z.re
    · simp [h0]
      -- 🎉 no goals
    simp only [cast_zero, natCoe_apply, zeta_apply, succ_ne_zero, if_false, cast_succ, one_div,
      Complex.norm_eq_abs, map_inv₀, Complex.abs_cpow_real, inv_inj, zero_add]
    rw [← cast_one, ← cast_add, Complex.abs_of_nat, cast_add, cast_one]
    -- 🎉 no goals
#align nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re Nat.ArithmeticFunction.zeta_LSeriesSummable_iff_one_lt_re

@[simp]
theorem LSeries_add {f g : ArithmeticFunction ℂ} {z : ℂ} (hf : f.LSeriesSummable z)
    (hg : g.LSeriesSummable z) : (f + g).LSeries z = f.LSeries z + g.LSeries z := by
  simp only [LSeries, add_apply]
  -- ⊢ ∑' (n : ℕ), (↑f n + ↑g n) / ↑n ^ z = ∑' (n : ℕ), ↑f n / ↑n ^ z + ∑' (n : ℕ), …
  rw [← tsum_add hf hg]
  -- ⊢ ∑' (n : ℕ), (↑f n + ↑g n) / ↑n ^ z = ∑' (b : ℕ), (↑f b / ↑b ^ z + ↑g b / ↑b  …
  apply congr rfl (funext fun n => _)
  -- ⊢ ∀ (n : ℕ), (↑f n + ↑g n) / ↑n ^ z = ↑f n / ↑n ^ z + ↑g n / ↑n ^ z
  simp [_root_.add_div]
  -- 🎉 no goals
#align nat.arithmetic_function.l_series_add Nat.ArithmeticFunction.LSeries_add

end ArithmeticFunction

end Nat
