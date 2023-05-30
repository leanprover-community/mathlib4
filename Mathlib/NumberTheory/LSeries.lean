/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module number_theory.l_series
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# L-series

Given an arithmetic function, we define the corresponding L-series.

## Main Definitions
 * `nat.arithmetic_function.l_series` is the `l_series` with a given arithmetic function as its
  coefficients. This is not the analytic continuation, just the infinite series.
 * `nat.arithmetic_function.l_series_summable` indicates that the `l_series`
  converges at a given point.

## Main Results
 * `nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re`: the `l_series` of a bounded
  arithmetic function converges when `1 < z.re`.
 * `nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re`: the `l_series` of `ζ`
  (whose analytic continuation is the Riemann ζ) converges iff `1 < z.re`.

-/


noncomputable section

open scoped BigOperators

namespace Nat

namespace ArithmeticFunction

/-- The L-series of an `arithmetic_function`. -/
def lSeries (f : ArithmeticFunction ℂ) (z : ℂ) : ℂ :=
  ∑' n, f n / n ^ z
#align nat.arithmetic_function.l_series Nat.ArithmeticFunction.lSeries

/-- `f.l_series_summable z` indicates that the L-series of `f` converges at `z`. -/
def LSeriesSummable (f : ArithmeticFunction ℂ) (z : ℂ) : Prop :=
  Summable fun n => f n / n ^ z
#align nat.arithmetic_function.l_series_summable Nat.ArithmeticFunction.LSeriesSummable

theorem lSeries_eq_zero_of_not_lSeriesSummable (f : ArithmeticFunction ℂ) (z : ℂ) :
    ¬f.LSeriesSummable z → f.lSeries z = 0 :=
  tsum_eq_zero_of_not_summable
#align nat.arithmetic_function.l_series_eq_zero_of_not_l_series_summable Nat.ArithmeticFunction.lSeries_eq_zero_of_not_lSeriesSummable

@[simp]
theorem lSeriesSummable_zero {z : ℂ} : LSeriesSummable 0 z := by
  simp [l_series_summable, summable_zero]
#align nat.arithmetic_function.l_series_summable_zero Nat.ArithmeticFunction.lSeriesSummable_zero

theorem lSeriesSummable_of_bounded_of_one_lt_real {f : ArithmeticFunction ℂ} {m : ℝ}
    (h : ∀ n : ℕ, Complex.abs (f n) ≤ m) {z : ℝ} (hz : 1 < z) : f.LSeriesSummable z := by
  by_cases h0 : m = 0
  · subst h0
    have hf : f = 0 :=
      arithmetic_function.ext fun n =>
        complex.abs.eq_zero.1 (le_antisymm (h n) (complex.abs.nonneg _))
    simp [hf]
  refine' summable_of_norm_bounded (fun n : ℕ => m / n ^ z) _ _
  · simp_rw [div_eq_mul_inv]
    exact (summable_mul_left_iff h0).2 (Real.summable_nat_rpow_inv.2 hz)
  · intro n
    have hm : 0 ≤ m := le_trans (complex.abs.nonneg _) (h 0)
    cases n
    · simp [hm, Real.zero_rpow (ne_of_gt (lt_trans Real.zero_lt_one hz))]
    simp only [map_div₀, Complex.norm_eq_abs]
    apply div_le_div hm (h _) (Real.rpow_pos_of_pos (Nat.cast_pos.2 n.succ_pos) _) (le_of_eq _)
    rw [Complex.abs_cpow_real, Complex.abs_cast_nat]
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_real Nat.ArithmeticFunction.lSeriesSummable_of_bounded_of_one_lt_real

theorem lSeriesSummable_iff_of_re_eq_re {f : ArithmeticFunction ℂ} {w z : ℂ} (h : w.re = z.re) :
    f.LSeriesSummable w ↔ f.LSeriesSummable z := by
  suffices h :
    ∀ n : ℕ, Complex.abs (f n) / Complex.abs (↑n ^ w) = Complex.abs (f n) / Complex.abs (↑n ^ z)
  · simp [l_series_summable, ← summable_norm_iff, h, Complex.norm_eq_abs]
  intro n
  cases n; · simp
  apply congr rfl
  have h0 : (n.succ : ℂ) ≠ 0 := by
    rw [Ne.def, Nat.cast_eq_zero]
    apply n.succ_ne_zero
  rw [Complex.cpow_def, Complex.cpow_def, if_neg h0, if_neg h0, Complex.abs_exp_eq_iff_re_eq]
  simp only [h, Complex.mul_re, mul_eq_mul_left_iff, sub_right_inj]
  right
  rw [Complex.log_im, ← Complex.ofReal_nat_cast]
  exact Complex.arg_of_real_of_nonneg (le_of_lt (cast_pos.2 n.succ_pos))
#align nat.arithmetic_function.l_series_summable_iff_of_re_eq_re Nat.ArithmeticFunction.lSeriesSummable_iff_of_re_eq_re

theorem lSeriesSummable_of_bounded_of_one_lt_re {f : ArithmeticFunction ℂ} {m : ℝ}
    (h : ∀ n : ℕ, Complex.abs (f n) ≤ m) {z : ℂ} (hz : 1 < z.re) : f.LSeriesSummable z := by
  rw [← l_series_summable_iff_of_re_eq_re (Complex.ofReal_re z.re)]
  apply l_series_summable_of_bounded_of_one_lt_real h
  exact hz
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re Nat.ArithmeticFunction.lSeriesSummable_of_bounded_of_one_lt_re

open scoped ArithmeticFunction

theorem zeta_lSeriesSummable_iff_one_lt_re {z : ℂ} : LSeriesSummable ζ z ↔ 1 < z.re := by
  rw [← l_series_summable_iff_of_re_eq_re (Complex.ofReal_re z.re), l_series_summable, ←
    summable_norm_iff, ← Real.summable_one_div_nat_rpow, iff_iff_eq]
  by_cases h0 : z.re = 0
  · rw [h0, ← summable_nat_add_iff 1]
    swap; · infer_instance
    apply congr rfl
    ext n
    simp [n.succ_ne_zero]
  · apply congr rfl
    ext ⟨- | n⟩
    · simp [h0]
    simp only [cast_zero, nat_coe_apply, zeta_apply, succ_ne_zero, if_false, cast_succ, one_div,
      Complex.norm_eq_abs, map_inv₀, Complex.abs_cpow_real, inv_inj, zero_add]
    rw [← cast_one, ← cast_add, Complex.abs_of_nat, cast_add, cast_one]
#align nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re Nat.ArithmeticFunction.zeta_lSeriesSummable_iff_one_lt_re

@[simp]
theorem lSeries_add {f g : ArithmeticFunction ℂ} {z : ℂ} (hf : f.LSeriesSummable z)
    (hg : g.LSeriesSummable z) : (f + g).lSeries z = f.lSeries z + g.lSeries z := by
  simp only [l_series, add_apply]
  rw [← tsum_add hf hg]
  apply congr rfl (funext fun n => _)
  apply _root_.add_div
#align nat.arithmetic_function.l_series_add Nat.ArithmeticFunction.lSeries_add

end ArithmeticFunction

end Nat

