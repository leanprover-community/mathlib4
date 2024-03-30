/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Michael Stoll
-/
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.NormedSpace.FiniteDimension

#align_import number_theory.l_series from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# L-series

Given an arithmetic function, we define the corresponding L-series.

## Main Definitions

 * `ArithmeticFunction.LSeries` is the `LSeries` with a given arithmetic function as its
  coefficients. This is not the analytic continuation, just the infinite series.

 * `ArithmeticFunction.LSeriesSummable` indicates that the `LSeries`
  converges at a given point.

 * `ArithmeticFunction.LSeriesHasSum f s a` expresses that the L-series
  of `f : ArithmeticFunction ℂ` converges (absolutely) at `s : ℂ` to `a : ℂ`.

## Main Results

 * `ArithmeticFunction.LSeriesSummable_of_le_const_mul_rpow`: the `LSeries` of an
  arithmetic function bounded by a constant times `n^(x-1)` converges at `s` when `x < s.re`.

 * `ArithmeticFunction.zeta_LSeriesSummable_iff_one_lt_re`: the `LSeries` of `ζ`
  (whose analytic continuation is the Riemann ζ) converges iff `1 < z.re`.

## Tags

L-series, abscissa of convergence

## TODO

* Move `zeta_LSeriesSummable_iff_one_lt_r` to a new file on L-series of specific functions

* Move `LSeries_add` to a new file on algebraic operations on L-series
-/


open scoped BigOperators

namespace ArithmeticFunction

open Complex Nat

/-- The L-series of an `ArithmeticFunction`. -/
noncomputable
def LSeries (f : ArithmeticFunction ℂ) (z : ℂ) : ℂ :=
  ∑' n, f n / n ^ z
#align nat.arithmetic_function.l_series ArithmeticFunction.LSeries

/-- `f.LSeriesSummable z` indicates that the L-series of `f` converges at `z`. -/
def LSeriesSummable (f : ArithmeticFunction ℂ) (z : ℂ) : Prop :=
  Summable fun n => f n / n ^ z
#align nat.arithmetic_function.l_series_summable ArithmeticFunction.LSeriesSummable

theorem LSeries_eq_zero_of_not_LSeriesSummable (f : ArithmeticFunction ℂ) (z : ℂ) :
    ¬f.LSeriesSummable z → f.LSeries z = 0 :=
  tsum_eq_zero_of_not_summable
#align nat.arithmetic_function.l_series_eq_zero_of_not_l_series_summable ArithmeticFunction.LSeries_eq_zero_of_not_LSeriesSummable

@[simp]
theorem LSeriesSummable_zero {z : ℂ} : LSeriesSummable 0 z := by
  simp [LSeriesSummable, summable_zero]
#align nat.arithmetic_function.l_series_summable_zero ArithmeticFunction.LSeriesSummable_zero

/-- This states that the L-series of the arithmetic function `f` converges at `s` to `a`. -/
def LSeriesHasSum (f : ArithmeticFunction ℂ) (s a : ℂ) : Prop :=
  HasSum (fun (n : ℕ) => f n / n ^ s) a

lemma LSeriesHasSum.LSeriesSummable {f : ArithmeticFunction ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeriesSummable f s :=
  h.summable

lemma LSeriesHasSum.LSeries_eq {f : ArithmeticFunction ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeries f s = a :=
  h.tsum_eq

lemma LSeriesSummable.LSeriesHasSum {f : ArithmeticFunction ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    LSeriesHasSum f s (LSeries f s) :=
  h.hasSum

lemma norm_LSeriesTerm_eq (f : ArithmeticFunction ℂ) (s : ℂ) (n : ℕ) :
    ‖f n / n ^ s‖ = ‖f n‖ / n ^ s.re := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [map_zero, zero_div, norm_zero, zero_mul]
  rw [norm_div, norm_natCast_cpow_of_pos hn]

lemma norm_LSeriesTerm_le_of_re_le_re (f : ArithmeticFunction ℂ) {w : ℂ} {z : ℂ}
    (h : w.re ≤ z.re) (n : ℕ) : ‖f n / n ^ z‖ ≤ ‖f n / n ^ w‖ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [map_zero, CharP.cast_eq_zero, zero_div, norm_zero, le_refl]
  have hn' := norm_natCast_cpow_pos_of_pos hn w
  simp_rw [norm_div]
  suffices H : ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ from div_le_div (norm_nonneg _) le_rfl hn' H
  refine (one_le_div hn').mp ?_
  rw [← norm_div, ← cpow_sub _ _ <| cast_ne_zero.mpr hn.ne', norm_natCast_cpow_of_pos hn]
  exact Real.one_le_rpow (one_le_cast.mpr hn) <| by simp only [sub_re, sub_nonneg, h]

lemma LSeriesSummable.of_re_le_re {f : ArithmeticFunction ℂ} {w : ℂ} {z : ℂ} (h : w.re ≤ z.re)
    (hf : LSeriesSummable f w) : LSeriesSummable f z := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_LSeriesTerm_le_of_re_le_re f h)

theorem LSeriesSummable_iff_of_re_eq_re {f : ArithmeticFunction ℂ} {w z : ℂ} (h : w.re = z.re) :
    f.LSeriesSummable w ↔ f.LSeriesSummable z :=
  ⟨fun H ↦  H.of_re_le_re h.le, fun H ↦ H.of_re_le_re h.symm.le⟩
#align nat.arithmetic_function.l_series_summable_iff_of_re_eq_re ArithmeticFunction.LSeriesSummable_iff_of_re_eq_re

lemma LSeriesSummable.le_const_mul_rpow {f : ArithmeticFunction ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : ∃ C, ∀ n, ‖f n‖ ≤ C * n ^ s.re := by
  replace h := h.norm
  by_contra! H
  obtain ⟨n, hn⟩ := H (tsum fun n ↦ ‖f n / n ^ s‖)
  have hn₀ : 0 < n := by
    refine n.eq_zero_or_pos.resolve_left ?_
    rintro rfl
    rw [map_zero, norm_zero, Nat.cast_zero, mul_neg_iff] at hn
    replace hn := hn.resolve_left <| fun hh ↦ hh.2.not_le <| Real.rpow_nonneg (le_refl 0) s.re
    exact hn.1.not_le <| tsum_nonneg (fun _ ↦ norm_nonneg _)
  have := le_tsum h n fun _ _ ↦ norm_nonneg _
  rw [norm_LSeriesTerm_eq, div_le_iff <| Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn₀) _] at this
  exact (this.trans_lt hn).false.elim

open Filter in
lemma LSeriesSummable.isBigO_rpow {f : ArithmeticFunction ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : f =O[atTop] fun n ↦ (n : ℝ) ^ s.re := by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
  refine Asymptotics.IsBigO.of_bound C ?_
  convert eventually_of_forall hC using 4 with n
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg hn₀, _root_.abs_of_nonneg hn₀]

lemma LSeriesSummable_of_le_const_mul_rpow {f : ArithmeticFunction ℂ} {x : ℝ} {s : ℂ}
    (hs : x < s.re) (h : ∃ C, ∀ n, ‖f n‖ ≤ C * n ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := h
  have hC₀ : 0 ≤ C := by
    specialize hC 1
    simp only [cast_one, Real.one_rpow, mul_one] at hC
    exact (norm_nonneg _).trans hC
  have hsum : Summable fun n : ℕ ↦ ‖(C : ℂ) / n ^ (s + (1 - x))‖ := by
    simp_rw [div_eq_mul_inv, norm_mul, ← cpow_neg]
    have hsx : -s.re + x - 1 < -1 := by linarith only [hs]
    refine Summable.mul_left _ <|
      Summable.of_norm_bounded_eventually_nat (fun n ↦ (n : ℝ) ^ (-s.re + x - 1)) ?_ ?_
    · simp only [Real.summable_nat_rpow, hsx]
    · simp only [neg_add_rev, neg_sub, norm_norm, Filter.eventually_atTop]
      refine ⟨1, fun n hn ↦ ?_⟩
      simp only [norm_natCast_cpow_of_pos hn, add_re, sub_re, neg_re, ofReal_re, one_re]
      convert le_refl ?_ using 2
      ring
  refine Summable.of_norm <| hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [map_zero, zero_div, norm_zero, norm_nonneg]
  have hn' : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  simp_rw [norm_div, norm_natCast_cpow_of_pos hn, div_le_iff hn', add_re, sub_re, one_re,
    ofReal_re, Real.rpow_add <| Nat.cast_pos.mpr hn, div_eq_mul_inv, mul_inv]
  rw [mul_assoc, mul_comm _ ((n : ℝ) ^ s.re), ← mul_assoc ((n : ℝ) ^ s.re), mul_inv_cancel hn'.ne',
    ← Real.rpow_neg n.cast_nonneg, norm_eq_abs (C : ℂ), abs_ofReal, _root_.abs_of_nonneg hC₀,
    neg_sub, one_mul]
  exact hC n

open Filter Finset Real Nat in
lemma LSeriesSummable_of_isBigO_rpow {f : ArithmeticFunction ℂ} {x : ℝ} {s : ℂ}
    (hs : x < s.re) (h : f =O[atTop] fun n ↦ (n : ℝ) ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : ℕ ↦ ‖f n‖ / (n : ℝ) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
  have hC'₀ : 0 ≤ C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans <| le_max_right ..
  have hCC' : C ≤ C' := le_max_left ..
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C', fun n ↦ ?_⟩
  rcases le_or_lt m n with hn | hn
  · refine (hm n hn).trans ?_
    have hn₀ : (0 : ℝ) ≤ n := cast_nonneg _
    gcongr
    rw [Real.norm_eq_abs, abs_rpow_of_nonneg hn₀, _root_.abs_of_nonneg hn₀]
  · rcases n.eq_zero_or_pos with rfl | hn'
    · simpa only [map_zero, norm_zero, cast_zero] using mul_nonneg hC'₀ <| zero_rpow_nonneg _
    refine (div_le_iff <| rpow_pos_of_pos (cast_pos.mpr hn') _).mp ?_
    refine (le_max' _ _ <| mem_insert_of_mem ?_).trans <| le_max_right ..
    exact mem_image.mpr ⟨n, mem_range.mpr hn, rfl⟩

theorem LSeriesSummable_of_bounded_of_one_lt_re {f : ArithmeticFunction ℂ} {m : ℝ}
    (h : ∀ n : ℕ, Complex.abs (f n) ≤ m) {z : ℂ} (hz : 1 < z.re) : f.LSeriesSummable z := by
  refine LSeriesSummable_of_le_const_mul_rpow hz ⟨m, fun n ↦ ?_⟩
  simp only [norm_eq_abs, sub_self, Real.rpow_zero, mul_one, h n]
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re ArithmeticFunction.LSeriesSummable_of_bounded_of_one_lt_re

theorem LSeriesSummable_of_bounded_of_one_lt_real {f : ArithmeticFunction ℂ} {m : ℝ}
    (h : ∀ n : ℕ, Complex.abs (f n) ≤ m) {z : ℝ} (hz : 1 < z) : f.LSeriesSummable z :=
  LSeriesSummable_of_bounded_of_one_lt_re h <| by simp only [ofReal_re, hz]
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_real ArithmeticFunction.LSeriesSummable_of_bounded_of_one_lt_real

open scoped ArithmeticFunction

theorem zeta_LSeriesSummable_iff_one_lt_re {z : ℂ} : LSeriesSummable ζ z ↔ 1 < z.re := by
  rw [← LSeriesSummable_iff_of_re_eq_re (Complex.ofReal_re z.re), LSeriesSummable, ←
    summable_norm_iff, ← Real.summable_one_div_nat_rpow, iff_iff_eq]
  by_cases h0 : z.re = 0
  · rw [h0, ← summable_nat_add_iff 1]
    apply congr rfl
    ext n
    simp [n.succ_ne_zero]
  · apply congr rfl
    ext ⟨- | n⟩
    · simp [h0]
    simp only [cast_zero, natCoe_apply, zeta_apply, succ_ne_zero, if_false, cast_succ, one_div,
      Complex.norm_eq_abs, map_inv₀, Complex.abs_cpow_real, inv_inj, zero_add]
    rw [← cast_one, ← cast_add, Complex.abs_natCast, cast_add, cast_one]
#align nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re ArithmeticFunction.zeta_LSeriesSummable_iff_one_lt_re

@[simp]
theorem LSeries_add {f g : ArithmeticFunction ℂ} {z : ℂ} (hf : f.LSeriesSummable z)
    (hg : g.LSeriesSummable z) : (f + g).LSeries z = f.LSeries z + g.LSeries z := by
  simp only [LSeries, add_apply]
  rw [← tsum_add hf hg]
  apply congr rfl (funext fun n => _)
  simp [_root_.add_div]
#align nat.arithmetic_function.l_series_add ArithmeticFunction.LSeries_add

end ArithmeticFunction
