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

Given a sequence `f: ℕ → ℂ`, we define the corresponding L-series.

## Main Definitions

 * `LSeries f` is the L-Series with a given sequence `f` as its
  coefficients. This is not the analytic continuation, just the infinite series.

 * `LSeriesSummable f` indicates that the L-series of `f`
  converges at a given point.

 * `LSeriesHasSum f s a` expresses that the L-series
  of `f` converges (absolutely) at `s : ℂ` to `a : ℂ`.

## Main Results

 * `LSeriesSummable_of_le_const_mul_rpow`: the `LSeries` of a
  sequence bounded by a constant times `n^(x-1)` converges at `s` when `x < s.re`.

 * `zeta_LSeriesSummable_iff_one_lt_re`: the `LSeries` of `fun n ↦ 1`
  (whose analytic continuation is the Riemann ζ) converges iff `1 < z.re`.

## Tags

L-series, abscissa of convergence

## TODO

* Move `zeta_LSeriesSummable_iff_one_lt_r` to a new file on L-series of specific functions

* Move `LSeries_add` to a new file on algebraic operations on L-series
-/


open scoped BigOperators

-- namespace ArithmeticFunction

open Complex Nat

/-- The `n`th term of the L-series of `f` evaluated at `s`. We set it to zero when `n = 0`. -/
noncomputable
def LSeriesTerm (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n / n ^ s

lemma LSeriesTerm_def (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeriesTerm f s n = if n = 0 then 0 else f n / n ^ s :=
  rfl

lemma LSeriesTerm_def' (f : ℕ → ℂ) (s : ℂ) :
    LSeriesTerm f s = fun n ↦ if n = 0 then 0 else f n / n ^ s :=
  rfl

@[simp]
lemma LSeriesTerm_zero (f : ℕ → ℂ) (s : ℂ) : LSeriesTerm f s 0 = 0 := rfl

@[simp]
lemma LSeriesTerm_ne_zero (f : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeriesTerm f s n = f n / n ^ s :=
  if_neg hn

@[simp]
lemma LSeriesTerm_pos (f : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    LSeriesTerm f s n = f n / n ^ s :=
  LSeriesTerm_ne_zero f s <| Nat.pos_iff_ne_zero.mp hn

/-- The L-series of the sequence `f`. -/
noncomputable
def LSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n, LSeriesTerm f s n
#align nat.arithmetic_function.l_series LSeries

/-- `LSeriesSummable f s` indicates that the L-series of `f` converges at `s`. -/
def LSeriesSummable (f : ℕ → ℂ) (s : ℂ) : Prop :=
  Summable (LSeriesTerm f s)
#align nat.arithmetic_function.l_series_summable LSeriesSummable

theorem LSeries_eq_zero_of_not_LSeriesSummable (f : ℕ → ℂ) (s : ℂ) :
    ¬ LSeriesSummable f s → LSeries f s = 0 :=
  tsum_eq_zero_of_not_summable
#align nat.arithmetic_function.l_series_eq_zero_of_not_l_series_summable LSeries_eq_zero_of_not_LSeriesSummable

@[simp]
theorem LSeriesSummable_zero {s : ℂ} : LSeriesSummable 0 s := by
  simp only [LSeriesSummable, LSeriesTerm_def', Pi.zero_apply, zero_div, ite_self, summable_zero]
#align nat.arithmetic_function.l_series_summable_zero LSeriesSummable_zero

/-- This states that the L-series of the sequence `f` converges at `s` to `a`. -/
def LSeriesHasSum (f : ℕ → ℂ) (s a : ℂ) : Prop :=
  HasSum (LSeriesTerm f s) a

lemma LSeriesHasSum.LSeriesSummable {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeriesSummable f s :=
  h.summable

lemma LSeriesHasSum.LSeries_eq {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeries f s = a :=
  h.tsum_eq

lemma LSeriesSummable.LSeriesHasSum {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    LSeriesHasSum f s (LSeries f s) :=
  h.hasSum

lemma norm_LSeriesTerm_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    ‖LSeriesTerm f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeriesTerm_zero, norm_zero, ↓reduceIte]
  rw [if_neg hn, LSeriesTerm_ne_zero _ _ hn, norm_div,
    norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]

lemma norm_LSeriesTerm_le_of_re_le_re (f : ℕ → ℂ) {w : ℂ} {z : ℂ}
    (h : w.re ≤ z.re) (n : ℕ) :
    ‖LSeriesTerm f z n‖ ≤ ‖LSeriesTerm f w n‖ := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp only [LSeriesTerm_zero, norm_zero, le_refl]
  have hn := Nat.pos_of_ne_zero hn₀
  have hn' := norm_natCast_cpow_pos_of_pos hn w
  simp_rw [LSeriesTerm_pos _ _ hn, norm_div]
  suffices H : ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ from div_le_div (norm_nonneg _) le_rfl hn' H
  refine (one_le_div hn').mp ?_
  rw [← norm_div, ← cpow_sub _ _ <| cast_ne_zero.mpr hn.ne', norm_natCast_cpow_of_pos hn]
  exact Real.one_le_rpow (one_le_cast.mpr hn) <| by simp only [sub_re, sub_nonneg, h]

lemma LSeriesSummable.of_re_le_re {f : ℕ → ℂ} {w : ℂ} {z : ℂ} (h : w.re ≤ z.re)
    (hf : LSeriesSummable f w) : LSeriesSummable f z := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_LSeriesTerm_le_of_re_le_re f h)

theorem LSeriesSummable_iff_of_re_eq_re {f : ℕ → ℂ} {w z : ℂ} (h : w.re = z.re) :
    LSeriesSummable f w ↔ LSeriesSummable f z :=
  ⟨fun H ↦  H.of_re_le_re h.le, fun H ↦ H.of_re_le_re h.symm.le⟩
#align nat.arithmetic_function.l_series_summable_iff_of_re_eq_re LSeriesSummable_iff_of_re_eq_re

lemma LSeriesSummable.le_const_mul_rpow {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ s.re := by
  replace h := h.norm
  by_contra! H
  obtain ⟨n, hn₀, hn⟩ := H (tsum fun n ↦ ‖LSeriesTerm f s n‖)
  have := le_tsum h n fun _ _ ↦ norm_nonneg _
  rw [norm_LSeriesTerm_eq, if_neg hn₀,
    div_le_iff <| Real.rpow_pos_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn₀) _] at this
  exact (this.trans_lt hn).false.elim

open Filter in
lemma LSeriesSummable.isBigO_rpow {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : f =O[atTop] fun n ↦ (n : ℝ) ^ s.re := by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
  refine Asymptotics.IsBigO.of_bound C <| eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
  convert hC n (Nat.pos_iff_ne_zero.mp hn) using 2
  rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg n.cast_nonneg, _root_.abs_of_nonneg n.cast_nonneg]

lemma LSeriesSummable_of_le_const_mul_rpow {f : ℕ → ℂ} {x : ℝ} {s : ℂ}
    (hs : x < s.re) (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := h
  have hC₀ : 0 ≤ C := by
    specialize hC 1 one_ne_zero
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
  · simp only [LSeriesTerm_zero, norm_zero]
    exact norm_nonneg _
  have hn' : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  simp_rw [LSeriesTerm_pos _ _ hn, norm_div, norm_natCast_cpow_of_pos hn, div_le_iff hn', add_re,
    sub_re, one_re, ofReal_re, Real.rpow_add <| Nat.cast_pos.mpr hn, div_eq_mul_inv, mul_inv]
  rw [mul_assoc, mul_comm _ ((n : ℝ) ^ s.re), ← mul_assoc ((n : ℝ) ^ s.re), mul_inv_cancel hn'.ne',
    ← Real.rpow_neg n.cast_nonneg, norm_eq_abs (C : ℂ), abs_ofReal, _root_.abs_of_nonneg hC₀,
    neg_sub, one_mul]
  exact hC n <| Nat.pos_iff_ne_zero.mp hn

open Filter Finset Real Nat in
lemma LSeriesSummable_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ} {s : ℂ}
    (hs : x < s.re) (h : f =O[atTop] fun n ↦ (n : ℝ) ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : ℕ ↦ ‖f n‖ / (n : ℝ) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
  have hC'₀ : 0 ≤ C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans <| le_max_right ..
  have hCC' : C ≤ C' := le_max_left ..
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C', fun n hn₀ ↦ ?_⟩
  rcases le_or_lt m n with hn | hn
  · refine (hm n hn).trans ?_
    have hn₀ : (0 : ℝ) ≤ n := cast_nonneg _
    gcongr
    rw [Real.norm_eq_abs, abs_rpow_of_nonneg hn₀, _root_.abs_of_nonneg hn₀]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn₀
    refine (div_le_iff <| rpow_pos_of_pos (cast_pos.mpr hn') _).mp ?_
    refine (le_max' _ _ <| mem_insert_of_mem ?_).trans <| le_max_right ..
    exact mem_image.mpr ⟨n, mem_range.mpr hn, rfl⟩

theorem LSeriesSummable_of_bounded_of_one_lt_re {f : ℕ → ℂ} {m : ℝ}
    (h : ∀ n ≠ 0, Complex.abs (f n) ≤ m) {z : ℂ} (hz : 1 < z.re) : LSeriesSummable f z := by
  refine LSeriesSummable_of_le_const_mul_rpow hz ⟨m, fun n hn ↦ ?_⟩
  simp only [norm_eq_abs, sub_self, Real.rpow_zero, mul_one, h n hn]
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re LSeriesSummable_of_bounded_of_one_lt_re

theorem LSeriesSummable_of_bounded_of_one_lt_real {f : ℕ → ℂ} {m : ℝ}
    (h : ∀ n ≠ 0, Complex.abs (f n) ≤ m) {z : ℝ} (hz : 1 < z) : LSeriesSummable f z :=
  LSeriesSummable_of_bounded_of_one_lt_re h <| by simp only [ofReal_re, hz]
#align nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_real LSeriesSummable_of_bounded_of_one_lt_real

open scoped ArithmeticFunction

theorem zeta_LSeriesSummable_iff_one_lt_re {z : ℂ} : LSeriesSummable (fun n ↦ 1) z ↔ 1 < z.re := by
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
    simp only [ne_eq, succ_ne_zero, not_false_eq_true, LSeriesTerm_ne_zero, cast_succ, one_div,
      norm_inv, norm_eq_abs, abs_cpow_real, inv_inj]
    rw [← cast_one, ← cast_add, Complex.abs_natCast, cast_add, cast_one]
#align nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re zeta_LSeriesSummable_iff_one_lt_re

lemma LSeriesTerm_add (f g : ℕ → ℂ) (s : ℂ) :
    LSeriesTerm (f + g) s = LSeriesTerm f s + LSeriesTerm g s := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeriesTerm_zero, Pi.add_apply, add_zero]
  simp only [LSeriesTerm_ne_zero _ _ hn, Pi.add_apply, _root_.add_div]

lemma LSeriesHasSum_add {f g : ℕ → ℂ} {z a b : ℂ} (hf : LSeriesHasSum f z a)
    (hg : LSeriesHasSum g z b) :
    LSeriesHasSum (f + g) z (a + b) := by
  simpa only [LSeriesHasSum, LSeriesTerm_add] using HasSum.add hf hg

@[simp]
theorem LSeries_add {f g : ℕ → ℂ} {z : ℂ} (hf : LSeriesSummable f z)
    (hg : LSeriesSummable g z) : LSeries (f + g) z = LSeries f z + LSeries g z := by
  simp only [LSeries, Pi.add_apply]
  rw [← tsum_add hf hg]
  congr
  exact LSeriesTerm_add ..
#align nat.arithmetic_function.l_series_add LSeries_add

-- end ArithmeticFunction
