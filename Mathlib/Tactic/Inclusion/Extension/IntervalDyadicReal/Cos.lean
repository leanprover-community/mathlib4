/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Series

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Cosine enclosures for interval_dyadic_real

This file defines an inclusion operation for the `interval_dyadic_real` inclusion family that
encloses `Real.cos` of an interval.
-/

public section

open Finset

open scoped Nat

namespace Inclusion

namespace IntervalDyadicReal
open Inclusion.IntervalDyadicReal

/-- An enclosure of `cos (x / 2 ^ k)` for `0 ≤ x ≤ 2 ^ k` by the first `n` terms of its series and
the remainder bound of `Real.abs_cos_sub_sum_range_le`, rounded outward to precision `prec`. -/
@[expose]
def cosShiftRightTaylor (x : Dyadic) (k n prec : ℕ) : Interval Dyadic :=
  let X := hypergeomPartialSum (fun _ ↦ -(x >>> k).toRat.num ^ 2)
    (fun j ↦ (x >>> k).toRat.den ^ 2 * ((2 * j + 1) * (2 * j + 2))) 0 n
  ratBall X.sumNum |X.termNum| X.den prec

theorem cosShiftRightTaylor_mem {x : Dyadic} {k : ℕ} (h0 : 0 ≤ x.toReal) (hx : x.toReal ≤ 2 ^ k)
    (n prec : ℕ) : Real.cos (x.toReal / 2 ^ k) ∈ cosShiftRightTaylor x k n prec := by
  have hs : x.toReal / 2 ^ k = (x >>> k).toRat := by
    simp [Dyadic.toReal, Dyadic.toRat_shiftRight_nat]
  have h := Real.abs_cos_sub_sum_range_le (r := x.toReal / 2 ^ k)
    (by rwa [abs_of_nonneg (by positivity), div_le_one (by positivity)]) n
  have hb := (x >>> k).toRat.den_nz
  rw [cosShiftRightTaylor, hs, Rat.cast_def] at *
  generalize (x >>> k).toRat.num = a, (x >>> k).toRat.den = b at *
  rw [← hypergeomPartialSum_div (Int.castRingHom ℝ) (fun _ ↦ -a ^ 2)
    (fun j ↦ b ^ 2 * ((2 * j + 1) * (2 * j + 2))) (fun j ↦ by positivity)
    (fun m ↦ (-1) ^ m * ((a : ℝ) / b) ^ (2 * m) / (2 * m)!) (fun j ↦ by
      push_cast [eq_intCast, mul_add_one, Nat.factorial_succ, pow_add]
      field)] at h
  obtain ⟨hterm, hden, -⟩ := hypergeomPartialSum_spec (fun _ ↦ -a ^ 2)
    (fun j ↦ b ^ 2 * ((2 * j + 1) * (2 * j + 2))) 0 n
  have hprod (n : ℕ) :
      ∏ j ∈ range n, b ^ 2 * ((2 * j + 1) * (2 * j + 2)) = b ^ (2 * n) * (2 * n)! := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, ih, mul_add_one, Nat.factorial_succ, Nat.factorial_succ]
      ring
  generalize hypergeomPartialSum (R := ℤ) _ _ 0 n = X at h hterm hden ⊢
  simp only [zero_add, Nat.Ico_zero_eq_range, prod_const, card_range, hprod] at hterm hden
  refine ratBall_mem ?_ prec
  convert h using 1 <;> simp [hterm, hden, div_pow, pow_mul, div_div]

/-- Apply the double-angle formula `cos (2 * x) = 2 * cos x ^ 2 - 1` `k` times to an enclosure `I`
of `cos x`, rounding outward after each step. The formula uses `cos x` once, so each step encloses
the exact image of `I`, which is at most `4` times as wide when `I ⊆ [-1, 1]`. -/
@[expose]
def cosDoubling (k : ℕ) (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match k with
  | 0 => I
  | m + 1 =>
    cosDoubling m
      (roundOut (((Interval.singleton 2).mul (I.pow 2)).sub (Interval.singleton 1)) prec) prec

theorem cosDoubling_mem {x : ℝ} {I : Interval Dyadic} (hx : Real.cos x ∈ I) (k prec : ℕ) :
    Real.cos (2 ^ k * x) ∈ cosDoubling k I prec := by
  induction k generalizing x I with
  | zero => simpa [cosDoubling] using hx
  | succ k ih =>
    rw [cosDoubling, pow_succ, mul_assoc]
    refine ih ?_
    rw [Real.cos_two_mul]
    exact roundOut_mem (sub_mem (mul_mem (ofNat_mem 2) (pow_mem 2 hx)) (ofNat_mem 1)) prec

/-- The cosine of an interval `I`, which is `[-1, 1]` when `I` is wider than `2π` (using `7` as a
proxy for efficiency). Otherwise, `cos [a, b]` is computed by halving the interval `k` times to
a small enough `[a / 2 ^ k, b / 2 ^ k]` so that `cos` is antitone on it. The constants are chosen
as follows:
- `k` is chosen so that `b / 2 ^ k ≤ 2 ^ (-⌊√prec⌋)`. This provides `√prec`
bits of precision per term in the series.
- `p` adds to `prec` `2` bits for each doubling, which widens an interval by a factor of at most
  `4`, and `8` more bits so that the result exceeds the range of `cos` on `I` by little more than
  `2 ^ (-prec - 1)` on each side, and has width at most `2 ^ (-prec)` when `I` is a point.
- The number of terms brings the remainder below `2 ^ (-p)`, since each term shrinks it by at
  least `2 * ⌊√prec⌋ + 1` bits (`2 * ⌊√prec⌋` from the bound on `b / 2 ^ k` and `1` from the
  factorial).
-/
@[expose]
def cos (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  (match I, I.abs with
  | ⟨some l, some u⟩, ⟨some a, some b⟩ =>
    if l + 7 < u then Interval.univ Dyadic else
      let k := Nat.clog 2 ⌈b.toRat⌉₊ + Nat.sqrt prec
      let p := prec + 2 * k + 8
      let taylor (x : Dyadic) := cosShiftRightTaylor x k (p / (2 * Nat.sqrt prec + 1) + 1) p
      roundOut (cosDoubling k
        (if a = b then taylor b else ⟨(taylor b).lb, (taylor a).ub⟩) p) (prec + 1)
  | _, _ => Interval.univ Dyadic).inter (Interval.Icc (-1 : Dyadic) (1 : Dyadic))

@[inclusion_op interval_dyadic_real]
theorem cos_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.cos x ∈ cos I prec := by
  refine Interval.inter_mem Dyadic.toRealOrderEmbedding ?_
    ((mem_mk_coe ..).2 (by simpa [Dyadic.toReal] using Real.cos_mem_Icc x))
  have habs := abs_mem hx
  have h0 := I.abs_lb_nonneg
  generalize I.abs = J at habs h0 ⊢
  rcases I with ⟨_ | l, _ | u⟩ <;> rcases J with ⟨_ | a, _ | b⟩ <;>
    try exact Interval.mem_map_univ _ _
  dsimp only
  split
  · exact Interval.mem_map_univ _ _
  obtain ⟨hax, hxb⟩ := (mem_mk_coe |x| a b).mp habs
  have ha : 0 ≤ a.toReal := by simpa using Dyadic.toReal_le_toReal.mpr (WithBot.coe_le_coe.mp h0)
  generalize hk : Nat.clog 2 ⌈b.toRat⌉₊ + Nat.sqrt prec = k
  have hb : b.toReal ≤ 2 ^ k := (Rat.cast_le.mpr (Nat.ceil_le.mp
    ((Nat.clog_le_iff_le_pow one_lt_two).mp (by lia : _ ≤ k)))).trans_eq (by norm_cast)
  have hπ := (div_le_one_of_le₀ hb (by positivity)).trans (one_le_two.trans Real.two_le_pi)
  rw [← Real.cos_abs, ← mul_div_cancel₀ |x| (pow_ne_zero k two_ne_zero),
    ite_eq_right_iff.mpr fun h ↦ h ▸ rfl]
  refine roundOut_mem (cosDoubling_mem (Interval.mem_Icc_of_le
    (cosShiftRightTaylor_mem (ha.trans (hax.trans hxb)) hb _ _) ?_ ?_
    (cosShiftRightTaylor_mem ha ((hax.trans hxb).trans hb) _ _)) k _) _ <;>
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (le_trans (by gcongr) hπ) (by gcongr)

end IntervalDyadicReal

end Inclusion
