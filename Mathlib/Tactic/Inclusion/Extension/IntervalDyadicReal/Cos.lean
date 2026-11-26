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

## Implementation notes

The argument is reduced by repeated halving, which the double-angle formula for `cos` then undoes
(rounding outward at each step so that the bits do not accumulate). The formula is applied to the
whole interval instead of the endpoints, so that the extrema of `cos` inside the interval do not
need case analysis. Monotonicity is used only on the halved interval, where `cos` is antitone and
the Taylor series is evaluated at the two endpoints.

We do not use reduction modulo `π` since that requires high precision of `π` itself, while halving
is exact on dyadic numbers.

This file is opt-in so that `dyadic_interval` doesn't import unnecessary theories.

## TODO

The number of halvings beyond the size of the argument is `⌊√prec⌋`, which is not tuned. A smaller
number is faster for an argument with few bits.

The series is summed exactly, so an argument with many bits is slow at high precision.
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
  rw [cosShiftRightTaylor, hs, Rat.cast_def] at *
  generalize (x >>> k).toRat = q at *
  rw [← hypergeomPartialSum_div (Int.castRingHom ℝ) (fun _ ↦ -q.num ^ 2)
    (fun j ↦ q.den ^ 2 * ((2 * j + 1) * (2 * j + 2))) (fun j ↦ by positivity)
    (fun m ↦ (-1) ^ m * ((q.num : ℝ) / q.den) ^ (2 * m) / (2 * m)!) (fun j ↦ by
      push_cast [eq_intCast, mul_add_one, Nat.factorial_succ, pow_add]
      field)] at h
  obtain ⟨hterm, hden, -⟩ := hypergeomPartialSum_spec (fun _ ↦ -q.num ^ 2)
    (fun j ↦ q.den ^ 2 * ((2 * j + 1) * (2 * j + 2))) 0 n
  have hprod (n : ℕ) : ∏ j ∈ range n, (2 * j + 1) * (2 * j + 2) = (2 * n)! := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, ih, mul_add_one, Nat.factorial_succ, Nat.factorial_succ]
      ring
  refine ratBall_mem ?_ prec
  convert h using 1 <;> simp [hterm, hden, hprod, prod_mul_distrib, div_pow, pow_mul, div_div]

/-- Apply the double-angle formula `cos (2 * x) = 2 * cos x ^ 2 - 1` `k` times to an enclosure `I`
of `cos x`, rounding outward after each step. -/
@[expose]
def cosDoubling (k : ℕ) (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match k with
  | 0 => I
  | m + 1 =>
    cosDoubling m
      (roundOut (((Interval.singleton 2).mul (I.pow 2)).sub (Interval.singleton 1)) prec) prec

theorem cosDoubling_mem {x : ℝ} {I : Interval Dyadic} {k : ℕ} (hx : Real.cos (x / 2 ^ k) ∈ I)
    (prec : ℕ) : Real.cos x ∈ cosDoubling k I prec := by
  induction k generalizing I with
  | zero => simpa [cosDoubling] using hx
  | succ k ih =>
    have h := roundOut_mem (sub_mem (mul_mem (ofNat_mem 2) (pow_mem 2 hx)) (ofNat_mem 1)) prec
    rw [← Real.cos_two_mul, pow_succ, ← div_div, mul_div_cancel₀ _ two_ne_zero] at h
    exact ih h

/-- The cosine of an interval `I`, which is `[-1, 1]` when `I` is wider than `2π` (tested as wider
than `7`, so that no enclosure of `π` is needed). Otherwise, with `[a, b] = I.abs`, `cos [a, b]` is
computed by halving the interval `k` times to a small enough `[a / 2 ^ k, b / 2 ^ k]` so that `cos`
is antitone on it. The constants are chosen as follows:
- `k` is chosen so that `b / 2 ^ k ≤ 2 ^ (-⌊√prec⌋)`. Each term of the series is then smaller than
  the previous one by at least `2 * ⌊√prec⌋ + 1` bits (`2 * ⌊√prec⌋` from the square of the
  argument and `1` from the factorial), so `p / (2 * ⌊√prec⌋ + 1) + 1` terms bring the remainder
  below `2 ^ (-p)`.
- `p` adds to `prec` two bits for each doubling, which multiplies an error by at most `4`, and `8`
  guard bits, so that the result has width at most `2 ^ (-prec)` when `I` is a point.
-/
@[expose]
def cos (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I, I.abs with
  | ⟨some l, some u⟩, ⟨some a, some b⟩ =>
    if l + 7 < u then Interval.Icc (-1 : Dyadic) (1 : Dyadic) else
      let k := Nat.clog 2 ⌈b.toRat⌉₊ + Nat.sqrt prec
      let p := prec + 2 * k + 8
      let taylor (x : Dyadic) := cosShiftRightTaylor x k (p / (2 * Nat.sqrt prec + 1) + 1) p
      roundOut (cosDoubling k
        (if a = b then taylor b else ⟨(taylor b).lb, (taylor a).ub⟩) p) (prec + 1)
  | _, _ => Interval.Icc (-1 : Dyadic) (1 : Dyadic)

@[inclusion_op interval_dyadic_real]
theorem cos_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.cos x ∈ cos I prec := by
  have h1 : Real.cos x ∈ (⟨(-1 : Dyadic), (1 : Dyadic)⟩ : Interval Dyadic) :=
    (mem_mk_coe _ (-1) 1).2 (by simpa [Dyadic.toReal] using Real.cos_mem_Icc x)
  have habs := abs_mem hx
  have h0 := I.abs_lb_nonneg
  unfold cos
  generalize I.abs = J at habs h0 ⊢
  rcases I with ⟨_ | l, _ | u⟩ <;> rcases J with ⟨_ | a, _ | b⟩ <;> try exact h1
  dsimp only
  split
  · exact h1
  obtain ⟨hax, hxb⟩ := (mem_mk_coe |x| a b).mp habs
  have ha : 0 ≤ a.toReal := by simpa using Dyadic.toReal_le_toReal.mpr (WithBot.coe_le_coe.mp h0)
  generalize hk : Nat.clog 2 ⌈b.toRat⌉₊ + Nat.sqrt prec = k
  have hb : b.toReal ≤ 2 ^ k := (Rat.cast_le.mpr (Nat.ceil_le.mp
    ((Nat.clog_le_iff_le_pow one_lt_two).mp (by lia : _ ≤ k)))).trans_eq (by norm_cast)
  have hπ := (div_le_one_of_le₀ hb (by positivity)).trans (one_le_two.trans Real.two_le_pi)
  rw [← Real.cos_abs, ite_eq_right_iff.mpr fun h ↦ h ▸ rfl]
  refine roundOut_mem (cosDoubling_mem (Interval.mem_Icc_of_le
    (cosShiftRightTaylor_mem (ha.trans (hax.trans hxb)) hb _ _) ?_ ?_
    (cosShiftRightTaylor_mem ha ((hax.trans hxb).trans hb) _ _)) _) _ <;>
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (le_trans (by gcongr) hπ) (by gcongr)

end IntervalDyadicReal

end Inclusion
