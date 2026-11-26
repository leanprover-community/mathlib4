/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Exponential enclosures for interval_dyadic_real

This file defines an inclusion operation for the `interval_dyadic_real` inclusion family that
encloses `Real.exp` of an interval.

## Implementation notes

The `exp` of the endpoints is constructed by evaluating the Taylor partial sum up to the required
precision level. The exponent is rewritten as `exp x = exp (x / m) ^ m`, where `m` is an integer
chosen so that `|x / m| < 1 / 2`. The exponent is divided further by `2 ^ k` (with `k` growing as
`√prec`) so that the Taylor series converges faster, and `k` squarings with outward rounding undo
that division.

This file is opt-in so that `dyadic_interval` doesn't import unnecessary theories.

## TODO

For larger exponents, we would eventually want to implement another optimisation that shifts the
`exp` exponent by multiples of `log 2` (which only shifts the exponent of the dyadic result).
This requires a certified computation of `log 2` to arbitrary precision, which is available as
`Inclusion.IntervalDyadicReal.logTwo` (with bounds `Inclusion.IntervalDyadicReal.logTwo_spec`).
-/

public section

open Finset

open scoped Nat

namespace Inclusion

namespace IntervalDyadicReal
open Inclusion.IntervalDyadicReal

/-- The numerator of the partial Taylor sum `∑ m ∈ range n, (a / b) ^ m / m!` as an unreduced
fraction over the common denominator `b ^ n * n!`. -/
@[expose]
def expPartialSumNum (a : ℤ) (b n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | n + 1 => (expPartialSumNum a b n + a ^ n) * (b * (n + 1) : ℕ)

theorem expPartialSumNum_div (a : ℤ) {b : ℕ} (hb : b ≠ 0) (n : ℕ) :
    (expPartialSumNum a b n : ℝ) / (b ^ n * n !) =
      ∑ m ∈ range n, ((a : ℝ) / b) ^ m / m ! := by
  induction n with
  | zero => simp [expPartialSumNum]
  | succ n ih =>
    rw [sum_range_succ, ← ih, expPartialSumNum, Nat.factorial_succ]
    push_cast [div_pow]
    field_simp
    ring

/-- An enclosure of `exp (a / b)` by the first `n` terms of its Taylor series and the remainder
bound of `Real.exp_bound`, rounded outward to precision `prec`. This is only intended for use
when `| a / b | ≤ 1`. -/
@[expose]
def expRatTaylor (a : ℤ) (b n prec : ℕ) : Interval Dyadic :=
  ratBall (n * expPartialSumNum a b n) ((n + 1) * |a ^ n|) (n * (b ^ n * n !)) prec

theorem expRatTaylor_mem (a : ℤ) {b : ℕ} (hb : b ≠ 0) (hab : a.natAbs ≤ b) {n : ℕ} (hn : 0 < n)
    (prec : ℕ) : Real.exp (a / b) ∈ expRatTaylor a b n prec := by
  have hy : |(a : ℝ) / b| ≤ 1 := by
    rw [abs_div, Nat.abs_cast, div_le_one (by positivity), ← Int.cast_abs, ← Int.natCast_natAbs]
    norm_cast
  refine ratBall_mem ?_ prec
  push_cast
  rw [mul_div_mul_left _ _ (by positivity), expPartialSumNum_div a hb n]
  refine (Real.exp_bound hy hn).trans_eq ?_
  rw [abs_div, Nat.abs_cast, abs_pow, div_pow]
  push_cast
  field_simp

/-- Square `I` `k` times, rounding outward to the `2 ^ (-prec)` grid after each squaring.
Compared with the exact `I.pow (2 ^ k)`, the roundings add an error of less than about
`2 ^ (k + 1) * max 1 M ^ (2 ^ k - 1)` steps of `2 ^ (-prec)`, where `M` is the largest absolute
value in `I`. So the error stays below `2 ^ (-q)` when `prec` is at least about
`q + k + 1 + (2 ^ k - 1) * log₂ (max 1 M)`.
The roundings keep the endpoints on the `2 ^ (-prec)` grid, where `I.pow (2 ^ k)` would have
endpoints with `2 ^ k` times as many bits. -/
@[expose]
def squareRoundOut (k : ℕ) (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match k with
  | 0 => I
  | k + 1 => squareRoundOut k (roundOut (I.pow 2) prec) prec

theorem squareRoundOut_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (k prec : ℕ) :
    x ^ 2 ^ k ∈ squareRoundOut k I prec := by
  induction k generalizing x I with
  | zero => simpa [squareRoundOut] using hx
  | succ k ih =>
    rw [squareRoundOut, pow_succ', pow_mul]
    exact ih (roundOut_mem (pow_mem 2 hx) prec)

/-- An enclosure of `exp x` by rewriting as `(exp (x / N) ^ 2 ^ k) ^ m`, where `N = m * 2 ^ k`, so
that `|x / N| < 2 ^ (-1 - k)` to make the Taylor series converge quickly. The interval is rounded
outward after the power to drop the redundant bits for the consumers.

Some relevant precision constants are chosen as follows:
- `m = ⌊2 |x|⌋ + 1` to shrink the exponent below `1/2`.
- `k`, the number of squarings, is an argument with default `⌊√prec⌋`, which balances the cost of
  the squarings against that of the Taylor terms. `powerBits` and `taylorTerms` below are computed
  from `k`, so every `k` gives the same precision and only the cost changes. With `k = 0`, about
  `prec / 2` terms are needed, and at `4500` bits their recursion exceeds the kernel's default
  `maxRecDepth`.
- `precTaylor` is the precision of `exp (x / N)` requested. The powers turn an absolute error `δ` on
  `exp (x / N)` into about `N * exp x * δ` on `exp x` (the derivative of the `N`-th power is
  `N * exp (x / N) ^ (N - 1)`). So `precTaylor` adds three amounts to `prec`.
  + `powerBits` is at least `⌈ log₂ N ⌉`.
  + `sizeBits = ⌊ 1.5x ⌋ + 1` (`1.5 > log₂ e`) which bounds the number of bits above 1 for `exp x`.
  + a constant (`8` here) so that the powered interval is narrower than `2 ^ (-prec - 1)`.
  Rounding it outward to the `2 ^ (-prec - 1)` grid then spans at most two grid steps, so the
  result has width at most `2 ^ (-prec)`. It also absorbs the roundings in `squareRoundOut`, which
  add less than four steps of `2 ^ (-precTaylor)` before the amplification.
- `taylorTerms` terms bring the Taylor remainder below `2 ^{-precTaylor}`. Each term shrinks the
  remainder by at least `1 + k` bits due to the `2 ^ (-1 - k)` bound on the exponent, with further
  shrinking from the factorial. It's sufficient for the number of terms `n` to satisfy
  `(1 + k) n + log₂ (n!) ≥ precTaylor + 1`, and we take a very crude bound here using
  `log₂(n!) ≥ n - 1`.
-/
@[expose]
def expPoint (x : Dyadic) (prec : ℕ) (k : ℕ := Nat.sqrt prec) : Interval Dyadic :=
  let r := x.toRat
  let m := 2 * r.num.natAbs / r.den + 1
  let powerBits := Nat.log2 m + 1 + k
  let sizeBits := 3 * r.num.toNat / (2 * r.den) + 1
  let precTaylor := prec + powerBits + sizeBits + 8
  let taylorTerms := (precTaylor + 2) / (k + 2) + 1
  let taylor := expRatTaylor r.num (r.den * m * 2 ^ k) taylorTerms precTaylor
  roundOut ((squareRoundOut k taylor precTaylor).pow m) (prec + 1)

theorem expPoint_mem (x : Dyadic) (prec : ℕ) {k : ℕ} :
    Real.exp x.toReal ∈ expPoint x prec k := by
  have hb : x.toRat.den ≠ 0 := x.toRat.den_nz
  dsimp only [expPoint]
  generalize hm : 2 * x.toRat.num.natAbs / x.toRat.den + 1 = m
  have hm0 : m ≠ 0 := by lia
  have hred : Real.exp x.toReal =
      (Real.exp (x.toRat.num / (x.toRat.den * m * 2 ^ k : ℕ)) ^ 2 ^ k) ^ m := by
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul, Dyadic.toReal, Rat.cast_def]
    push_cast
    field_simp
  have hab : x.toRat.num.natAbs ≤ x.toRat.den * m := by
    have := Nat.lt_mul_div_succ (2 * x.toRat.num.natAbs) (Nat.pos_of_ne_zero hb)
    rw [← hm]
    lia
  rw [hred]
  refine roundOut_mem (pow_mem m (squareRoundOut_mem ?_ k _)) (prec + 1)
  refine expRatTaylor_mem x.toRat.num (by positivity) (hab.trans ?_) (by lia) _
  exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)

/-- The exponential of an interval, from the enclosures `expPoint` at its endpoints. -/
@[expose]
def exp (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic where
  lb := match I.lb with
    | some l => (expPoint l prec).lb
    | ⊥ => 0
  ub := match I.ub with
    | some u => (expPoint u prec).ub
    | ⊤ => ⊤

@[inclusion_op interval_dyadic_real]
theorem exp_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.exp x ∈ exp I prec := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
  have h0 : Dyadic.toReal 0 ≤ Real.exp x := by simpa [Dyadic.toReal] using (Real.exp_pos x).le
  have h0I := Interval.mem_map_singleton (0 : Dyadic) Dyadic.toReal
  rw [mem_iff_mem_map]
  rcases I with ⟨_ | l, _ | u⟩ <;> simp only [exp]
  · exact Interval.mem_Ici_of_le h0 h0I
  · exact Interval.mem_Icc_of_le h0I h0 (Real.exp_le_exp.mpr (hx.2 u rfl)) (expPoint_mem u prec)
  · exact Interval.mem_Ici_of_le (Real.exp_le_exp.mpr (hx.1 l rfl)) (expPoint_mem l prec)
  · exact Interval.mem_Icc_of_le (expPoint_mem l prec) (Real.exp_le_exp.mpr (hx.1 l rfl))
      (Real.exp_le_exp.mpr (hx.2 u rfl)) (expPoint_mem u prec)

end IntervalDyadicReal

end Inclusion
