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
chosen so that `|x / m| < 1 / 32`, so that the Taylor series converges faster.

This file is opt-in so that `dyadic_interval` doesn't import unnecessary theories.

## TODO

For larger exponents, we would eventually want to implement another optimisation that shifts the
`exp` exponent by multiples of `log 2` (which only shifts the exponent of the dyadic result).
This is deferred since it requires a certified computation of `log 2` to arbitrary precision, which
is a separate from the main instance.
-/

public section

open Finset

namespace Inclusion

namespace IntervalDyadicReal

/-- The numerator of the partial Taylor sum `∑ m ∈ range n, (a / b) ^ m / m!` as an unreduced
fraction over the common denominator `b ^ n * n!`. -/
@[expose]
def expPartialSumNum (a : ℤ) (b n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | n + 1 => (expPartialSumNum a b n + a ^ n) * (b * (n + 1) : ℕ)

theorem expPartialSumNum_div (a : ℤ) {b : ℕ} (hb : b ≠ 0) (n : ℕ) :
    (expPartialSumNum a b n : ℝ) / (b ^ n * n.factorial) =
      ∑ m ∈ range n, ((a : ℝ) / b) ^ m / m.factorial := by
  induction n with
  | zero => simp [expPartialSumNum]
  | succ n ih =>
    rw [sum_range_succ, ← ih, expPartialSumNum, Nat.factorial_succ]
    push_cast [div_pow]
    field_simp
    ring

-- TODO: move this to Rational.lean once there's a second user.
/-- The interval `[(c - r) / d, (c + r) / d]`, rounded outward to precision `prec`. -/
@[expose]
def ratBall (c r : ℤ) (d prec : ℕ) : Interval Dyadic :=
  Interval.Icc (rat (mkRat (c - r) d) prec).lb (rat (mkRat (c + r) d) prec).ub

theorem ratBall_mem {x : ℝ} {c r : ℤ} {d : ℕ} (hx : |x - c / d| ≤ r / d) (prec : ℕ) :
    x ∈ ratBall c r d prec := by
  obtain ⟨h₁, h₂⟩ := abs_sub_le_iff.mp hx
  refine mem_iff_mem_map.mpr
    (Interval.mem_Icc_of_le (ratCast_mem _ prec) ?_ ?_ (ratCast_mem _ prec))
  · push_cast [Rat.mkRat_eq_div, sub_div]
    exact sub_le_comm.mp h₂
  · push_cast [Rat.mkRat_eq_div, add_div]
    exact sub_le_iff_le_add'.mp h₁

/-- An enclosure of `exp (a / b)` by the first `n` terms of its Taylor series and the remainder
bound of `Real.exp_bound`, rounded outward to precision `prec`. This is only intended for use
when `| a / b | ≤ 1`. -/
@[expose]
def expRatTaylor (a : ℤ) (b n prec : ℕ) : Interval Dyadic :=
  ratBall (n * expPartialSumNum a b n) ((n + 1) * |a ^ n|) (n * (b ^ n * n.factorial)) prec

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

-- TODO: refactor this to a general util file once there's a second user.
/-- Round the endpoints of `I` outward to precision `prec`. This allows downstream intervals to
not carry an unnecessary number of bits (e.g. due to taking a large power in the case of `exp`). -/
@[expose]
def roundOut (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  ⟨I.lb.map (fun l ↦ Dyadic.roundDown l prec), I.ub.map (fun u ↦ Dyadic.roundUp u prec)⟩

theorem roundOut_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    x ∈ roundOut I prec := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx ⊢
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := WithBot.map_eq_some_iff.mp hc
    exact (Dyadic.toReal_le_toReal.mpr Dyadic.roundDown_le).trans (hx.1 l hl)
  · obtain ⟨u, hu, rfl⟩ := WithTop.map_eq_some_iff.mp hc
    exact (hx.2 u hu).trans (Dyadic.toReal_le_toReal.mpr Dyadic.le_roundUp)

/-- An enclosure of `exp x` by rewriting as `exp (x / m) ^ m` so that `|x / m| < 1 / 32` to make
the Taylor series converge quickly. The interval is rounded outward after the power to drop the
redundant bits for the consumers.

Some relevant precision constants are chosen as follows:
- `m = 16 (⌊2 |x|⌋ + 1)` to shrink the exponent below `1/32`.
- `precTaylor` is the precision of `exp (x / m)` requested. The power turns an absolute error `δ` on
  `exp (x / m)` into about `m * exp x * δ` on `exp x`, since its derivative is
  `m * exp (x / m) ^ (m - 1)`. So `precTaylor` adds three amounts to `prec`.
  + `powerBits` is at least `⌈ log₂ m ⌉`.
  + `sizeBits = ⌊ 1.5x ⌋ + 1` (`1.5 > log₂ e`) which bounds the number of bits above 1 for `exp x`.
  + a constant (`8` here) so that the powered interval is narrower than the requested
  precision, to make it more likely that the resulting interval has width `2^{-prec}`.
- `taylorTerms` terms bring the Taylor remainder below `2 ^{-precTaylor}`. Each term shrinks the
  remainder by at least 5 bits due to the `1/32` bound on the exponent, with further shrinking
  from the factorial. It's sufficient for the number of terms `n` to satisfy
  `5n + log₂ (n!) ≥ precTaylor + 1`, and we take a very crude bound here using `log₂(n!) ≥ n - 1`.
-/
@[expose]
def expPoint (x : Dyadic) (prec : ℕ) : Interval Dyadic :=
  let r := x.toRat
  let m := 16 * (2 * r.num.natAbs / r.den + 1)
  let powerBits := Nat.log2 m + 1
  let sizeBits := 3 * r.num.toNat / (2 * r.den) + 1
  let precTaylor := prec + powerBits + sizeBits + 8
  let taylorTerms := (precTaylor + 2) / 6 + 1
  roundOut ((expRatTaylor r.num (r.den * m) taylorTerms precTaylor).pow m) prec

theorem expPoint_mem (x : Dyadic) (prec : ℕ) : Real.exp x.toReal ∈ expPoint x prec := by
  have hb : x.toRat.den ≠ 0 := x.toRat.den_nz
  unfold expPoint
  dsimp only
  generalize hm : 16 * (2 * x.toRat.num.natAbs / x.toRat.den + 1) = m
  have hm0 : m ≠ 0 := by lia
  have hred : Real.exp x.toReal =
      Real.exp ((x.toRat.num : ℝ) / ((x.toRat.den * m : ℕ) : ℝ)) ^ m := by
    rw [← Real.exp_nat_mul, Dyadic.toReal, Rat.cast_def]
    push_cast
    field_simp
  have hab : x.toRat.num.natAbs ≤ x.toRat.den * m := by
    have := Nat.lt_mul_div_succ (2 * x.toRat.num.natAbs) (Nat.pos_of_ne_zero hb)
    rw [← hm]
    lia
  rw [hred]
  refine roundOut_mem (pow_mem m ?_) prec
  exact expRatTaylor_mem x.toRat.num (Nat.mul_ne_zero hb hm0) hab (by lia) _

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
