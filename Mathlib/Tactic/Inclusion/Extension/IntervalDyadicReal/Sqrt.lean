/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Sqrt extension for tactic `dyadic_interval`

This file implements sqrt extension for the tactic `dyadic_interval` using `Nat.sqrt`
-/

public section

namespace Inclusion

namespace IntervalDyadicReal

open Inclusion.IntervalDyadicReal.Dyadic

/-- Computes an lower bound for `√x` with precision `prec`. -/
@[expose]
def lowerSqrt (lb : Dyadic) (prec : ℕ) : Dyadic :=
  Dyadic.ofIntWithPrec ⌊(lb <<< (2 * prec)).toRat⌋₊.sqrt prec

/-- Computes an upper bound for `√x` with precision `prec`. -/
@[expose]
def upperSqrt (ub : Dyadic) (prec : ℕ) : Dyadic :=
  let ub' : ℕ := ⌈(ub <<< (2 * prec)).toRat⌉₊
  let ubsqrt : ℕ := ub'.sqrt
  if ub' ≤ ubsqrt ^ 2 then Dyadic.ofIntWithPrec ubsqrt prec
  else Dyadic.ofIntWithPrec (ubsqrt + 1) prec

/-- Square root of an `Interval Dyadic`. -/
@[expose]
def sqrt (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic where
  lb := match I.lb with
    | ⊥ => 0
    | WithBot.some lb => lowerSqrt lb prec
  ub := match I.ub with
    | ⊤ => ⊤
    | WithTop.some ub => upperSqrt ub prec

private theorem toRat_shiftLeft_two_mul (d : Dyadic) (n : ℕ) :
    (d <<< (2 * n)).toRat = d.toRat * 4 ^ n := by
  norm_num [Dyadic.toRat_shiftLeft_nat, pow_mul]

theorem lowerSqrt_le {lb : Dyadic} {prec : ℕ} {x : ℝ} (hx : Dyadic.toReal lb ≤ x) :
    Dyadic.toReal (lowerSqrt lb prec) ≤ √x := by
  unfold lowerSqrt
  unfold Dyadic.toReal at *
  by_cases hlb : 0 ≤ lb
  · apply Real.le_sqrt_of_sq_le
    norm_num [Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, ← pow_mul, mul_comm, field]
    grw [Dyadic.toRat_shiftLeft_nat, sq, ← Nat.cast_mul, ⌊lb.toRat * 2 ^ (prec * 2)⌋₊.sqrt_le,
      ← Rat.cast_natCast, Nat.floor_le (by simp; simpa [← Dyadic.toRat_zero])]
    simpa using hx
  · have : (lb <<< (2 * prec)).toRat < 0 := by
      rw [toRat_shiftLeft_nat]
      exact mul_neg_of_neg_of_pos (by simp [← Dyadic.toRat_zero]; simpa using hlb) (by simp)
    simp [Nat.floor_eq_zero.mpr <| zero_lt_one.trans' this]

theorem le_upperSqrt {ub : Dyadic} {prec : ℕ} {x : ℝ} (hx : x ≤ Dyadic.toReal ub) :
    √x ≤ Dyadic.toReal (upperSqrt ub prec) := by
  unfold upperSqrt
  set ub' : ℕ := ⌈(ub <<< (2 * prec)).toRat⌉₊
  have H {n : ℕ} (hn : ub' ≤ n ^ 2) :
      √x ≤ Dyadic.toReal (Dyadic.ofIntWithPrec n prec) := by
    replace hn : _ ≤ (n : ℚ) ^ 2 := Nat.le_ceil (ub <<< (2 * prec)).toRat |>.trans (mod_cast hn)
    rw [toRat_shiftLeft_nat, mul_comm 2] at hn
    apply Real.sqrt_le_iff.mpr ⟨by simp [toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow], ?_⟩
    grw [hx, toReal, toReal, ← Rat.cast_pow, Rat.cast_le, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
    simpa [mul_pow, ← pow_mul, field] using hn
  by_cases hub' : ub' ≤ ub'.sqrt ^ 2 <;> simp only [hub', ↓reduceIte]
  · exact H hub'
  · exact H ub'.lt_succ_sqrt'.le

@[inclusion_op interval_dyadic_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : √x ∈ sqrt I prec := by
  have hx₀ : Dyadic.toReal 0 ≤ √x := by simp [Dyadic.toReal]
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
  rw [mem_iff_mem_map]
  rcases I with ⟨_ | lb, _ | ub⟩ <;> simp only [sqrt]
  · simpa [Interval.map] using hx₀
  · simpa [Interval.map] using ⟨hx₀, le_upperSqrt (hx.right ub rfl)⟩
  · simpa [Interval.map] using lowerSqrt_le (hx.left lb rfl)
  · simpa [Interval.map] using ⟨lowerSqrt_le (hx.left lb rfl), le_upperSqrt (hx.right ub rfl)⟩

end IntervalDyadicReal

end Inclusion
