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

/-- Computes a lower bound for `√x` with precision `prec`, given a lower bound `lb` for `x`. -/
@[expose]
def lowerSqrt (lb : Dyadic) (prec : ℕ) : Dyadic :=
  Dyadic.ofIntWithPrec ⌊(lb <<< (2 * prec)).toRat⌋₊.sqrt prec

/-- Computes an upper bound for `√x` with precision `prec`, given an upper bound `ub` for `x`. -/
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

theorem lowerSqrt_le {lb : Dyadic} {prec : ℕ} {x : ℝ} (hx : Dyadic.toReal lb ≤ x) :
    Dyadic.toReal (lowerSqrt lb prec) ≤ √x := by
  rcases le_or_gt 0 lb.toRat with hlb | hlb
  · apply Real.le_sqrt_of_sq_le
    have h : ⌊(lb <<< (2 * prec)).toRat⌋₊.sqrt ^ 2 ≤ (lb <<< (2 * prec)).toRat := by
      grw [← Nat.cast_pow, Nat.sqrt_le', Nat.floor_le (by rw [toRat_shiftLeft_nat]; positivity)]
    grw [← hx]
    simp only [lowerSqrt, Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
      ← Rat.cast_pow, Rat.cast_le]
    generalize ⌊(lb <<< (2 * prec)).toRat⌋₊.sqrt = m at h ⊢
    rw [toRat_shiftLeft_nat, mul_comm 2, mul_comm] at h
    simpa [mul_pow, ← pow_mul, field] using h
  · have : (lb <<< (2 * prec)).toRat < 0 := by
      rw [toRat_shiftLeft_nat]
      exact mul_neg_of_neg_of_pos hlb (by positivity)
    simp [lowerSqrt, Nat.floor_eq_zero.mpr <| zero_lt_one.trans' this, Dyadic.toReal]

theorem le_upperSqrt {ub : Dyadic} {prec : ℕ} {x : ℝ} (hx : x ≤ Dyadic.toReal ub) :
    √x ≤ Dyadic.toReal (upperSqrt ub prec) := by
  set n := ⌈(ub <<< (2 * prec)).toRat⌉₊
  suffices H : ∀ m : ℕ, n ≤ m ^ 2 → √x ≤ Dyadic.toReal (Dyadic.ofIntWithPrec m prec) by
    dsimp only [upperSqrt]
    split_ifs with h
    exacts [H _ h, H _ n.lt_succ_sqrt'.le]
  intro m hm
  replace hm : _ ≤ (m : ℚ) ^ 2 := (Nat.le_ceil _).trans (mod_cast hm)
  rw [Real.sqrt_le_left (by simp [toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow])]
  grw [hx]
  simp only [Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, ← Rat.cast_pow, Rat.cast_le]
  simpa [← pow_mul, field, toRat_shiftLeft_nat, mul_comm 2] using hm

@[inclusion_op interval_dyadic_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : √x ∈ sqrt I prec := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx
  rw [mem_iff_mem_map]
  rcases I with ⟨_ | lb, _ | ub⟩ <;> simp only [sqrt]
  · simp [Interval.map]
  · simpa [Interval.map] using le_upperSqrt (hx.right ub rfl)
  · simpa [Interval.map] using lowerSqrt_le (hx.left lb rfl)
  · simpa [Interval.map] using ⟨lowerSqrt_le (hx.left lb rfl), le_upperSqrt (hx.right ub rfl)⟩

end IntervalDyadicReal

end Inclusion
