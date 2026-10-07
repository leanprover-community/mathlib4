/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Sqrt

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

public section

namespace Dyadic

variable {z a b prec : ℤ}

theorem ofIntWithPrec_pow {n : ℕ} :
    ofIntWithPrec z prec ^ n = ofIntWithPrec (z ^ n) (prec * n) := by
  rw [← toRat_inj]
  rw [toRat_ofIntWithPrec_eq_mul_two_pow, toRat_pow, toRat_ofIntWithPrec_eq_mul_two_pow]
  rw [mul_pow, Int.cast_pow, ← _root_.neg_mul, zpow_mul, zpow_natCast]

@[simp]
theorem ofIntWithPrec_le_iff :
    ofIntWithPrec a prec ≤ ofIntWithPrec b prec ↔ a ≤ b := by
  change ble (ofIntWithPrec a prec) (ofIntWithPrec b prec) ↔ a ≤ b
  rw [ble_iff_toRat, toRat_ofIntWithPrec_eq_mul_two_pow, toRat_ofIntWithPrec_eq_mul_two_pow]
  rw [zpow_neg, ← div_eq_mul_inv, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ (zpow_pos (by decide) prec) (zpow_pos (by decide) prec)]
  rw [mul_le_mul_iff_left₀ (zpow_pos (by decide) prec), Int.cast_le]

@[simp]
theorem ofIntWithPrec_lt_iff :
    ofIntWithPrec a prec < ofIntWithPrec b prec ↔ a < b := by
  change blt (ofIntWithPrec a prec) (ofIntWithPrec b prec) ↔ a < b
  rw [blt_iff_toRat, toRat_ofIntWithPrec_eq_mul_two_pow, toRat_ofIntWithPrec_eq_mul_two_pow]
  rw [zpow_neg, ← div_eq_mul_inv, ← div_eq_mul_inv]
  rw [div_lt_div_iff₀ (zpow_pos (by decide) prec) (zpow_pos (by decide) prec)]
  rw [mul_lt_mul_iff_left₀ (zpow_pos (by decide) prec), Int.cast_lt]

@[simp]
theorem ofIntWithPrec_nonneg_iff : 0 ≤ ofIntWithPrec z prec ↔ 0 ≤ z := by
  rw [← ofIntWithPrec_zero (i := prec), ofIntWithPrec_le_iff]

@[simp]
theorem ofIntWithPrec_pos_iff : 0 < ofIntWithPrec z prec ↔ 0 < z := by
  rw [← ofIntWithPrec_zero (i := prec), ofIntWithPrec_lt_iff]

@[simp]
theorem ofIntWithPrec_nonpos_iff : ofIntWithPrec z prec ≤ 0 ↔ z ≤ 0 := by
  rw [← ofIntWithPrec_zero (i := prec), ofIntWithPrec_le_iff]

@[simp]
theorem ofIntWithPrec_neg_iff : ofIntWithPrec z prec < 0 ↔ z < 0 := by
  rw [← ofIntWithPrec_zero (i := prec), ofIntWithPrec_lt_iff]

end Dyadic

namespace Inclusion

def natSqrt (fuel geuss n : ℕ) : ℕ := match fuel, geuss, n with
  | 0, _, geuss => geuss
  | fuel + 1, n, geuss =>
    let next : ℕ := (geuss + n / geuss) / 2
    if next < geuss then natSqrt fuel n next else geuss

def Interval.sqrt (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic where
  lb := match I.lb with
    | ⊥ => WithBot.some 0
    | WithBot.some q =>
      if 0 ≤ q.toRat then
        let lbsq : ℕ := ⌊q.toRat * 4 ^ prec⌋.toNat
        let lb : ℕ := natSqrt 8192 lbsq lbsq
        if lb ^ 2 ≤ lbsq then Dyadic.ofIntWithPrec lb prec else WithBot.some 0
      else WithBot.some 0
  ub := match I.ub with
    | ⊤ => ⊤
    | WithTop.some q =>
      let ubsq : ℕ := ⌈q.toRat * 4 ^ prec⌉.toNat
      let ub : ℕ := natSqrt 8192 ubsq ubsq
      if ubsq ≤ ub ^ 2 then Dyadic.ofIntWithPrec ub prec
      else if ubsq ≤ (ub + 1) ^ 2 then Dyadic.ofIntWithPrec (ub + 1) prec
      else ⊤

theorem Interval.sqrt_mem
    (f : Dyadic ↪o ℝ) (map_zero : f 0 = 0) (map_sq : ∀ x, f (x ^ 2) = f x ^ 2)
    {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I.map f) (prec : ℕ) :
    √x ∈ (I.sqrt prec).map f := by
  rcases I with ⟨lb, ub⟩
  simp [map, Interval.sqrt, -Int.toNat_le]
  constructor
  · match lb with
    | ⊥ => simp [map_zero]
    | WithBot.some lb =>
      simp [-Int.toNat_le]
      split_ifs with hlb h
      · simp [-Int.toNat_le]
        refine Real.le_sqrt_of_sq_le ?_
        simp [map] at hx
        apply hx.left.trans'
        simp [← map_sq]
        rw [Dyadic.ofIntWithPrec_pow, ← Nat.cast_pow]
        apply Dyadic.ofIntWithPrec_le_iff.mpr (Nat.cast_le.mpr h) |>.trans
        rw [← Dyadic.toRat_le_toRat_iff, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
        simp
        rw [← div_eq_mul_inv, mul_comm _ 2, zpow_mul, zpow_natCast, show (2 : ℚ) ^ (2 : ℤ) = 4 by rfl]
        rw [div_le_iff₀ (pow_pos (by simp) _)]
        simpa [Int.floor_le]
      · simp [map_zero]
      · simp [map_zero]
  · match ub with
    | ⊤ => simp
    | WithTop.some ub =>
      simp [-Int.toNat_le]
      split_ifs with h1 h2
      · simp []
        refine Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
        · simp [← map_zero]
        simp [map] at hx
        apply hx.right.trans
        simp [← map_sq]
        rw [Dyadic.ofIntWithPrec_pow, ← Nat.cast_pow]
        apply Dyadic.ofIntWithPrec_le_iff.mpr (Nat.cast_le.mpr h1) |>.trans'
        rw [← Dyadic.toRat_le_toRat_iff, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
        simp
        have := Int.le_ceil (ub.toRat * 4 ^ prec)
        have := le_max_left (⌈ub.toRat * 4 ^ prec⌉ : ℚ) 0
        rw [← div_eq_mul_inv, mul_comm _ 2, zpow_mul, zpow_natCast, show (2 : ℚ) ^ (2 : ℤ) = 4 by rfl]
        rw [le_div_iff₀ (pow_pos (by simp) _)]
        grind
      · simp []
        refine Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
        · simp [← map_zero, add_nonneg]
        simp [map] at hx
        apply hx.right.trans
        simp [← map_sq]
        rw [Dyadic.ofIntWithPrec_pow, ← Nat.cast_add_one, ← Nat.cast_pow]
        apply Dyadic.ofIntWithPrec_le_iff.mpr (Nat.cast_le.mpr h2) |>.trans'
        rw [← Dyadic.toRat_le_toRat_iff, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
        simp
        have := Int.le_ceil (ub.toRat * 4 ^ prec)
        have := le_max_left (⌈ub.toRat * 4 ^ prec⌉ : ℚ) 0
        rw [← div_eq_mul_inv, mul_comm _ 2, zpow_mul, zpow_natCast, show (2 : ℚ) ^ (2 : ℤ) = 4 by rfl]
        rw [le_div_iff₀ (pow_pos (by simp) _)]
        grind
      · simp

@[inclusion_op interval_dyadic_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : √x ∈ I.sqrt prec :=
  Interval.sqrt_mem Dyadic.toRealOrderEmbedding (map_zero Dyadic.toRealAddMonoidHom)
    (Dyadic.toReal_pow (n := 2)) hx prec

end Inclusion
