/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Dyadic.Basic
public import Mathlib.Data.Rat.Cast.Order

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Dyadic rationals

This file provides general API for Dyadic rationals that are used in Mathlib but not available in
core.
-/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

open Dyadic
namespace Dyadic

@[simp]
theorem ofOdd_pos {n k : ℤ} {hn : n % 2 = 1} : 0 < ofOdd n k hn ↔ 0 < n := by
  simp [← toRat_lt_toRat_iff, toRat_ofOdd_eq_mul_two_pow, zpow_pos]

@[simp]
theorem ofOdd_nonneg {n k : ℤ} {hn : n % 2 = 1} : 0 ≤ ofOdd n k hn ↔ 0 ≤ n := by
  simp [← toRat_le_toRat_iff, toRat_ofOdd_eq_mul_two_pow, zpow_pos]

@[simp]
theorem toRat_pos (x : Dyadic) : 0 < x.toRat ↔ 0 < x := by
  rw [← toRat_zero, toRat_lt_toRat_iff]

@[simp]
theorem toRat_nonneg (x : Dyadic) : 0 ≤ x.toRat ↔ 0 ≤ x := by
  rw [← toRat_zero, toRat_le_toRat_iff]

@[simp]
theorem toRat_abs (x : Dyadic) : |x|.toRat = |x.toRat| := by
  rcases abs_choice x with h | h
  · grind [toRat_le_toRat_iff.mpr <| sup_eq_left.mp h, toRat_neg x]
  · grind [toRat_le_toRat_iff.mpr <| sup_eq_right.mp h, toRat_neg x]

/-- One unit on the dyadic grid with precision `prec`. -/
def step (prec : Int) : Dyadic := .ofOdd 1 prec (by decide)

theorem ofIntWithPrec_one (prec : Int) : ofIntWithPrec 1 prec = step prec := by
  simp [step, ofIntWithPrec, Int.trailingZeros_eq_zero_of_mod_eq (show 1 % 2 = 1 by decide)]

@[simp]
theorem step_pos (prec : ℤ) : 0 < step prec := ofOdd_pos.mpr zero_lt_one

@[simp]
theorem step_nonneg (prec : ℤ) : 0 ≤ step prec := ofOdd_nonneg.mpr zero_le_one

theorem toRat_step (prec : ℤ) : (step prec).toRat = (1 / 2) ^ prec := by
  simp [← ofIntWithPrec_one, toRat_ofIntWithPrec_eq_mul_two_pow]

theorem toRat_step_real (prec : ℤ) : (step prec).toRat = (1 / 2 : ℝ) ^ prec := by
  simp [toRat_step]

theorem toRat_step_add_one (prec : ℤ) : (step (prec + 1)).toRat = (step prec).toRat / 2 := by
  norm_num [toRat_step, zpow_add_one₀, div_eq_mul_inv]

theorem step_eq_add (prec : ℤ) : step prec = step (prec + 1) + step (prec + 1) := by
  norm_num [← toRat_inj, toRat_step_add_one]

theorem abs_toRat_toDyadic_le {x : ℚ} {prec : ℤ} :
    |x - (x.toDyadic prec).toRat| ≤ (step prec).toRat := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · grw [neg_le_sub_iff_le_add, Rat.toRat_toDyadic_le, le_add_iff_nonneg_right]
    simp
  · rw [tsub_le_iff_right, Rat.add_comm, ← toRat_add, ← ofIntWithPrec_one]
    exact Rat.lt_toRat_toDyadic_add.le

theorem abs_toRat_toDyadic_le_real {x : ℚ} {prec : ℤ} :
    |(x - (x.toDyadic prec).toRat : ℝ)| ≤ (step prec).toRat :=
  mod_cast abs_toRat_toDyadic_le

section Real

/-- Interpret a dyadic rational as a real number. -/
def toReal (d : Dyadic) : ℝ := d.toRat

@[simp]
lemma toReal_natCast (n : ℕ) : toReal (n : Dyadic) = (n : ℝ) := by simp [toReal]

@[simp]
lemma toReal_zero : toReal 0 = 0 := by
  simp [toReal]

@[simp]
lemma toReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    toReal (ofNat(n) : Dyadic) = (ofNat(n) : ℝ) := by
  rw [← Nat.cast_ofNat (R := Dyadic), ← Nat.cast_ofNat (R := ℝ)]
  exact toReal_natCast n

@[simp]
lemma toReal_intCast (z : ℤ) : toReal (z : Dyadic) = (z : ℝ) := by simp [toReal]

@[simp]
lemma toReal_add (a b : Dyadic) : toReal (a + b) = toReal a + toReal b := by simp [toReal]

@[simp]
lemma toReal_mul (a b : Dyadic) : toReal (a * b) = toReal a * toReal b := by simp [toReal]

@[simp]
lemma toReal_pow (a : Dyadic) (n : ℕ) : toReal (a ^ n) = toReal a ^ n := by
  simpa [toReal] using map_pow (Rat.castHom ℝ) a.toRat n

/-- `Dyadic.toReal` as an additive monoid homomorphism. -/
def toRealAddMonoidHom : Dyadic →+ ℝ where
  toFun := toReal
  map_zero' := by simp [toReal]
  map_add' := toReal_add

@[simp]
lemma toReal_le_toReal {a b : Dyadic} : toReal a ≤ toReal b ↔ a ≤ b := by simp [toReal]

@[simp]
lemma toReal_lt_toReal {a b : Dyadic} : toReal a < toReal b ↔ a < b := by simp [toReal]

/-- `Dyadic.toReal` as an order embedding. -/
def toRealOrderEmbedding : Dyadic ↪o ℝ :=
  OrderEmbedding.ofStrictMono toReal fun _ _ h ↦ toReal_lt_toReal.mpr h

end Real

end Dyadic

end Inclusion.IntervalDyadicReal
