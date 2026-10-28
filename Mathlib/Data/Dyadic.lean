/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

/-!
# Dyadic rationals

This file provides general API for Dyadic rationals that are used in Mathlib but not available in
core.
-/

@[expose] public section

instance : LinearOrder Dyadic where
  le_refl := Std.IsPreorder.le_refl
  le_trans := Std.IsPreorder.le_trans
  le_antisymm := Std.IsPartialOrder.le_antisymm
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  le_total := Std.IsLinearOrder.le_total
  toDecidableLE := Dyadic.instDecidableLE

instance : AddCommGroup Dyadic where
  nsmul := (· * ·)
  zsmul := (· * ·)
  add_zero := Dyadic.add_zero
  zero_add := Dyadic.zero_add
  add_assoc := Dyadic.add_assoc
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel := Dyadic.neg_add_cancel
  add_comm := Dyadic.add_comm
  nsmul_zero := by grind
  nsmul_succ := by grind
  zsmul_zero' := by grind
  zsmul_succ' := by grind
  zsmul_neg' := by grind

namespace Dyadic

@[simp]
lemma ofOdd_pos {n k : ℤ} {hn : n % 2 = 1} : 0 < ofOdd n k hn ↔ 0 < n := by
  simp [← toRat_lt_toRat_iff, toRat_ofOdd_eq_mul_two_pow, zpow_pos]

@[simp]
lemma toRat_one : toRat 1 = 1 := rfl

@[simp]
lemma toRat_ofNat {n : ℕ} : toRat ofNat(n) = ofNat(n) := toRat_natCast n

@[simp]
lemma toRat_pos (x : Dyadic) : 0 < x.toRat ↔ 0 < x := by
  rw [← toRat_zero, toRat_lt_toRat_iff]

@[simp]
lemma toRat_abs (x : Dyadic) : |x|.toRat = |x.toRat| := by
  rcases abs_choice x with h | h
  · grind [toRat_le_toRat_iff.mpr <| sup_eq_left.mp h, toRat_neg x]
  · grind [toRat_le_toRat_iff.mpr <| sup_eq_right.mp h, toRat_neg x]

/-- One unit on the dyadic grid with precision `prec`. -/
def step (prec : Int) : Dyadic := .ofOdd 1 prec (by decide)

theorem ofIntWithPrec_one (prec : Int) : ofIntWithPrec 1 prec = step prec := by
  simp [step, ofIntWithPrec, Int.trailingZeros_eq_zero_of_mod_eq (show 1 % 2 = 1 by decide)]

lemma step_pos (prec : ℤ) : 0 < step prec := ofOdd_pos.mpr zero_lt_one

lemma step_eq_add (prec : ℤ) : step prec = step (prec + 1) + step (prec + 1) := by
  norm_num [← toRat_inj, toRat_ofOdd_eq_mul_two_pow, zpow_add₀, ← _root_.add_mul, ← one_div, step]

lemma toRat_step (prec : ℤ) : (step prec).toRat = (1 / 2) ^ prec := by
  simp [← ofIntWithPrec_one, toRat_ofIntWithPrec_eq_mul_two_pow]

lemma toRat_step_real (prec : ℤ) : (step prec).toRat = (1 / 2 : ℝ) ^ prec := by
  simp [toRat_step]

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
