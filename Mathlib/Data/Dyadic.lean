/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

set_option doc.verso true
set_option doc.verso.suggestions false

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

/-- One unit on the dyadic grid with precision `prec`. -/
def step (prec : Int) : Dyadic := .ofOdd 1 prec (by decide)

theorem ofIntWithPrec_one (prec : Int) : ofIntWithPrec 1 prec = step prec := by
  simp [step, ofIntWithPrec, Int.trailingZeros_eq_zero_of_mod_eq (show 1 % 2 = 1 by decide)]

section Shift

variable (k e : ℤ) (hk : k % 2 = 1) (d x y : Dyadic) (a b : ℤ) (m n : ℕ)

@[simp] theorem zero_shiftLeft : (0 : Dyadic) <<< a = 0 := rfl

@[simp] theorem zero_shiftRight : (0 : Dyadic) >>> a = 0 := rfl

@[simp] theorem ofOdd_shiftLeft {k e : ℤ} {hk : k % 2 = 1} {a : ℤ} :
    ofOdd k e hk <<< a = ofOdd k (e - a) hk := rfl

@[simp] theorem ofOdd_shiftRight {k e : ℤ} {hk : k % 2 = 1} {a : ℤ} :
    ofOdd k e hk >>> a = ofOdd k (e + a) hk := rfl

@[simp, norm_cast]
theorem shiftLeft_natCast : d <<< (m : ℤ) = d <<< m := rfl

@[simp, norm_cast]
theorem shiftRight_natCast : d >>> (m : ℤ) = d >>> m := rfl

theorem shiftLeft_add : d <<< (a + b) = d <<< a <<< b := by
  induction d <;> simp [Int.sub_sub]

theorem shiftRight_add : d >>> (a + b) = d >>> a >>> b := by
  induction d <;> simp [Int.add_assoc]

@[simp] theorem shiftLeft_neg : d <<< (-a) = d >>> a := by
  induction d <;> simp

@[simp] theorem shiftRight_neg : d >>> (-a) = d <<< a := by
  induction d <;> simp [Int.sub_eq_add_neg]

theorem shiftLeft_shiftRight : d <<< a >>> b = d <<< (a - b) := by
  rw [Int.sub_eq_add_neg, shiftLeft_add, shiftLeft_neg]

theorem shiftRight_shiftLeft : d >>> a <<< b = d >>> (a - b) := by
  rw [Int.sub_eq_add_neg, shiftRight_add, shiftRight_neg]

theorem shiftLeft_shiftRight' : d <<< a >>> b = d >>> (b - a) := by
  rw [← Int.neg_sub, shiftRight_neg, shiftLeft_shiftRight]

theorem shiftRight_shiftLeft' : d >>> a <<< b = d <<< (b - a) := by
  rw [← Int.neg_sub, shiftLeft_neg, shiftRight_shiftLeft]

section toRat

@[simp]
theorem toRat_shiftLeft : (d <<< a).toRat = d.toRat * 2 ^ a := by
  rcases d with _ | ⟨d, k, hd⟩
  · simp
  · norm_num [toRat_ofOdd_eq_mul_two_pow, sub_eq_add_neg, zpow_add₀]
    ac_rfl

theorem toRat_shiftRight : (d >>> a).toRat = d.toRat * 2 ^ (-a) := by
  rw [← shiftLeft_neg, toRat_shiftLeft]

@[simp]
theorem toRat_shiftRight' : (d >>> a).toRat = d.toRat / 2 ^ a := by
  rw [toRat_shiftRight, zpow_neg, div_eq_mul_inv]

theorem toRat_shiftLeft_nat : (d <<< n).toRat = d.toRat * 2 ^ n :=
  toRat_shiftLeft d n

theorem toRat_shiftRight_nat : (d >>> n).toRat = d.toRat / 2 ^ n :=
  toRat_shiftRight' d n

end toRat

@[simp] theorem shiftLeft_inj : x <<< a = y <<< a ↔ x = y := by
  simp [← toRat_inj, zpow_ne_zero]

@[simp] theorem shiftRight_inj : x >>> a = y >>> a ↔ x = y := by
  simp [← toRat_inj, zpow_ne_zero]

@[simp] theorem shiftLeft_eq_zero : d <<< a = 0 ↔ d = 0 := by
  simpa using shiftLeft_inj d 0 a

@[simp] theorem shiftRight_eq_zero : d >>> a = 0 ↔ d = 0 := by
  simpa using shiftRight_inj d 0 a

@[simp] theorem neg_shiftLeft : (-d) <<< a = -(d <<< a) := by
  induction d <;> simp

@[simp] theorem neg_shiftRight : (-d) >>> a = -(d >>> a) := by
  induction d <;> simp

theorem add_shiftLeft : (x + y) <<< a = x <<< a + y <<< a := by
  simp [← toRat_inj, Rat.add_mul]

theorem add_shiftRight : (x + y) >>> a = x >>> a + y >>> a := by
  simp [← toRat_inj, add_div]

theorem sub_shiftLeft : (x - y) <<< a = x <<< a - y <<< a := by
  simp [sub_eq_add_neg, add_shiftLeft, neg_shiftLeft]

theorem sub_shiftRight : (x - y) >>> a = x >>> a - y >>> a := by
  simp [sub_eq_add_neg, add_shiftRight, neg_shiftRight]

end Shift

section Real

/-- Interpret a dyadic rational as a real number. -/
def toReal (d : Dyadic) : ℝ := d.toRat

@[simp]
lemma toReal_natCast (n : ℕ) : toReal (n : Dyadic) = (n : ℝ) := by simp [toReal]

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
