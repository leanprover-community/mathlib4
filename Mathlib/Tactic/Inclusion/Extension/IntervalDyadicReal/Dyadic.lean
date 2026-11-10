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

namespace Inclusion.IntervalDyadicReal

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

-- TODO: remove this once #43038 lands.
instance : AddLeftMono Dyadic where
  elim a b c h := Dyadic.toRat_le_toRat_iff.mp <| by
    simpa [Dyadic.toRat_add] using add_le_add_right (Dyadic.toRat_le_toRat_iff.mpr h) c.toRat

open Dyadic
namespace Dyadic

@[simp]
theorem ofOdd_pos {n k : ℤ} {hn : n % 2 = 1} : 0 < ofOdd n k hn ↔ 0 < n := by
  simp [← toRat_lt_toRat_iff, toRat_ofOdd_eq_mul_two_pow, zpow_pos]

@[simp]
theorem ofOdd_nonneg {n k : ℤ} {hn : n % 2 = 1} : 0 ≤ ofOdd n k hn ↔ 0 ≤ n := by
  simp [← toRat_le_toRat_iff, toRat_ofOdd_eq_mul_two_pow, zpow_pos]

@[simp]
theorem toRat_one : toRat 1 = 1 := rfl

@[simp]
theorem toRat_ofNat {n : ℕ} [n.AtLeastTwo] : toRat ofNat(n) = ofNat(n) := toRat_natCast n

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

section Shift

variable (d x y : Dyadic) (a b : ℤ) (m n : ℕ)

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

theorem shiftLeft_add_int : d <<< (a + b) = d <<< a <<< b := by
  induction d <;> simp [Int.sub_sub]

theorem shiftLeft_add_nat : d <<< (m + n) = d <<< m <<< n := by
  simp only [← shiftLeft_natCast, Nat.cast_add, shiftLeft_add_int]

theorem shiftRight_add_int : d >>> (a + b) = d >>> a >>> b := by
  induction d <;> simp [Int.add_assoc]

theorem shiftRight_add_nat : d >>> (m + n) = d >>> m >>> n := by
  simp only [← shiftRight_natCast, Nat.cast_add, shiftRight_add_int]

@[simp] theorem shiftLeft_neg : d <<< (-a) = d >>> a := by
  induction d <;> simp

@[simp] theorem shiftRight_neg : d >>> (-a) = d <<< a := by
  induction d <;> simp [Int.sub_eq_add_neg]

theorem shiftLeft_shiftRight : d <<< a >>> b = d <<< (a - b) := by
  rw [Int.sub_eq_add_neg, shiftLeft_add_int, shiftLeft_neg]

theorem shiftRight_shiftLeft : d >>> a <<< b = d >>> (a - b) := by
  rw [Int.sub_eq_add_neg, shiftRight_add_int, shiftRight_neg]

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

theorem add_shiftLeft_int : (x + y) <<< a = x <<< a + y <<< a := by
  simp [← toRat_inj, Rat.add_mul]

theorem add_shiftLeft_nat : (x + y) <<< m = x <<< m + y <<< m :=
  add_shiftLeft_int x y m

theorem add_shiftRight_int : (x + y) >>> a = x >>> a + y >>> a := by
  simp [← toRat_inj, add_div]

theorem add_shiftRight_nat : (x + y) >>> m = x >>> m + y >>> m :=
  add_shiftRight_int x y m

theorem sub_shiftLeft_int : (x - y) <<< a = x <<< a - y <<< a := by
  simp [sub_eq_add_neg, add_shiftLeft_int, neg_shiftLeft]

theorem sub_shiftLeft_nat : (x - y) <<< m = x <<< m - y <<< m :=
  sub_shiftLeft_int x y m

theorem sub_shiftRight_int : (x - y) >>> a = x >>> a - y >>> a := by
  simp [sub_eq_add_neg, add_shiftRight_int, neg_shiftRight]

theorem sub_shiftRight_nat : (x - y) >>> m = x >>> m - y >>> m :=
  sub_shiftRight_int x y m

end Shift

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
