/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Hom.Basic

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum.Basic

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

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
attribute [coe] toRat

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
instance : Coe Dyadic Rat := ⟨toRat⟩

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
attribute [norm_cast] toRat_zero toRat_add toRat_neg toRat_sub toRat_mul toRat_pow
  toRat_intCast toRat_natCast toRat_eq_zero_iff toRat_lt_toRat_iff toRat_le_toRat_iff

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
attribute [simp, norm_cast] toRat_inj

@[simp, norm_cast]
theorem toRat_ofNat (n : ℕ) [n.AtLeastTwo] :
    toRat (ofNat(n) : Dyadic) = (ofNat(n) : Rat) := by
  rw [← Nat.cast_ofNat (R := Dyadic)]
  exact toRat_natCast n

/-- Coercion from dyadic rationals to rational numbers as an additive monoid homomorphism. -/
@[simps]
def toRatAddMonoidHom : Dyadic →+ ℚ where
  toFun := toRat
  map_zero' := toRat_zero
  map_add' := toRat_add

/-- Coercion from dyadic rationals to rational numbers as an order embedding. -/
@[simps]
def toRatOrderEmbedding : Dyadic ↪o ℚ where
  toFun := toRat
  inj' := fun _ _ ↦ toRat_inj.mp
  map_rel_iff' := toRat_le_toRat_iff

/-- One unit on the dyadic grid with precision `prec`. -/
def step (prec : Int) : Dyadic := .ofOdd 1 prec (by decide)

theorem ofIntWithPrec_one (prec : Int) : ofIntWithPrec 1 prec = step prec := by
  simp [step, ofIntWithPrec, Int.trailingZeros_eq_zero_of_mod_eq (show 1 % 2 = 1 by decide)]

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

end Dyadic
