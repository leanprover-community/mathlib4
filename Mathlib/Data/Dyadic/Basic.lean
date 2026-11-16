/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.Algebra.Order.Ring.Basic

/-!
# Dyadic rationals form an ordered ring

We provide instances of `LinearOrder Dyadic`, `CommRing Dyadic`, and `IsOrderedRing Dyadic`.
-/

public section
namespace Dyadic

section Lemmas

@[simp] theorem toRat_one : toRat 1 = 1 := rfl

@[simp] protected theorem natCast_zero : (Nat.cast 0 : Dyadic) = 0 := rfl
@[simp] protected theorem natCast_one : (Nat.cast 1 : Dyadic) = 1 := rfl

@[norm_cast]
protected theorem natCast_add (a b : ℕ) : (Nat.cast (a + b) : Dyadic) = a + b := by
  simp [← Dyadic.toRat_inj]

@[simp] protected theorem intCast_zero : (Int.cast 0 : Dyadic) = 0 := rfl

@[simp] protected theorem intCast_one : (Int.cast 1 : Dyadic) = 1 := rfl

@[norm_cast]
protected theorem intCast_add (a b : ℤ) : (Int.cast (a + b) : Dyadic) = a + b := by
  simp [← Dyadic.toRat_inj]

@[simp, norm_cast]
theorem intCast_natCast (n : ℕ) : (Int.cast n : Dyadic) = n := rfl

@[norm_cast]
protected theorem intCast_neg (a : Int) : ((-a : Int) : Dyadic) = -(a : Dyadic) := by
  simp [← Dyadic.toRat_inj]

end Lemmas

section Instances

instance : LinearOrder Dyadic where
  le_refl := Dyadic.le_refl
  le_trans := @Dyadic.le_trans
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  le_antisymm := @Dyadic.le_antisymm
  le_total := Dyadic.le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance

instance : CommRing Dyadic where
  add_assoc := Dyadic.add_assoc
  zero_add := Dyadic.zero_add
  add_zero := Dyadic.add_zero
  nsmul n x := n * x
  nsmul_zero := by simp [· • ·, SMul.smul]
  nsmul_succ := by simp [· • ·, SMul.smul, Dyadic.add_mul, Dyadic.one_mul, Dyadic.natCast_add]
  add_comm := Dyadic.add_comm
  mul_assoc := Dyadic.mul_assoc
  one_mul := Dyadic.one_mul
  mul_one := Dyadic.mul_one
  npow_zero := Dyadic.pow_zero
  npow_succ n x := Dyadic.pow_succ x n
  zero_mul := Dyadic.zero_mul
  mul_zero := Dyadic.mul_zero
  left_distrib := Dyadic.mul_add
  right_distrib := Dyadic.add_mul
  natCast_zero := Dyadic.natCast_zero
  natCast_succ := by simp [Dyadic.natCast_add]
  zsmul n x := n * x
  sub_eq_add_neg _ _ := rfl
  zsmul_zero' := by simp [· • ·, SMul.smul]
  zsmul_succ' := by simp [· • ·, SMul.smul, Dyadic.add_mul, Dyadic.one_mul, Dyadic.intCast_add]
  zsmul_neg' := by
    intro n a
    change (Int.negSucc n : ℤ) * a = -(n.succ * a)
    rw [Int.negSucc_eq, Nat.succ_eq_add_one, ← toRat_inj, toRat_mul, toRat_intCast, toRat_neg,
      toRat_mul, toRat_natCast, Rat.intCast_neg, Rat.intCast_add, Rat.intCast_natCast,
      Rat.natCast_add, ← Rat.intCast_natCast 1, Int.natCast_one, Rat.neg_mul]
  neg_add_cancel := Dyadic.neg_add_cancel
  intCast_ofNat := Dyadic.intCast_natCast
  intCast_negSucc := by
    intro n
    change Int.cast (Int.negSucc n) = -Nat.cast (n + 1)
    rw [Int.negSucc_eq, ← toRat_inj, toRat_intCast, toRat_neg, toRat_natCast, Rat.intCast_neg,
      Rat.intCast_add, Rat.intCast_natCast, Rat.natCast_add, ← Rat.intCast_natCast 1,
      Int.natCast_one]
  mul_comm := Dyadic.mul_comm

instance : IsStrictOrderedRing Dyadic where
  add_le_add_left := by simp [← Dyadic.toRat_le_toRat_iff, Rat.add_le_add_right]
  add_le_add_right := by simp [← Dyadic.toRat_le_toRat_iff, Rat.add_le_add_left]
  le_of_add_le_add_left := by simp [← Dyadic.toRat_le_toRat_iff, Rat.add_le_add_left]
  le_of_add_le_add_right := by simp [← Dyadic.toRat_le_toRat_iff, Rat.add_le_add_right]
  mul_lt_mul_of_pos_left := by simp +contextual [← Dyadic.toRat_lt_toRat_iff, Rat.mul_lt_mul_left]
  mul_lt_mul_of_pos_right := by simp +contextual [← Dyadic.toRat_lt_toRat_iff, Rat.mul_lt_mul_right]
  zero_le_one := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩

end Instances

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
