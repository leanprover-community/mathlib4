/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Order.Hom.Basic

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

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
attribute [coe] toRat

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
instance : Coe Dyadic Rat := ⟨toRat⟩

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
attribute [norm_cast] toRat_zero toRat_add toRat_neg toRat_sub toRat_mul toRat_pow
  toRat_intCast toRat_natCast toRat_eq_zero_iff toRat_lt_toRat_iff toRat_le_toRat_iff

-- From @vihdzp's leanprover/lean4#15532. TODO: Remove once merged.
attribute [simp, norm_cast] toRat_inj

/-- Coercion from dyadic rationals to rational numbers as a ring homomorphism. -/
@[expose, simps]
def toRatRingHom : Dyadic →+* ℚ where
  toFun := toRat
  map_zero' := toRat_zero
  map_one' := toRat_one
  map_add' := toRat_add
  map_mul' := toRat_mul

@[simp, norm_cast]
theorem toRat_ofNat (n : ℕ) [n.AtLeastTwo] :
    toRat (ofNat(n) : Dyadic) = (ofNat(n) : Rat) :=
  map_ofNat toRatRingHom n

/-- Coercion from dyadic rationals to rational numbers as an order embedding. -/
@[expose, simps]
def toRatOrderEmbedding : Dyadic ↪o ℚ where
  toFun := toRat
  inj' := fun _ _ ↦ toRat_inj.mp
  map_rel_iff' := toRat_le_toRat_iff

end Dyadic
