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

@[simp, norm_cast]
protected theorem natCast_add (a b : ℕ) : (Nat.cast (a + b) : Dyadic) = a + b := by
  simp [← Dyadic.toRat_inj]

@[simp] protected theorem intCast_zero : (Int.cast 0 : Dyadic) = 0 := rfl

@[simp] protected theorem intCast_one : (Int.cast 1 : Dyadic) = 1 := rfl

@[simp, norm_cast]
protected theorem intCast_add (a b : ℤ) : (Int.cast (a + b) : Dyadic) = a + b := by
  simp [← Dyadic.toRat_inj]

@[simp, norm_cast]
theorem intCast_natCast (n : ℕ) : (Int.cast n : Dyadic) = n := rfl

@[simp, norm_cast]
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
  nsmul_succ := by simp [· • ·, SMul.smul, Dyadic.add_mul, Dyadic.one_mul]
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
  natCast_succ := by simp
  zsmul n x := n * x
  sub_eq_add_neg _ _ := rfl
  zsmul_zero' := by simp [· • ·, SMul.smul]
  zsmul_succ' := by simp [· • ·, SMul.smul, Dyadic.add_mul, Dyadic.one_mul]
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

section Two

@[expose, simps]
def twoUnit : Units Dyadic where
  val := 2
  inv := (1 : Dyadic) >>> 1
  val_inv := rfl
  inv_val := rfl

theorem isUnit_iff_exists_twoUnit_pow {x : Dyadic} : IsUnit x ↔ ∃ n : ℤ, ↑(twoUnit ^ n) = x := by
  refine ⟨fun hx => ?_, fun h => h.elim fun n hn => hn ▸ Units.isUnit (twoUnit ^ n)⟩
  rw [isUnit_iff_exists] at hx
  obtain ⟨b, hxb, hbx⟩ := hx
  cases x with | zero => simp at hxb | ofOdd nx kx hnx
  cases b with | zero => simp at hxb | ofOdd nb kb hnb
  refine ⟨-kx, ?_⟩
  rw [← toRat_inj, toRat_mul, toRat_ofOdd_eq_mkRat, toRat_ofOdd_eq_mkRat, toRat_one,
    Rat.mkRat_mul_mkRat, ← Rat.intCast_one, ← Rat.mkRat_one,
    Rat.mkRat_eq_iff (NeZero.ne _) (by decide), Int.natCast_one, Int.mul_one, Int.one_mul,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← Nat.pow_add,
    Int.natCast_pow, Nat.cast_ofNat, Int.shiftLeft_eq, Int.shiftLeft_eq, mul_mul_mul_comm,
    ← Int.pow_add] at hxb
  induction kx using Int.negInduction with
  | nat kx =>
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, val_inv_twoUnit]
    change (ofOdd (1 ^ kx) (1 * kx) (by simp)) = ofOdd nx kx hnx
    cases kb using Int.negInduction with
    | nat kb =>
      simp_rw [Int.toNat_neg_natCast, Int.toNat_natCast, add_zero, pow_zero, Int.mul_one] at hxb
      have hxb2 := congr($hxb % 2)
      rw [Int.mul_emod, hnx, hnb, Int.mul_one, Int.one_emod_two] at hxb2
      cases kx with
      | succ _ => rw [Nat.add_right_comm, pow_succ, Int.mul_emod_left] at hxb2; simp at hxb2
      | zero =>
        rw [zero_add] at hxb hxb2
        cases kb with
        | succ _ => rw [pow_succ, Int.mul_emod_left] at hxb2; simp at hxb2
        | zero =>
          rw [pow_zero] at hxb
          cases Int.mul_eq_one hxb
      simp

      sorry
    | neg _ kb =>
      sorry
  | neg _ kx => sorry

end Two

end Dyadic
