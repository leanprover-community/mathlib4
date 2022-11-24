import Mathlib.Algebra.Group.Commute
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Spread
import Mathlib.Algebra.Ring.Defs

/-
# Semirings and rings
-/


export Distrib (left_distrib right_distrib)

section Semiring

-- TODO: put these in the right place
@[simp] theorem Commute.zero_right [Semiring R] (a : R) : Commute a 0 :=
  (mul_zero _).trans (zero_mul _).symm

@[simp] theorem Commute.zero_left [Semiring R] (a : R) : Commute 0 a :=
  (zero_mul _).trans (mul_zero _).symm

@[simp] theorem Commute.add_right [Semiring R] {a b c : R} (h : Commute a b) (h' : Commute a c) :
    Commute a (b + c) := by
  simp only [Commute, SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp] theorem Commute.add_left [Semiring R] {a b c : R} (h : Commute a c) (h' : Commute b c) :
    Commute (a + b) c := by
  simp only [Commute, SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp]
lemma Nat.cast_mul [Semiring R] {m n : ℕ} : (m * n).cast = (m.cast * n.cast : R) := by
  induction n generalizing m <;> simp_all [mul_succ, mul_add]

@[simp]
lemma Nat.cast_pow [Semiring R] {m n : ℕ} : (m ^ n).cast = (m.cast ^ n : R) := by
  induction n generalizing m <;> simp_all [Nat.pow_succ', _root_.pow_succ'', pow_zero]

theorem Nat.cast_commute [Semiring α] (n : ℕ) (x : α) : Commute (↑n) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)

end Semiring

example [Ring R] : HasInvolutiveNeg R := inferInstance


/- Instances -/

namespace Nat

instance : CommSemiring ℕ where
  mul_comm := Nat.mul_comm
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow (n x) := x ^ n
  npow_zero := Nat.pow_zero
  npow_succ n x := by simp [Nat.pow_succ, Nat.mul_comm]
  mul_assoc := Nat.mul_assoc
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul := (·*·)
  nsmul_zero := Nat.zero_mul
  nsmul_succ n x := by simp [Nat.add_comm, (Nat.succ_mul n x)]
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl

@[simp, norm_cast] lemma cast_id : Nat.cast n = n := rfl

end Nat

namespace Int

instance : CommRing ℤ where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := by rw [Int.mul_comm]; rfl
  mul_assoc := Int.mul_assoc
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x := by
    show ofNat (Nat.succ n) * x = x + ofNat n * x
    rw [Int.ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

@[simp, norm_cast] lemma cast_id : Int.cast n = n := rfl

@[simp] lemma ofNat_eq_cast : Int.ofNat n = n := rfl

@[simp, norm_cast]
lemma cast_Nat_cast [AddGroupWithOne R] : (Int.cast (Nat.cast n) : R) = Nat.cast n :=
  Int.cast_ofNat _

@[simp, norm_cast]
lemma cast_eq_cast_iff_Nat (m n : ℕ) : (m : ℤ) = (n : ℤ) ↔ m = n := ofNat_inj

@[simp, norm_cast]
lemma natAbs_cast (n : ℕ) : natAbs ↑n = n := rfl

@[norm_cast]
protected lemma coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := ofNat_sub

end Int

-- TODO restore @[to_additive coe_nat_zsmul]
@[norm_cast]
theorem zpow_coe_nat [DivInvMonoid G] (a : G) (n : ℕ) : a ^ (n : ℤ) = a ^ n := zpow_ofNat ..
theorem coe_nat_zsmul [SubNegMonoid G] (a : G) (n : ℕ) : (n : ℤ) • a = n • a := ofNat_zsmul ..
attribute [to_additive coe_nat_zsmul] zpow_coe_nat
