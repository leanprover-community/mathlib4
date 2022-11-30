import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Spread
import Mathlib.Algebra.Ring.Defs

/-
# Semirings and rings
-/


export Distrib (left_distrib right_distrib)

section Semiring

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


section no_zero_divisors

variable (α)

lemma IsLeftCancelMulZero.to_NoZeroDivisors [Ring α] [IsLeftCancelMulZero α] :
    NoZeroDivisors α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := @fun x y h ↦ by
    by_cases hx : x = 0
    { left
      exact hx }
    { right
      rw [← sub_zero (x * y), ← mul_zero x, ← mul_sub] at h
      convert (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero) hx h
      rw [sub_zero] } }
#align is_left_cancel_mul_zero.to_no_zero_divisors IsLeftCancelMulZero.to_NoZeroDivisors

lemma IsRightCancelMulZero.to_NoZeroDivisors [Ring α] [IsRightCancelMulZero α] :
    NoZeroDivisors α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := @fun x y h ↦ by
    by_cases hy : y = 0
    { right
      exact hy }
    { left
      rw [← sub_zero (x * y), ← zero_mul y, ← sub_mul] at h
      convert (IsRightCancelMulZero.mul_right_cancel_of_ne_zero) hy h
      rw [sub_zero] } }
#align is_right_cancel_mul_zero.to_no_zero_divisors IsRightCancelMulZero.to_NoZeroDivisors

instance (priority := 100) NoZeroDivisors.to_IsCancelMulZero [Ring α] [NoZeroDivisors α] :
    IsCancelMulZero α :=
{ mul_left_cancel_of_ne_zero := fun ha h ↦ by
    rw [← sub_eq_zero, ← mul_sub] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  mul_right_cancel_of_ne_zero := fun hb h ↦ by
    rw [← sub_eq_zero, ← sub_mul] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb) }
#align no_zero_divisors.to_is_cancel_mul_zero NoZeroDivisors.to_IsCancelMulZero

lemma NoZeroDivisors.to_IsDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
  IsDomain α :=
{ NoZeroDivisors.to_IsCancelMulZero α, h with .. }
#align no_zero_divisors.to_is_domain.to_no_zero_divisors NoZeroDivisors.to_IsDomain

instance (priority := 100) IsDomain.to_NoZeroDivisors [Ring α] [IsDomain α] :
    NoZeroDivisors α :=
IsRightCancelMulZero.to_NoZeroDivisors α
#align is_domain.to_no_zero_divisors IsDomain.to_NoZeroDivisors

end no_zero_divisors
