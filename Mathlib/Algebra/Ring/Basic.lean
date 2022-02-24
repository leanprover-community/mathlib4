import Mathlib.Init.Data.Int.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Spread
import Mathlib.Util.WhatsNew

/-
# Semirings and rings
-/

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
class Distrib (R : Type u) extends Mul R, Add R where
  left_distrib : ∀ a b c : R, a * (b + c) = (a * b) + (a * c)
  right_distrib : ∀ a b c : R, (a + b) * c = (a * c) + (b * c)

export Distrib (left_distrib right_distrib)

section
variable {R} [Distrib R]
theorem mul_add (a b c : R) : a * (b + c) = a * b + a * c := Distrib.left_distrib a b c
theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := Distrib.right_distrib a b c
end

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
class NonUnitalNonAssocSemiring (R : Type u) extends
  AddCommMonoid R, Distrib R, MulZeroClass R, AddMonoidWithOne R

/-- An associative but not-necessarily unital semiring. -/
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

/-- A unital but not-necessarily-associative semiring. -/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α

class Semiring (R : Type u) extends NonUnitalSemiring R, NonAssocSemiring R, MonoidWithZero R

section Semiring

@[simp]
lemma Nat.cast_mul [Semiring R] {m n : ℕ} : (m * n).cast = (m.cast * n.cast : R) := by
  induction n generalizing m <;> simp_all [mul_succ, mul_add]

@[simp]
lemma Nat.cast_pow [Semiring R] {m n : ℕ} : (m ^ n).cast = (m.cast ^ n : R) := by
  induction n generalizing m <;> simp_all [Nat.pow_succ', _root_.pow_succ', pow_zero]

end Semiring

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R where
  -- TODO: doesn't work
  right_distrib a b c := (by rw [mul_comm, mul_add, mul_comm c, mul_comm c])

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

theorem neg_mul_eq_neg_mul {R} [Ring R] (a b : R) : -(a * b) = (-a) * b :=
  Eq.symm <| eq_of_sub_eq_zero' <| by
    rw [sub_eq_add_neg, neg_neg (a * b) /- TODO: why is arg necessary? -/]
    rw [← add_mul, neg_add_self a /- TODO: why is arg necessary? -/, zero_mul]

class CommRing (R : Type u) extends Ring R, CommSemiring R

/- Instances -/

namespace Nat

instance : CommSemiring ℕ where
  mul_comm := Nat.mul_comm
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow (n x) := x ^ n
  npow_zero' := Nat.pow_zero
  npow_succ' n x := by simp [Nat.pow_succ, Nat.mul_comm]
  mul_assoc := Nat.mul_assoc
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul := (·*·)
  nsmul_zero' := Nat.zero_mul
  nsmul_succ' n x := by simp [Nat.add_comm, (Nat.succ_mul n x)]
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
  left_distrib := Int.distrib_left
  right_distrib := Int.distrib_right
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow (n x) := x ^ n
  npow_zero' n := rfl
  npow_succ' n x := by rw [Int.mul_comm]; rfl
  mul_assoc := Int.mul_assoc
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero' := Int.zero_mul
  nsmul_succ' n x := by
    show ofNat (Nat.succ n) * x = x + ofNat n * x
    rw [Int.ofNat_succ, Int.distrib_right, Int.add_comm, Int.one_mul]
  sub_eq_add_neg a b := Int.sub_eq_add_neg
  gsmul := HMul.hMul
  gsmul_zero' := Int.zero_mul
  gsmul_succ' n x := by rw [Int.ofNat_succ, Int.distrib_right, Int.add_comm, Int.one_mul]
  gsmul_neg' n x := by
    cases x with
    | ofNat m =>
      rw [Int.negSucc_ofNat_ofNat, Int.ofNat_mul_ofNat]
      exact rfl
    | negSucc m =>
      rw [Int.mul_negSucc_ofNat_negSucc_ofNat, Int.ofNat_mul_negSucc_ofNat]
      exact rfl
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
  Int.cast_ofNat

@[simp, norm_cast]
lemma cast_eq_cast_iff_Nat (m n : ℕ) : (m : ℤ) = (n : ℤ) ↔ m = n :=
  ofNat_eq_ofNat_iff _ _

@[simp, norm_cast]
lemma natAbs_cast (n : ℕ) : natAbs ↑n = n := rfl

@[norm_cast]
protected lemma coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := ofNat_sub

end Int
