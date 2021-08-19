import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Spread
/-

# Semirings and rings

-/

class Numeric (α : Type u) where
  ofNat : Nat → α

instance Numeric.OfNat [Numeric α] : OfNat α n := ⟨Numeric.ofNat n⟩
instance [Numeric α] : Coe ℕ α := ⟨Numeric.ofNat⟩

class Semiring (R : Type u) extends Monoid R, AddCommMonoid R, Numeric R where
  zero_mul (a : R) : 0 * a = 0
  mul_zero (a : R) : a * 0 = 0
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c
  ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b
  ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b
  ofNat_one : ofNat (nat_lit 1) = One.one
  ofNat_zero : ofNat (nat_lit 0) = Zero.zero

section Semiring
variable {R} [Semiring R]
instance : MonoidWithZero R where
  __ := ‹Semiring R›

theorem mul_add  (a b c : R) : a * (b + c) = a * b + a * c := Semiring.mul_add a b c

theorem add_mul {R} [Semiring R] (a b c : R) : (a + b) * c = a * c + b * c := Semiring.add_mul a b c

@[simp] theorem mul_zero {R} [Semiring R] (a : R) : a * 0 = 0 := Semiring.mul_zero a

@[simp] theorem zero_mul {R} [Semiring R] (a : R) : 0 * a = 0 := Semiring.zero_mul a

theorem Semiring.ofNat_pow (a n : ℕ) : Numeric.ofNat (a^n) = (Numeric.ofNat a : R)^n := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.pow_zero, Semiring.ofNat_one]
    exact rfl
  | succ n ih =>
    rw [pow_succ, Nat.pow_succ, Semiring.ofNat_mul, ih]

end Semiring

class CommSemiring (R : Type u) extends Semiring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [CommSemiring R] : CommMonoid R where
  __ := ‹CommSemiring R›

class Ring (R : Type u) extends Monoid R, AddCommGroup R, Numeric R where
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c
  ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b
  ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b
  ofNat_one : ofNat (nat_lit 1) = One.one
  ofNat_zero : ofNat (nat_lit 0) = Zero.zero

instance (R : Type u) [Ring R] : Semiring R where
  zero_mul := λ a => by rw [← add_right_eq_self (a := 0 * a), ← Ring.add_mul, zero_add]
  mul_zero := λ a => by rw [← add_right_eq_self (a := a * 0), ← Ring.mul_add]; simp
  __ := ‹Ring R›

class CommRing (R : Type u) extends Ring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [CommRing R] : CommSemiring R where
  __ := inferInstanceAs (Semiring R)
  __ := ‹CommRing R›

/- Instances -/

namespace Nat

instance : Numeric Nat := ⟨id⟩
@[simp] theorem ofNat_eq_Nat (n : Nat): Numeric.ofNat n = n := rfl

instance : CommSemiring Nat where
  mul_comm := Nat.mul_comm
  mul_add := Nat.left_distrib
  add_mul := Nat.right_distrib
  ofNat_add := by simp
  ofNat_mul := by simp
  ofNat_one := rfl
  ofNat_zero := rfl
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow (n x) := HPow.hPow x n
  npow_zero' := Nat.pow_zero
  npow_succ' n x := by simp [Nat.pow_succ, Nat.mul_comm]
  one := 1
  zero := 0
  mul_assoc := Nat.mul_assoc
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul := HMul.hMul
  nsmul_zero' := Nat.zero_mul
  nsmul_succ' n x := by simp [Nat.add_comm, (Nat.succ_mul n x)]
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

end Nat

namespace Int

instance : Numeric ℤ := ⟨Int.ofNat⟩

theorem pow_succ (n : ℤ) (m : ℕ ) : n^(Nat.succ m) = n^m * n :=
  rfl

@[simp] theorem ofNat_eq_ofNat (n : ℕ): Numeric.ofNat n = ofNat n := rfl

instance : CommRing ℤ where
  mul_comm := Int.mul_comm
  mul_add := Int.distrib_left
  add_mul := Int.distrib_right
  ofNat_add := by simp [ofNat_add]
  ofNat_mul := by simp [ofNat_mul]
  ofNat_one := rfl
  ofNat_zero := rfl
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow (n x) := HPow.hPow x n
  npow_zero' n := rfl
  npow_succ' n x := by
    rw [Int.mul_comm]
    exact rfl
  one := 1
  zero := 0
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

end Int
