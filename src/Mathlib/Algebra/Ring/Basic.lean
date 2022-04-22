import Mathlib.Init.Data.Int.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Spread
/-

# Semirings and rings

-/

class Numeric (α : Type u) where
  ofNat : Nat → α

instance Numeric.OfNat [Numeric α] : OfNat α n := ⟨Numeric.ofNat n⟩
instance [Numeric α] : CoeTail ℕ α := ⟨Numeric.ofNat⟩

theorem ofNat_eq_ofNat (α) (n : ℕ) [Numeric α] : Numeric.ofNat (α := α) n = OfNat.ofNat n := rfl

class Semiring (R : Type u) extends Semigroup R, AddCommSemigroup R, Numeric R where
  add_zero (a : R) : a + 0 = a
  zero_add (a : R) : 0 + a = a
  nsmul : ℕ → R → R := nsmul_rec
  nsmul_zero' : ∀ x, nsmul 0 x = 0 -- fill in with tactic once we can do this
  nsmul_succ' : ∀ (n : ℕ) x, nsmul n.succ x = x + nsmul n x -- fill in with tactic

  zero_mul (a : R) : 0 * a = 0
  mul_zero (a : R) : a * 0 = 0

  -- Monoid R
  one_mul (a : R) : 1 * a = a
  mul_one (a : R) : a * 1 = a
  npow : ℕ → R → R := npow_rec
  npow_zero' : ∀ x, npow 0 x = 1 -- fill in with tactic once we can do this
  npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x -- fill in with tactic

  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c
  ofNat_succ (a : Nat) : ofNat (a + 1) = ofNat a + 1

section Semiring
variable {R} [Semiring R]
open Numeric

instance : MonoidWithZero R where
  __ := ‹Semiring R›

instance : AddCommMonoid R where
  __ := ‹Semiring R›

theorem mul_add (a b c : R) : a * (b + c) = a * b + a * c := Semiring.mul_add a b c

theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := Semiring.add_mul a b c

@[simp] lemma ofNat_zero : (ofNat 0 : R) = 0 := rfl
@[simp] lemma ofNat_one : (ofNat 1 : R) = 1 := rfl

@[simp] lemma ofNat_add : ∀ {a b}, (ofNat (a + b) : R) = ofNat a + ofNat b
  | a, 0 => (add_zero _).symm
  | a, b + 1 => trans (Semiring.ofNat_succ _)
    (by simp [Semiring.ofNat_succ, ofNat_add (b := b), add_assoc])

@[simp] lemma ofNat_mul : ∀ {a b}, (ofNat (a * b) : R) = ofNat a * ofNat b
  | a, 0 => by simp
  | a, b + 1 => by simp [Nat.mul_succ, mul_add,
    (show ofNat (a * b) = ofNat a * ofNat b from ofNat_mul)]

@[simp] theorem ofNat_pow (a n : ℕ) : Numeric.ofNat (a^n) = (Numeric.ofNat a : R)^n := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.pow_zero]
    exact rfl
  | succ n ih =>
    rw [pow_succ, Nat.pow_succ, ofNat_mul, ih]

end Semiring

class CommSemiring (R : Type u) extends Semiring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [CommSemiring R] : CommMonoid R where
  __ := ‹CommSemiring R›

class Ring (R : Type u) extends Semiring R, Neg R, Sub R where
  -- AddGroup R
  sub := λ a b => a + -b
  sub_eq_add_neg : ∀ a b : R, a - b = a + -b
  gsmul : ℤ → R → R := gsmul_rec
  gsmul_zero' : ∀ (a : R), gsmul 0 a = 0
  gsmul_succ' (n : ℕ) (a : R) : gsmul (Int.ofNat n.succ) a = a + gsmul (Int.ofNat n) a
  gsmul_neg' (n : ℕ) (a : R) : gsmul (Int.negSucc n) a = -(gsmul ↑(n.succ) a)
  add_left_neg (a : R) : -a + a = 0

instance {R} [Ring R] : AddCommGroup R := { ‹Ring R› with }

class CommRing (R : Type u) extends Ring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [CommRing R] : CommSemiring R where
  __ := inferInstanceAs (Semiring R)
  __ := ‹CommRing R›

/- Instances -/

namespace Nat

instance : Numeric Nat := ⟨id⟩

@[simp] theorem ofNat_eq_Nat (n : Nat) : Numeric.ofNat n = n := rfl

instance : CommSemiring ℕ where
  mul_comm := Nat.mul_comm
  mul_add := Nat.left_distrib
  add_mul := Nat.right_distrib
  ofNat_succ := fun _ => rfl
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

end Nat

namespace Int

instance : Numeric ℤ := ⟨Int.ofNat⟩

instance : CommRing ℤ where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_comm := Int.mul_comm
  mul_add := Int.distrib_left
  add_mul := Int.distrib_right
  ofNat_succ := fun _ => rfl
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow (n x) := HPow.hPow x n
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

end Int
