import Mathlib.Algebra.Ring.Basic

instance : Numeric ℕ where
  ofNat := id

instance : One ℕ where
  one := (1: ℕ)

instance : Mul ℕ where
  mul := Nat.mul

instance : Semigroup ℕ where
  mul_assoc := Nat.mul_assoc

instance : Monoid ℕ where
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow_zero' := sorry
  npow_succ' := sorry

instance : AddSemigroup ℕ where
  add_assoc := Nat.add_assoc

instance : Zero ℕ where
  zero := (0: ℕ)

instance : AddMonoid ℕ where
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul_zero' := sorry
  nsmul_succ' := sorry

instance : AddCommMonoid ℕ where
  add_comm := Nat.add_comm

instance : Semiring ℕ where
  __ := inferInstanceAs (Numeric ℕ)
  __ := inferInstanceAs (AddCommMonoid ℕ)
  __ := inferInstanceAs (Monoid ℕ)
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
  ofNat_add := by simp [Numeric.ofNat]
  ofNat_mul := by simp [Numeric.ofNat]
