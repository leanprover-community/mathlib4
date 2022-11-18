/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.NormCast

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into an
additive group with a one (typically a `ring`).  In additive groups with a one
element, there exists a unique such homomorphism and we store it in the
`int_cast : ℤ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `int.cast`: Canonical homomorphism `ℤ → R`.
* `add_group_with_one`: Type class for `int.cast`.
-/

namespace Nat
variable [AddGroupWithOne R]

@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]

end Nat

namespace Int
variable [AddGroupWithOne R]

@[simp, norm_cast]
theorem cast_neg [AddGroupWithOne R] : ∀ n:ℤ, ((-n : ℤ) : R) = -↑n
  | (0 : ℕ) => by erw [cast_zero, neg_zero]
  | (n + 1 : ℕ) => by erw [cast_ofNat, cast_negSucc]
  | -[n +1] => by erw [cast_ofNat, cast_negSucc, neg_neg]

@[simp]
theorem cast_subNatNat [AddGroupWithOne R] (m n) : ((subNatNat m n : ℤ) : R) = m - n := by
  unfold Int.subNatNat
  cases e : n - m
  · simp only [subNatNat, cast_ofNat]
    simp [e, Nat.le_of_sub_eq_zero e]
  · rw [cast_negSucc, Nat.add_one, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e,
      neg_sub]
#align int.cast_sub_nat_nat Int.cast_subNatNat

@[simp, norm_cast]
theorem cast_add [AddGroupWithOne R] : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [← ofNat_add]
  | (m : ℕ), -[n+1] => by erw [cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_add_neg]
  | -[m+1], (n : ℕ) => by
    erw [cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_iff_eq_add,
      add_assoc, eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[m+1], -[n+1] => show (-[m + n + 1 +1] : R) = _ by
    rw [cast_negSucc, cast_negSucc, cast_negSucc, ← neg_add_rev, ← Nat.cast_add,
      Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]

@[simp, norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by simp [Int.sub_eq_add_neg, sub_eq_add_neg]
