/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Invertibility of factorials

This file contains lemmas providing sufficient conditions for the cast of `n!` to a (semi)ring `A`
to be a unit.

-/

namespace IsUnit

open Nat
section Semiring

variable {A : Type*} [Semiring A]

theorem natCast_factorial_of_le {n : ℕ} (hn_fac : IsUnit (n ! : A))
    {m : ℕ} (hmn : m ≤ n) : IsUnit (m ! : A) := by
  obtain ⟨k, rfl⟩ := exists_add_of_le hmn
  clear hmn
  induction k generalizing m with
  | zero => simpa using hn_fac
  | succ k ih =>
    rw [← add_assoc, add_right_comm] at hn_fac
    have := ih hn_fac
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_commute _ _ |>.isUnit_mul_iff] at this
    exact this.2

theorem natCast_factorial_of_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A))
    {m : ℕ} (hmn : m < n) : IsUnit (m ! : A) :=
  hn_fac.natCast_factorial_of_le <| le_sub_one_of_lt hmn

theorem natCast_factorial_of_ratAlgebra [Algebra ℚ A] (n : ℕ) : IsUnit (n ! : A) := by
  rw [← map_natCast (algebraMap ℚ A)]
  apply IsUnit.map
  simp [isUnit_iff_ne_zero, n.factorial_ne_zero]

end Semiring

section CharP

variable {A : Type*} [Ring A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]

theorem natCast_factorial_of_charP  {n : ℕ} (h : n < p) : IsUnit (n ! : A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [factorial_succ, cast_mul, Nat.cast_commute _ _ |>.isUnit_mul_iff]
    refine ⟨?_, ih (lt_trans (lt_add_one n) h)⟩
    have h1 := Int.cast_one (R := A)
    rw [← cast_one, ← coprime_of_lt_prime (zero_lt_succ n) h (Fact.elim inferInstance),
      gcd_eq_gcd_ab, Int.cast_add] at h1
    simp only [succ_eq_add_one, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul,
      zero_add] at h1
    have h2 :=  Nat.cast_commute _ _ |>.eq.symm.trans h1
    exact ⟨⟨_, _, h1, h2⟩, rfl⟩

end CharP

end IsUnit
