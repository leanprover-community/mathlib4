/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod

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

/-- If `A` is an algebra over a characteristic-zero (semi)field, then `n!` is a unit. -/
theorem natCast_factorial_of_algebra (K : Type*) [Semifield K] [CharZero K] [Algebra K A] (n : ℕ) :
    IsUnit (n ! : A) := by
  suffices IsUnit (n ! : K) by
    simpa using this.map (algebraMap K A)
  simp [isUnit_iff_ne_zero, n.factorial_ne_zero]

end Semiring

section CharP

variable {A : Type*} [Ring A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]

-- TODO: move / golf
theorem natCast_iff_of_charP {n : ℕ} : IsUnit (n : A) ↔ ¬ (p ∣ n) := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← CharP.cast_eq_zero_iff (R := A), ← hx]
    have := CharP.nontrivial_of_char_ne_one (R := A) (Nat.Prime.ne_one Fact.out : p ≠ 1)
    exact x.ne_zero
  · intro h
    rw [ ← ZMod.cast_natCast' (n := p)]
    refine ⟨⟨ZMod.cast (n : ZMod p), ZMod.cast (n⁻¹ : ZMod p), ?_, ?_⟩, rfl⟩
    all_goals rw [← ZMod.cast_mul (m := p) dvd_rfl]
    · rw [mul_inv_cancel₀ (G₀ := ZMod p), ZMod.cast_one']
      rw [ne_eq, ZMod.natCast_zmod_eq_zero_iff_dvd]
      assumption
    · rw [inv_mul_cancel₀ (G₀ := ZMod p), ZMod.cast_one']
      rw [ne_eq, ZMod.natCast_zmod_eq_zero_iff_dvd]
      assumption

theorem natCast_factorial_iff_of_charP {n : ℕ} : IsUnit (n ! : A) ↔ n < p := by
  have hp : p.Prime := Fact.out
  induction n with
  | zero => simp [hp.pos]
  | succ n ih =>
    -- TODO: why is `.symm.symm` needed here!?
    rw [factorial_succ, cast_mul, Nat.cast_commute _ _ |>.isUnit_mul_iff, ih.symm.symm,
      ← Nat.add_one_le_iff, natCast_iff_of_charP (p := p)]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h2 (mt (· ▸ dvd_rfl) h1)
    · intro h
      exact ⟨not_dvd_of_pos_of_lt (Nat.succ_pos _) h, h.le⟩

end CharP

end IsUnit
