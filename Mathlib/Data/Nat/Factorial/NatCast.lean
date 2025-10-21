/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.RingTheory.Nilpotent.Defs

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

theorem natCast_factorial_iff_of_charP {n : ℕ} : IsUnit (n ! : A) ↔ n < p := by
  have hp : p.Prime := Fact.out
  induction n with
  | zero => simp [hp.pos]
  | succ n ih =>
    -- TODO: why is `.symm.symm` needed here!?
    rw [factorial_succ, cast_mul, Nat.cast_commute _ _ |>.isUnit_mul_iff, ih.symm.symm,
      ← Nat.add_one_le_iff, CharP.isUnit_natCast_iff hp]
    exact ⟨fun ⟨h1, h2⟩ ↦ lt_of_le_of_ne h2 (mt (· ▸ dvd_rfl) h1),
      fun h ↦ ⟨not_dvd_of_pos_of_lt (Nat.succ_pos _) h, h.le⟩⟩

end CharP

section Nilpotent

variable {A : Type*} [CommRing A] {n p : ℕ} (hp : IsNilpotent (p : A))
include hp

lemma natCast_of_isNilpotent_of_coprime (h : p.Coprime n) :
    IsUnit (n : A) := by
  obtain ⟨m, hm⟩ := hp
  suffices ∃ a b : A, p ^ m * a + n * b = 1 by
    obtain ⟨a, b, h⟩ := this
    apply isUnit_of_mul_eq_one (n : A) b
    simpa [hm] using h
  refine ⟨(p ^ m).gcdA n, (p ^ m).gcdB n, ?_⟩
  norm_cast
  rw [← Nat.cast_one, ← Int.cast_natCast 1, ← (h.pow_left m).gcd_eq_one, Nat.gcd_eq_gcd_ab]

theorem natCast_factorial_of_isNilpotent [Fact p.Prime] (h : n < p) :
    IsUnit (n ! : A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [factorial_succ, cast_mul, IsUnit.mul_iff]
    refine ⟨.natCast_of_isNilpotent_of_coprime hp ?_, ih (by cutsat)⟩
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact Nat.not_dvd_of_pos_of_lt (by cutsat) h

end Nilpotent

end IsUnit

open Nat Ring

lemma Nat.castChoose_eq {A : Type*} [CommSemiring A] {m : ℕ} {k : ℕ × ℕ}
    (hm : IsUnit (m ! : A)) (hk : k ∈ Finset.antidiagonal m) :
    (choose m k.1 : A) = ↑m ! * inverse ↑k.1! * inverse ↑k.2! := by
  rw [Finset.mem_antidiagonal] at hk
  subst hk
  rw [eq_mul_inverse_iff_mul_eq, eq_mul_inverse_iff_mul_eq, ← Nat.cast_mul, ← Nat.cast_mul,
    add_comm, Nat.add_choose_mul_factorial_mul_factorial] <;>
    apply hm.natCast_factorial_of_le
  exacts [Nat.le_add_right k.1 k.2, Nat.le_add_left k.2 k.1]
