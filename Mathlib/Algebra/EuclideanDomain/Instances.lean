/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro

! This file was ported from Lean 3 source module algebra.euclidean_domain.instances
! leanprover-community/mathlib commit cf9386b56953fb40904843af98b7a80757bbe7f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Init.Data.Int.Order
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Int.Order.Basic

/-!
# Instances for Euclidean domains
* `Int.euclideanDomain`: shows that `ℤ` is a Euclidean domain.
* `Field.toEuclideanDomain`: shows that any field is a Euclidean domain.
-/

instance Int.euclideanDomain : EuclideanDomain ℤ :=
  { inferInstanceAs (CommRing Int), inferInstanceAs (Nontrivial Int) with
    add := (· + ·), mul := (· * ·), one := 1, zero := 0,
    neg := Neg.neg,
    quotient := (· / ·), quotient_zero := Int.ediv_zero, remainder := (· % ·),
    quotient_mul_add_remainder_eq := Int.ediv_add_emod,
    r := fun a b => a.natAbs < b.natAbs,
    r_wellFounded := (measure natAbs).wf
    remainder_lt := fun a b b0 => Int.ofNat_lt.1 <| by
      rw [Int.natAbs_of_nonneg (Int.emod_nonneg _ b0), ← Int.abs_eq_natAbs]
      exact Int.emod_lt _ b0
    mul_left_not_lt := fun a b b0 =>
      not_lt_of_ge <| by
        rw [← mul_one a.natAbs, Int.natAbs_mul]
        rw [←Int.natAbs_pos] at b0
        exact Nat.mul_le_mul_of_nonneg_left b0  }

-- Porting note: this seems very slow.
-- see Note [lower instance priority]
instance (priority := 100) Field.toEuclideanDomain {K : Type _} [Field K] : EuclideanDomain K :=
  { ‹Field K› with
    add := (· + ·), mul := (· * ·), one := 1, zero := 0, neg := Neg.neg,
    quotient := (· / ·), remainder := fun a b => a - a * b / b, quotient_zero := div_zero,
    quotient_mul_add_remainder_eq := fun a b => by
      -- Porting note: was `by_cases h : b = 0 <;> simp [h, mul_div_cancel']`
      by_cases h : b = 0 <;> dsimp only
      · dsimp only
        rw [h, zero_mul, mul_zero, zero_div, zero_add, sub_zero]
      · dsimp only
        rw [mul_div_cancel' _ h]
        simp only [ne_eq, h, not_false_iff, mul_div_cancel, sub_self, add_zero]
    r := fun a b => a = 0 ∧ b ≠ 0,
    r_wellFounded :=
      WellFounded.intro fun a =>
        (Acc.intro _) fun b ⟨hb, _⟩ => (Acc.intro _) fun c ⟨_, hnb⟩ => False.elim <| hnb hb,
    remainder_lt := fun a b hnb => by simp [hnb],
    mul_left_not_lt := fun a b hnb ⟨hab, hna⟩ => Or.casesOn (mul_eq_zero.1 hab) hna hnb }
#align field.to_euclidean_domain Field.toEuclideanDomain
