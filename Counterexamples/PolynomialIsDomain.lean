/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.GroupWithZero.TransferInstance
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Equiv
import Mathlib.RingTheory.Polynomial.Opposites

/-!
# A commutative semiring without cancellative addition that is a domain

`NatMaxAdd` is the natural numbers equipped with the usual multiplication but with maximum as
addition. Under these operations it is a commutative semiring that is a domain, but
`1 + 1 = 1 + 0 = 1` in this semiring so addition is not cancellative.
As a consequence, the polynomial semiring `NatMaxAdd[X]` is not a domain.
-/

/-- A type synonym for ℕ equipped with maximum as addition. -/
def NatMaxAdd := ℕ

namespace NatMaxAdd

/-- Identification of `NatMaxAdd` with `ℕ`. -/
protected abbrev mk : ℕ ≃ NatMaxAdd := Equiv.refl _

attribute [irreducible] NatMaxAdd

open NatMaxAdd (mk)

instance : AddCommSemigroup NatMaxAdd where
  add a b := mk (mk.symm a ⊔ mk.symm b)
  add_assoc _ _ _ := mk.symm.injective (sup_assoc ..)
  add_comm _ _ := mk.symm.injective (sup_comm ..)

instance : AddZeroClass NatMaxAdd where
  zero := mk 0
  zero_add _ := mk.symm.injective (bot_sup_eq _)
  add_zero _ := mk.symm.injective (sup_bot_eq _)

instance : CommMonoidWithZero NatMaxAdd := mk.symm.commMonoidWithZero

/-- `NatMaxAdd` is isomorphic to `ℕ` multiplicatively. -/
protected def mulEquiv : NatMaxAdd ≃* ℕ where
  __ := mk.symm
  map_mul' _ _ := rfl

instance : CommSemiring NatMaxAdd where
  nsmul := nsmulRec
  left_distrib _ _ _ := mk.symm.injective (Nat.mul_max_mul_left ..).symm
  right_distrib _ _ _ := mk.symm.injective (Nat.mul_max_mul_right ..).symm

instance : IsDomain NatMaxAdd := NatMaxAdd.mulEquiv.isDomain

theorem natCast_eq_one (n : ℕ) : ∀ [NeZero n], (n : NatMaxAdd) = 1 := by
  induction' n with n ih
  · intro; exact (NeZero.ne 0 rfl).elim
  obtain _ | n := n
  · intro; rfl
  · rw [Nat.cast_succ, ih]; intro; rfl

theorem not_isCancelAdd : ¬ IsCancelAdd NatMaxAdd := fun h ↦ by cases h.1.1 1 0 1 rfl

open Polynomial

theorem not_isDomain_polynomial : ¬ IsDomain NatMaxAdd[X] :=
  isDomain_iff.not.mpr fun h ↦ not_isCancelAdd h.2

end NatMaxAdd

theorem not_isDomain_commSemiring_imp_isDomain_polynomial :
    ¬ (∀ (R : Type) [CommSemiring R] [IsDomain R], IsDomain (Polynomial R)) :=
  fun h ↦ NatMaxAdd.not_isDomain_polynomial (h _)
