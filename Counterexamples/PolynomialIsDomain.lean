/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.GroupWithZero.TransferInstance
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# A commutative semiring that is a domain whose polynomial semiring is not a domain

`NatMaxAdd` is the natural numbers equipped with the usual multiplication but with maximum as
addition. Under these operations it is a commutative semiring that is a domain.
However, in the polynomial semiring `NatMaxAdd[X]`, we have the identity
`(X + 1) * (X ^ 2 + 1) = (X + 1) * (X ^ 2 + X + 1)`, so `NatMaxAdd[X]` is not a domain.
This shows `Polynomial.instIsDomain` cannot be generalized from `Ring` to `Semiring`.

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

open Polynomial

theorem not_isDomain_polynomial_natMaxAdd : ¬ IsDomain NatMaxAdd[X] :=
  have hX1 : (X + 1 : NatMaxAdd[X]) ≠ 0 := X_add_C_ne_zero _
  have ne : (X ^ 2 + 1 : NatMaxAdd[X]) ≠ (X ^ 2 + X + 1) := fun h ↦ by
    have : coeff (1 : NatMaxAdd[X]) 1 = 0 := by rw [← C_1, coeff_C, if_neg one_ne_zero]
    simpa [this] using congr(coeff $h 1)
  fun h ↦ ne <| h.1.1.1 hX1 <| by
    ring_nf
    rw [← Nat.cast_ofNat (R := NatMaxAdd[X]) (n := 2),
      ← C_eq_natCast, natCast_eq_one, C_1, mul_one, mul_one]

end NatMaxAdd
