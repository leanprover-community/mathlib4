/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
import Mathlib.SetTheory.ZFC.Integers

/-! # ZFC Rational Numbers

This file defines the rational numbers in ZFC, based on the integers and using the `ZFInt` type.

-/

namespace ZFSet

section Rationals

abbrev ZFInt' := {x : ZFInt // x ≠ 0}

/-- The equivalence relation on `ℤ × ℤ⋆` that defines the rational numbers. -/
protected abbrev qrel (p q : ZFInt × ZFInt') : Prop := p.1 * q.2 = p.2 * q.1

protected def qrel_eq : Equivalence ZFSet.qrel where
  refl x := ZFInt.mul_comm x.1 x.2
  symm h := by
    unfold ZFSet.qrel at h ⊢
    rw [ZFInt.mul_comm, ←h, ZFInt.mul_comm]
  trans := by
    rintro ⟨p, q, hq⟩ ⟨u, v, hv⟩ ⟨s, t, ht⟩ hpq huv
    dsimp [ZFSet.qrel] at hpq huv ⊢
    -- have : p * v * u * t = q * u * s * v := by
    have : p * t * u * v = q * s * u * v := by
      suffices p * v * u * t = q * u * s * v by
        rw [
          mul_assoc, mul_assoc,
          mul_comm t, mul_comm u,
          ←mul_assoc, ←mul_assoc,
          this,
          mul_assoc, mul_assoc,
          mul_comm u, mul_assoc, mul_comm v,
          ←mul_assoc, ←mul_assoc]
      rw [hpq, mul_assoc, huv, mul_comm v s, ← mul_assoc]
    conv at this =>
      conv => lhs; rw [mul_assoc]
      conv => rhs; rw [mul_assoc]
    by_cases u_mul_v : u * v = 0
    · rw [ZFInt.mul_comm] at u_mul_v
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero u_mul_v hv
      rw [ZFInt.mul_zero, ZFInt.mul_comm] at hpq
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero hpq hv
      rw [ZFInt.zero_mul] at huv
      symm at huv
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero huv hv
      rw [ZFInt.mul_zero, ZFInt.zero_mul]
    · rwa [ZFInt.mul_right_cancel_iff u_mul_v] at this

/-- `ℤ × ℤ⋆` equipped with `qrel` is a setoid. -/
protected instance instSetoidZFIntZFInt' : Setoid (ZFInt × ZFInt') where
  r := ZFSet.qrel
  iseqv := ZFSet.qrel_eq

/-- `ℚ` is defined as `ℤ × ℤ⋆` quotiented by `qrel` -/
abbrev ZFRat := Quotient ZFSet.instSetoidZFIntZFInt'

end Rationals

end ZFSet
