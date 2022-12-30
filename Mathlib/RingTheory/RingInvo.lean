/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau

! This file was ported from Lean 3 source module ring_theory.ring_invo
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Opposite

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notations

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/


variable (R : Type _)

/-- A ring involution -/
structure RingInvo [Semiring R] extends R ≃+* Rᵐᵒᵖ where
/-- The requirement that the ring homomorphism is its own inverse -/
  involution' : ∀ x, (toFun (toFun x).unop).unop = x
#align ring_invo RingInvo

namespace RingInvo

variable {R} [Semiring R]

/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
    right_inv := fun r => MulOpposite.unop_injective <| involution _
    involution' := involution }
#align ring_invo.mk' RingInvo.mk'

instance : CoeFun (RingInvo R) fun _ => R → Rᵐᵒᵖ :=
  ⟨fun f => f.toRingEquiv.toFun⟩

@[simp]
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x
#align ring_invo.involution RingInvo.involution

instance hasCoeToRingEquiv : Coe (RingInvo R) (R ≃+* Rᵐᵒᵖ) :=
  ⟨RingInvo.toRingEquiv⟩
#align ring_invo.has_coe_to_ring_equiv RingInvo.hasCoeToRingEquiv

@[norm_cast]
theorem coe_ring_equiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl
#align ring_invo.coe_ring_equiv RingInvo.coe_ring_equiv

@[simp]
theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff
#align ring_invo.map_eq_zero_iff RingInvo.map_eq_zero_iff

end RingInvo

open RingInvo

section CommRing

variable [CommRing R]

/-- The identity function of a `CommRing` is a ring involution. -/
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun r => rfl }
#align ring_invo.id RingInvo.id

instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩

end CommRing

#lint
