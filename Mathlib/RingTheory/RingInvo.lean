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

-- porting note: TODO this first needs to be backported to mathlib3, see mathlib PR #18175.
/-- `RingInvoClass F R` states that `F` is a type of ring involutions.
You should extend this class when you extend `RingInvo`. -/
class RingInvoClass (F : Type _) (R : outParam (Type _)) [Semiring R] extends
  RingEquivClass F R Rᵐᵒᵖ  where
  /-- Every ring involution must be its own inverse -/
  involution : ∀ (f : F) (x), (f (f x).unop).unop = x
#align ring_invo_class RingInvoClass

/-- Turn an element of a type `F` satisfying `RingInvoClass F R` into an actual
`RingInvo`. This is declared as the default coercion from `F` to `RingInvo R`. -/
@[coe]
def RingInvoClass.toRingInvo {R} [Semiring R] [RingInvoClass F R] (f : F) :
    RingInvo R :=
  { (f : R ≃+* Rᵐᵒᵖ) with involution' := RingInvoClass.involution f }

namespace RingInvo

variable {R} [Semiring R]

/-- Any type satisfying `RingInvoClass` can be cast into `RingInvo` via
`RingInvoClass.toRingInvo`. -/
instance [Semiring R] [RingInvoClass F R] : CoeTC F (RingInvo R) :=
  ⟨RingInvoClass.toRingInvo⟩

instance [Semiring R] : RingInvoClass (RingInvo R) R where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    rcases e with ⟨⟨tE, _⟩, _⟩; rcases f with ⟨⟨tF, _⟩, _⟩
    cases tE
    cases tF
    congr
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  involution f := f.involution'

/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
    right_inv := fun _ => MulOpposite.unop_injective <| involution _
    involution' := involution }
#align ring_invo.mk' RingInvo.mk'

#noalign ring_invo.to_fun_eq_coe

@[simp]
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x
#align ring_invo.involution RingInvo.involution

-- porting note: TODO clarify whether we want a Coe instance like this at all.
-- instance hasCoeToRingEquiv : Coe (RingInvo R) (R ≃+* Rᵐᵒᵖ) :=
--   ⟨RingInvo.toRingEquiv⟩
-- #align ring_invo.has_coe_to_ring_equiv RingInvo.hasCoeToRingEquiv

@[norm_cast]
theorem coe_ring_equiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl
#align ring_invo.coe_ring_equiv RingInvo.coe_ring_equiv

-- porting Note: simp can prove this
-- @[simp]
theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff
#align ring_invo.map_eq_zero_iff RingInvo.map_eq_zero_iff

end RingInvo

open RingInvo

section CommRing

variable [CommRing R]

/-- The identity function of a `CommRing` is a ring involution. -/
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun _ => rfl }
#align ring_invo.id RingInvo.id

instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩

end CommRing
