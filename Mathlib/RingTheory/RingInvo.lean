/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Opposite

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notation

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/

variable {F : Type*} (R : Type*)

/-- A ring involution -/
structure RingInvo [Semiring R] extends R ≃+* Rᵐᵒᵖ where
  /-- The requirement that the ring homomorphism is its own inverse -/
  involution' : ∀ x, (toFun (toFun x).unop).unop = x

/-- The equivalence of rings underlying a ring involution. -/
add_decl_doc RingInvo.toRingEquiv

/-- `RingInvoClass F R` states that `F` is a type of ring involutions.
You should extend this class when you extend `RingInvo`. -/
class RingInvoClass (F R : Type*) [Semiring R] [EquivLike F R Rᵐᵒᵖ] : Prop
  extends RingEquivClass F R Rᵐᵒᵖ where
  /-- Every ring involution must be its own inverse -/
  involution : ∀ (f : F) (x), (f (f x).unop).unop = x


/-- Turn an element of a type `F` satisfying `RingInvoClass F R` into an actual
`RingInvo`. This is declared as the default coercion from `F` to `RingInvo R`. -/
@[coe]
def RingInvoClass.toRingInvo {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ] [RingInvoClass F R] (f : F) :
    RingInvo R :=
  { (f : R ≃+* Rᵐᵒᵖ) with involution' := RingInvoClass.involution f }

namespace RingInvo

variable {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ]

/-- Any type satisfying `RingInvoClass` can be cast into `RingInvo` via
`RingInvoClass.toRingInvo`. -/
instance [RingInvoClass F R] : CoeTC F (RingInvo R) :=
  ⟨RingInvoClass.toRingInvo⟩

instance : EquivLike (RingInvo R) R Rᵐᵒᵖ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    rcases e with ⟨⟨tE, _⟩, _⟩; rcases f with ⟨⟨tF, _⟩, _⟩
    cases tE
    cases tF
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance : RingInvoClass (RingInvo R) R where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  involution f := f.involution'

/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
    right_inv := fun _ => MulOpposite.unop_injective <| involution _
    involution' := involution }

@[simp]
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x

-- Porting note: remove Coe instance, not needed
-- instance hasCoeToRingEquiv : Coe (RingInvo R) (R ≃+* Rᵐᵒᵖ) :=
--   ⟨RingInvo.toRingEquiv⟩

@[norm_cast]
theorem coe_ringEquiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl

theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff

end RingInvo

open RingInvo

section CommRing

variable [CommRing R]

/-- The identity function of a `CommRing` is a ring involution. -/
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun _ => rfl }

instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩

end CommRing
