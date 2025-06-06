/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/

-- Porting note: used to import `tactic.pi_instances`

namespace Pi

universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

variable (i : I)

instance distrib [∀ i, Distrib <| f i] : Distrib (∀ i : I, f i) :=
  { add := (· + ·)
    mul := (· * ·)
    left_distrib := by intros; ext; exact mul_add _ _ _
    right_distrib := by intros; ext; exact add_mul _ _ _}

instance hasDistribNeg [∀ i, Mul (f i)] [∀ i, HasDistribNeg (f i)] : HasDistribNeg (∀ i, f i) where
  neg_mul _ _ := funext fun _ ↦ neg_mul _ _
  mul_neg _ _ := funext fun _ ↦ mul_neg _ _

instance addMonoidWithOne [∀ i, AddMonoidWithOne (f i)] : AddMonoidWithOne (∀ i, f i) where
  natCast n _ := n
  natCast_zero := funext fun _ ↦ AddMonoidWithOne.natCast_zero
  natCast_succ n := funext fun _ ↦ AddMonoidWithOne.natCast_succ n

instance addGroupWithOne [∀ i, AddGroupWithOne (f i)] : AddGroupWithOne (∀ i, f i) where
  __ := addGroup
  __ := addMonoidWithOne
  intCast n _ := n
  intCast_ofNat n := funext fun _ ↦ AddGroupWithOne.intCast_ofNat n
  intCast_negSucc n := funext fun _ ↦ AddGroupWithOne.intCast_negSucc n

instance nonUnitalNonAssocSemiring [∀ i, NonUnitalNonAssocSemiring <| f i] :
    NonUnitalNonAssocSemiring (∀ i : I, f i) :=
  { Pi.distrib, Pi.addCommMonoid, Pi.mulZeroClass with }

instance nonUnitalSemiring [∀ i, NonUnitalSemiring <| f i] : NonUnitalSemiring (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocSemiring, Pi.semigroupWithZero with }

instance nonAssocSemiring [∀ i, NonAssocSemiring <| f i] : NonAssocSemiring (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocSemiring, Pi.mulZeroOneClass, Pi.addMonoidWithOne with }

instance semiring [∀ i, Semiring <| f i] : Semiring (∀ i : I, f i) :=
  { Pi.nonUnitalSemiring, Pi.nonAssocSemiring, Pi.monoidWithZero with }

instance nonUnitalCommSemiring [∀ i, NonUnitalCommSemiring <| f i] :
    NonUnitalCommSemiring (∀ i : I, f i) :=
  { Pi.nonUnitalSemiring, Pi.commSemigroup with }

instance commSemiring [∀ i, CommSemiring <| f i] : CommSemiring (∀ i : I, f i) :=
  { Pi.semiring, Pi.commMonoid with }

instance nonUnitalNonAssocRing [∀ i, NonUnitalNonAssocRing <| f i] :
    NonUnitalNonAssocRing (∀ i : I, f i) :=
  { Pi.addCommGroup, Pi.nonUnitalNonAssocSemiring with }

instance nonUnitalRing [∀ i, NonUnitalRing <| f i] : NonUnitalRing (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocRing, Pi.nonUnitalSemiring with }

instance nonAssocRing [∀ i, NonAssocRing <| f i] : NonAssocRing (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocRing, Pi.nonAssocSemiring, Pi.addGroupWithOne with }

instance ring [∀ i, Ring <| f i] : Ring (∀ i : I, f i) :=
  { Pi.semiring, Pi.addCommGroup, Pi.addGroupWithOne with }

instance nonUnitalCommRing [∀ i, NonUnitalCommRing <| f i] : NonUnitalCommRing (∀ i : I, f i) :=
  { Pi.nonUnitalRing, Pi.commSemigroup with }

instance commRing [∀ i, CommRing <| f i] : CommRing (∀ i : I, f i) :=
  { Pi.ring, Pi.commSemiring with }

/-- A family of non-unital ring homomorphisms `f a : γ →ₙ+* β a` defines a non-unital ring
homomorphism `Pi.nonUnitalRingHom f : γ →+* Π a, β a` given by
`Pi.nonUnitalRingHom f x b = f b x`. -/
@[simps]
protected def nonUnitalRingHom {γ : Type w} [∀ i, NonUnitalNonAssocSemiring (f i)]
    [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i) : γ →ₙ+* ∀ i, f i :=
  { Pi.mulHom fun i => (g i).toMulHom, Pi.addMonoidHom fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

theorem nonUnitalRingHom_injective {γ : Type w} [Nonempty I]
    [∀ i, NonUnitalNonAssocSemiring (f i)] [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.nonUnitalRingHom g) :=
  mulHom_injective (fun i => (g i).toMulHom) hg

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`Pi.ringHom f : γ →+* Π a, β a` given by `Pi.ringHom f x b = f b x`. -/
@[simps]
protected def ringHom {γ : Type w} [∀ i, NonAssocSemiring (f i)] [NonAssocSemiring γ]
    (g : ∀ i, γ →+* f i) : γ →+* ∀ i, f i :=
  { Pi.monoidHom fun i => (g i).toMonoidHom, Pi.addMonoidHom fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

theorem ringHom_injective {γ : Type w} [Nonempty I] [∀ i, NonAssocSemiring (f i)]
    [NonAssocSemiring γ] (g : ∀ i, γ →+* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.ringHom g) :=
  monoidHom_injective (fun i => (g i).toMonoidHom) hg

end Pi

section NonUnitalRingHom

universe u v

variable {I : Type u}

/-- Evaluation of functions into an indexed collection of non-unital rings at a point is a
non-unital ring homomorphism. This is `Function.eval` as a `NonUnitalRingHom`. -/
@[simps!]
def Pi.evalNonUnitalRingHom (f : I → Type v) [∀ i, NonUnitalNonAssocSemiring (f i)] (i : I) :
    (∀ i, f i) →ₙ+* f i :=
  { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }

/-- `Function.const` as a `NonUnitalRingHom`. -/
@[simps]
def Pi.constNonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring β] : β →ₙ+* α → β :=
  { Pi.nonUnitalRingHom fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }

/-- Non-unital ring homomorphism between the function spaces `I → α` and `I → β`, induced by a
non-unital ring homomorphism `f` between `α` and `β`. -/
@[simps]
protected def NonUnitalRingHom.compLeft {α β : Type*} [NonUnitalNonAssocSemiring α]
    [NonUnitalNonAssocSemiring β] (f : α →ₙ+* β) (I : Type*) : (I → α) →ₙ+* I → β :=
  { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end NonUnitalRingHom

section RingHom

universe u v

variable {I : Type u}

/-- Evaluation of functions into an indexed collection of rings at a point is a ring
homomorphism. This is `Function.eval` as a `RingHom`. -/
@[simps!]
def Pi.evalRingHom (f : I → Type v) [∀ i, NonAssocSemiring (f i)] (i : I) : (∀ i, f i) →+* f i :=
  { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }

instance (f : I → Type*) [∀ i, Semiring (f i)] (i) :
    RingHomSurjective (Pi.evalRingHom f i) where
  is_surjective x := ⟨by classical exact (if h : · = i then h ▸ x else 0), by simp⟩

/-- `Function.const` as a `RingHom`. -/
@[simps]
def Pi.constRingHom (α β : Type*) [NonAssocSemiring β] : β →+* α → β :=
  { Pi.ringHom fun _ => RingHom.id β with toFun := Function.const _ }

/-- Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a ring
homomorphism `f` between `α` and `β`. -/
@[simps]
protected def RingHom.compLeft {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) (I : Type*) : (I → α) →+* I → β :=
  { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end RingHom
