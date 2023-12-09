/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Hom.Ring.Defs

#align_import algebra.ring.opposite from "leanprover-community/mathlib"@"76de8ae01554c3b37d66544866659ff174e66e1f"

/-!
# Ring structures on the multiplicative opposite
-/


universe u v

variable (α : Type u)

namespace MulOpposite

instance distrib [Distrib α] : Distrib αᵐᵒᵖ :=
  { MulOpposite.add α, MulOpposite.mul α with
    left_distrib := fun x y z => unop_injective <| add_mul (unop y) (unop z) (unop x),
    right_distrib := fun x y z => unop_injective <| mul_add (unop z) (unop x) (unop y) }

instance mulZeroClass [MulZeroClass α] : MulZeroClass αᵐᵒᵖ where
  zero := 0
  mul := (· * ·)
  zero_mul x := unop_injective <| mul_zero <| unop x
  mul_zero x := unop_injective <| zero_mul <| unop x

instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ :=
  { MulOpposite.mulZeroClass α, MulOpposite.mulOneClass α with }

instance semigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ :=
  { MulOpposite.semigroup α, MulOpposite.mulZeroClass α with }

instance monoidWithZero [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.mulZeroOneClass α with }

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵐᵒᵖ :=
  { MulOpposite.addCommMonoid α, MulOpposite.mulZeroClass α, MulOpposite.distrib α with }

instance nonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring αᵐᵒᵖ :=
  { MulOpposite.semigroupWithZero α, MulOpposite.nonUnitalNonAssocSemiring α with }

instance nonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring αᵐᵒᵖ :=
  { MulOpposite.addMonoidWithOne α, MulOpposite.mulZeroOneClass α,
    MulOpposite.nonUnitalNonAssocSemiring α with }

instance semiring [Semiring α] : Semiring αᵐᵒᵖ :=
  { MulOpposite.nonUnitalSemiring α, MulOpposite.nonAssocSemiring α,
    MulOpposite.monoidWithZero α with }

instance nonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵐᵒᵖ :=
  { MulOpposite.nonUnitalSemiring α, MulOpposite.commSemigroup α with }

instance commSemiring [CommSemiring α] : CommSemiring αᵐᵒᵖ :=
  { MulOpposite.semiring α, MulOpposite.commSemigroup α with }

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵐᵒᵖ :=
  { MulOpposite.addCommGroup α, MulOpposite.mulZeroClass α,
    MulOpposite.distrib α with }

instance nonUnitalRing [NonUnitalRing α] : NonUnitalRing αᵐᵒᵖ :=
  { MulOpposite.addCommGroup α, MulOpposite.semigroupWithZero α,
    MulOpposite.distrib α with }

instance nonAssocRing [NonAssocRing α] : NonAssocRing αᵐᵒᵖ :=
  { MulOpposite.addCommGroup α, MulOpposite.mulZeroOneClass α,
    MulOpposite.distrib α, MulOpposite.addGroupWithOne α with }

instance ring [Ring α] : Ring αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.nonAssocRing α with }

instance nonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing αᵐᵒᵖ :=
  { MulOpposite.nonUnitalRing α,
    MulOpposite.nonUnitalCommSemiring α with }

instance commRing [CommRing α] : CommRing αᵐᵒᵖ :=
  { MulOpposite.ring α, MulOpposite.commSemiring α with }

instance noZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
      Or.casesOn (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
        (fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl <| unop_injective <| hx

instance isDomain [Ring α] [IsDomain α] : IsDomain αᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance groupWithZero [GroupWithZero α] : GroupWithZero αᵐᵒᵖ :=
  { MulOpposite.monoidWithZero α, MulOpposite.divInvMonoid α,
    MulOpposite.nontrivial α with
    mul_inv_cancel := fun _ hx => unop_injective <| inv_mul_cancel <| unop_injective.ne hx,
    inv_zero := unop_injective inv_zero }

end MulOpposite

namespace AddOpposite

instance distrib [Distrib α] : Distrib αᵃᵒᵖ :=
  { AddOpposite.add α, @AddOpposite.mul α _ with
    left_distrib := fun x y z => unop_injective <| mul_add (unop x) (unop z) (unop y),
    right_distrib := fun x y z => unop_injective <| add_mul (unop y) (unop x) (unop z) }

instance mulZeroClass [MulZeroClass α] : MulZeroClass αᵃᵒᵖ where
  zero := 0
  mul := (· * ·)
  zero_mul x := unop_injective <| zero_mul <| unop x
  mul_zero x := unop_injective <| mul_zero <| unop x

instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ :=
  { AddOpposite.mulZeroClass α, AddOpposite.mulOneClass α with }

instance semigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ :=
  { AddOpposite.semigroup α, AddOpposite.mulZeroClass α with }

instance monoidWithZero [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ :=
  { AddOpposite.monoid α, AddOpposite.mulZeroOneClass α with }

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵃᵒᵖ :=
  { AddOpposite.addCommMonoid α, AddOpposite.mulZeroClass α, AddOpposite.distrib α with }

instance nonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring αᵃᵒᵖ :=
  { AddOpposite.semigroupWithZero α, AddOpposite.nonUnitalNonAssocSemiring α with }

instance nonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring αᵃᵒᵖ :=
  { AddOpposite.mulZeroOneClass α, AddOpposite.nonUnitalNonAssocSemiring α,
    AddOpposite.addCommMonoidWithOne _ with }

instance semiring [Semiring α] : Semiring αᵃᵒᵖ :=
  { AddOpposite.nonUnitalSemiring α, AddOpposite.nonAssocSemiring α,
    AddOpposite.monoidWithZero α with }

instance nonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵃᵒᵖ :=
  { AddOpposite.nonUnitalSemiring α, AddOpposite.commSemigroup α with }

instance commSemiring [CommSemiring α] : CommSemiring αᵃᵒᵖ :=
  { AddOpposite.semiring α, AddOpposite.commSemigroup α with }

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵃᵒᵖ :=
  { AddOpposite.addCommGroup α, AddOpposite.mulZeroClass α, AddOpposite.distrib α with }

instance nonUnitalRing [NonUnitalRing α] : NonUnitalRing αᵃᵒᵖ :=
  { AddOpposite.addCommGroup α, AddOpposite.semigroupWithZero α, AddOpposite.distrib α with }

instance nonAssocRing [NonAssocRing α] : NonAssocRing αᵃᵒᵖ :=
  { AddOpposite.addCommGroupWithOne α, AddOpposite.mulZeroOneClass α, AddOpposite.distrib α with }

instance ring [Ring α] : Ring αᵃᵒᵖ :=
  { AddOpposite.nonAssocRing α, AddOpposite.semiring α with }

instance nonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing αᵃᵒᵖ :=
  { AddOpposite.nonUnitalRing α, AddOpposite.nonUnitalCommSemiring α with }

instance commRing [CommRing α] : CommRing αᵃᵒᵖ :=
  { AddOpposite.ring α, AddOpposite.commSemiring α with }

instance noZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
    Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
    (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

instance isDomain [Ring α] [IsDomain α] : IsDomain αᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance groupWithZero [GroupWithZero α] : GroupWithZero αᵃᵒᵖ :=
  { AddOpposite.monoidWithZero α, AddOpposite.divInvMonoid α,
    AddOpposite.nontrivial α with
    mul_inv_cancel := fun _ hx => unop_injective <| mul_inv_cancel <| unop_injective.ne hx,
    inv_zero := unop_injective inv_zero }

end AddOpposite

open MulOpposite

/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align non_unital_ring_hom.to_opposite NonUnitalRingHom.toOpposite

/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def NonUnitalRingHom.fromOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →ₙ+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }
#align non_unital_ring_hom.from_opposite NonUnitalRingHom.fromOpposite

/-- A non-unital ring hom `α →ₙ+* β` can equivalently be viewed as a non-unital ring hom
`αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def NonUnitalRingHom.op {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (α →ₙ+* β) ≃ (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }
  left_inv _ := rfl
  right_inv _ := rfl
#align non_unital_ring_hom.op NonUnitalRingHom.op

/-- The 'unopposite' of a non-unital ring hom `αᵐᵒᵖ →ₙ+* βᵐᵒᵖ`. Inverse to
`NonUnitalRingHom.op`. -/
@[simp]
def NonUnitalRingHom.unop {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ) ≃ (α →ₙ+* β) :=
  NonUnitalRingHom.op.symm
#align non_unital_ring_hom.unop NonUnitalRingHom.unop

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align ring_hom.to_opposite RingHom.toOpposite
#align ring_hom.to_opposite_apply RingHom.toOpposite_apply

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def RingHom.fromOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }
#align ring_hom.from_opposite RingHom.fromOpposite
#align ring_hom.from_opposite_apply RingHom.fromOpposite_apply

/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
def RingHom.op {α β} [NonAssocSemiring α] [NonAssocSemiring β] :
    (α →+* β) ≃ (αᵐᵒᵖ →+* βᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }
  left_inv _ := rfl
  right_inv _ := rfl
#align ring_hom.op RingHom.op
#align ring_hom.op_symm_apply_apply RingHom.op_symm_apply_apply

/-- The 'unopposite' of a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. Inverse to `RingHom.op`. -/
@[simp]
def RingHom.unop {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (αᵐᵒᵖ →+* βᵐᵒᵖ) ≃ (α →+* β) :=
  RingHom.op.symm
#align ring_hom.unop RingHom.unop
