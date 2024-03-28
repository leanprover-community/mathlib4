/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Ring.Hom.Defs

#align_import algebra.ring.opposite from "leanprover-community/mathlib"@"76de8ae01554c3b37d66544866659ff174e66e1f"

/-!
# Ring structures on the multiplicative opposite
-/

variable {α : Type*}

namespace MulOpposite

instance instDistrib [Distrib α] : Distrib αᵐᵒᵖ where
  toAdd := instAdd
  toMul := instMul
  left_distrib _ _ _ := unop_injective <| add_mul _ _ _
  right_distrib _ _ _ := unop_injective <| mul_add _ _ _

instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵐᵒᵖ where
  toZero := instZero
  toMul := instMul
  zero_mul _ := unop_injective <| mul_zero _
  mul_zero _ := unop_injective <| zero_mul _

instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ where
  toMulOneClass := instMulOneClass
  __ := instMulZeroClass

instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ where
  toSemigroup := instSemigroup
  __ := instMulZeroClass

instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instMulZeroOneClass

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring αᵐᵒᵖ where
  toAddCommMonoid := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

instance instNonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring αᵐᵒᵖ where
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

instance instNonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring αᵐᵒᵖ where
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

instance instSemiring [Semiring α] : Semiring αᵐᵒᵖ where
  toNonUnitalSemiring := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

instance instNonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵐᵒᵖ where
  toNonUnitalSemiring := instNonUnitalSemiring
  __ := instCommSemigroup

instance instCommSemiring [CommSemiring α] : CommSemiring αᵐᵒᵖ where
  toSemiring := instSemiring
  __ := instCommMonoid

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵐᵒᵖ where
  toAddCommGroup := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

instance instNonUnitalRing [NonUnitalRing α] : NonUnitalRing αᵐᵒᵖ where
  toNonUnitalNonAssocRing := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

instance instNonAssocRing [NonAssocRing α] : NonAssocRing αᵐᵒᵖ where
  toNonUnitalNonAssocRing := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

instance instRing [Ring α] : Ring αᵐᵒᵖ where
  toSemiring := instSemiring
  __ := instAddCommGroupWithOne

instance instNonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing αᵐᵒᵖ where
  toNonUnitalRing := instNonUnitalRing
  __ := instNonUnitalCommSemiring

instance instCommRing [CommRing α] : CommRing αᵐᵒᵖ where
  toRing := instRing
  __ := instCommMonoid

instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
      Or.casesOn (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
        (fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl <| unop_injective <| hx

instance instIsDomain [Ring α] [IsDomain α] : IsDomain αᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵐᵒᵖ where
  toMonoidWithZero := instMonoidWithZero
  __ := instDivInvMonoid
  toNontrivial := instNontrivial
  mul_inv_cancel _ hx := unop_injective <| inv_mul_cancel <| unop_injective.ne hx
  inv_zero := unop_injective inv_zero

end MulOpposite

namespace AddOpposite

instance instDistrib [Distrib α] : Distrib αᵃᵒᵖ where
  toAdd := instAdd
  toMul := instMul
  left_distrib _ _ _ := unop_injective <| mul_add _ _ _
  right_distrib _ _ _ := unop_injective <| add_mul _ _ _

instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵃᵒᵖ where
  toZero := instZero
  toMul := instMul
  zero_mul _ := unop_injective <| zero_mul _
  mul_zero _ := unop_injective <| mul_zero _

instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ where
  toMulOneClass := instMulOneClass
  __ := instMulZeroClass

instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ where
  toSemigroup := instSemigroup
  __ := instMulZeroClass

instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ where
  toMonoid := instMonoid
  __ := instMulZeroOneClass

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring αᵃᵒᵖ where
  toAddCommMonoid := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

instance instNonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring αᵃᵒᵖ where
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

instance instNonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring αᵃᵒᵖ where
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

instance instSemiring [Semiring α] : Semiring αᵃᵒᵖ where
  toNonUnitalSemiring := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

instance instNonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵃᵒᵖ where
  toNonUnitalSemiring := instNonUnitalSemiring
  __ := instCommSemigroup

instance instCommSemiring [CommSemiring α] : CommSemiring αᵃᵒᵖ where
  toSemiring := instSemiring
  __ := instCommMonoid

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵃᵒᵖ where
  toAddCommGroup := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

instance instNonUnitalRing [NonUnitalRing α] : NonUnitalRing αᵃᵒᵖ where
  toNonUnitalNonAssocRing := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

instance instNonAssocRing [NonAssocRing α] : NonAssocRing αᵃᵒᵖ where
  toNonUnitalNonAssocRing := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

instance instRing [Ring α] : Ring αᵃᵒᵖ where
  toSemiring := instSemiring
  __ := instAddCommGroupWithOne

instance instNonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing αᵃᵒᵖ where
  toNonUnitalRing := instNonUnitalRing
  __ := instNonUnitalCommSemiring

instance instCommRing [CommRing α] : CommRing αᵃᵒᵖ where
  toRing := instRing
  __ := instCommMonoid

instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
    Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
    (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

instance instIsDomain [Ring α] [IsDomain α] : IsDomain αᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵃᵒᵖ where
  toMonoidWithZero := instMonoidWithZero
  __ := instDivInvMonoid
  toNontrivial := instNontrivial
  mul_inv_cancel _ hx := unop_injective <| mul_inv_cancel <| unop_injective.ne hx
  inv_zero := unop_injective inv_zero

end AddOpposite

open MulOpposite

/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := .asFn)]
def NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align non_unital_ring_hom.to_opposite NonUnitalRingHom.toOpposite

/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := .asFn)]
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
@[simps (config := .asFn)]
def RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align ring_hom.to_opposite RingHom.toOpposite
#align ring_hom.to_opposite_apply RingHom.toOpposite_apply

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := .asFn)]
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
