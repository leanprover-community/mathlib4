/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.GroupWithZero.Opposite
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Ring structures on the multiplicative opposite
-/

variable {α : Type*}

namespace MulOpposite

instance instDistrib [Distrib α] : Distrib αᵐᵒᵖ where
  left_distrib _ _ _ := unop_injective <| add_mul _ _ _
  right_distrib _ _ _ := unop_injective <| mul_add _ _ _

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring αᵐᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

instance instNonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring αᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

instance instNonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring αᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

instance instSemiring [Semiring α] : Semiring αᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

instance instNonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup

instance instCommSemiring [CommSemiring α] : CommSemiring αᵐᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵐᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

instance instNonUnitalRing [NonUnitalRing α] : NonUnitalRing αᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

instance instNonAssocRing [NonAssocRing α] : NonAssocRing αᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

instance instRing [Ring α] : Ring αᵐᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne

instance instNonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring

instance instCommRing [CommRing α] : CommRing αᵐᵒᵖ where
  __ := instRing
  __ := instCommMonoid

instance instIsDomain [Ring α] [IsDomain α] : IsDomain αᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵐᵒᵖ where
  __ := instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
  mul_inv_cancel _ hx := unop_injective <| inv_mul_cancel <| unop_injective.ne hx
  inv_zero := unop_injective inv_zero

end MulOpposite

namespace AddOpposite

instance instDistrib [Distrib α] : Distrib αᵃᵒᵖ where
  left_distrib _ _ _ := unop_injective <| mul_add _ _ _
  right_distrib _ _ _ := unop_injective <| add_mul _ _ _

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring αᵃᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

instance instNonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring αᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

instance instNonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring αᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

instance instSemiring [Semiring α] : Semiring αᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

instance instNonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup

instance instCommSemiring [CommSemiring α] : CommSemiring αᵃᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵃᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

instance instNonUnitalRing [NonUnitalRing α] : NonUnitalRing αᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

instance instNonAssocRing [NonAssocRing α] : NonAssocRing αᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

instance instRing [Ring α] : Ring αᵃᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne

instance instNonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing αᵃᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring

instance instCommRing [CommRing α] : CommRing αᵃᵒᵖ where
  __ := instRing
  __ := instCommMonoid

instance instIsDomain [Ring α] [IsDomain α] : IsDomain αᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

end AddOpposite

open MulOpposite

/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := .asFn)]
def NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := .asFn)]
def NonUnitalRingHom.fromOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →ₙ+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A non-unital ring hom `α →ₙ+* β` can equivalently be viewed as a non-unital ring hom
`αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def NonUnitalRingHom.op {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (α →ₙ+* β) ≃ (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The 'unopposite' of a non-unital ring hom `αᵐᵒᵖ →ₙ+* βᵐᵒᵖ`. Inverse to
`NonUnitalRingHom.op`. -/
@[simp]
def NonUnitalRingHom.unop {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ) ≃ (α →ₙ+* β) :=
  NonUnitalRingHom.op.symm

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := .asFn)]
def RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := .asFn)]
def RingHom.fromOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
def RingHom.op {α β} [NonAssocSemiring α] [NonAssocSemiring β] :
    (α →+* β) ≃ (αᵐᵒᵖ →+* βᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The 'unopposite' of a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. Inverse to `RingHom.op`. -/
@[simp]
def RingHom.unop {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (αᵐᵒᵖ →+* βᵐᵒᵖ) ≃ (α →+* β) :=
  RingHom.op.symm
