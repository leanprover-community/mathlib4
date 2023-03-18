/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.ring.opposite
! leanprover-community/mathlib commit fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Hom.Ring

/-!
# Ring structures on the multiplicative opposite
-/


universe u v

variable (α : Type u)

namespace MulOpposite

instance [Distrib α] : Distrib αᵐᵒᵖ :=
  { MulOpposite.instAddMulOpposite α, MulOpposite.instMulMulOpposite α with
    left_distrib := fun x y z => unop_injective <| add_mul (unop y) (unop z) (unop x),
    right_distrib := fun x y z => unop_injective <| mul_add (unop z) (unop x) (unop y) }

instance [MulZeroClass α] : MulZeroClass αᵐᵒᵖ where
  zero := 0
  mul := (· * ·)
  zero_mul x := unop_injective <| mul_zero <| unop x
  mul_zero x := unop_injective <| zero_mul <| unop x

instance [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ :=
  { MulOpposite.instMulZeroClassMulOpposite α, MulOpposite.instMulOneClassMulOpposite α with }

instance [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ :=
  { MulOpposite.instSemigroupMulOpposite α, MulOpposite.instMulZeroClassMulOpposite α with }

instance [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ :=
  { MulOpposite.instMonoidMulOpposite α, MulOpposite.instMulZeroOneClassMulOpposite α with }

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵐᵒᵖ :=
  { MulOpposite.instAddCommMonoidMulOpposite α, MulOpposite.instMulZeroClassMulOpposite α,
    MulOpposite.instDistribMulOpposite α with }

instance [NonUnitalSemiring α] : NonUnitalSemiring αᵐᵒᵖ :=
  { MulOpposite.instSemigroupWithZeroMulOpposite α,
    MulOpposite.instNonUnitalNonAssocSemiringMulOpposite α with }

instance [NonAssocSemiring α] : NonAssocSemiring αᵐᵒᵖ :=
  { MulOpposite.instAddMonoidWithOneMulOpposite α, MulOpposite.instMulZeroOneClassMulOpposite α,
    MulOpposite.instNonUnitalNonAssocSemiringMulOpposite α with }

instance [Semiring α] : Semiring αᵐᵒᵖ :=
  { MulOpposite.instNonUnitalSemiringMulOpposite α, MulOpposite.instNonAssocSemiringMulOpposite α,
    MulOpposite.instMonoidWithZeroMulOpposite α with }

instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵐᵒᵖ :=
  { MulOpposite.instNonUnitalSemiringMulOpposite α,
    MulOpposite.instCommSemigroupMulOpposite α with }

instance [CommSemiring α] : CommSemiring αᵐᵒᵖ :=
  { MulOpposite.instSemiringMulOpposite α, MulOpposite.instCommSemigroupMulOpposite α with }

instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵐᵒᵖ :=
  { MulOpposite.instAddCommGroupMulOpposite α, MulOpposite.instMulZeroClassMulOpposite α,
    MulOpposite.instDistribMulOpposite α with }

instance [NonUnitalRing α] : NonUnitalRing αᵐᵒᵖ :=
  { MulOpposite.instAddCommGroupMulOpposite α, MulOpposite.instSemigroupWithZeroMulOpposite α,
    MulOpposite.instDistribMulOpposite α with }

instance [NonAssocRing α] : NonAssocRing αᵐᵒᵖ :=
  { MulOpposite.instAddCommGroupMulOpposite α, MulOpposite.instMulZeroOneClassMulOpposite α,
    MulOpposite.instDistribMulOpposite α, MulOpposite.instAddGroupWithOneMulOpposite α with }

instance [Ring α] : Ring αᵐᵒᵖ :=
  { MulOpposite.instMonoidMulOpposite α, MulOpposite.instNonAssocRingMulOpposite α with }

instance [NonUnitalCommRing α] : NonUnitalCommRing αᵐᵒᵖ :=
  { MulOpposite.instNonUnitalRingMulOpposite α,
    MulOpposite.instNonUnitalCommSemiringMulOpposite α with }

instance [CommRing α] : CommRing αᵐᵒᵖ :=
  { MulOpposite.instRingMulOpposite α, MulOpposite.instCommSemiringMulOpposite α with }

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐᵒᵖ where
eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
    Or.casesOn (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
      (fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl <| unop_injective <| hx

instance [Ring α] [IsDomain α] : IsDomain αᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance [GroupWithZero α] : GroupWithZero αᵐᵒᵖ :=
  { MulOpposite.instMonoidWithZeroMulOpposite α, MulOpposite.instDivInvMonoidMulOpposite α,
    MulOpposite.instNontrivialMulOpposite α with
    mul_inv_cancel := fun _ hx => unop_injective <| inv_mul_cancel <| unop_injective.ne hx,
    inv_zero := unop_injective inv_zero }

end MulOpposite

namespace AddOpposite

instance [Distrib α] : Distrib αᵃᵒᵖ :=
  { AddOpposite.instAddAddOpposite α, @AddOpposite.instMulAddOpposite α _ with
    left_distrib := fun x y z => unop_injective <| mul_add (unop x) (unop z) (unop y),
    right_distrib := fun x y z => unop_injective <| add_mul (unop y) (unop x) (unop z) }

instance [MulZeroClass α] : MulZeroClass αᵃᵒᵖ where
  zero := 0
  mul := (· * ·)
  zero_mul x := unop_injective <| zero_mul <| unop x
  mul_zero x := unop_injective <| mul_zero <| unop x

instance [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ :=
  { AddOpposite.instMulZeroClassAddOpposite α, AddOpposite.instMulOneClassAddOpposite α with }

instance [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ :=
  { AddOpposite.instSemigroupAddOpposite α, AddOpposite.instMulZeroClassAddOpposite α with }

instance [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ :=
  { AddOpposite.instMonoidAddOpposite α, AddOpposite.instMulZeroOneClassAddOpposite α with }

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵃᵒᵖ :=
  { AddOpposite.instAddCommMonoidAddOpposite α, AddOpposite.instMulZeroClassAddOpposite α,
    AddOpposite.instDistribAddOpposite α with }

instance [NonUnitalSemiring α] : NonUnitalSemiring αᵃᵒᵖ :=
  { AddOpposite.instSemigroupWithZeroAddOpposite α,
    AddOpposite.instNonUnitalNonAssocSemiringAddOpposite α with }

instance [NonAssocSemiring α] : NonAssocSemiring αᵃᵒᵖ :=
  { AddOpposite.instMulZeroOneClassAddOpposite α,
    AddOpposite.instNonUnitalNonAssocSemiringAddOpposite α with }

instance [Semiring α] : Semiring αᵃᵒᵖ :=
  { AddOpposite.instNonUnitalSemiringAddOpposite α, AddOpposite.instNonAssocSemiringAddOpposite α,
    AddOpposite.instMonoidWithZeroAddOpposite α with }

instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵃᵒᵖ :=
  { AddOpposite.instNonUnitalSemiringAddOpposite α,
    AddOpposite.instCommSemigroupAddOpposite α with }

instance [CommSemiring α] : CommSemiring αᵃᵒᵖ :=
  { AddOpposite.instSemiringAddOpposite α, AddOpposite.instCommSemigroupAddOpposite α with }

instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵃᵒᵖ :=
  { AddOpposite.instAddCommGroupAddOpposite α, AddOpposite.instMulZeroClassAddOpposite α,
    AddOpposite.instDistribAddOpposite α with }

instance [NonUnitalRing α] : NonUnitalRing αᵃᵒᵖ :=
  { AddOpposite.instAddCommGroupAddOpposite α, AddOpposite.instSemigroupWithZeroAddOpposite α,
    AddOpposite.instDistribAddOpposite α with }

instance [NonAssocRing α] : NonAssocRing αᵃᵒᵖ :=
  { AddOpposite.instAddCommGroupAddOpposite α, AddOpposite.instMulZeroOneClassAddOpposite α,
    AddOpposite.instDistribAddOpposite α with }

instance [Ring α] : Ring αᵃᵒᵖ :=
  { AddOpposite.instAddCommGroupAddOpposite α, AddOpposite.instMonoidAddOpposite α,
    AddOpposite.instSemiringAddOpposite α with }

instance [NonUnitalCommRing α] : NonUnitalCommRing αᵃᵒᵖ :=
  { AddOpposite.instNonUnitalRingAddOpposite α,
    AddOpposite.instNonUnitalCommSemiringAddOpposite α with }

instance [CommRing α] : CommRing αᵃᵒᵖ :=
  { AddOpposite.instRingAddOpposite α, AddOpposite.instCommSemiringAddOpposite α with }

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃᵒᵖ where
eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
  Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
  (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

instance [Ring α] [IsDomain α] : IsDomain αᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance [GroupWithZero α] : GroupWithZero αᵃᵒᵖ :=
  { AddOpposite.instMonoidWithZeroAddOpposite α, AddOpposite.instDivInvMonoidAddOpposite α,
    AddOpposite.instNontrivialAddOpposite α with
    mul_inv_cancel := fun _ hx => unop_injective <| mul_inv_cancel <| unop_injective.ne hx,
    inv_zero := unop_injective inv_zero }

end AddOpposite

open MulOpposite

/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def NonUnitalRingHom.toOpposite {R S : Type _} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align non_unital_ring_hom.to_opposite NonUnitalRingHom.toOpposite

/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def NonUnitalRingHom.fromOpposite {R S : Type _} [NonUnitalNonAssocSemiring R]
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
def RingHom.toOpposite {R S : Type _} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align ring_hom.to_opposite RingHom.toOpposite
#align ring_hom.to_opposite_apply RingHom.toOpposite_apply

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def RingHom.fromOpposite {R S : Type _} [Semiring R] [Semiring S] (f : R →+* S)
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
