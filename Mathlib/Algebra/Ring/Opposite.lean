/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.GroupWithZero.Opposite
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Int.Cast.Basic

/-!
# Ring structures on the multiplicative opposite
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

variable {R : Type*}

namespace MulOpposite

instance instDistrib [Distrib R] : Distrib Rᵐᵒᵖ where
  left_distrib _ _ _ := unop_injective <| add_mul _ _ _
  right_distrib _ _ _ := unop_injective <| mul_add _ _ _

@[to_additive] instance instNatCast [NatCast R] : NatCast Rᵐᵒᵖ where natCast n := op n
@[to_additive] instance instIntCast [IntCast R] : IntCast Rᵐᵒᵖ where intCast n := op n

@[to_additive (attr := simp, norm_cast)]
theorem op_natCast [NatCast R] (n : ℕ) : op (n : R) = n :=
  rfl

@[to_additive (attr := simp)]
theorem op_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    op (ofNat(n) : R) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem op_intCast [IntCast R] (n : ℤ) : op (n : R) = n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem unop_natCast [NatCast R] (n : ℕ) : unop (n : Rᵐᵒᵖ) = n :=
  rfl

@[to_additive (attr := simp)]
theorem unop_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    unop (ofNat(n) : Rᵐᵒᵖ) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem unop_intCast [IntCast R] (n : ℤ) : unop (n : Rᵐᵒᵖ) = n :=
  rfl

instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne Rᵐᵒᵖ where
  toNatCast := instNatCast
  toAddMonoid := instAddMonoid
  toOne := instOne
  natCast_zero := show op ((0 : ℕ) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show ∀ n, op ((n + 1 : ℕ) : R) = op ↑(n : ℕ) + 1 by simp

instance instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  __ := instAddCommMonoid

instance instAddGroupWithOne [AddGroupWithOne R] : AddGroupWithOne Rᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  toIntCast := instIntCast
  __ := instAddGroup
  intCast_ofNat n := show op ((n : ℤ) : R) = op (n : R) by rw [Int.cast_natCast]
  intCast_negSucc n := show op _ = op (-unop (op ((n + 1 : ℕ) : R))) by simp

instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵐᵒᵖ where
  toAddCommGroup := instAddCommGroup
  __ := instAddGroupWithOne

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring Rᵐᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

instance instSemiring [Semiring R] : Semiring Rᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup

instance instCommSemiring [CommSemiring R] : CommSemiring Rᵐᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵐᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

instance instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

instance instRing [Ring R] : Ring Rᵐᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne

instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring

instance instCommRing [CommRing R] : CommRing Rᵐᵒᵖ where
  __ := instRing
  __ := instCommMonoid

instance instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

end MulOpposite

namespace AddOpposite

instance instDistrib [Distrib R] : Distrib Rᵃᵒᵖ where
  left_distrib _ _ _ := unop_injective <| mul_add _ _ _
  right_distrib _ _ _ := unop_injective <| add_mul _ _ _

-- NOTE: `addMonoidWithOne R → addMonoidWithOne Rᵃᵒᵖ` does not hold
instance instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵃᵒᵖ where
  toNatCast := instNatCast
  toOne := instOne
  __ := instAddCommMonoid
  natCast_zero := show op ((0 : ℕ) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show ∀ n, op ((n + 1 : ℕ) : R) = op ↑(n : ℕ) + 1 by simp [add_comm]

instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵃᵒᵖ where
  toIntCast := instIntCast
  toAddCommGroup := instAddCommGroup
  __ := instAddCommMonoidWithOne
  intCast_ofNat _ := congr_arg op <| Int.cast_natCast _
  intCast_negSucc _ := congr_arg op <| Int.cast_negSucc _

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring Rᵃᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

instance instSemiring [Semiring R] : Semiring Rᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup

instance instCommSemiring [CommSemiring R] : CommSemiring Rᵃᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵃᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

instance instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

instance instRing [Ring R] : Ring Rᵃᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne

instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵃᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring

instance instCommRing [CommRing R] : CommRing Rᵃᵒᵖ where
  __ := instRing
  __ := instCommMonoid

instance instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

end AddOpposite

open MulOpposite

/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps -fullyApplied]
def NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps -fullyApplied]
def NonUnitalRingHom.fromOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →ₙ+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A non-unital ring hom `R →ₙ+* S` can equivalently be viewed as a non-unital ring hom
`Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def NonUnitalRingHom.op {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    (R →ₙ+* S) ≃ (Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }

/-- The 'unopposite' of a non-unital ring hom `Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ`. Inverse to
`NonUnitalRingHom.op`. -/
@[simp]
def NonUnitalRingHom.unop {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    (Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ) ≃ (R →ₙ+* S) :=
  NonUnitalRingHom.op.symm

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps -fullyApplied]
def RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps -fullyApplied]
def RingHom.fromOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A ring hom `R →+* S` can equivalently be viewed as a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
def RingHom.op {R S} [NonAssocSemiring R] [NonAssocSemiring S] :
    (R →+* S) ≃ (Rᵐᵒᵖ →+* Sᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }

/-- The 'unopposite' of a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. Inverse to `RingHom.op`. -/
@[simp]
def RingHom.unop {R S} [NonAssocSemiring R] [NonAssocSemiring S] : (Rᵐᵒᵖ →+* Sᵐᵒᵖ) ≃ (R →+* S) :=
  RingHom.op.symm
