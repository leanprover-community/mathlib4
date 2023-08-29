/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finite.Defs

#align_import algebra.group.type_tags from "leanprover-community/mathlib"@"2e0975f6a25dd3fbfb9e41556a77f075f6269748"

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `Additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `Order.Synonym`.

## Porting notes

- Since bundled morphism applications that rely on `CoeFun` currently don't work, they are ported
  as `toFoo a` rather than `a.toFoo` for now. (https://github.com/leanprover/lean4/issues/1910)

-/

universe u v

variable {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `Additive α` carries the corresponding
additive structure. -/
def Additive (α : Type*) := α
#align additive Additive

/-- If `α` carries some additive structure, then `Multiplicative α` carries the corresponding
multiplicative structure. -/
def Multiplicative (α : Type*) := α
#align multiplicative Multiplicative

namespace Additive

/-- Reinterpret `x : α` as an element of `Additive α`. -/
def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
#align additive.of_mul Additive.ofMul

/-- Reinterpret `x : Additive α` as an element of `α`. -/
def toMul : Additive α ≃ α := ofMul.symm
#align additive.to_mul Additive.toMul

@[simp]
theorem ofMul_symm_eq : (@ofMul α).symm = toMul :=
  rfl
#align additive.of_mul_symm_eq Additive.ofMul_symm_eq

@[simp]
theorem toMul_symm_eq : (@toMul α).symm = ofMul :=
  rfl
#align additive.to_mul_symm_eq Additive.toMul_symm_eq

end Additive

namespace Multiplicative

/-- Reinterpret `x : α` as an element of `Multiplicative α`. -/
def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩
#align multiplicative.of_add Multiplicative.ofAdd

/-- Reinterpret `x : Multiplicative α` as an element of `α`. -/
def toAdd : Multiplicative α ≃ α := ofAdd.symm
#align multiplicative.to_add Multiplicative.toAdd

@[simp]
theorem ofAdd_symm_eq : (@ofAdd α).symm = toAdd :=
  rfl
#align multiplicative.of_add_symm_eq Multiplicative.ofAdd_symm_eq

@[simp]
theorem toAdd_symm_eq : (@toAdd α).symm = ofAdd :=
  rfl
#align multiplicative.to_add_symm_eq Multiplicative.toAdd_symm_eq

end Multiplicative

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

@[simp]
theorem toAdd_ofAdd (x : α) : toAdd (ofAdd x) = x :=
  rfl
#align to_add_of_add toAdd_ofAdd

@[simp]
theorem ofAdd_toAdd (x : Multiplicative α) : ofAdd (toAdd x) = x :=
  rfl
#align of_add_to_add ofAdd_toAdd

@[simp]
theorem toMul_ofMul (x : α) : toMul (ofMul x) = x :=
  rfl
#align to_mul_of_mul toMul_ofMul

@[simp]
theorem ofMul_toMul (x : Additive α) : ofMul (toMul x) = x :=
  rfl
#align of_mul_to_mul ofMul_toMul

instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨ofMul default⟩

instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨ofAdd default⟩

instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α (by rfl)
                        -- 🎉 no goals

instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α (by rfl)
                        -- 🎉 no goals

instance [h: Infinite α] : Infinite (Additive α) := h

instance [h: Infinite α] : Infinite (Multiplicative α) := h

instance instNontrivialAdditive [Nontrivial α] : Nontrivial (Additive α) :=
  ofMul.injective.nontrivial
#align additive.nontrivial instNontrivialAdditive

instance instNontrivialMultiplicative [Nontrivial α] : Nontrivial (Multiplicative α) :=
  ofAdd.injective.nontrivial
#align multiplicative.nontrivial instNontrivialMultiplicative

instance Additive.add [Mul α] : Add (Additive α) where
  add x y := ofMul (toMul x * toMul y)

instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
  mul x y := ofAdd (toAdd x + toAdd y)

@[simp]
theorem ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y := rfl
#align of_add_add ofAdd_add

@[simp]
theorem toAdd_mul [Add α] (x y : Multiplicative α) : toAdd (x * y) = toAdd x + toAdd y := rfl
#align to_add_mul toAdd_mul

@[simp]
theorem ofMul_mul [Mul α] (x y : α) : ofMul (x * y) = ofMul x + ofMul y := rfl
#align of_mul_mul ofMul_mul

@[simp]
theorem toMul_add [Mul α] (x y : Additive α) : toMul (x + y) = toMul x * toMul y := rfl
#align to_mul_add toMul_add

instance Additive.addSemigroup [Semigroup α] : AddSemigroup (Additive α) :=
  { Additive.add with add_assoc := @mul_assoc α _ }

instance Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.mul with mul_assoc := @add_assoc α _ }

instance Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm := @mul_comm α _ }

instance Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := @add_comm α _ }

instance Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Additive α) :=
  ⟨@mul_left_cancel α _ _⟩

instance Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) :=
  ⟨@add_left_cancel α _ _⟩

instance Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd (Additive α) :=
  ⟨@mul_right_cancel α _ _⟩

instance Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) :=
  ⟨@add_right_cancel α _ _⟩

instance Additive.isCancelAdd [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α) :=
  ⟨⟩

instance Multiplicative.isCancelMul [Add α] [IsCancelAdd α] : IsCancelMul (Multiplicative α) :=
  ⟨⟩

instance Additive.addLeftCancelSemigroup [LeftCancelSemigroup α] :
    AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isLeftCancelAdd with }

instance Multiplicative.leftCancelSemigroup [AddLeftCancelSemigroup α] :
    LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }

instance Additive.addRightCancelSemigroup [RightCancelSemigroup α] :
    AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isRightCancelAdd with }

instance Multiplicative.rightCancelSemigroup [AddRightCancelSemigroup α] :
    RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }

instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

@[simp]
theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 := rfl
#align of_mul_one ofMul_one

@[simp]
theorem ofMul_eq_zero {A : Type*} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 := Iff.rfl
#align of_mul_eq_zero ofMul_eq_zero

@[simp]
theorem toMul_zero [One α] : toMul (0 : Additive α) = 1 := rfl
#align to_mul_zero toMul_zero

instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl
#align of_add_zero ofAdd_zero

@[simp]
theorem ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  Iff.rfl
#align of_add_eq_one ofAdd_eq_one

@[simp]
theorem toAdd_one [Zero α] : toAdd (1 : Multiplicative α) = 0 :=
  rfl
#align to_add_one toAdd_one

instance Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where
  zero := 0
  add := (· + ·)
  zero_add := @one_mul α _
  add_zero := @mul_one α _

instance Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative α) where
  one := 1
  mul := (· * ·)
  one_mul := @zero_add α _
  mul_one := @add_zero α _

instance Additive.addMonoid [h : Monoid α] : AddMonoid (Additive α) :=
  { Additive.addZeroClass, Additive.addSemigroup with
    zero := 0
    add := (· + ·)
    nsmul := @Monoid.npow α h
    nsmul_zero := @Monoid.npow_zero α h
    nsmul_succ := @Monoid.npow_succ α h }

instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) :=
  { Multiplicative.mulOneClass, Multiplicative.semigroup with
    one := 1
    mul := (· * ·)
    npow := @AddMonoid.nsmul α h
    npow_zero := @AddMonoid.nsmul_zero α h
    npow_succ := @AddMonoid.nsmul_succ α h }

instance Additive.addLeftCancelMonoid [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with zero := 0, add := (· + ·) }

instance Multiplicative.leftCancelMonoid [AddLeftCancelMonoid α] :
    LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with one := 1, mul := (· * ·) }

instance Additive.addRightCancelMonoid [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with zero := 0, add := (· + ·) }

instance Multiplicative.rightCancelMonoid [AddRightCancelMonoid α] :
    RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with one := 1, mul := (· * ·) }

instance Additive.addCommMonoid [CommMonoid α] : AddCommMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with zero := 0, add := (· + ·) }

instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with one := 1, mul := (· * ·) }

instance Additive.neg [Inv α] : Neg (Additive α) :=
  ⟨fun x => ofAdd (toMul x)⁻¹⟩

@[simp]
theorem ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x :=
  rfl
#align of_mul_inv ofMul_inv

@[simp]
theorem toMul_neg [Inv α] (x : Additive α) : toMul (-x) = (toMul x)⁻¹ :=
  rfl
#align to_mul_neg toMul_neg

instance Multiplicative.inv [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => ofMul (-toAdd x)⟩

@[simp]
theorem ofAdd_neg [Neg α] (x : α) : ofAdd (-x) = (ofAdd x)⁻¹ :=
  rfl
#align of_add_neg ofAdd_neg

@[simp]
theorem toAdd_inv [Neg α] (x : Multiplicative α) : toAdd x⁻¹ = -(toAdd x) :=
  rfl
#align to_add_inv toAdd_inv

instance Additive.sub [Div α] : Sub (Additive α) where
  sub x y := ofMul (toMul x / toMul y)
#align additive.has_sub Additive.sub

instance Multiplicative.div [Sub α] : Div (Multiplicative α) where
  div x y := ofAdd (toAdd x - toAdd y)
#align multiplicative.has_div Multiplicative.div

@[simp]
theorem ofAdd_sub [Sub α] (x y : α) : ofAdd (x - y) = ofAdd x / ofAdd y :=
  rfl
#align of_add_sub ofAdd_sub

@[simp]
theorem toAdd_div [Sub α] (x y : Multiplicative α) : toAdd (x / y) = toAdd x - toAdd y :=
  rfl
#align to_add_div toAdd_div

@[simp]
theorem ofMul_div [Div α] (x y : α) : ofMul (x / y) = ofMul x - ofMul y :=
  rfl
#align of_mul_div ofMul_div

@[simp]
theorem toMul_sub [Div α] (x y : Additive α) : toMul (x - y) = toMul x / toMul y :=
  rfl
#align to_mul_sub toMul_sub

instance Additive.involutiveNeg [InvolutiveInv α] : InvolutiveNeg (Additive α) :=
  { Additive.neg with neg_neg := @inv_inv α _ }

instance Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.inv with inv_inv := @neg_neg α _ }

instance Additive.subNegMonoid [DivInvMonoid α] : SubNegMonoid (Additive α) :=
  { Additive.neg, Additive.sub, Additive.addMonoid with
    sub_eq_add_neg := @div_eq_mul_inv α _
    zsmul := @DivInvMonoid.zpow α _
    zsmul_zero' := @DivInvMonoid.zpow_zero' α _
    zsmul_succ' := @DivInvMonoid.zpow_succ' α _
    zsmul_neg' := @DivInvMonoid.zpow_neg' α _ }

instance Multiplicative.divInvMonoid [SubNegMonoid α] : DivInvMonoid (Multiplicative α) :=
  { Multiplicative.inv, Multiplicative.div, Multiplicative.monoid with
    div_eq_mul_inv := @sub_eq_add_neg α _
    zpow := @SubNegMonoid.zsmul α _
    zpow_zero' := @SubNegMonoid.zsmul_zero' α _
    zpow_succ' := @SubNegMonoid.zsmul_succ' α _
    zpow_neg' := @SubNegMonoid.zsmul_neg' α _ }

instance Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := @mul_inv_rev α _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right α _ }

instance Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := @neg_add_rev α _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right α _ }

instance Additive.subtractionCommMonoid [DivisionCommMonoid α] :
    SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

instance Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] :
    DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

instance Additive.addGroup [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with add_left_neg := @mul_left_inv α _ }

instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with mul_left_inv := @add_left_neg α _ }

instance Additive.addCommGroup [CommGroup α] : AddCommGroup (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }

instance Multiplicative.commGroup [AddCommGroup α] : CommGroup (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }

/-- Reinterpret `α →+ β` as `Multiplicative α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] :
    (α →+ β) ≃ (Multiplicative α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (toAdd a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative AddMonoidHom.toMultiplicative
#align add_monoid_hom.to_multiplicative_symm_apply_apply AddMonoidHom.toMultiplicative_symm_apply_apply
#align add_monoid_hom.to_multiplicative_apply_apply AddMonoidHom.toMultiplicative_apply_apply

/-- Reinterpret `α →* β` as `Additive α →+ Additive β`. -/
@[simps]
def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α →* β) ≃ (Additive α →+ Additive β) where
  toFun f := {
    toFun := fun a => ofMul (f (toMul a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => toMul (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align monoid_hom.to_additive MonoidHom.toAdditive
#align monoid_hom.to_additive_symm_apply_apply MonoidHom.toAdditive_symm_apply_apply
#align monoid_hom.to_additive_apply_apply MonoidHom.toAdditive_apply_apply

/-- Reinterpret `Additive α →+ β` as `α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative' [MulOneClass α] [AddZeroClass β] :
    (Additive α →+ β) ≃ (α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (toMul a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative' AddMonoidHom.toMultiplicative'
#align add_monoid_hom.to_multiplicative'_apply_apply AddMonoidHom.toMultiplicative'_apply_apply
#align add_monoid_hom.to_multiplicative'_symm_apply_apply AddMonoidHom.toMultiplicative'_symm_apply_apply

/-- Reinterpret `α →* Multiplicative β` as `Additive α →+ β`. -/
@[simps!]
def MonoidHom.toAdditive' [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicative'.symm
#align monoid_hom.to_additive' MonoidHom.toAdditive'
#align monoid_hom.to_additive'_symm_apply_apply MonoidHom.toAdditive'_symm_apply_apply
#align monoid_hom.to_additive'_apply_apply MonoidHom.toAdditive'_apply_apply

/-- Reinterpret `α →+ Additive β` as `Multiplicative α →* β`. -/
@[simps]
def AddMonoidHom.toMultiplicative'' [AddZeroClass α] [MulOneClass β] :
    (α →+ Additive β) ≃ (Multiplicative α →* β) where
  toFun f := {
    toFun := fun a => toMul (f (toAdd a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative'' AddMonoidHom.toMultiplicative''
#align add_monoid_hom.to_multiplicative''_symm_apply_apply AddMonoidHom.toMultiplicative''_symm_apply_apply
#align add_monoid_hom.to_multiplicative''_apply_apply AddMonoidHom.toMultiplicative''_apply_apply

/-- Reinterpret `Multiplicative α →* β` as `α →+ Additive β`. -/
@[simps!]
def MonoidHom.toAdditive'' [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicative''.symm
#align monoid_hom.to_additive'' MonoidHom.toAdditive''
#align monoid_hom.to_additive''_symm_apply_apply MonoidHom.toAdditive''_symm_apply_apply
#align monoid_hom.to_additive''_apply_apply MonoidHom.toAdditive''_apply_apply

/-- If `α` has some multiplicative structure and coerces to a function,
then `Additive α` should also coerce to the same function.

This allows `Additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Additive.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Additive α) fun a => β (toMul a) :=
  ⟨fun a => CoeFun.coe (toMul a)⟩
#align additive.has_coe_to_fun Additive.coeToFun

/-- If `α` has some additive structure and coerces to a function,
then `Multiplicative α` should also coerce to the same function.

This allows `Multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Multiplicative.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β (toAdd a) :=
  ⟨fun a => CoeFun.coe (toAdd a)⟩
#align multiplicative.has_coe_to_fun Multiplicative.coeToFun
