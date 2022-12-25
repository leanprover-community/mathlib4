/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module algebra.group.type_tags
! leanprover-community/mathlib commit 6eb334bd8f3433d5b08ba156b8ec3e6af47e1904
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finite.Defs

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
open Function

variable {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `Additive α` carries the corresponding
additive structure. -/
structure Additive (α : Type _) where
  /-- The element of `Additive α` that represents `x : α`. -/ ofMul ::
  /-- The element of `α` represented by `x : Additive α`. -/ toMul : α
#align additive Additive

/-- If `α` carries some additive structure, then `Multiplicative α` carries the corresponding
multiplicative structure. -/
structure Multiplicative (α : Type _) where
  /-- The element of `Multiplicative α` that represents `x : α`. -/ ofAdd ::
  /-- The element of `α` represented by `x : Multiplicative α`. -/ toAdd : α
#align multiplicative Multiplicative

namespace Additive

/-- Reinterpret `x : α` as an element of `Additive α`, the `Equiv` version. -/
@[simps] def ofMulEquiv : α ≃ Additive α :=
  ⟨ofMul, toMul, fun _ ↦ rfl, fun _ ↦ rfl⟩
#align additive.of_mul Additive.ofMulEquiv

/-- Reinterpret `x : Additive α` as an element of `α`, the `Equiv` version. -/
def toMulEquiv : Additive α ≃ α := ofMulEquiv.symm
#align additive.to_mul Additive.toMulEquiv

@[simp]
theorem ofMulEquiv_symm_eq : (@ofMulEquiv α).symm = toMulEquiv :=
  rfl
#align additive.of_mul_symm_eq Additive.ofMulEquiv_symm_eq

@[simp]
theorem toMulEquiv_symm_eq : (@toMulEquiv α).symm = ofMulEquiv :=
  rfl
#align additive.to_mul_symm_eq Additive.toMulEquiv_symm_eq

theorem «forall» {p : Additive α → Prop} : (∀ x, p x) ↔ ∀ x, p (ofMul x) :=
  ofMulEquiv.surjective.forall

theorem «exists» {p : Additive α → Prop} : (∃ x, p x) ↔ ∃ x, p (ofMul x) :=
  ofMulEquiv.surjective.exists

end Additive

namespace Multiplicative

/-- Reinterpret `x : α` as an element of `Multiplicative α`, the `Equiv` version. -/
def ofAddEquiv : α ≃ Multiplicative α :=
  ⟨ofAdd, toAdd, fun _ => rfl, fun _ => rfl⟩
#align multiplicative.of_add Multiplicative.ofAddEquiv

/-- Reinterpret `x : Multiplicative α` as an element of `α`, the `Equiv` version. -/
def toAddEquiv : Multiplicative α ≃ α := ofAddEquiv.symm
#align multiplicative.to_add Multiplicative.toAddEquiv

@[simp]
theorem ofAddEquiv_symm_eq : (@ofAddEquiv α).symm = toAddEquiv :=
  rfl
#align multiplicative.of_add_symm_eq Multiplicative.ofAddEquiv_symm_eq

@[simp]
theorem toAddEquiv_symm_eq : (@toAddEquiv α).symm = ofAddEquiv :=
  rfl
#align multiplicative.to_add_symm_eq Multiplicative.toAddEquiv_symm_eq

theorem «forall» {p : Multiplicative α → Prop} : (∀ x, p x) ↔ ∀ x, p (ofAdd x) :=
  ofAddEquiv.surjective.forall

theorem «exists» {p : Multiplicative α → Prop} : (∃ x, p x) ↔ ∃ x, p (ofAdd x) :=
  ofAddEquiv.surjective.exists

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

theorem ofMul_injective : Injective (@ofMul α) := Additive.ofMulEquiv.injective
theorem ofMul_bijective : Bijective (@ofMul α) := Additive.ofMulEquiv.bijective
theorem ofMul_surjective : Surjective (@ofMul α) := Additive.ofMulEquiv.surjective
@[simp] theorem ofMul_inj {x y : α} : ofMul x = ofMul y ↔ x = y := ofMul_injective.eq_iff

theorem toMul_injective : Injective (@toMul α) := Additive.toMulEquiv.injective
theorem toMul_bijective : Bijective (@toMul α) := Additive.toMulEquiv.bijective
theorem toMul_surjective : Surjective (@toMul α) := Additive.toMulEquiv.surjective
@[simp] theorem toMul_inj {x y : Additive α} : toMul x = toMul y ↔ x = y := toMul_injective.eq_iff

theorem ofAdd_injective : Injective (@ofAdd α) := Multiplicative.ofAddEquiv.injective
theorem ofAdd_bijective : Bijective (@ofAdd α) := Multiplicative.ofAddEquiv.bijective
theorem ofAdd_surjective : Surjective (@ofAdd α) := Multiplicative.ofAddEquiv.surjective
@[simp] theorem ofAdd_inj {x y : α} : ofAdd x = ofAdd y ↔ x = y := ofAdd_injective.eq_iff

theorem toAdd_injective : Injective (@toAdd α) := Multiplicative.toAddEquiv.injective
theorem toAdd_bijective : Bijective (@toAdd α) := Multiplicative.toAddEquiv.bijective
theorem toAdd_surjective : Surjective (@toAdd α) := Multiplicative.toAddEquiv.surjective

@[simp]
theorem toAdd_inj {x y : Multiplicative α} : toAdd x = toAdd y ↔ x = y :=
  toAdd_injective.eq_iff

instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨ofMul default⟩

instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨ofAdd default⟩

instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α Additive.ofMulEquiv

instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α Multiplicative.ofAddEquiv

instance [Infinite α] : Infinite (Additive α) :=
  Additive.ofMulEquiv.infinite_iff.1 ‹_›

instance [Infinite α] : Infinite (Multiplicative α) :=
  Multiplicative.ofAddEquiv.infinite_iff.1 ‹_›

instance [Nontrivial α] : Nontrivial (Additive α) :=
  ofMul_injective.nontrivial
#align additive.nontrivial instNontrivialAdditive

instance [Nontrivial α] : Nontrivial (Multiplicative α) :=
  ofAdd_injective.nontrivial
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
  { Additive.add with add_assoc := fun ⟨x⟩ ⟨y⟩ ⟨z⟩ => congr_arg ofMul <| mul_assoc x y z }

instance Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.mul with mul_assoc := fun ⟨x⟩ ⟨y⟩ ⟨z⟩ => congr_arg ofAdd <| add_assoc x y z }

instance Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm := fun ⟨x⟩ ⟨y⟩ => congr_arg ofMul <| mul_comm x y }

instance Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := fun ⟨x⟩ ⟨y⟩ => congr_arg ofAdd <| add_comm x y }

instance Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Additive α) :=
  ⟨fun ⟨_⟩ ⟨_⟩ ⟨_⟩ h => congr_arg ofMul <| mul_left_cancel <| ofMul_injective h⟩

instance Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) :=
  ⟨fun ⟨_⟩ ⟨_⟩ ⟨_⟩ h => congr_arg ofAdd <| add_left_cancel <| ofAdd_injective h⟩

instance Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd (Additive α) :=
  ⟨fun ⟨_⟩ ⟨_⟩ ⟨_⟩ h => congr_arg ofMul <| mul_right_cancel <| ofMul_injective h⟩

instance Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) :=
  ⟨fun ⟨_⟩ ⟨_⟩ ⟨_⟩ h => congr_arg ofAdd <| add_right_cancel <| ofAdd_injective h⟩

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
theorem ofMul_eq_zero {A : Type _} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 := ofMul_inj
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
theorem ofAdd_eq_one {A : Type _} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 := ofAdd_inj
#align of_add_eq_one ofAdd_eq_one

@[simp]
theorem toAdd_one [Zero α] : toAdd (1 : Multiplicative α) = 0 :=
  rfl
#align to_add_one toAdd_one

instance Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where
  zero := 0
  add := (· + ·)
  zero_add := fun ⟨x⟩ => congr_arg ofMul <| one_mul x
  add_zero := fun ⟨x⟩ => congr_arg ofMul <| mul_one x

instance Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative α) where
  one := 1
  mul := (· * ·)
  one_mul := fun ⟨x⟩ => congr_arg ofAdd <| zero_add x
  mul_one := fun ⟨x⟩ => congr_arg ofAdd <| add_zero x

instance Additive.addMonoid [Monoid α] : AddMonoid (Additive α) :=
  { Additive.addZeroClass, Additive.addSemigroup with
    zero := 0
    add := (· + ·)
    nsmul := fun n x => ⟨x.1 ^ n⟩
    nsmul_zero := fun _ => congr_arg ofMul <| pow_zero _
    nsmul_succ := fun _ _ => congr_arg ofMul <| pow_succ _ _ }

instance Multiplicative.monoid [AddMonoid α] : Monoid (Multiplicative α) :=
  { Multiplicative.mulOneClass, Multiplicative.semigroup with
    one := 1
    mul := (· * ·)
    npow := fun n x => ⟨n • x.1⟩
    npow_zero := fun _ => congr_arg ofAdd <| zero_nsmul _
    npow_succ := fun _ _ => congr_arg ofAdd <| succ_nsmul _ _ }

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
  ⟨fun x => ofMul (toMul x)⁻¹⟩

@[simp]
theorem ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x :=
  rfl
#align of_mul_inv ofMul_inv

@[simp]
theorem toMul_neg [Inv α] (x : Additive α) : toMul (-x) = (toMul x)⁻¹ :=
  rfl
#align to_mul_neg toMul_neg

instance Multiplicative.inv [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => ofAdd (-toAdd x)⟩

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
  { Additive.neg with neg_neg := fun _ => toMul_injective <| inv_inv _ }

instance Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.inv with inv_inv := fun _ => toAdd_injective <| neg_neg _ }

instance Additive.subNegMonoid [DivInvMonoid α] : SubNegMonoid (Additive α) :=
  { Additive.neg, Additive.sub, Additive.addMonoid with
    sub_eq_add_neg := fun _ _ => toMul_injective <| div_eq_mul_inv _ _
    zsmul := fun n x => ⟨x.1 ^ n⟩
    zsmul_zero' := fun _ => toMul_injective <| zpow_zero _
    zsmul_succ' := fun _ _ => toMul_injective <| DivInvMonoid.zpow_succ' _ _
    zsmul_neg' := fun _ _ => toMul_injective <| DivInvMonoid.zpow_neg' _ _ }

instance Multiplicative.divInvMonoid [SubNegMonoid α] : DivInvMonoid (Multiplicative α) :=
  { Multiplicative.inv, Multiplicative.div, Multiplicative.monoid with
    div_eq_mul_inv := fun _ _ => toAdd_injective <| sub_eq_add_neg _ _
    zpow := fun n x => ⟨n • x.1⟩
    zpow_zero' := fun _ => toAdd_injective <| SubNegMonoid.zsmul_zero' _
    zpow_succ' := fun _ _ => toAdd_injective <| SubNegMonoid.zsmul_succ' _ _
    zpow_neg' := fun _ _ => toAdd_injective <| SubNegMonoid.zsmul_neg' _ _ }

instance Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := fun _ _ => toMul_injective <| mul_inv_rev _ _
    neg_eq_of_add := fun _ _ h => toMul_injective <| inv_eq_of_mul_eq_one_right <|
      congr_arg toMul h }

instance Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := fun _ _ => toAdd_injective <| neg_add_rev _ _
    inv_eq_of_mul := fun _ _ h => toAdd_injective <| neg_eq_of_add_eq_zero_right <|
      congr_arg toAdd h }

instance Additive.subtractionCommMonoid [DivisionCommMonoid α] :
    SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

instance Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] :
    DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

instance Additive.addGroup [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with add_left_neg := fun _ => toMul_injective <| mul_left_inv _ }

instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with mul_left_inv := fun _ => toAdd_injective <| add_left_neg _ }

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
    map_mul' := fun _ _ => toAdd_injective <| f.map_add _ _
    map_one' := toAdd_injective f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (ofAdd a))
    map_add' := fun _ _ => ofAdd_injective <| f.map_mul _ _
    map_zero' := ofAdd_injective f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative AddMonoidHom.toMultiplicative

/-- Reinterpret `α →* β` as `Additive α →+ Additive β`. -/
@[simps]
def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α →* β) ≃ (Additive α →+ Additive β) where
  toFun f := {
    toFun := fun a => ofMul (f (toMul a))
    map_add' := fun _ _ => toMul_injective <| f.map_mul _ _
    map_zero' := toMul_injective f.map_one
  }
  invFun f := {
    toFun := fun a => toMul (f (ofMul a))
    map_mul' := fun _ _ => ofMul_injective <| f.map_add _ _
    map_one' := ofMul_injective f.map_zero
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align monoid_hom.to_additive MonoidHom.toAdditive

/-- Reinterpret `Additive α →+ β` as `α →* Multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative' [MulOneClass α] [AddZeroClass β] :
    (Additive α →+ β) ≃ (α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := fun _ _ => toAdd_injective <| f.map_add _ _
    map_one' := toAdd_injective f.map_zero
  }
  invFun f := {
    toFun := fun a => toAdd (f (toMul a))
    map_add' := fun _ _ => ofAdd_injective <| f.map_mul _ _
    map_zero' := ofAdd_injective f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative' AddMonoidHom.toMultiplicative'

/-- Reinterpret `α →* Multiplicative β` as `Additive α →+ β`. -/
@[simps]
def MonoidHom.toAdditive' [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicative'.symm
#align monoid_hom.to_additive' MonoidHom.toAdditive'

/-- Reinterpret `α →+ Additive β` as `Multiplicative α →* β`. -/
@[simps]
def AddMonoidHom.toMultiplicative'' [AddZeroClass α] [MulOneClass β] :
    (α →+ Additive β) ≃ (Multiplicative α →* β) where
  toFun f := {
    toFun := fun a => toMul (f (toAdd a))
    map_mul' := fun _ _ => ofMul_injective <| f.map_add _ _
    map_one' := ofMul_injective f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := fun _ _ => toMul_injective <| f.map_mul _ _
    map_zero' := toMul_injective f.map_one
  }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.to_multiplicative'' AddMonoidHom.toMultiplicative''

/-- Reinterpret `Multiplicative α →* β` as `α →+ Additive β`. -/
@[simps]
def MonoidHom.toAdditive'' [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicative''.symm
#align monoid_hom.to_additive'' MonoidHom.toAdditive''

/-- If `α` has some multiplicative structure and coerces to a function,
then `Additive α` should also coerce to the same function.

This allows `Additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Additive.coeToFun {α : Type _} {β : α → Sort _} [CoeFun α β] :
    CoeFun (Additive α) fun a => β (toMul a) :=
  ⟨fun a => CoeFun.coe (toMul a)⟩
#align additive.has_coe_to_fun Additive.coeToFun

/-- If `α` has some additive structure and coerces to a function,
then `Multiplicative α` should also coerce to the same function.

This allows `Multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Multiplicative.coeToFun {α : Type _} {β : α → Sort _} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β (toAdd a) :=
  ⟨fun a => CoeFun.coe (toAdd a)⟩
#align multiplicative.has_coe_to_fun Multiplicative.coeToFun

instance Additive.decidableEq [DecidableEq α] : DecidableEq (Additive α) :=
  fun _ _ => decidable_of_iff _ toMul_inj

instance Multiplicative.decidableEq [DecidableEq α] : DecidableEq (Multiplicative α) :=
  fun _ _ => decidable_of_iff _ toAdd_inj
