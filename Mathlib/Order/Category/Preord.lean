/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.Preord
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Order.Hom.Basic

/-!
# Category of preorders

This defines `Preord`, the category of preorders with monotone maps.
-/


universe u

open CategoryTheory

/-- The category of preorders. -/
def Preord :=
  Bundled Preorder
set_option linter.uppercaseLean3 false in
#align Preord Preord

namespace Preord

instance : BundledHom @OrderHom where
  toFun := @OrderHom.toFun
  id := @OrderHom.id
  comp := @OrderHom.comp
  hom_ext := @OrderHom.ext

deriving instance LargeCategory for Preord

instance : ConcreteCategory Preord :=
  BundledHom.concreteCategory _

instance : CoeSort Preord (Type _) :=
  Bundled.coeSort

/-- Construct a bundled Preord from the underlying type and typeclass. -/
def of (α : Type _) [Preorder α] : Preord :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align Preord.of Preord.of

@[simp]
theorem coe_of (α : Type _) [Preorder α] : ↥(of α) = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align Preord.coe_of Preord.coe_of

instance : Inhabited Preord :=
  ⟨of PUnit⟩

instance (α : Preord) : Preorder α :=
  α.str

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Preord.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom α β)
  inv := (e.symm : OrderHom β α)
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x
set_option linter.uppercaseLean3 false in
#align Preord.iso.mk Preord.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : Preord ⥤ Preord where
  obj X := of Xᵒᵈ
  map := OrderHom.dual
set_option linter.uppercaseLean3 false in
#align Preord.dual Preord.dual

/-- The equivalence between `Preord` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : Preord ≌ Preord where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) (fun _ => rfl)
set_option linter.uppercaseLean3 false in
#align Preord.dual_equiv Preord.dualEquiv

end Preord

/-- The embedding of `Preord` into `Cat`.
-/
@[simps]
def preordCatToCat : Preord.{u} ⥤ Cat where
  obj X := Cat.of X.1
  map f := f.monotone.functor
set_option linter.uppercaseLean3 false in
#align Preord_to_Cat preordCatToCat

instance : Faithful preordCatToCat.{u}
    where map_injective h := by ext x; exact Functor.congr_obj h x

instance : Full preordCatToCat.{u} where
  preimage {X Y} f := ⟨f.obj, @CategoryTheory.Functor.monotone X Y _ _ f⟩
