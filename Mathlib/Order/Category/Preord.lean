/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.Preord
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Order.Hom.Basic

/-!
# Category of preorders

This defines `Preord`, the category of preorders with monotone maps.
-/


universe u

open CategoryTheory

/-- The category of preorders. -/
def Preord :=
  Bundled Preorder
#align Preord Preord

namespace Preord

instance : BundledHom @OrderHom where
  toFun := @OrderHom.toFun
  id := @OrderHom.id
  comp := @OrderHom.comp
  hom_ext := @OrderHom.ext

deriving instance LargeCategory, ConcreteCategory for Preord

instance : CoeSort Preord (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled Preord from the underlying type and typeclass. -/
def of (α : Type _) [Preorder α] : Preord :=
  Bundled.of α
#align Preord.of Preord.of

@[simp]
theorem coe_of (α : Type _) [Preorder α] : ↥(of α) = α :=
  rfl
#align Preord.coe_of Preord.coe_of

instance : Inhabited Preord :=
  ⟨of PUnit⟩

instance (α : Preord) : Preorder α :=
  α.str

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Preord.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x
#align Preord.iso.mk Preord.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : Preord ⥤ Preord where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align Preord.dual Preord.dual

/-- The equivalence between `Preord` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : Preord ≌ Preord :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align Preord.dual_equiv Preord.dualEquiv

end Preord

/-- The embedding of `Preord` into `Cat`.
-/
@[simps]
def preordToCat : Preord.{u} ⥤ Cat where
  obj X := Cat.of X.1
  map X Y f := f.Monotone.Functor
  map_id' X := by apply CategoryTheory.Functor.ext; tidy
  map_comp' X Y Z f g := by apply CategoryTheory.Functor.ext; tidy
#align Preord_to_Cat preordToCat

instance : Faithful preordToCat.{u}
    where map_injective' X Y f g h := by ext x; exact functor.congr_obj h x

instance : Full preordToCat.{u}
    where
  preimage X Y f := ⟨f.obj, f.Monotone⟩
  witness' X Y f := by apply CategoryTheory.Functor.ext; tidy

