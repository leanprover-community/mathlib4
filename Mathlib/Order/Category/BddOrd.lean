/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BddOrd
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Bounded

/-!
# The category of bounded orders

This defines `BddOrd`, the category of bounded orders.
-/


universe u v

open CategoryTheory

/-- The category of bounded orders with monotone functions. -/
structure BddOrd where
  toPartOrd : PartOrdCat
  [isBoundedOrder : BoundedOrder to_PartOrd]
#align BddOrd BddOrd

namespace BddOrd

instance : CoeSort BddOrd (Type _) :=
  InducedCategory.hasCoeToSort toPartOrd

instance (X : BddOrd) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] BddOrd.isBoundedOrder

/-- Construct a bundled `BddOrd` from a `fintype` `partial_order`. -/
def of (α : Type _) [PartialOrder α] [BoundedOrder α] : BddOrd :=
  ⟨⟨α⟩⟩
#align BddOrd.of BddOrd.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddOrd.coe_of BddOrd.coe_of

instance : Inhabited BddOrd :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory.{u} BddOrd where
  Hom X Y := BoundedOrderHom X Y
  id X := BoundedOrderHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := BoundedOrderHom.comp_id
  comp_id' X Y := BoundedOrderHom.id_comp
  assoc' W X Y Z _ _ _ := BoundedOrderHom.comp_assoc _ _ _
#align BddOrd.large_category BddOrd.largeCategory

instance concreteCategory : ConcreteCategory BddOrd where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩
#align BddOrd.concrete_category BddOrd.concreteCategory

instance hasForgetToPartOrd : HasForget₂ BddOrd PartOrdCat
    where forget₂ :=
    { obj := fun X => X.toPartOrd
      map := fun X Y => BoundedOrderHom.toOrderHom }
#align BddOrd.has_forget_to_PartOrd BddOrd.hasForgetToPartOrd

instance hasForgetToBipointed : HasForget₂ BddOrd Bipointed where
  forget₂ :=
    { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun X Y f => ⟨f, map_bot f, map_top f⟩ }
  forget_comp := rfl
#align BddOrd.has_forget_to_Bipointed BddOrd.hasForgetToBipointed

/-- `order_dual` as a functor. -/
@[simps]
def dual : BddOrd ⥤ BddOrd where
  obj X := of Xᵒᵈ
  map X Y := BoundedOrderHom.dual
#align BddOrd.dual BddOrd.dual

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BddOrd.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BddOrd.iso.mk BddOrd.Iso.mk

/-- The equivalence between `BddOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddOrd ≌ BddOrd :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddOrd.dual_equiv BddOrd.dualEquiv

end BddOrd

theorem bddOrd_dual_comp_forget_to_partOrdCat :
    BddOrd.dual ⋙ forget₂ BddOrd PartOrdCat = forget₂ BddOrd PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align BddOrd_dual_comp_forget_to_PartOrd bddOrd_dual_comp_forget_to_partOrdCat

theorem bddOrd_dual_comp_forget_to_bipointed :
    BddOrd.dual ⋙ forget₂ BddOrd Bipointed = forget₂ BddOrd Bipointed ⋙ Bipointed.swap :=
  rfl
#align BddOrd_dual_comp_forget_to_Bipointed bddOrd_dual_comp_forget_to_bipointed

