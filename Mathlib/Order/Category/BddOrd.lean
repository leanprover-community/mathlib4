/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Bounded

#align_import order.category.BddOrd from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of bounded orders

This defines `BddOrd`, the category of bounded orders.
-/

set_option linter.uppercaseLean3 false

universe u v

open CategoryTheory

/-- The category of bounded orders with monotone functions. -/
structure BddOrd where
  /-- The underlying object in the category of partial orders. -/
  toPartOrd : PartOrd
  [isBoundedOrder : BoundedOrder toPartOrd]
#align BddOrd BddOrd

namespace BddOrd

instance : CoeSort BddOrd Type* :=
  InducedCategory.hasCoeToSort toPartOrd

instance (X : BddOrd) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] BddOrd.isBoundedOrder

/-- Construct a bundled `BddOrd` from a `Fintype` `PartialOrder`. -/
def of (α : Type*) [PartialOrder α] [BoundedOrder α] : BddOrd :=
  -- Porting note: was ⟨⟨α⟩⟩, see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨{ α := α }⟩
#align BddOrd.of BddOrd.of

@[simp]
theorem coe_of (α : Type*) [PartialOrder α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddOrd.coe_of BddOrd.coe_of

instance : Inhabited BddOrd :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory.{u} BddOrd where
  Hom X Y := BoundedOrderHom X Y
  id X := BoundedOrderHom.id X
  comp f g := g.comp f
  id_comp := BoundedOrderHom.comp_id
  comp_id := BoundedOrderHom.id_comp
  assoc _ _ _ := BoundedOrderHom.comp_assoc _ _ _
#align BddOrd.large_category BddOrd.largeCategory

-- Porting note: added.
-- see https://github.com/leanprover-community/mathlib4/issues/5017
instance instFunLike (X Y : BddOrd) : FunLike (X ⟶ Y) X Y :=
  show FunLike (BoundedOrderHom X Y) X Y from inferInstance

instance concreteCategory : ConcreteCategory BddOrd where
  forget :=
    { obj := (↥)
      map := DFunLike.coe }
  forget_faithful := ⟨(DFunLike.coe_injective ·)⟩
#align BddOrd.concrete_category BddOrd.concreteCategory

instance hasForgetToPartOrd : HasForget₂ BddOrd PartOrd where
  forget₂ :=
    { obj := fun X => X.toPartOrd
      map := fun {X Y} => BoundedOrderHom.toOrderHom }
#align BddOrd.has_forget_to_PartOrd BddOrd.hasForgetToPartOrd

instance hasForgetToBipointed : HasForget₂ BddOrd Bipointed where
  forget₂ :=
    { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun f => ⟨f, f.map_bot', f.map_top'⟩ }
  forget_comp := rfl
#align BddOrd.has_forget_to_Bipointed BddOrd.hasForgetToBipointed

/-- `OrderDual` as a functor. -/
@[simps]
def dual : BddOrd ⥤ BddOrd where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedOrderHom.dual
#align BddOrd.dual BddOrd.dual

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BddOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedOrderHom _ _)
  inv := (e.symm : BoundedOrderHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align BddOrd.iso.mk BddOrd.Iso.mk

/-- The equivalence between `BddOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BddOrd ≌ BddOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align BddOrd.dual_equiv BddOrd.dualEquiv

end BddOrd

theorem bddOrd_dual_comp_forget_to_partOrd :
    BddOrd.dual ⋙ forget₂ BddOrd PartOrd =
    forget₂ BddOrd PartOrd ⋙ PartOrd.dual :=
  rfl
#align BddOrd_dual_comp_forget_to_PartOrd bddOrd_dual_comp_forget_to_partOrd

theorem bddOrd_dual_comp_forget_to_bipointed :
    BddOrd.dual ⋙ forget₂ BddOrd Bipointed =
    forget₂ BddOrd Bipointed ⋙ Bipointed.swap :=
  rfl
#align BddOrd_dual_comp_forget_to_Bipointed bddOrd_dual_comp_forget_to_bipointed
