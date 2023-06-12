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
import Mathlib.Order.Category.PartOrdCat
import Mathlib.Order.Hom.Bounded

/-!
# The category of bounded orders

This defines `BddOrdCat`, the category of bounded orders.
-/

-- Porting note: TODO, remove
set_option autoImplicit false

set_option linter.uppercaseLean3 false

universe u v

open CategoryTheory

/-- The category of bounded orders with monotone functions. -/
structure BddOrdCat where
  toPartOrd : PartOrdCat
  [isBoundedOrder : BoundedOrder toPartOrd]
#align BddOrd BddOrdCat

namespace BddOrdCat

instance : CoeSort BddOrdCat (Type _) :=
  InducedCategory.hasCoeToSort toPartOrd

instance (X : BddOrdCat) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] BddOrdCat.isBoundedOrder

/-- Construct a bundled `BddOrdCat` from a `Fintype` `PartialOrder`. -/
def of (α : Type _) [PartialOrder α] [BoundedOrder α] : BddOrdCat :=
  ⟨⟨α, inferInstance⟩⟩ -- Porting note: was ⟨⟨α⟩⟩
#align BddOrd.of BddOrdCat.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddOrd.coe_of BddOrdCat.coe_of

instance : Inhabited BddOrdCat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory.{u} BddOrdCat where
  Hom X Y := BoundedOrderHom X Y
  id X := BoundedOrderHom.id X
  comp f g := g.comp f
  id_comp := BoundedOrderHom.comp_id
  comp_id := BoundedOrderHom.id_comp
  assoc _ _ _ := BoundedOrderHom.comp_assoc _ _ _
#align BddOrd.large_category BddOrdCat.largeCategory

-- Porting note: TODO, added. Another problem with Quivers?
instance funLike (X Y : BddOrdCat) : FunLike (X ⟶ Y) X (fun _ => Y) :=
  sorry
--show FunLike (NormedAddGroupHom X Y) X (fun _ => Y) from inferInstance

instance concreteCategory : ConcreteCategory BddOrdCat where
  -- Porting note: mathport output.
  -- forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  -- forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩
  forget := {
    obj := (↥)
    map := FunLike.coe
    map_id := fun X => by
      dsimp
      sorry -- Porting note: HERE!
    map_comp := fun f g => by
      dsimp
      sorry
  }
  forget_faithful := ⟨(FunLike.coe_injective ·)⟩
#align BddOrd.concrete_category BddOrdCat.concreteCategory

instance hasForgetToPartOrd : HasForget₂ BddOrdCat PartOrdCat where
  forget₂ :=
    { obj := fun X => X.toPartOrd
      map := fun {X Y} => BoundedOrderHom.toOrderHom }
#align BddOrd.has_forget_to_PartOrd BddOrdCat.hasForgetToPartOrd

instance hasForgetToBipointed : HasForget₂ BddOrdCat Bipointed where
  forget₂ :=
    { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun f => ⟨f, map_bot f, map_top f⟩ }
  forget_comp := rfl
#align BddOrd.has_forget_to_Bipointed BddOrdCat.hasForgetToBipointed

/-- `order_dual` as a functor. -/
@[simps]
def dual : BddOrdCat ⥤ BddOrdCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedOrderHom.dual
#align BddOrd.dual BddOrdCat.dual

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BddOrdCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := e
  inv := e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align BddOrd.iso.mk BddOrdCat.Iso.mk

/-- The equivalence between `BddOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddOrdCat ≌ BddOrdCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddOrd.dual_equiv BddOrdCat.dualEquiv

end BddOrdCat

theorem bddOrd_dual_comp_forget_to_partOrdCat :
    BddOrdCat.dual ⋙ forget₂ BddOrdCat PartOrdCat =
    forget₂ BddOrdCat PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align BddOrd_dual_comp_forget_to_PartOrd bddOrd_dual_comp_forget_to_partOrdCat

theorem bddOrd_dual_comp_forget_to_bipointed :
    BddOrdCat.dual ⋙ forget₂ BddOrdCat Bipointed =
    forget₂ BddOrdCat Bipointed ⋙ Bipointed.swap :=
  rfl
#align BddOrd_dual_comp_forget_to_Bipointed bddOrd_dual_comp_forget_to_bipointed
