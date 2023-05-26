/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.FinPartOrd
! leanprover-community/mathlib commit 937b1c59c58710ef8ed91f8727ef402d49d621a2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Fintype
import Mathbin.Order.Category.PartOrd

/-!
# The category of finite partial orders

This defines `FinPartOrd`, the category of finite partial orders.

Note: `FinPartOrd` is *not* a subcategory of `BddOrd` because finite orders are not necessarily
bounded.

## TODO

`FinPartOrd` is equivalent to a small category.
-/


universe u v

open CategoryTheory

/-- The category of finite partial orders with monotone functions. -/
structure FinPartOrd where
  toPartOrd : PartOrdCat
  [isFintype : Fintype to_PartOrd]
#align FinPartOrd FinPartOrd

namespace FinPartOrd

instance : CoeSort FinPartOrd (Type _) :=
  ⟨fun X => X.toPartOrd⟩

instance (X : FinPartOrd) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] FinPartOrd.isFintype

@[simp]
theorem coe_toPartOrd (X : FinPartOrd) : ↥X.toPartOrd = ↥X :=
  rfl
#align FinPartOrd.coe_to_PartOrd FinPartOrd.coe_toPartOrd

/-- Construct a bundled `FinPartOrd` from `fintype` + `partial_order`. -/
def of (α : Type _) [PartialOrder α] [Fintype α] : FinPartOrd :=
  ⟨⟨α⟩⟩
#align FinPartOrd.of FinPartOrd.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [Fintype α] : ↥(of α) = α :=
  rfl
#align FinPartOrd.coe_of FinPartOrd.coe_of

instance : Inhabited FinPartOrd :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinPartOrd :=
  InducedCategory.category FinPartOrd.toPartOrd
#align FinPartOrd.large_category FinPartOrd.largeCategory

instance concreteCategory : ConcreteCategory FinPartOrd :=
  InducedCategory.concreteCategory FinPartOrd.toPartOrd
#align FinPartOrd.concrete_category FinPartOrd.concreteCategory

instance hasForgetToPartOrd : HasForget₂ FinPartOrd PartOrdCat :=
  InducedCategory.hasForget₂ FinPartOrd.toPartOrd
#align FinPartOrd.has_forget_to_PartOrd FinPartOrd.hasForgetToPartOrd

instance hasForgetToFintype : HasForget₂ FinPartOrd FintypeCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => coeFn }
#align FinPartOrd.has_forget_to_Fintype FinPartOrd.hasForgetToFintype

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FinPartOrd.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align FinPartOrd.iso.mk FinPartOrd.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinPartOrd ⥤ FinPartOrd where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align FinPartOrd.dual FinPartOrd.dual

/-- The equivalence between `FinPartOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinPartOrd ≌ FinPartOrd :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinPartOrd.dual_equiv FinPartOrd.dualEquiv

end FinPartOrd

theorem finPartOrd_dual_comp_forget_to_partOrdCat :
    FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrdCat =
      forget₂ FinPartOrd PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align FinPartOrd_dual_comp_forget_to_PartOrd finPartOrd_dual_comp_forget_to_partOrdCat

