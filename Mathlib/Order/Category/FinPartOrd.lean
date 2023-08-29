/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Order.Category.PartOrdCat

#align_import order.category.FinPartOrd from "leanprover-community/mathlib"@"937b1c59c58710ef8ed91f8727ef402d49d621a2"

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

set_option linter.uppercaseLean3 false -- `FinPartOrd`

/-- The category of finite partial orders with monotone functions. -/
structure FinPartOrd where
  toPartOrdCat : PartOrdCat
  [isFintype : Fintype toPartOrdCat]
#align FinPartOrd FinPartOrd

namespace FinPartOrd

instance : CoeSort FinPartOrd (Type*) :=
  ⟨fun X => X.toPartOrdCat⟩

instance (X : FinPartOrd) : PartialOrder X :=
  X.toPartOrdCat.str

attribute [instance] FinPartOrd.isFintype

-- synTaut
#noalign FinPartOrd.coe_to_PartOrd

/-- Construct a bundled `FinPartOrd` from `PartialOrder` + `Fintype`. -/
def of (α : Type*) [PartialOrder α] [Fintype α] : FinPartOrd :=
  ⟨⟨α, inferInstance⟩⟩
#align FinPartOrd.of FinPartOrd.of

@[simp]
theorem coe_of (α : Type*) [PartialOrder α] [Fintype α] : ↥(of α) = α := rfl
#align FinPartOrd.coe_of FinPartOrd.coe_of

instance : Inhabited FinPartOrd :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinPartOrd :=
  InducedCategory.category FinPartOrd.toPartOrdCat
#align FinPartOrd.large_category FinPartOrd.largeCategory

instance concreteCategory : ConcreteCategory FinPartOrd :=
  InducedCategory.concreteCategory FinPartOrd.toPartOrdCat
#align FinPartOrd.concrete_category FinPartOrd.concreteCategory

instance hasForgetToPartOrdCat : HasForget₂ FinPartOrd PartOrdCat :=
  InducedCategory.hasForget₂ FinPartOrd.toPartOrdCat
#align FinPartOrd.has_forget_to_PartOrd FinPartOrd.hasForgetToPartOrdCat

instance hasForgetToFintype : HasForget₂ FinPartOrd FintypeCat where
  forget₂ :=
    { obj := fun X => ⟨X, inferInstance⟩
      -- Porting note: Originally `map := fun X Y => coeFn`
      map := fun {X Y} (f : OrderHom X Y) => ⇑f }
#align FinPartOrd.has_forget_to_Fintype FinPartOrd.hasForgetToFintype

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FinPartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom _ _)
  inv := (e.symm : OrderHom _ _)
  hom_inv_id := by
    ext
    -- ⊢ ↑(↑e ≫ ↑(OrderIso.symm e)) x✝ = ↑(𝟙 α) x✝
    exact e.symm_apply_apply _
    -- 🎉 no goals
  inv_hom_id := by
    ext
    -- ⊢ ↑(↑(OrderIso.symm e) ≫ ↑e) x✝ = ↑(𝟙 β) x✝
    exact e.apply_symm_apply _
    -- 🎉 no goals
#align FinPartOrd.iso.mk FinPartOrd.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : FinPartOrd ⥤ FinPartOrd where
  obj X := of Xᵒᵈ
  map {X Y} := OrderHom.dual
#align FinPartOrd.dual FinPartOrd.dual

/-- The equivalence between `FinPartOrd` and itself induced by `OrderDual` both ways. -/
@[simps! functor inverse]
def dualEquiv : FinPartOrd ≌ FinPartOrd :=
  CategoryTheory.Equivalence.mk dual dual
    (NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X)
    (NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X)
#align FinPartOrd.dual_equiv FinPartOrd.dualEquiv

end FinPartOrd

theorem FinPartOrd_dual_comp_forget_to_partOrdCat :
    FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrdCat =
      forget₂ FinPartOrd PartOrdCat ⋙ PartOrdCat.dual := rfl
#align FinPartOrd_dual_comp_forget_to_PartOrd FinPartOrd_dual_comp_forget_to_partOrdCat
