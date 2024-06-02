/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Order.Category.PartOrd

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
  toPartOrd : PartOrd
  [isFintype : Fintype toPartOrd]
#align FinPartOrd FinPartOrd

namespace FinPartOrd

instance : CoeSort FinPartOrd Type* :=
  ⟨fun X => X.toPartOrd⟩

instance (X : FinPartOrd) : PartialOrder X :=
  X.toPartOrd.str

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
  InducedCategory.category FinPartOrd.toPartOrd
#align FinPartOrd.large_category FinPartOrd.largeCategory

instance concreteCategory : ConcreteCategory FinPartOrd :=
  InducedCategory.concreteCategory FinPartOrd.toPartOrd
#align FinPartOrd.concrete_category FinPartOrd.concreteCategory

instance hasForgetToPartOrd : HasForget₂ FinPartOrd PartOrd :=
  InducedCategory.hasForget₂ FinPartOrd.toPartOrd
#align FinPartOrd.has_forget_to_PartOrd FinPartOrd.hasForgetToPartOrd

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
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
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

theorem FinPartOrd_dual_comp_forget_to_partOrd :
    FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrd =
      forget₂ FinPartOrd PartOrd ⋙ PartOrd.dual := rfl
#align FinPartOrd_dual_comp_forget_to_PartOrd FinPartOrd_dual_comp_forget_to_partOrd
