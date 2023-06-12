/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Semilat
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Lattice

/-!
# The categories of semilattices

This defines `SemilatSup` and `SemilatInf`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/


universe u

open CategoryTheory

/-- The category of sup-semilattices with a bottom element. -/
structure SemilatSup : Type (u + 1) where
  pt : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot X]
#align SemilatSup SemilatSup

/-- The category of inf-semilattices with a top element. -/
structure SemilatInf : Type (u + 1) where
  pt : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop X]
#align SemilatInf SemilatInf

attribute [protected] SemilatSup.X SemilatInf.X

namespace SemilatSup

instance : CoeSort SemilatSup (Type _) :=
  ⟨SemilatSup.X⟩

attribute [instance] is_semilattice_sup is_order_bot

/-- Construct a bundled `SemilatSup` from a `semilattice_sup`. -/
def of (α : Type _) [SemilatticeSup α] [OrderBot α] : SemilatSup :=
  ⟨α⟩
#align SemilatSup.of SemilatSup.of

@[simp]
theorem coe_of (α : Type _) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl
#align SemilatSup.coe_of SemilatSup.coe_of

instance : Inhabited SemilatSup :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatSup where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := SupBotHom.comp_id
  comp_id' X Y := SupBotHom.id_comp
  assoc' W X Y Z _ _ _ := SupBotHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatSup where
  forget :=
    { obj := SemilatSup.X
      map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => FunLike.coe_injective⟩

instance hasForgetToPartOrd : HasForget₂ SemilatSup PartOrdCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
#align SemilatSup.has_forget_to_PartOrd SemilatSup.hasForgetToPartOrd

@[simp]
theorem coe_forget_to_partOrdCat (X : SemilatSup) : ↥((forget₂ SemilatSup PartOrdCat).obj X) = ↥X :=
  rfl
#align SemilatSup.coe_forget_to_PartOrd SemilatSup.coe_forget_to_partOrdCat

end SemilatSup

namespace SemilatInf

instance : CoeSort SemilatInf (Type _) :=
  ⟨SemilatInf.X⟩

attribute [instance] is_semilattice_inf is_order_top

/-- Construct a bundled `SemilatInf` from a `semilattice_inf`. -/
def of (α : Type _) [SemilatticeInf α] [OrderTop α] : SemilatInf :=
  ⟨α⟩
#align SemilatInf.of SemilatInf.of

@[simp]
theorem coe_of (α : Type _) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl
#align SemilatInf.coe_of SemilatInf.coe_of

instance : Inhabited SemilatInf :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatInf where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := InfTopHom.comp_id
  comp_id' X Y := InfTopHom.id_comp
  assoc' W X Y Z _ _ _ := InfTopHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatInf where
  forget :=
    { obj := SemilatInf.X
      map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => FunLike.coe_injective⟩

instance hasForgetToPartOrd : HasForget₂ SemilatInf PartOrdCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
#align SemilatInf.has_forget_to_PartOrd SemilatInf.hasForgetToPartOrd

@[simp]
theorem coe_forget_to_partOrdCat (X : SemilatInf) : ↥((forget₂ SemilatInf PartOrdCat).obj X) = ↥X :=
  rfl
#align SemilatInf.coe_forget_to_PartOrd SemilatInf.coe_forget_to_partOrdCat

end SemilatInf

/-! ### Order dual -/


namespace SemilatSup

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatSup.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align SemilatSup.iso.mk SemilatSup.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : SemilatSup ⥤ SemilatInf where
  obj X := SemilatInf.of Xᵒᵈ
  map X Y := SupBotHom.dual
#align SemilatSup.dual SemilatSup.dual

end SemilatSup

namespace SemilatInf

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatInf.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align SemilatInf.iso.mk SemilatInf.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : SemilatInf ⥤ SemilatSup where
  obj X := SemilatSup.of Xᵒᵈ
  map X Y := InfTopHom.dual
#align SemilatInf.dual SemilatInf.dual

end SemilatInf

/-- The equivalence between `SemilatSup` and `SemilatInf` induced by `order_dual` both ways.
-/
@[simps Functor inverse]
def semilatSupEquivSemilatInf : SemilatSup ≌ SemilatInf :=
  Equivalence.mk SemilatSup.dual SemilatInf.dual
    (NatIso.ofComponents (fun X => SemilatSup.Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => SemilatInf.Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align SemilatSup_equiv_SemilatInf semilatSupEquivSemilatInf

theorem semilatSup_dual_comp_forget_to_partOrdCat :
    SemilatSup.dual ⋙ forget₂ SemilatInf PartOrdCat =
      forget₂ SemilatSup PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align SemilatSup_dual_comp_forget_to_PartOrd semilatSup_dual_comp_forget_to_partOrdCat

theorem semilatInf_dual_comp_forget_to_partOrdCat :
    SemilatInf.dual ⋙ forget₂ SemilatSup PartOrdCat =
      forget₂ SemilatInf PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align SemilatInf_dual_comp_forget_to_PartOrd semilatInf_dual_comp_forget_to_partOrdCat

