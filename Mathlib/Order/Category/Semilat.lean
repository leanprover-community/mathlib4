/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.BoundedLattice

/-!
# The categories of semilattices

This defines `SemilatSupCat` and `SemilatInfCat`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/


universe u

open CategoryTheory

/-- The category of sup-semilattices with a bottom element. -/
structure SemilatSupCat : Type (u + 1) where
  /-- The underlying type of a sup-semilattice with a bottom element. -/
  protected X : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot.{u} X]

/-- The category of inf-semilattices with a top element. -/
structure SemilatInfCat : Type (u + 1) where
  /-- The underlying type of an inf-semilattice with a top element. -/
  protected X : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop.{u} X]

namespace SemilatSupCat

instance : CoeSort SemilatSupCat Type* :=
  ⟨SemilatSupCat.X⟩

attribute [instance] isSemilatticeSup isOrderBot

/-- Construct a bundled `SemilatSupCat` from a `SemilatticeSup`. -/
abbrev of (α : Type*) [SemilatticeSup α] [OrderBot α] : SemilatSupCat :=
  ⟨α⟩

theorem coe_of (α : Type*) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl

instance : Inhabited SemilatSupCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatSupCat where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp f g := g.comp f
  id_comp := SupBotHom.comp_id
  comp_id := SupBotHom.id_comp
  assoc _ _ _ := SupBotHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatSupCat (SupBotHom · ·) where
  hom f := f
  ofHom f := f

instance hasForgetToPartOrd : HasForget₂ SemilatSupCat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toSupHom, OrderHomClass.mono f.toSupHom⟩

@[simp]
theorem coe_forget_to_partOrd (X : SemilatSupCat) :
    ↥((forget₂ SemilatSupCat PartOrd).obj X) = ↥X :=
  rfl

end SemilatSupCat

namespace SemilatInfCat

instance : CoeSort SemilatInfCat Type* :=
  ⟨SemilatInfCat.X⟩

attribute [instance] isSemilatticeInf isOrderTop

/-- Construct a bundled `SemilatInfCat` from a `SemilatticeInf`. -/
abbrev of (α : Type*) [SemilatticeInf α] [OrderTop α] : SemilatInfCat :=
  ⟨α⟩

theorem coe_of (α : Type*) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl

instance : Inhabited SemilatInfCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatInfCat where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp f g := g.comp f
  id_comp := InfTopHom.comp_id
  comp_id := InfTopHom.id_comp
  assoc _ _ _ := InfTopHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatInfCat (InfTopHom · ·) where
  hom f := f
  ofHom f := f

instance hasForgetToPartOrd : HasForget₂ SemilatInfCat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toInfHom, OrderHomClass.mono f.toInfHom⟩

@[simp]
theorem coe_forget_to_partOrd (X : SemilatInfCat) :
    ↥((forget₂ SemilatInfCat PartOrd).obj X) = ↥X :=
  rfl

end SemilatInfCat

/-! ### Order dual -/

namespace SemilatSupCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatSupCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : SupBotHom _ _)
  inv := (e.symm : SupBotHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : SemilatSupCat ⥤ SemilatInfCat where
  obj X := .of Xᵒᵈ
  map {_ _} := SupBotHom.dual

end SemilatSupCat

namespace SemilatInfCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatInfCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : InfTopHom _ _)
  inv := (e.symm :  InfTopHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps]
def dual : SemilatInfCat ⥤ SemilatSupCat where
  obj X := .of Xᵒᵈ
  map {_ _} := InfTopHom.dual

end SemilatInfCat

/-- The equivalence between `SemilatSupCat` and `SemilatInfCat` induced by `OrderDual` both ways. -/
@[simps functor inverse]
def SemilatSupCatEquivSemilatInfCat : SemilatSupCat ≌ SemilatInfCat where
  functor := SemilatSupCat.dual
  inverse := SemilatInfCat.dual
  unitIso := NatIso.ofComponents fun X => SemilatSupCat.Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => SemilatInfCat.Iso.mk <| OrderIso.dualDual X

theorem SemilatSupCat_dual_comp_forget_to_partOrd :
    SemilatSupCat.dual ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ SemilatSupCat PartOrd ⋙ PartOrd.dual :=
  rfl

theorem SemilatInfCat_dual_comp_forget_to_partOrd :
    SemilatInfCat.dual ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ SemilatInfCat PartOrd ⋙ PartOrd.dual :=
  rfl
