/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Lattice

#align_import order.category.Semilat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The categories of semilattices

This defines `SemilatSupCat` and `SemilatInfCat`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory

/-- The category of sup-semilattices with a bottom element. -/
structure SemilatSupCat : Type (u + 1) where
  /-- The underlying type of a sup-semilattice with a bottom element. -/
  protected X : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot.{u} X]
#align SemilatSup SemilatSupCat

/-- The category of inf-semilattices with a top element. -/
structure SemilatInfCat : Type (u + 1) where
  /-- The underlying type of an inf-semilattice with a top element. -/
  protected X : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop.{u} X]
#align SemilatInf SemilatInfCat

namespace SemilatSupCat

instance : CoeSort SemilatSupCat Type* :=
  ⟨SemilatSupCat.X⟩

attribute [instance] isSemilatticeSup isOrderBot

/-- Construct a bundled `SemilatSupCat` from a `SemilatticeSup`. -/
def of (α : Type*) [SemilatticeSup α] [OrderBot α] : SemilatSupCat :=
  ⟨α⟩
#align SemilatSup.of SemilatSupCat.of

@[simp]
theorem coe_of (α : Type*) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl
#align SemilatSup.coe_of SemilatSupCat.coe_of

instance : Inhabited SemilatSupCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatSupCat where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp f g := g.comp f
  id_comp := SupBotHom.comp_id
  comp_id := SupBotHom.id_comp
  assoc _ _ _ := SupBotHom.comp_assoc _ _ _

-- Porting note: added
-- see https://github.com/leanprover-community/mathlib4/issues/5017
instance instFunLike (X Y : SemilatSupCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (SupBotHom X Y) X Y from inferInstance

instance : ConcreteCategory SemilatSupCat where
  forget :=
    { obj := SemilatSupCat.X
      map := DFunLike.coe }
  forget_faithful := ⟨(DFunLike.coe_injective ·)⟩

instance hasForgetToPartOrd : HasForget₂ SemilatSupCat PartOrd where
  forget₂ :=
    -- Porting note: was ⟨X⟩, see https://github.com/leanprover-community/mathlib4/issues/4998
    { obj := fun X => {α := X}
      -- Porting note: was `map := fun f => f`
      map := fun f => ⟨f.toSupHom, OrderHomClass.mono f.toSupHom⟩ }
#align SemilatSup.has_forget_to_PartOrd SemilatSupCat.hasForgetToPartOrd

@[simp]
theorem coe_forget_to_partOrd (X : SemilatSupCat) :
    ↥((forget₂ SemilatSupCat PartOrd).obj X) = ↥X :=
  rfl
#align SemilatSup.coe_forget_to_PartOrd SemilatSupCat.coe_forget_to_partOrd

end SemilatSupCat

namespace SemilatInfCat

instance : CoeSort SemilatInfCat Type* :=
  ⟨SemilatInfCat.X⟩

attribute [instance] isSemilatticeInf isOrderTop

/-- Construct a bundled `SemilatInfCat` from a `SemilatticeInf`. -/
def of (α : Type*) [SemilatticeInf α] [OrderTop α] : SemilatInfCat :=
  ⟨α⟩
#align SemilatInf.of SemilatInfCat.of

@[simp]
theorem coe_of (α : Type*) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl
#align SemilatInf.coe_of SemilatInfCat.coe_of

instance : Inhabited SemilatInfCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatInfCat where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp f g := g.comp f
  id_comp := InfTopHom.comp_id
  comp_id := InfTopHom.id_comp
  assoc _ _ _ := InfTopHom.comp_assoc _ _ _

-- Porting note (#10754): added instance
instance instFunLike (X Y : SemilatInfCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (InfTopHom X Y) X Y from inferInstance

instance : ConcreteCategory SemilatInfCat where
  forget :=
    { obj := SemilatInfCat.X
      map := DFunLike.coe }
  forget_faithful := ⟨(DFunLike.coe_injective ·)⟩

instance hasForgetToPartOrd : HasForget₂ SemilatInfCat PartOrd where
  forget₂ :=
    { obj := fun X => ⟨X, inferInstance⟩
      -- Porting note: was `map := fun f => f`
      map := fun f => ⟨f.toInfHom, OrderHomClass.mono f.toInfHom⟩ }
#align SemilatInf.has_forget_to_PartOrd SemilatInfCat.hasForgetToPartOrd

@[simp]
theorem coe_forget_to_partOrd (X : SemilatInfCat) :
    ↥((forget₂ SemilatInfCat PartOrd).obj X) = ↥X :=
  rfl
#align SemilatInf.coe_forget_to_PartOrd SemilatInfCat.coe_forget_to_partOrd

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
#align SemilatSup.iso.mk SemilatSupCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : SemilatSupCat ⥤ SemilatInfCat where
  obj X := SemilatInfCat.of Xᵒᵈ
  map {X Y} := SupBotHom.dual
#align SemilatSup.dual SemilatSupCat.dual

end SemilatSupCat

namespace SemilatInfCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatInfCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : InfTopHom _ _)
  inv := (e.symm :  InfTopHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align SemilatInf.iso.mk SemilatInfCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : SemilatInfCat ⥤ SemilatSupCat where
  obj X := SemilatSupCat.of Xᵒᵈ
  map {X Y} := InfTopHom.dual
#align SemilatInf.dual SemilatInfCat.dual

end SemilatInfCat

/-- The equivalence between `SemilatSupCat` and `SemilatInfCat` induced by `OrderDual` both ways. -/
@[simps functor inverse]
def SemilatSupCatEquivSemilatInfCat : SemilatSupCat ≌ SemilatInfCat where
  functor := SemilatSupCat.dual
  inverse := SemilatInfCat.dual
  unitIso := NatIso.ofComponents fun X => SemilatSupCat.Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => SemilatInfCat.Iso.mk <| OrderIso.dualDual X
#align SemilatSup_equiv_SemilatInf SemilatSupCatEquivSemilatInfCat

theorem SemilatSupCat_dual_comp_forget_to_partOrd :
    SemilatSupCat.dual ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ SemilatSupCat PartOrd ⋙ PartOrd.dual :=
  rfl
#align SemilatSup_dual_comp_forget_to_PartOrd SemilatSupCat_dual_comp_forget_to_partOrd

theorem SemilatInfCat_dual_comp_forget_to_partOrd :
    SemilatInfCat.dual ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ SemilatInfCat PartOrd ⋙ PartOrd.dual :=
  rfl
#align SemilatInf_dual_comp_forget_to_PartOrd SemilatInfCat_dual_comp_forget_to_partOrd
