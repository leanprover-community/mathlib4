/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BddLat
! leanprover-community/mathlib commit 7581030920af3dcb241d1df0e36f6ec8289dd6be
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.Order.Category.BddOrdCat
import Mathlib.Order.Category.LatCat
import Mathlib.Order.Category.SemilatCat

/-!
# The category of bounded lattices

This file defines `BddLatCat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BddLatCat where
  toLat : LatCat
  [isBoundedOrder : BoundedOrder to_Lat]
#align BddLat BddLatCat

namespace BddLat

instance : CoeSort BddLat (Type _) :=
  ⟨fun X => X.toLat⟩

instance (X : BddLat) : Lattice X :=
  X.toLat.str

attribute [instance] BddLatCat.isBoundedOrder

/-- Construct a bundled `BddLatCat` from `lattice` + `bounded_order`. -/
def of (α : Type _) [Lattice α] [BoundedOrder α] : BddLatCat :=
  ⟨⟨α⟩⟩
#align BddLat.of BddLatCat.of

@[simp]
theorem coe_of (α : Type _) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddLat.coe_of BddLatCat.coe_of

instance : Inhabited BddLatCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BddLatCat where
  Hom X Y := BoundedLatticeHom X Y
  id X := BoundedLatticeHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := BoundedLatticeHom.comp_id
  comp_id' X Y := BoundedLatticeHom.id_comp
  assoc' W X Y Z _ _ _ := BoundedLatticeHom.comp_assoc _ _ _

instance : ConcreteCategory BddLatCat where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩

instance hasForgetToBddOrd : HasForget₂ BddLatCat BddOrd
    where forget₂ :=
    { obj := fun X => BddOrd.of X
      map := fun X Y => BoundedLatticeHom.toBoundedOrderHom }
#align BddLat.has_forget_to_BddOrd BddLatCat.hasForgetToBddOrd

instance hasForgetToLat : HasForget₂ BddLatCat LatCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BddLat.has_forget_to_Lat BddLatCat.hasForgetToLat

instance hasForgetToSemilatSup : HasForget₂ BddLatCat SemilatSup
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toSupBotHom }
#align BddLat.has_forget_to_SemilatSup BddLatCat.hasForgetToSemilatSup

instance hasForgetToSemilatInf : HasForget₂ BddLatCat SemilatInf
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toInfTopHom }
#align BddLat.has_forget_to_SemilatInf BddLatCat.hasForgetToSemilatInf

@[simp]
theorem coe_forget_to_bddOrd (X : BddLatCat) : ↥((forget₂ BddLatCat BddOrd).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_BddOrd BddLatCat.coe_forget_to_bddOrd

@[simp]
theorem coe_forget_to_latCat (X : BddLatCat) : ↥((forget₂ BddLatCat LatCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_Lat BddLatCat.coe_forget_to_latCat

@[simp]
theorem coe_forget_to_semilatSup (X : BddLatCat) : ↥((forget₂ BddLatCat SemilatSup).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatSup BddLatCat.coe_forget_to_semilatSup

@[simp]
theorem coe_forget_to_semilatInf (X : BddLatCat) : ↥((forget₂ BddLatCat SemilatInf).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatInf BddLatCat.coe_forget_to_semilatInf

theorem forget_latCat_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLatCat LatCat ⋙ forget₂ LatCat PartOrdCat =
      forget₂ BddLatCat BddOrd ⋙ forget₂ BddOrd PartOrdCat :=
  rfl
#align BddLat.forget_Lat_PartOrd_eq_forget_BddOrd_PartOrd BddLatCat.forget_latCat_partOrdCat_eq_forget_bddOrd_partOrdCat

theorem forget_semilatSup_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLatCat SemilatSup ⋙ forget₂ SemilatSup PartOrdCat =
      forget₂ BddLatCat BddOrd ⋙ forget₂ BddOrd PartOrdCat :=
  rfl
#align BddLat.forget_SemilatSup_PartOrd_eq_forget_BddOrd_PartOrd BddLatCat.forget_semilatSup_partOrdCat_eq_forget_bddOrd_partOrdCat

theorem forget_semilatInf_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLatCat SemilatInf ⋙ forget₂ SemilatInf PartOrdCat =
      forget₂ BddLatCat BddOrd ⋙ forget₂ BddOrd PartOrdCat :=
  rfl
#align BddLat.forget_SemilatInf_PartOrd_eq_forget_BddOrd_PartOrd BddLatCat.forget_semilatInf_partOrdCat_eq_forget_bddOrd_partOrdCat

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddLatCat.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BddLat.iso.mk BddLatCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BddLatCat ⥤ BddLatCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BddLat.dual BddLatCat.dual

/-- The equivalence between `BddLatCat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddLatCat ≌ BddLatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddLat.dual_equiv BddLatCat.dualEquiv

end BddLatCat

theorem bddLatCat_dual_comp_forget_to_bddOrd :
    BddLatCat.dual ⋙ forget₂ BddLatCat BddOrd = forget₂ BddLatCat BddOrd ⋙ BddOrd.dual :=
  rfl
#align BddLat_dual_comp_forget_to_BddOrd bddLatCat_dual_comp_forget_to_bddOrd

theorem bddLatCat_dual_comp_forget_to_latCat :
    BddLatCat.dual ⋙ forget₂ BddLatCat LatCat = forget₂ bddLatCat LatCat ⋙ LatCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_Lat BddLatCat_dual_comp_forget_to_latCat

theorem bddLatCat_dual_comp_forget_to_semilatSup :
    BddLatCat.dual ⋙ forget₂ BddLatCat SemilatSup = forget₂ bddLatCat SemilatInf ⋙ SemilatInf.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatSup BddLatCat_dual_comp_forget_to_semilatSup

theorem bddLatCat_dual_comp_forget_to_semilatInf :
    BddLat.dual ⋙ forget₂ BddLat SemilatInf = forget₂ bddLatCat SemilatSup ⋙ SemilatSup.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatInf BddLatCat_dual_comp_forget_to_semilatInf

/-- The functor that adds a bottom and a top element to a lattice. This is the free functor. -/
def latToBddLatCat : LatCat.{u} ⥤ BddLatCat where
  obj X := BddLatCat.of <| WithTop <| WithBot X
  map X Y := LatticeHom.withTopWithBot
  map_id' X := LatticeHom.withTopWithBot_id
  map_comp' X Y Z _ _ := LatticeHom.withTopWithBot_comp _ _
#align Lat_to_BddLat latToBddLatCat

/-- `Lat_to_BddLatCat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLatCat`. -/
def latToBddLatCatForgetAdjunction : latToBddLatCat.{u} ⊣ forget₂ BddLat LatCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.map_inf' _ _) }
          invFun := LatticeHom.withTopWithBot'
          left_inv := fun f =>
            BoundedLatticeHom.ext fun a =>
              match a with
              | none => f.map_top'.symm
              | some none => f.map_bot'.symm
              | some (some a) => rfl
          right_inv := fun f => LatticeHom.ext fun a => rfl }
      homEquiv_naturality_left_symm := fun X Y Z f g =>
        BoundedLatticeHom.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some a) => rfl
      homEquiv_naturality_right := fun X Y Z f g => LatticeHom.ext fun a => rfl }
#align Lat_to_BddLat_forget_adjunction latToBddLatCatForgetAdjunction

/-- `Lat_to_BddLatCat` and `order_dual` commute. -/
@[simps]
def latToBddLatCatCompDualIsoDualCompLatToBddLatCat :
    latToBddLatCat.{u} ⋙ BddLatCat.dual ≅ LatCat.dual ⋙ latToBddLatCat :=
  Adjunction.leftAdjointUniq (latToBddLatCatForgetAdjunction.comp BddLatCat.dualEquiv.toAdjunction)
    (LatCat.dualEquiv.toAdjunction.comp latToBddLatCatForgetAdjunction)
#align Lat_to_BddLat_comp_dual_iso_dual_comp_Lat_to_BddLatCat latToBddLatCatCompDualIsoDualCompLatToBddLatCat
