/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.Order.Category.BddOrdCat
import Mathlib.Order.Category.LatCat
import Mathlib.Order.Category.SemilatCat

#align_import order.category.BddLat from "leanprover-community/mathlib"@"7581030920af3dcb241d1df0e36f6ec8289dd6be"

/-!
# The category of bounded lattices

This file defines `BddLatCat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BddLatCat where
  toLat : LatCat
  [isBoundedOrder : BoundedOrder toLat]
#align BddLat BddLatCat

namespace BddLatCat

instance : CoeSort BddLatCat (Type*) :=
  ⟨fun X => X.toLat⟩

instance (X : BddLatCat) : Lattice X :=
  X.toLat.str

attribute [instance] BddLatCat.isBoundedOrder

/-- Construct a bundled `BddLatCat` from `Lattice` + `BoundedOrder`. -/
def of (α : Type*) [Lattice α] [BoundedOrder α] : BddLatCat :=
  -- porting note: was `⟨⟨α⟩⟩`, see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨{α := α}⟩
#align BddLat.of BddLatCat.of

@[simp]
theorem coe_of (α : Type*) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddLat.coe_of BddLatCat.coe_of

instance : Inhabited BddLatCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BddLatCat where
  Hom X Y := BoundedLatticeHom X Y
  id X := BoundedLatticeHom.id X
  comp f g := g.comp f
  id_comp := BoundedLatticeHom.comp_id
  comp_id := BoundedLatticeHom.id_comp
  assoc _ _ _ := BoundedLatticeHom.comp_assoc _ _ _

-- Porting note: added.
instance instFunLike (X Y : BddLatCat) : FunLike (X ⟶ Y) X (fun _ => Y) :=
  show FunLike (BoundedLatticeHom X Y) X (fun _ => Y) from inferInstance

instance : ConcreteCategory BddLatCat where
  forget :=
  { obj := (↑)
    map := FunLike.coe }
  forget_faithful := ⟨(FunLike.coe_injective ·)⟩

instance hasForgetToBddOrd : HasForget₂ BddLatCat BddOrdCat where
  forget₂ :=
    { obj := fun X => BddOrdCat.of X
      map := fun {X Y} => BoundedLatticeHom.toBoundedOrderHom }
#align BddLat.has_forget_to_BddOrd BddLatCat.hasForgetToBddOrd

instance hasForgetToLat : HasForget₂ BddLatCat LatCat where
  forget₂ :=
    -- Porting note: was `⟨X⟩`, see https://github.com/leanprover-community/mathlib4/issues/4998
    { obj := fun X => {α := X}
      map := fun {X Y} => BoundedLatticeHom.toLatticeHom }
#align BddLat.has_forget_to_Lat BddLatCat.hasForgetToLat

instance hasForgetToSemilatSup : HasForget₂ BddLatCat SemilatSupCat where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun {X Y} => BoundedLatticeHom.toSupBotHom }
#align BddLat.has_forget_to_SemilatSup BddLatCat.hasForgetToSemilatSup

instance hasForgetToSemilatInf : HasForget₂ BddLatCat SemilatInfCat where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun {X Y} => BoundedLatticeHom.toInfTopHom }
#align BddLat.has_forget_to_SemilatInf BddLatCat.hasForgetToSemilatInf

@[simp]
theorem coe_forget_to_bddOrd (X : BddLatCat) : ↥((forget₂ BddLatCat BddOrdCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_BddOrd BddLatCat.coe_forget_to_bddOrd

@[simp]
theorem coe_forget_to_latCat (X : BddLatCat) : ↥((forget₂ BddLatCat LatCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_Lat BddLatCat.coe_forget_to_latCat

@[simp]
theorem coe_forget_to_semilatSup (X : BddLatCat) :
    ↥((forget₂ BddLatCat SemilatSupCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatSup BddLatCat.coe_forget_to_semilatSup

@[simp]
theorem coe_forget_to_semilatInf (X : BddLatCat) :
    ↥((forget₂ BddLatCat SemilatInfCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatInf BddLatCat.coe_forget_to_semilatInf

theorem forget_latCat_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLatCat LatCat ⋙ forget₂ LatCat PartOrdCat =
      forget₂ BddLatCat BddOrdCat ⋙ forget₂ BddOrdCat PartOrdCat :=
  rfl
#align BddLat.forget_Lat_PartOrd_eq_forget_BddOrd_PartOrd BddLatCat.forget_latCat_partOrdCat_eq_forget_bddOrd_partOrdCat

theorem forget_semilatSup_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLatCat SemilatSupCat ⋙ forget₂ SemilatSupCat PartOrdCat =
      forget₂ BddLatCat BddOrdCat ⋙ forget₂ BddOrdCat PartOrdCat :=
  rfl
#align BddLat.forget_SemilatSup_PartOrd_eq_forget_BddOrd_PartOrd BddLatCat.forget_semilatSup_partOrdCat_eq_forget_bddOrd_partOrdCat

theorem forget_semilatInf_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLatCat SemilatInfCat ⋙ forget₂ SemilatInfCat PartOrdCat =
      forget₂ BddLatCat BddOrdCat ⋙ forget₂ BddOrdCat PartOrdCat :=
  rfl
#align BddLat.forget_SemilatInf_PartOrd_eq_forget_BddOrd_PartOrd BddLatCat.forget_semilatInf_partOrdCat_eq_forget_bddOrd_partOrdCat

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddLatCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom _ _)
  inv := (e.symm : BoundedLatticeHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align BddLat.iso.mk BddLatCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : BddLatCat ⥤ BddLatCat where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align BddLat.dual BddLatCat.dual

/-- The equivalence between `BddLatCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BddLatCat ≌ BddLatCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align BddLat.dual_equiv BddLatCat.dualEquiv

end BddLatCat

theorem bddLatCat_dual_comp_forget_to_bddOrdCat :
    BddLatCat.dual ⋙ forget₂ BddLatCat BddOrdCat =
    forget₂ BddLatCat BddOrdCat ⋙ BddOrdCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_BddOrd bddLatCat_dual_comp_forget_to_bddOrdCat

theorem bddLatCat_dual_comp_forget_to_latCat :
    BddLatCat.dual ⋙ forget₂ BddLatCat LatCat = forget₂ BddLatCat LatCat ⋙ LatCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_Lat bddLatCat_dual_comp_forget_to_latCat

theorem bddLatCat_dual_comp_forget_to_semilatSupCat :
    BddLatCat.dual ⋙ forget₂ BddLatCat SemilatSupCat =
    forget₂ BddLatCat SemilatInfCat ⋙ SemilatInfCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatSup bddLatCat_dual_comp_forget_to_semilatSupCat

theorem bddLatCat_dual_comp_forget_to_semilatInfCat :
    BddLatCat.dual ⋙ forget₂ BddLatCat SemilatInfCat =
    forget₂ BddLatCat SemilatSupCat ⋙ SemilatSupCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatInf bddLatCat_dual_comp_forget_to_semilatInfCat

/-- The functor that adds a bottom and a top element to a lattice. This is the free functor. -/
def latToBddLatCat : LatCat.{u} ⥤ BddLatCat where
  obj X := BddLatCat.of <| WithTop <| WithBot X
  map := LatticeHom.withTopWithBot
  map_id _ := LatticeHom.withTopWithBot_id
  map_comp _ _ := LatticeHom.withTopWithBot_comp _ _
#align Lat_to_BddLat latToBddLatCat

/-- `latToBddLatCat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLatCat`. -/
def latToBddLatCatForgetAdjunction : latToBddLatCat.{u} ⊣ forget₂ BddLatCat LatCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.map_inf' _ _) }
          invFun := fun f => LatticeHom.withTopWithBot' f
          left_inv := fun f =>
            BoundedLatticeHom.ext fun a =>
              match a with
              | none => f.map_top'.symm
              | some none => f.map_bot'.symm
              | some (some a) => rfl
          right_inv := fun f => LatticeHom.ext fun a => rfl }
      homEquiv_naturality_left_symm := fun f g =>
        BoundedLatticeHom.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some a) => rfl
      homEquiv_naturality_right := fun f g => LatticeHom.ext fun a => rfl }
#align Lat_to_BddLat_forget_adjunction latToBddLatCatForgetAdjunction

/-- `latToBddLatCat` and `OrderDual` commute. -/
-- Porting note: the `simpNF` linter is not happy as it simplifies something that does not
-- have prettyprinting effects.
-- It seems like it is simplifying for example the first type
-- `(↑(BddLatCat.dualEquiv.functor.obj (latToBddLatCat.obj X.op.unop)).toLat)`
-- to
-- `(↑(latToBddLatCat.obj X).toLat)ᵒᵈ`
-- Interestingly, the linter is silent, if the proof is `sorry`-ed out...
-- see https://github.com/leanprover-community/mathlib4/issues/5049
-- @[simps!]
def latToBddLatCatCompDualIsoDualCompLatToBddLatCat :
    latToBddLatCat.{u} ⋙ BddLatCat.dual ≅ LatCat.dual ⋙ latToBddLatCat :=
  Adjunction.leftAdjointUniq (latToBddLatCatForgetAdjunction.comp BddLatCat.dualEquiv.toAdjunction)
    (LatCat.dualEquiv.toAdjunction.comp latToBddLatCatForgetAdjunction)
#align Lat_to_BddLat_comp_dual_iso_dual_comp_Lat_to_BddLatCat latToBddLatCatCompDualIsoDualCompLatToBddLatCat
