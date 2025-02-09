/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Order.Category.BddOrd
import Mathlib.Order.Category.Lat
import Mathlib.Order.Category.Semilat

/-!
# The category of bounded lattices

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BddLat where
  /-- The underlying lattice of a bounded lattice. -/
  toLat : Lat
  [isBoundedOrder : BoundedOrder toLat]

namespace BddLat

instance : CoeSort BddLat Type* :=
  ⟨fun X => X.toLat⟩

instance (X : BddLat) : Lattice X :=
  X.toLat.str

attribute [instance] BddLat.isBoundedOrder

/-- Construct a bundled `BddLat` from `Lattice` + `BoundedOrder`. -/
def of (α : Type*) [Lattice α] [BoundedOrder α] : BddLat :=
  -- Porting note: was `⟨⟨α⟩⟩`, see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨{α := α}⟩

@[simp]
theorem coe_of (α : Type*) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited BddLat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BddLat where
  Hom X Y := BoundedLatticeHom X Y
  id X := BoundedLatticeHom.id X
  comp f g := g.comp f
  id_comp := BoundedLatticeHom.comp_id
  comp_id := BoundedLatticeHom.id_comp
  assoc _ _ _ := BoundedLatticeHom.comp_assoc _ _ _

-- Porting note: added.
instance instFunLike (X Y : BddLat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (BoundedLatticeHom X Y) X Y from inferInstance

instance : HasForget BddLat where
  forget :=
  { obj := (↑)
    map := DFunLike.coe }
  forget_faithful := ⟨(DFunLike.coe_injective ·)⟩

instance hasForgetToBddOrd : HasForget₂ BddLat BddOrd where
  forget₂ :=
    { obj := fun X => BddOrd.of X
      map := fun {_ _} => BoundedLatticeHom.toBoundedOrderHom }

instance hasForgetToLat : HasForget₂ BddLat Lat where
  forget₂ :=
    -- Porting note: was `⟨X⟩`, see https://github.com/leanprover-community/mathlib4/issues/4998
    { obj := fun X => {α := X}
      map := fun {_ _} => BoundedLatticeHom.toLatticeHom }

instance hasForgetToSemilatSup : HasForget₂ BddLat SemilatSupCat where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun {_ _} => BoundedLatticeHom.toSupBotHom }

instance hasForgetToSemilatInf : HasForget₂ BddLat SemilatInfCat where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun {_ _} => BoundedLatticeHom.toInfTopHom }

@[simp]
theorem coe_forget_to_bddOrd (X : BddLat) : ↥((forget₂ BddLat BddOrd).obj X) = ↥X :=
  rfl

@[simp]
theorem coe_forget_to_lat (X : BddLat) : ↥((forget₂ BddLat Lat).obj X) = ↥X :=
  rfl

@[simp]
theorem coe_forget_to_semilatSup (X : BddLat) :
    ↥((forget₂ BddLat SemilatSupCat).obj X) = ↥X :=
  rfl

@[simp]
theorem coe_forget_to_semilatInf (X : BddLat) :
    ↥((forget₂ BddLat SemilatInfCat).obj X) = ↥X :=
  rfl

theorem forget_lat_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat Lat ⋙ forget₂ Lat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl

theorem forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatSupCat ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl

theorem forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatInfCat ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom _ _)
  inv := (e.symm : BoundedLatticeHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps]
def dual : BddLat ⥤ BddLat where
  obj X := of Xᵒᵈ
  map {_ _} := BoundedLatticeHom.dual

/-- The equivalence between `BddLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BddLat ≌ BddLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end BddLat

theorem bddLat_dual_comp_forget_to_bddOrd :
    BddLat.dual ⋙ forget₂ BddLat BddOrd =
    forget₂ BddLat BddOrd ⋙ BddOrd.dual :=
  rfl

theorem bddLat_dual_comp_forget_to_lat :
    BddLat.dual ⋙ forget₂ BddLat Lat = forget₂ BddLat Lat ⋙ Lat.dual :=
  rfl

theorem bddLat_dual_comp_forget_to_semilatSupCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatSupCat =
    forget₂ BddLat SemilatInfCat ⋙ SemilatInfCat.dual :=
  rfl

theorem bddLat_dual_comp_forget_to_semilatInfCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatInfCat =
    forget₂ BddLat SemilatSupCat ⋙ SemilatSupCat.dual :=
  rfl

/-- The functor that adds a bottom and a top element to a lattice. This is the free functor. -/
def latToBddLat : Lat.{u} ⥤ BddLat where
  obj X := BddLat.of <| WithTop <| WithBot X
  map := LatticeHom.withTopWithBot
  map_id _ := LatticeHom.withTopWithBot_id
  map_comp _ _ := LatticeHom.withTopWithBot_comp _ _

/-- `latToBddLat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLat`. -/
def latToBddLatForgetAdjunction : latToBddLat.{u} ⊣ forget₂ BddLat Lat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X _ =>
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
              | some (some _) => rfl
          right_inv := fun _ => LatticeHom.ext fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        BoundedLatticeHom.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some _) => rfl
      homEquiv_naturality_right := fun _ _ => LatticeHom.ext fun _ => rfl }

/-- `latToBddLat` and `OrderDual` commute. -/
def latToBddLatCompDualIsoDualCompLatToBddLat :
    latToBddLat.{u} ⋙ BddLat.dual ≅ Lat.dual ⋙ latToBddLat :=
  Adjunction.leftAdjointUniq (latToBddLatForgetAdjunction.comp BddLat.dualEquiv.toAdjunction)
    (Lat.dualEquiv.toAdjunction.comp latToBddLatForgetAdjunction)
