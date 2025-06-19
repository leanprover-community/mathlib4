/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Order.Category.BddOrd
import Mathlib.Order.Category.Lat
import Mathlib.Order.Category.Semilat
import Mathlib.Order.Hom.WithTopBot

/-!
# The category of bounded lattices

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BddLat extends Lat where
  [isBoundedOrder : BoundedOrder toLat]

/-- The underlying lattice of a bounded lattice. -/
add_decl_doc BddLat.toLat

namespace BddLat

instance : CoeSort BddLat Type* :=
  ⟨fun X => X.toLat⟩

attribute [instance] BddLat.isBoundedOrder

/-- Construct a bundled `BddLat` from `Lattice` + `BoundedOrder`. -/
abbrev of (α : Type*) [Lattice α] [BoundedOrder α] : BddLat where
  carrier := α

theorem coe_of (α : Type*) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

/-- The type of morphisms in `BddLat`. -/
@[ext]
structure Hom (X Y : BddLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

instance : Inhabited BddLat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BddLat where
  Hom := Hom
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory BddLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `BddLat` back into a `BoundedLatticeHom`. -/
abbrev Hom.hom {X Y : BddLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddLat) f

/-- Typecheck a `BoundedLatticeHom` as a morphism in `BddLat`. -/
abbrev ofHom {X Y : Type u} [Lattice X] [BoundedOrder X] [Lattice Y] [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : BddLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
lemma hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : Lat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma ext {X Y : BddLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[ext]
lemma hom_ext {X Y : BddLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

instance hasForgetToBddOrd : HasForget₂ BddLat BddOrd where
  forget₂.obj X := .of X
  forget₂.map f := BddOrd.ofHom f.hom.toBoundedOrderHom

instance hasForgetToLat : HasForget₂ BddLat Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom.toLatticeHom

instance hasForgetToSemilatSup : HasForget₂ BddLat SemilatSupCat where
  forget₂.obj X := .of X
  forget₂.map f := f.hom.toSupBotHom

instance hasForgetToSemilatInf : HasForget₂ BddLat SemilatInfCat where
  forget₂.obj X := .of X
  forget₂.map f := f.hom.toInfTopHom

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
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : BddLat ⥤ BddLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

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
  obj X := .of <| WithTop <| WithBot X
  map f := BddLat.ofHom <| LatticeHom.withTopWithBot f.hom

/-- `latToBddLat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLat`. -/
def latToBddLatForgetAdjunction : latToBddLat.{u} ⊣ forget₂ BddLat Lat :=
  Adjunction.mkOfHomEquiv
    { homEquiv X _ :=
        { toFun f := Lat.ofHom
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_inf' _ _) }
          invFun f := BddLat.ofHom <| LatticeHom.withTopWithBot' f.hom
          left_inv := fun f =>
            BddLat.ext fun a =>
              match a with
              | none => f.hom.map_top'.symm
              | some none => f.hom.map_bot'.symm
              | some (some _) => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        BddLat.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some _) => rfl
      homEquiv_naturality_right := fun _ _ => Lat.ext fun _ => rfl }

/-- `latToBddLat` and `OrderDual` commute. -/
def latToBddLatCompDualIsoDualCompLatToBddLat :
    latToBddLat.{u} ⋙ BddLat.dual ≅ Lat.dual ⋙ latToBddLat :=
  Adjunction.leftAdjointUniq (latToBddLatForgetAdjunction.comp BddLat.dualEquiv.toAdjunction)
    (Lat.dualEquiv.toAdjunction.comp latToBddLatForgetAdjunction)
