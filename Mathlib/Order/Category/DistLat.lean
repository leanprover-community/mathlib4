/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Lat

/-!
# The category of distributive lattices

This file defines `DistLat`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLat` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BddDistLat`.
-/

@[expose] public section


universe u

open CategoryTheory

/-- The category of distributive lattices. -/
structure DistLat where
  /-- The underlying distributive lattice. -/
  carrier : Type*
  [str : DistribLattice carrier]

attribute [instance] DistLat.str

initialize_simps_projections DistLat (carrier → coe, -str)

namespace DistLat

instance : CoeSort DistLat.{u} (Type u) :=
  ⟨DistLat.carrier⟩

attribute [coe] DistLat.carrier

/-- Construct a bundled `DistLat` from the underlying type and typeclass. -/
abbrev of (X : Type*) [DistribLattice X] : DistLat := ⟨X⟩

set_option backward.privateInPublic true in
/-- The type of morphisms in `DistLat R`. -/
@[ext]
structure Hom (X Y : DistLat.{u}) where
  private mk ::
  /-- The underlying `LatticeHom`. -/
  hom' : LatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category DistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory DistLat (LatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `DistLat` back into a `LatticeHom`. -/
abbrev Hom.hom {X Y : DistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := DistLat) f

/-- Typecheck a `LatticeHom` as a morphism in `DistLat`. -/
abbrev ofHom {X Y : Type u} [DistribLattice X] [DistribLattice Y] (f : LatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := DistLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : DistLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [DistribLattice X] : (DistLat.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : DistLat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

@[simp]
lemma hom_comp {X Y Z : DistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
lemma ofHom_id {X : Type u} [DistribLattice X] : ofHom (LatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [DistribLattice Y] [DistribLattice Z]
    (f : LatticeHom X Y) (g : LatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

instance hasForgetToLat : HasForget₂ DistLat Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom

/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps]
def Iso.mk {α β : DistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : DistLat ⥤ DistLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `DistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : DistLat ≌ DistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl

end DistLat

theorem distLat_dual_comp_forget_to_Lat :
    DistLat.dual ⋙ forget₂ DistLat Lat = forget₂ DistLat Lat ⋙ Lat.dual :=
  rfl
