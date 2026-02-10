/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Hom.Lattice

/-!
# The category of lattices

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → WithTop (WithBot X)`.
-/

@[expose] public section

universe u

open CategoryTheory

/-- The category of lattices. -/
structure Lat where
  /-- The underlying lattices. -/
  (carrier : Type*)
  [str : Lattice carrier]

attribute [instance] Lat.str

initialize_simps_projections Lat (carrier → coe, -str)

namespace Lat

instance : CoeSort Lat (Type _) :=
  ⟨Lat.carrier⟩

attribute [coe] Lat.carrier

/-- Construct a bundled `Lat` from the underlying type and typeclass. -/
abbrev of (X : Type*) [Lattice X] : Lat := ⟨X⟩

set_option backward.privateInPublic true in
/-- The type of morphisms in `Lat R`. -/
@[ext]
structure Hom (X Y : Lat.{u}) where
  private mk ::
  /-- The underlying `LatticeHom`. -/
  hom' : LatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category Lat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory Lat (LatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Lat` back into a `LatticeHom`. -/
abbrev Hom.hom {X Y : Lat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Lat) f

/-- Typecheck a `LatticeHom` as a morphism in `Lat`. -/
abbrev ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Lat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : Lat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [Lattice X] : (Lat.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

@[simp]
lemma hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
lemma ofHom_id {X : Type u} [Lattice X] : ofHom (LatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [Lattice X] [Lattice Y] [Lattice Z]
    (f : LatticeHom X Y) (g : LatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

instance hasForgetToPartOrd : HasForget₂ Lat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `Lat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : Lat ≌ Lat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end Lat

theorem Lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl
