/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Lat
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# The category of frames

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/

@[expose] public section


universe u

open CategoryTheory Order

/-- The category of frames. -/
structure Frm where
  /-- Construct a bundled `Frm` from the underlying type and typeclass. -/
  of ::
  /-- The underlying frame. -/
  (carrier : Type*)
  [str : Frame carrier]

attribute [instance] Frm.str

initialize_simps_projections Frm (carrier → coe, -str)

namespace Frm

instance : CoeSort Frm (Type _) :=
  ⟨Frm.carrier⟩

attribute [coe] Frm.carrier

set_option backward.privateInPublic true in
/-- The type of morphisms in `Frm R`. -/
@[ext]
structure Hom (X Y : Frm.{u}) where
  private mk ::
  /-- The underlying `FrameHom`. -/
  hom' : FrameHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category Frm.{u} where
  Hom X Y := Hom X Y
  id X := ⟨FrameHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory Frm (FrameHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Frm` back into a `FrameHom`. -/
abbrev Hom.hom {X Y : Frm.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Frm) f

/-- Typecheck a `FrameHom` as a morphism in `Frm`. -/
abbrev ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Frm) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : Frm.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [Frame X] : (Frm.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : Frm} : (𝟙 X : X ⟶ X).hom = FrameHom.id _ := rfl

@[simp]
lemma hom_comp {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
lemma ofHom_id {X : Type u} [Frame X] : ofHom (FrameHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [Frame X] [Frame Y] [Frame Z]
    (f : FrameHom X Y) (g : FrameHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

instance : Inhabited Frm :=
  ⟨of PUnit⟩

instance hasForgetToLat : HasForget₂ Frm Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Frm.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

end Frm
