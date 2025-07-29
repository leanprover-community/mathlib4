/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.Lat
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# The category of frames

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/


universe u

open CategoryTheory Order

/-- The category of frames. -/
structure Frm where
  /-- The underlying frame. -/
  (carrier : Type*)
  [str : Frame carrier]

attribute [instance] Frm.str

initialize_simps_projections Frm (carrier → coe, -str)

namespace Frm

instance : CoeSort Frm (Type _) :=
  ⟨Frm.carrier⟩

attribute [coe] Frm.carrier

/-- Construct a bundled `Frm` from the underlying type and typeclass. -/
abbrev of (X : Type*) [Frame X] : Frm := ⟨X⟩

/-- The type of morphisms in `Frm R`. -/
@[ext]
structure Hom (X Y : Frm.{u}) where
  private mk ::
  /-- The underlying `FrameHom`. -/
  hom' : FrameHom X Y

instance : Category Frm.{u} where
  Hom X Y := Hom X Y
  id X := ⟨FrameHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

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

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : Frm} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : Frm} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : Frm} (f : X ⟶ Y) :
    (forget Frm).map f = f := rfl

@[ext]
lemma ext {X Y : Frm} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [Frame X] : (Frm.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : Frm} : (𝟙 X : X ⟶ X).hom = FrameHom.id _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : Frm) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : Frm} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {X Y : Frm} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [Frame X] : ofHom (FrameHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [Frame X] [Frame Y] [Frame Z]
    (f : FrameHom X Y) (g : FrameHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : Frm} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : Frm} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

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
