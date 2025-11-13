/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# The forgetful-core adjunction

Taking the core of a category defines a functor `Cat ⥤ Grpd`. This functor is left adjoint
to the forgetful functor from `Grpd ⥤ Cat`.

# Main definitions

* `CategoryTheory.Core.functor`: the functor `Cat ⥤ Grpd` that on objects takes
  the core of a category
* `CategoryTheory.Core.adjunction`: the adjunction with the forgetful functor
  `Grpd.forgetToCat` on the left, and the core functor `Core.functor` on the right.
* An instance that `Grpd.forgetToCat` is coreflective.

-/

universe v u v₁ u₁

noncomputable section

namespace CategoryTheory
namespace Core

variable {G : Type u} [Groupoid.{v} G] {C : Type u} [Category.{v} C]

/-- The functor from `Cat` to `Grpd` that takes the core of a category, on objects. -/
def functor : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := F.core

/-- The adjunction between the forgetful functor from `Grpd` to `Cat` and the core
functor from `Cat` to `Grpd`. -/
def adjunction : Grpd.forgetToCat ⊣ functor :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := functorEquiv
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right := functorToCore_comp_right }

lemma adjunction_homEquiv_apply (F : G ⥤ C) :
    adjunction.homEquiv (Grpd.of G) (Cat.of C) F = functorToCore F :=
  rfl

@[simp]
lemma adjunction_homEquiv_apply_obj (F : G ⥤ C) (X : G) :
    ((adjunction.homEquiv (Grpd.of G) (Cat.of C) F).obj X).of = F.obj X :=
  rfl

@[simp]
lemma adjunction_homEquiv_apply_map_iso_hom (F : G ⥤ C) {X Y : G} (f : X ⟶ Y) :
    ((adjunction.homEquiv (Grpd.of G) (Cat.of C) F).map f).iso.hom = F.map f :=
  rfl

@[simp]
lemma adjunction_homEquiv_apply_map_iso_inv (F : G ⥤ C) {X Y : G} (f : X ⟶ Y) :
    ((adjunction.homEquiv (Grpd.of G) (Cat.of C) F).map f).iso.inv = inv (F.map f) := by
  simp [adjunction_homEquiv_apply]

lemma adjunction_homEquiv_symm_apply (F : G ⥤ Core C) :
    (adjunction.homEquiv (Grpd.of G) (Cat.of C)).symm F = F ⋙ inclusion C :=
  rfl

@[simp]
lemma adjunction_homEquiv_symm_apply_obj (F : G ⥤ Core C) (X : G) :
    ((adjunction.homEquiv (Grpd.of G) (Cat.of C)).symm F).obj X = (F.obj X).of :=
  rfl

@[simp]
lemma adjunction_homEquiv_symm_apply_map (F : G ⥤ Core C) {X Y : G} (f : X ⟶ Y) :
    ((adjunction.homEquiv (Grpd.of G) (Cat.of C)).symm F).map f = (F.map f).iso.hom :=
  rfl

@[simp]
lemma adjunction_unit_app_obj (X : G) :
    (adjunction.unit.app (Grpd.of G)).obj X = ⟨X⟩ :=
  rfl

lemma adjunction_unit_app_map {X Y : G} (f : X ⟶ Y) :
    (adjunction.unit.app (Grpd.of G)).map f = (functorToCore _).map f :=
  rfl

@[simp]
lemma adjunction_unit_app_map_iso_hom {X Y : G} (f : X ⟶ Y) :
    ((adjunction.unit.app (Grpd.of G)).map f).iso.hom = f :=
  rfl

@[simp]
lemma adjunction_unit_app_map_iso_inv {X Y : G} (f : X ⟶ Y) :
    ((adjunction.unit.app (Grpd.of G)).map f).iso.inv = Groupoid.inv f :=
  rfl

@[simp]
lemma adjunction_counit_app_obj (X : Core C) :
    (adjunction.counit.app (Cat.of C)).obj X = X.of :=
  rfl

@[simp]
lemma adjunction_counit_app_map {X Y : Core C} (f : X ⟶ Y) :
    (adjunction.counit.app (Cat.of C)).map f = f.iso.hom :=
  rfl

end Core

namespace Grpd

open Functor Core

instance : IsLeftAdjoint Grpd.forgetToCat :=
  IsLeftAdjoint.mk ⟨functor, ⟨adjunction⟩⟩

instance : IsRightAdjoint functor :=
  IsRightAdjoint.mk ⟨Grpd.forgetToCat, ⟨adjunction⟩⟩

instance : Coreflective Grpd.forgetToCat where
  R := functor
  adj := adjunction

end Grpd

end CategoryTheory
