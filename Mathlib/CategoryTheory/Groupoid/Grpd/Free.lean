/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Groupoid.Grpd
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Free groupoid functor

This file defines the free groupoid functor and its associated adjunction.

## Main results

Given a type `C` and a category instance on `C`:

- `CategoryTheory.Grpd.free`: the free functor from `Cat` to `Grpd` that takes a
  category to the free groupoid on it.
- `CategoryTheory.Grpd.freeForgetAdjunction`: that `free` is left adjoint to
  `Grpd.forgetToCat`.

-/

universe v u

namespace CategoryTheory
namespace Grpd

open FreeGroupoid

/-- The free groupoid construction on a category as a functor. -/
def free : Cat.{u, u} ⥤ Grpd.{u, u} where
  obj C := Grpd.of <| FreeGroupoid C
  map {C D} F := map F
  map_id C := by simp [Grpd.id_eq_id, map_id, Cat.id_eq_id]
  map_comp F G := by simp [Grpd.comp_eq_comp, map_comp, Cat.comp_eq_comp]

@[simp]
lemma free_obj (C : Cat.{u, u}) : free.obj C = FreeGroupoid C :=
  rfl

@[simp]
lemma free_map {C D : Cat.{u, u}} (F : C ⟶ D) : free.map F = map F :=
  rfl

/-- The free-forgetful adjunction between `Grpd` and `Cat`. -/
def freeForgetAdjunction : free ⊣ Grpd.forgetToCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := FreeGroupoid.functorEquiv
      homEquiv_naturality_left_symm _ _ := (FreeGroupoid.map_comp_lift _ _).symm
      homEquiv_naturality_right _ _ := rfl }

variable {C : Type u} [Category.{u} C] {D : Type u} [Groupoid.{u} D]

@[simp]
lemma freeForgetAdjunction_homEquiv_apply (F : FreeGroupoid C ⥤ D) :
    freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D) F = FreeGroupoid.of C ⋙ F :=
  rfl

@[simp]
lemma freeForgetAdjunction_homEquiv_symm_apply (F : C ⥤ D) :
    (freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D)).symm F = map F ⋙ lift (𝟭 D) :=
  rfl

@[simp]
lemma freeForgetAdjunction_unit_app :
    freeForgetAdjunction.unit.app (Cat.of C) = FreeGroupoid.of C :=
  rfl

@[simp]
lemma freeForgetAdjunction_counit_app :
    freeForgetAdjunction.counit.app (Grpd.of D) = lift (𝟭 D) :=
  rfl

instance : Reflective Grpd.forgetToCat where
  L := free
  adj := freeForgetAdjunction

end Grpd
end CategoryTheory
