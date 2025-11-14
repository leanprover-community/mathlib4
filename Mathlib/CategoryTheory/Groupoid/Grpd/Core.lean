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

@[simp]
lemma adjunction_homEquiv_apply (F : G ⥤ C) :
    adjunction.homEquiv (Grpd.of G) (Cat.of C) F = functorToCore F :=
  rfl

@[simp]
lemma adjunction_homEquiv_symm_apply (F : G ⥤ Core C) :
    (adjunction.homEquiv (Grpd.of G) (Cat.of C)).symm F = F ⋙ inclusion C :=
  rfl

@[simp]
lemma adjunction_unit_app :
    adjunction.unit.app (Grpd.of G) = functorToCore (𝟭 _) := rfl

@[simp]
lemma adjunction_counit_app :
    (adjunction.counit.app (Cat.of C)) = inclusion C := rfl

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
