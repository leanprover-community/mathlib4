/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.TypeFlat
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Points of a site

-/

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace GrothendieckTopology

structure Point where
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) (A : Type u') [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A] [HasFiniteLimits A]

instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
    hasColimitsOfShape_of_finallySmall _ _

noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  colimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A)

-- TODO: show `presheafFiber` inverts `J.W` under suitable assumptions

instance : PreservesFiniteLimits (Φ.presheafFiber A) := sorry

noncomputable def sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber A

variable (K : Type) [SmallCategory K] [FinCategory K]

instance : PreservesFiniteLimits (Φ.sheafFiber A) := comp_preservesFiniteLimits _ _

end Point

end GrothendieckTopology

end CategoryTheory
