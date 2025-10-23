/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.CategoryTheory.Limits.Preserves.Basic

universe v₀ u₀ v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable {J : Type u₀} [Category.{v₀} J]

variable (D) in
/-- The property of objects in `C ⥤ D` which preserves the colimit
of a functor `F : J ⥤ C`. -/
abbrev preservesColimit (F : J ⥤ C) : ObjectProperty (C ⥤ D) := PreservesColimit F

@[simp]
lemma preservesColimit_iff (F : J ⥤ C) (G : C ⥤ D) :
    preservesColimit D F G ↔ PreservesColimit F G := Iff.rfl

variable (J D) in
def preservesColimitsOfShape : ObjectProperty (C ⥤ D) := by
  refine ⨅ (j : J), ?_
  sorry

end Functor

end CategoryTheory
