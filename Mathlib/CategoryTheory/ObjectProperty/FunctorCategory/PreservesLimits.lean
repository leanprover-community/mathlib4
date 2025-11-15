/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Preservation of limits, as a property of objects in the functor category

We make the typeclass `PreservesLimitsOfShape K` (resp. `PreservesFiniteLimits`)
properties of objects in the functor category `J ⥤ C`, and show that
they are stable under colimits of shape `K'` when colimits of shape `K'`
commute to limits of shape `K` (resp. to finite limits).

-/

namespace CategoryTheory

open Limits

variable (K K' J C K' : Type*) [Category K] [Category K'] [Category J] [Category C]

namespace ObjectProperty

variable {J C}

/-- The property of objects in the functor category `J ⥤ C`
which preserves limits of shape `K`. -/
def preservesLimitsOfShape : ObjectProperty (J ⥤ C) :=
  fun F ↦ PreservesLimitsOfShape K F

@[simp]
lemma preservesLimitsOfShape_iff (F : J ⥤ C) :
    preservesLimitsOfShape K F ↔ PreservesLimitsOfShape K F := Iff.rfl

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite limits. -/
def preservesFiniteLimits : ObjectProperty (J ⥤ C) :=
  fun F ↦ PreservesFiniteLimits F

@[simp]
lemma preservesFiniteLimits_iff (F : J ⥤ C) :
    preservesFiniteLimits F ↔ PreservesFiniteLimits F := Iff.rfl

instance [HasColimitsOfShape K' C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)).IsClosedUnderColimitsOfShape K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have (k' : K') : PreservesLimitsOfShape K (h.diag.obj k') := h.prop_diag_obj k'
    have : PreservesLimitsOfShape K h.diag.flip := ⟨fun {F} ↦ ⟨fun {c} hc ↦
      ⟨evaluationJointlyReflectsLimits _
        (fun k' ↦ isLimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents (fun j ↦ (colimit.isColimit (h.diag.flip.obj j)).coconePointUniqueUpToIso
        (isColimitOfPreserves ((evaluation _ _).obj j) h.isColimit))
    exact preservesLimitsOfShape_of_natIso e

instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesFiniteLimits : ObjectProperty (J ⥤ C)) K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    exact ⟨fun K _ _ ↦ (preservesLimitsOfShape K).prop_of_isColimit h.isColimit (fun k' ↦ by
      have : PreservesFiniteLimits (h.diag.obj k') := h.prop_diag_obj k'
      rw [preservesLimitsOfShape_iff]
      infer_instance)⟩

end ObjectProperty

end CategoryTheory
