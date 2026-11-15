/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.ColimitLimit
public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits

/-!
# Exact colimits and preservation of limits

If a category `C` has exact colimits of shape `K'` and has finite limits, we
show that the full subcategory of `J ⥤ C` consisting of functors preserving finite
limits is stable under colimits of shape `K'`

-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {J C : Type*} (K K' : Type*)
  [Category* K] [Category* K'] [Category* J] [Category* C]

instance [HasColimitsOfShape K' C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)).IsClosedUnderColimitsOfShape K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    have : PreservesLimitsOfShape K h.diag.flip := ⟨fun {F} ↦ ⟨fun {c} hc ↦
      ⟨evaluationJointlyReflectsLimits _
        (fun k' ↦ isLimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents
        (fun j ↦ (colimit.isColimit (h.diag.flip.obj j)).coconePointUniqueUpToIso
          (isColimitOfPreserves ((evaluation _ _).obj j) h.isColimit))
    exact preservesLimitsOfShape_of_natIso e

instance [HasColimitsOfShape K' C] [HasLimitsOfShape K C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (preservesColimitsOfShape K' : ObjectProperty (J ⥤ C)) K where
  limitsOfShape_le := by
    have : PreservesColimitsOfShape K' (lim (J := K) (C := C)) := by
      rwa [preservesColimitsOfShape_lim_iff_preservesLimitsOfShape_colim]
    intro G ⟨p⟩
    have := p.prop_diag_obj
    have : PreservesColimitsOfShape K' p.diag.flip := ⟨fun {F} ↦ ⟨fun {c} hc ↦
      ⟨evaluationJointlyReflectsColimits _
        (fun k ↦ isColimitOfPreserves (p.diag.obj k) hc)⟩⟩⟩
    let e : G ≅ p.diag.flip ⋙ lim :=
      NatIso.ofComponents
        (fun j ↦ (isLimitOfPreserves ((evaluation _ _).obj j) p.isLimit).conePointUniqueUpToIso
          (limit.isLimit (p.diag.flip.obj j))) (fun {j₁ j₂} f ↦ by
            dsimp
            ext
            simp [IsLimit.conePointUniqueUpToIso])
    exact preservesColimitsOfShape_of_natIso e.symm

instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesFiniteLimits : ObjectProperty (J ⥤ C)) K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    exact ⟨fun K _ _ ↦ (preservesLimitsOfShape K).prop_of_isColimit h.isColimit inferInstance⟩

instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] [HasFiniteLimits C] :
    ObjectProperty.IsClosedUnderFiniteLimits
      (preservesColimitsOfShape K' : ObjectProperty (J ⥤ C)) where

end CategoryTheory.ObjectProperty
