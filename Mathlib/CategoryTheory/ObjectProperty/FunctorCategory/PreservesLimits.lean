/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Fubini2
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Preservation of limits, as a property of objects in the functor category

We make the typeclass `PreservesLimitsOfShape K` (resp. `PreservesFiniteLimits`)
a property of objects in the functor category `J ⥤ C`, and show that
it is stable under colimits of shape `K'` when colimits of shape `K'`
commute to limits of shape `K` (resp. to finite limits).

-/

namespace CategoryTheory

open Limits

variable (K K' J C K' : Type*) [Category K] [Category K'] [Category J] [Category C]

namespace ObjectProperty

variable {J C}

/-- The property of objects in the functor category `J ⥤ C`
which preserves limits of shape `K`. -/
abbrev preservesLimitsOfShape : ObjectProperty (J ⥤ C) := PreservesLimitsOfShape K

@[simp]
lemma preservesLimitsOfShape_iff (F : J ⥤ C) :
    preservesLimitsOfShape K F ↔ PreservesLimitsOfShape K F := Iff.rfl

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite limits. -/
abbrev preservesFiniteLimits : ObjectProperty (J ⥤ C) := PreservesFiniteLimits

@[simp]
lemma preservesFiniteLimits_iff (F : J ⥤ C) :
    preservesFiniteLimits F ↔ PreservesFiniteLimits F := Iff.rfl

/-- The property of objects in the functor category `J ⥤ C`
which preserves colimits of shape `K`. -/
abbrev preservesColimitsOfShape : ObjectProperty (J ⥤ C) := PreservesColimitsOfShape K

@[simp]
lemma preservesColimitsOfShape_iff (F : J ⥤ C) :
    preservesColimitsOfShape K F ↔ PreservesColimitsOfShape K F := Iff.rfl

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite colimits. -/
abbrev preservesFiniteColimits : ObjectProperty (J ⥤ C) := PreservesFiniteColimits

@[simp]
lemma preservesFiniteColimits_iff (F : J ⥤ C) :
    preservesFiniteColimits F ↔ PreservesFiniteColimits F := Iff.rfl

instance [HasColimitsOfShape K' C] :
    (preservesColimitsOfShape K : ObjectProperty (J ⥤ C)).IsClosedUnderColimitsOfShape K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
    let Φ := F ⋙ h.diag.flip
    let D₁ : DiagramOfCocones Φ :=
      { obj k :=
          { pt := G.obj (F.obj k)
            ι.app k' := (h.ι.app k').app (F.obj k) }
        map {k₁ k₂} f :=
          { hom := G.map (F.map f) } }
    let D₂ : DiagramOfCocones Φ.flip :=
      { obj k' :=
          { pt := (h.diag.obj k').obj c.pt
            ι.app k := (h.diag.obj k').map (c.ι.app k)
            ι.naturality {k₁ k₂} f := by simp [Φ, ← Functor.map_comp] }
        map {k'₁ k'₂} f :=
          { hom := (h.diag.map f).app c.pt } }
    exact DiagramOfCocones.isColimitFubiniFlip D₁ D₂
      (fun k ↦ isColimitOfPreserves ((evaluation _ _).obj (F.obj k)) h.isColimit)
      (fun k' ↦ isColimitOfPreserves (h.diag.obj k') hc)
      (isColimitOfPreserves ((evaluation _ _).obj c.pt) h.isColimit) (Iso.refl _)

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

instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesFiniteLimits : ObjectProperty (J ⥤ C)) K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    exact ⟨fun K _ _ ↦ (preservesLimitsOfShape K).prop_of_isColimit h.isColimit inferInstance⟩

end ObjectProperty

end CategoryTheory
