/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Preservation of limits, as a property of objects in the functor category

We make the typeclass `PreservesLimitsOfShape K` (resp. `PreservesFiniteLimits`)
a property of objects in the functor category `J ⥤ C`, and show that
it is stable under colimits of shape `K'` when they
commute to limits of shape `K` (resp. to finite limits).

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {J J' C D : Type*} (K K' : Type*)
  [Category* K] [Category* K'] [Category* J] [Category* J'] [Category* C] [Category* D]

namespace ObjectProperty

variable {K} in
/-- The property of objects in the functor category `J ⥤ C`
which preserves the limit of a functor `F : K ⥤ J`. -/
abbrev preservesLimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesLimit F

@[simp]
lemma preservesLimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesLimit F G ↔ PreservesLimit F G := Iff.rfl

lemma congr_preservesLimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesLimit (C := C) F = preservesLimit (C := C) F' := by
  ext G
  simp_rw [preservesLimit_iff]
  exact ⟨fun h ↦ preservesLimit_of_iso_diagram _ e,
    fun h ↦ preservesLimit_of_iso_diagram _ e.symm⟩

variable {K} in
/-- The property of objects in the functor category `J ⥤ C`
which preserves the colimit of a functor `F : K ⥤ J`. -/
abbrev preservesColimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesColimit F

@[simp]
lemma preservesColimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesColimit F G ↔ PreservesColimit F G := Iff.rfl

lemma congr_preservesColimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesColimit (C := C) F = preservesColimit (C := C) F' := by
  ext G
  simp_rw [preservesColimit_iff]
  exact ⟨fun h ↦ preservesColimit_of_iso_diagram _ e,
    fun h ↦ preservesColimit_of_iso_diagram _ e.symm⟩

/-- The property of objects in the functor category `J ⥤ C`
which preserves limits of shape `K`. -/
abbrev preservesLimitsOfShape : ObjectProperty (J ⥤ C) := PreservesLimitsOfShape K

@[simp]
lemma preservesLimitsOfShape_iff (F : J ⥤ C) :
    preservesLimitsOfShape K F ↔ PreservesLimitsOfShape K F := Iff.rfl

lemma preservesLimitsOfShape_eq_iSup :
    preservesLimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesLimit F := by
  ext G
  simp only [preservesLimitsOfShape_iff, iInf_apply, preservesLimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance⟩⟩

variable (J C) {K K'} in
lemma congr_preservesLimitsOfShape (e : K ≌ K') :
    preservesLimitsOfShape (J := J) (C := C) K = preservesLimitsOfShape K' := by
  ext G
  simp only [preservesLimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesLimitsOfShape_of_equiv e _,
    fun _ ↦ preservesLimitsOfShape_of_equiv e.symm _⟩

/-- The property of objects in the functor category `J ⥤ C`
which preserves colimits of shape `K`. -/
abbrev preservesColimitsOfShape : ObjectProperty (J ⥤ C) := PreservesColimitsOfShape K

@[simp]
lemma preservesColimitsOfShape_iff (F : J ⥤ C) :
    preservesColimitsOfShape K F ↔ PreservesColimitsOfShape K F := Iff.rfl

lemma preservesColimitsOfShape_eq_iSup :
    preservesColimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesColimit F := by
  ext G
  simp only [preservesColimitsOfShape_iff, iInf_apply, preservesColimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance⟩⟩

variable (J C) {K K'} in
lemma congr_preservesColimitsOfShape (e : K ≌ K') :
    preservesColimitsOfShape (J := J) (C := C) K = preservesColimitsOfShape K' := by
  ext G
  simp only [preservesColimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesColimitsOfShape_of_equiv e _,
    fun _ ↦ preservesColimitsOfShape_of_equiv e.symm _⟩

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite limits. -/
abbrev preservesFiniteLimits : ObjectProperty (J ⥤ C) := PreservesFiniteLimits

@[simp]
lemma preservesFiniteLimits_iff (F : J ⥤ C) :
    preservesFiniteLimits F ↔ PreservesFiniteLimits F := Iff.rfl

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite colimits. -/
abbrev preservesFiniteColimits : ObjectProperty (J ⥤ C) := PreservesFiniteColimits

@[simp]
lemma preservesFiniteColimits_iff (F : J ⥤ C) :
    preservesFiniteColimits F ↔ PreservesFiniteColimits F := Iff.rfl

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
