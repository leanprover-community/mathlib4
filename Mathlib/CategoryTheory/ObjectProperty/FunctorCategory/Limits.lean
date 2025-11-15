/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Functors which preserves limits

-/

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

instance (F : J ⥤ C) : (preservesColimit D F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesColimit_of_natIso _ e

@[simp]
lemma preservesColimit_iff (F : J ⥤ C) (G : C ⥤ D) :
    preservesColimit D F G ↔ PreservesColimit F G := Iff.rfl

variable (C D J) in
def preservesColimitsOfShape : ObjectProperty (C ⥤ D) :=
  ⨅ (F : J ⥤ C), preservesColimit D F

instance : (preservesColimitsOfShape C D J).IsClosedUnderIsomorphisms := by
  dsimp [preservesColimitsOfShape]
  infer_instance

@[simp]
lemma preservesColimitsOfShape_iff (G : C ⥤ D) :
    preservesColimitsOfShape C D J G ↔ PreservesColimitsOfShape J G := by
  simp only [preservesColimitsOfShape, iInf_apply, preservesColimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ ⟨inferInstance⟩, fun _ ↦ inferInstance⟩

variable (C D) in
lemma congr_preservesColimitsOfShape {J' : Type*} [Category J'] (e : J ≌ J') :
    preservesColimitsOfShape C D J = preservesColimitsOfShape C D J' := by
  ext G
  simp only [preservesColimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesColimitsOfShape_of_equiv e _,
    fun _ ↦ preservesColimitsOfShape_of_equiv e.symm _⟩

variable (D) in
/-- The property of objects in `C ⥤ D` which preserves the limit
of a functor `F : J ⥤ C`. -/
abbrev preservesLimit (F : J ⥤ C) : ObjectProperty (C ⥤ D) := PreservesLimit F

instance (F : J ⥤ C) : (preservesLimit D F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesLimit_of_natIso _ e

@[simp]
lemma preservesLimit_iff (F : J ⥤ C) (G : C ⥤ D) :
    preservesLimit D F G ↔ PreservesLimit F G := Iff.rfl

variable (C D J) in
def preservesLimitsOfShape : ObjectProperty (C ⥤ D) :=
  ⨅ (F : J ⥤ C), preservesLimit D F

instance : (preservesLimitsOfShape C D J).IsClosedUnderIsomorphisms := by
  dsimp [preservesLimitsOfShape]
  infer_instance

@[simp]
lemma preservesLimitsOfShape_iff (G : C ⥤ D) :
    preservesLimitsOfShape C D J G ↔ PreservesLimitsOfShape J G := by
  simp only [preservesLimitsOfShape, iInf_apply, preservesLimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ ⟨inferInstance⟩, fun _ ↦ inferInstance⟩

variable (C D) in
lemma congr_preservesLimitsOfShape {J' : Type*} [Category J'] (e : J ≌ J') :
    preservesLimitsOfShape C D J = preservesLimitsOfShape C D J' := by
  ext G
  simp only [preservesLimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesLimitsOfShape_of_equiv e _,
    fun _ ↦ preservesLimitsOfShape_of_equiv e.symm _⟩

end Functor

end CategoryTheory
