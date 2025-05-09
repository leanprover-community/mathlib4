/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DoubleHomology

/-!
# Exact functors preserves quasi-isomorphisms

-/


namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

namespace ShortComplex

variable (C) in
protected def quasiIso : MorphismProperty (ShortComplex C) :=
  fun _ _ f ↦ QuasiIso f

@[simp]
lemma mem_quasiIso_iff {K L : ShortComplex C} (f : K ⟶ L) :
    ShortComplex.quasiIso C f ↔ QuasiIso f := Iff.rfl

end ShortComplex

namespace Functor

def preservesQuasiIso {ι₁ ι₂ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} :
    ObjectProperty (HomologicalComplex C c₁ ⥤ HomologicalComplex D c₂) :=
  fun F ↦ (HomologicalComplex.quasiIso C c₁ ≤ (HomologicalComplex.quasiIso D c₂).inverseImage F)

abbrev PreservesQuasiIso {ι₁ ι₂ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
    (F : HomologicalComplex C c₁ ⥤ HomologicalComplex D c₂) : Prop :=
  preservesQuasiIso.Is F

lemma preserves_shortComplexQuasiIso [F.PreservesHomology] :
    ShortComplex.quasiIso C ≤ (ShortComplex.quasiIso D).inverseImage F.mapShortComplex := by
  intro _ _ _ hf
  simp only [ShortComplex.mem_quasiIso_iff, MorphismProperty.inverseImage_iff,
    mapShortComplex_obj] at hf ⊢
  infer_instance

instance [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) {K L : HomologicalComplex C c}
    (f : K ⟶ L) (i : ι) [hf : QuasiIsoAt f i] :
        QuasiIsoAt ((F.mapHomologicalComplex c).map f) i := by
  rw [quasiIsoAt_iff] at hf ⊢
  change ShortComplex.QuasiIso (F.mapShortComplex.map
    ((HomologicalComplex.shortComplexFunctor C c i).map f))
  infer_instance

instance [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) {K L : HomologicalComplex C c}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso ((F.mapHomologicalComplex c).map f) where

instance preservesQuasiIso_mapHomologicalComplex
    [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).PreservesQuasiIso := ⟨by
  intro _ _ _ hf
  simp only [HomologicalComplex.mem_quasiIso_iff, MorphismProperty.inverseImage_iff] at hf ⊢
  infer_instance⟩

noncomputable def mapHomologicalComplexCompShortComplexFunctorIso
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} (c : ComplexShape ι) (i : ι) :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.shortComplexFunctor D c i ≅
      HomologicalComplex.shortComplexFunctor C c i ⋙ F.mapShortComplex := Iso.refl _

noncomputable def mapHomologicalComplexHomologyIso [F.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  isoWhiskerLeft _ (HomologicalComplex.homologyFunctorIso D c i) ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (F.mapHomologicalComplexCompShortComplexFunctorIso c i) _ ≪≫
    (associator _ _ _) ≪≫ isoWhiskerLeft _ (ShortComplex.homologyFunctorIso F) ≪≫
    (associator _ _ _).symm ≪≫
      isoWhiskerRight (HomologicalComplex.homologyFunctorIso C c i).symm _

/-lemma preservesQuasiIso_mapHomologicalComplex_iff {ι : Type*} (c : ComplexShape ι)
    {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (hi₀₁' : i₀ ≠ i₁) :
    (F.mapHomologicalComplex c).PreservesQuasiIso ↔ F.PreservesHomology where
  mpr _ := inferInstance
  mp h := by
    -- use ShortComplex.quasiIso_doubleFunctor_map_arrowHomToG_iff_exact
    sorry -/

end Functor

end CategoryTheory
