/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DoubleHomology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exact functors preserves quasi-isomorphisms

-/

namespace HomologicalComplex

open CategoryTheory Limits

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  {ι₁ ι₂ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  [CategoryWithHomology C₁] [CategoryWithHomology C₂]

def preservesQuasiIso :
    ObjectProperty (HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂) :=
  fun F ↦ (HomologicalComplex.quasiIso C₁ c₁ ≤ (HomologicalComplex.quasiIso C₂ c₂).inverseImage F)


end HomologicalComplex

namespace CategoryTheory

open Limits ZeroObject

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
    HomologicalComplex.preservesQuasiIso  (F.mapHomologicalComplex c) := by
  intro _ _ _ hf
  simp only [HomologicalComplex.mem_quasiIso_iff, MorphismProperty.inverseImage_iff] at hf ⊢
  infer_instance

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

open HomologicalComplex in
lemma preservesQuasiIso_mapHomologicalComplex_iff {C D : Type*} [Category C]
    [Category D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    {ι : Type*} (c : ComplexShape ι)
    {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (hi₀₁' : i₀ ≠ i₁) :
    preservesQuasiIso (F.mapHomologicalComplex c) ↔ F.PreservesHomology where
  mpr _ _ _ _ hf := by
    simp only [mem_quasiIso_iff, MorphismProperty.inverseImage_iff] at hf ⊢
    infer_instance
  mp h := by
    apply (F.exact_tfae.out 0 2).1
    intro S hS
    rw [← ShortComplex.quasiIso_doubleFunctor_map_arrowHomToG_iff_exact _ hi₀₁ hi₀₁'] at hS ⊢
    let e : Arrow.mk (F.map (0 : S.X₁ ⟶ 0)) ≅ Arrow.mk (0 : F.obj S.X₁ ⟶ 0) :=
      Arrow.isoMk (Iso.refl _) (IsZero.iso (F.map_isZero (isZero_zero C)) (isZero_zero D))
    refine ((quasiIso _ _).arrow_mk_iso_iff ?_).1 (h _ hS)
    refine Arrow.isoMk ((doubleFunctorCompMapHomologicalComplex hi₀₁ hi₀₁' F).app _ ≪≫
        (doubleFunctor D hi₀₁ hi₀₁').mapIso e)
      ((doubleFunctorCompMapHomologicalComplex hi₀₁ hi₀₁' F).app _) (by
        dsimp
        ext <;> simp [mapHomologicalComplexObjDoubleXIso, doubleFunctor_map, e])

end Functor

end CategoryTheory
