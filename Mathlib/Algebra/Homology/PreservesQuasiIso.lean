/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exact functors preserves quasi-isomorphisms

-/

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]

namespace ShortComplex

variable (C) in
protected def quasiIso : MorphismProperty (ShortComplex C) :=
  fun _ _ f ↦ QuasiIso f

@[simp]
lemma mem_quasiIso_iff {K L : ShortComplex C} (f : K ⟶ L) :
    ShortComplex.quasiIso C f ↔ QuasiIso f := Iff.rfl

end ShortComplex

namespace Functor

lemma preserves_shortComplexQuasiIso :
    ShortComplex.quasiIso C ≤ (ShortComplex.quasiIso D).inverseImage F.mapShortComplex := by
  intro _ _ _ hf
  simp only [ShortComplex.mem_quasiIso_iff, MorphismProperty.inverseImage_iff,
    mapShortComplex_obj] at hf ⊢
  infer_instance

instance {ι : Type*} (c : ComplexShape ι) {K L : HomologicalComplex C c} (f : K ⟶ L)
    (i : ι) [hf : QuasiIsoAt f i] : QuasiIsoAt ((F.mapHomologicalComplex c).map f) i := by
  rw [quasiIsoAt_iff] at hf ⊢
  change ShortComplex.QuasiIso (F.mapShortComplex.map
    ((HomologicalComplex.shortComplexFunctor C c i).map f))
  infer_instance

instance {ι : Type*} (c : ComplexShape ι) {K L : HomologicalComplex C c} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso ((F.mapHomologicalComplex c).map f) where

lemma preserves_quasiIso {ι : Type*} (c : ComplexShape ι) :
    HomologicalComplex.quasiIso C c ≤
      (HomologicalComplex.quasiIso D c).inverseImage (F.mapHomologicalComplex c) := by
  intro _ _ _ hf
  simp only [HomologicalComplex.mem_quasiIso_iff, MorphismProperty.inverseImage_iff] at hf ⊢
  infer_instance

end Functor

end CategoryTheory
