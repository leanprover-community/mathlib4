import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc
import Mathlib.Algebra.Homology.SpectralSequence.Construction

open CategoryTheory Category Limits Pretriangulated Triangulated ZeroObject Preadditive

variable {C A : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category A] [Abelian A]
  (t : TStructure C) (X : C) (H : C ⥤ A) [H.PreservesZeroMorphisms] [H.IsHomological]
  [H.ShiftSequence ℤ]

namespace CategoryTheory

namespace Triangulated

namespace TStructure

open Abelian.SpectralObject

lemma isZero_truncLTt_obj (X : C) (n : ℤ) [t.IsGE X n] (j : ℤt) (hj : j ≤ ℤt.mk n) :
  IsZero ((t.truncLTt.obj j).obj X) := sorry

instance (i : ℤt) : (t.truncGEt.obj i).Additive := sorry

instance [t.IsGE X 0] :
    ((t.spectralObject X).mapHomologicalFunctor H).IsStationary Bounds.firstQuadrant where
  isZero₁' n i j g α := by
    refine' IsZero.of_iso _
      ((t.truncGEt.obj i ⋙ H.shift n).mapIso ((t.isZero_truncLTt_obj X 0 j (leOfHom α)).isoZero))
    rw [IsZero.iff_id_eq_zero]
    simp only [Functor.comp_obj, ← Functor.map_id, id_zero,
      (t.truncGEt.obj i).map_zero, (H.shift n).map_zero]
  isZero₂' n i j g α := by
    dsimp [spectralObject, SpectralObject.mapHomologicalFunctor,
      SpectralObject.AbstractSpectralObject.spectralObject]
    sorry

noncomputable def spectralSequence : E₂CohomologicalSpectralSequence A :=
  ((t.spectralObject X).mapHomologicalFunctor H).toE₂CohomologicalSpectralSequence

end TStructure

end Triangulated

end CategoryTheory
