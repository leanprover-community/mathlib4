/-import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc
import Mathlib.Algebra.Homology.SpectralSequence.Construction

open CategoryTheory Category Limits Pretriangulated Triangulated ZeroObject Preadditive

variable {C A : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [CategoryTheory.IsTriangulated C]
  [Category A] [Abelian A]

namespace CategoryTheory

namespace Functor

variable {D : Type _} [Category D]

class VanishesOnGEOne (H : C ⥤ D) (t : TStructure C) where
  isZero' (X : C) (hX : t.IsGE X 1) : IsZero (H.obj X)

variable (H : C ⥤ D) (t : TStructure C) [hH : H.VanishesOnGEOne t]
  [H.ShiftSequence ℤ]

lemma isZero_shift_obj_of_vanishesOnGEOne (a b : ℤ) (h : a < b) (X : C)
    [t.IsGE X b] : IsZero ((H.shift a).obj X) := by
  have : t.IsGE (X⟦a⟧) (b-a) := t.isGE_shift _ b a (b-a) (by linarith)
  exact IsZero.of_iso (hH.isZero' _ (t.isGE_of_GE _ 1 (b-a) (by linarith)))
    (((H.shiftIso a 0 a (add_zero a)).symm ≪≫
      isoWhiskerLeft (shiftFunctor C a) (H.isoShiftZero ℤ)).app X)

end Functor

namespace Triangulated

namespace TStructure

variable (t : TStructure C) (X : C) (H : C ⥤ A) [H.PreservesZeroMorphisms] [H.IsHomological]
  [H.ShiftSequence ℤ] [H.VanishesOnGEOne t]

open Abelian.SpectralObject

instance [t.IsGE X 0] :
    ((t.spectralObject X).mapHomologicalFunctor H).IsStationary Bounds.firstQuadrant where
  isZero₁' n i j g α := by
    refine' IsZero.of_iso _
      ((t.truncGEt.obj i ⋙ H.shift n).mapIso ((t.isZero_truncLTt_obj_obj X 0 j (leOfHom α)).isoZero))
    rw [IsZero.iff_id_eq_zero]
    simp only [Functor.comp_obj, ← Functor.map_id, id_zero,
      (t.truncGEt.obj i).map_zero, (H.shift n).map_zero]
  isZero₂' n i j g α := by
    dsimp
    have := t.truncGEt_obj_obj_isGE (n+1) i (by simpa using leOfHom α)
    apply H.isZero_shift_obj_of_vanishesOnGEOne t n (n+1) (by linarith)

noncomputable def spectralSequence : E₂CohomologicalSpectralSequence A :=
  ((t.spectralObject X).mapHomologicalFunctor H).toE₂CohomologicalSpectralSequence

noncomputable def spectralSequenceE₂Iso (pq : ℤ × ℤ) :
    (t.spectralSequence X H).page 2 pq ≅
      (t.homology' pq.2 ⋙ t.ιHeart' ⋙ H.shift pq.1).obj X :=
  ((t.spectralObject X).mapHomologicalFunctor H).toE₂CohomologicalSpectralSequencePageTwoIso
    pq _ rfl _ rfl ≪≫ (H.shiftIso _ _ _ (add_comm pq.2 pq.1)).symm.app _ ≪≫
    (H.shift pq.1).mapIso (t.shiftSpectralObjectω₁IsoHomologyιHeart X pq.2 _ rfl)

instance [t.IsGE X 0] : (t.spectralSequence X H).IsFirstQuadrant := by
  dsimp only [spectralSequence]
  infer_instance

noncomputable def spectralSequenceStronglyConvergesTo [t.IsGE X 0] :
    (t.spectralSequence X H).StronglyConvergesTo (fun n => (H.shift n).obj X) :=
  toE₂CohomologicalSpectralSequenceStronglyConvergesToOfBoundsFirstQuadrant
    ((t.spectralObject X).mapHomologicalFunctor H)

end TStructure

end Triangulated

end CategoryTheory
-/
