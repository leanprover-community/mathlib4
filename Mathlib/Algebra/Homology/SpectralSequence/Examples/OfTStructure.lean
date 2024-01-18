import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.SpectralObject.Convergence
import Mathlib.Algebra.Homology.SpectralObject.FirstPage

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
    ((t.spectralObject X).mapHomologicalFunctor H).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    refine' IsZero.of_iso _
      ((t.truncGEt.obj i ⋙ H.shift n).mapIso ((t.isZero_truncLTt_obj_obj X 0 j hj).isoZero))
    rw [IsZero.iff_id_eq_zero]
    dsimp
    simp only [Functor.comp_obj, ← Functor.map_id, id_zero,
      (t.truncGEt.obj i).map_zero, (H.shift n).map_zero]
  isZero₂ i j hij n hi := by
    dsimp
    have := t.truncGEt_obj_obj_isGE (n+1) i (by
      obtain _|_|i := i
      · apply le_top
      · change _ < ⊥ at hi
        simp at hi
      · change _ < ℤt.mk _ at hi
        change _ ≤ ℤt.mk _
        simp only [ℤt.mk_lt_mk_iff, ℤt.mk_le_mk_iff] at hi ⊢
        linarith)
    apply H.isZero_shift_obj_of_vanishesOnGEOne t n (n+1) (by linarith)

noncomputable def spectralSequence : E₂CohomologicalSpectralSequence A :=
  ((t.spectralObject X).mapHomologicalFunctor H).E₂SpectralSequence

variable [t.HasHeart] [HasHomology₀ t] [Functor.ShiftSequence (homology₀ t) ℤ]

noncomputable def spectralSequenceE₂Iso (pq : ℤ × ℤ) :
    ((t.spectralSequence X H).page 2).X pq ≅
      (t.homology pq.2 ⋙ t.ιHeart ⋙ H.shift pq.1).obj X :=
  ((t.spectralObject X).mapHomologicalFunctor H).spectralSequenceFirstPageXIso
      mkDataE₂Cohomological pq _ rfl _ _ rfl rfl ≪≫
    (H.shiftIso _ _ _ (add_comm pq.2 pq.1)).symm.app _ ≪≫
    (H.shift pq.1).mapIso (t.shiftSpectralObjectω₁IsoHomologyιHeart X pq.2 _ rfl)

noncomputable def spectralSequenceStronglyConvergesTo [t.IsGE X 0] (n : ℤ) :
    (t.spectralSequence X H).StronglyConvergesToInDegree
      SpectralSequence.cohomologicalStripes n ((H.shift n).obj X) :=
  ((t.spectralObject X).mapHomologicalFunctor H).convergesAt
    mkDataE₂CohomologicalCompatibility n

end TStructure

end Triangulated

end CategoryTheory
