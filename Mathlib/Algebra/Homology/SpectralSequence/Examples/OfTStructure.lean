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

class VanishesOnLESubOne (H : C ⥤ D) (t : TStructure C) where
  isZero' (X : C) (hX : t.IsLE X (-1)) : IsZero (H.obj X)

variable (H : C ⥤ D) (t : TStructure C)

lemma isZero_shift_obj_of_vanishesOnGEOne
    [hH : H.VanishesOnGEOne t] [H.ShiftSequence ℤ]
    (a b : ℤ) (h : a < b) (X : C)
    [t.IsGE X b] : IsZero ((H.shift a).obj X) := by
  have : t.IsGE (X⟦a⟧) (b-a) := t.isGE_shift _ b a (b-a) (by linarith)
  exact IsZero.of_iso (hH.isZero' _ (t.isGE_of_GE _ 1 (b-a) (by linarith)))
    (((H.shiftIso a 0 a (add_zero a)).symm ≪≫
      isoWhiskerLeft (shiftFunctor C a) (H.isoShiftZero ℤ)).app X)

lemma isZero_shift_obj_of_vanishesOnLESubOne
    [hH : H.VanishesOnLESubOne t] [H.ShiftSequence ℤ]
    (a b : ℤ) (h : a < b) (X : C)
    [t.IsLE X a] : IsZero ((H.shift b).obj X) := by
  have : t.IsLE (X⟦b⟧) (a-b) := t.isLE_shift _ a b (a-b) (by linarith)
  exact IsZero.of_iso (hH.isZero' _ (t.isLE_of_LE (X⟦b⟧) (a - b) (-1) (by linarith)))
    (((H.shiftIso b 0 b (add_zero b)).symm ≪≫ isoWhiskerLeft (shiftFunctor C b) (H.isoShiftZero ℤ)).app X)

end Functor

namespace Triangulated

namespace TStructure

open Abelian.SpectralObject

section

variable (t : TStructure C) (X : C) (H : C ⥤ A) [H.PreservesZeroMorphisms] [H.IsHomological]
  [H.ShiftSequence ℤ] [H.VanishesOnGEOne t]

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

end

section

variable (t : TStructure C) (X : C) (H : C ⥤ A) [H.PreservesZeroMorphisms] [H.IsHomological]
  [H.ShiftSequence ℤ] [H.VanishesOnLESubOne t]

instance [t.IsLE X 0] :
    ((t.spectralObject X).mapHomologicalFunctor H).IsThirdQuadrant where
  isZero₁ i j hij hi n := by
    refine IsZero.of_iso ?_ ((H.shift n).mapIso (t.isZero_truncGEt_obj_obj (((t.truncLTt).obj j).obj X) 0 i hi).isoZero)
    rw [IsZero.iff_id_eq_zero, ← Functor.map_id, id_zero, Functor.map_zero]
  isZero₂ i j hij n hj := by
    dsimp
    have := t.truncLTt_obj_obj_isLE (n - 1) j (by simpa using hj) X
    exact H.isZero_shift_obj_of_vanishesOnLESubOne t (n - 1) n (by linarith) _

end

end TStructure

end Triangulated

end CategoryTheory
