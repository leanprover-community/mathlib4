/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
public import Mathlib.Algebra.Homology.SpectralObject.Convergence
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# The spectral sequence of a t-structure
-/

@[expose] public section

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

omit [CategoryTheory.IsTriangulated C] in
lemma isZero_shift_obj_of_vanishesOnGEOne
    [hH : H.VanishesOnGEOne t] [H.ShiftSequence ℤ]
    (a b : ℤ) (h : a < b) (X : C)
    [t.IsGE X b] : IsZero ((H.shift a).obj X) := by
  have : t.IsGE (X⟦a⟧) (b-a) := t.isGE_shift _ b a (b-a) (by lia)
  exact IsZero.of_iso (hH.isZero' _ (t.isGE_of_GE _ 1 (b-a) (by lia)))
    (((H.shiftIso a 0 a (add_zero a)).symm ≪≫
      isoWhiskerLeft (shiftFunctor C a) (H.isoShiftZero ℤ)).app X)

omit [CategoryTheory.IsTriangulated C] in
lemma isZero_shift_obj_of_vanishesOnLESubOne
    [hH : H.VanishesOnLESubOne t] [H.ShiftSequence ℤ]
    (a b : ℤ) (h : a < b) (X : C)
    [t.IsLE X a] : IsZero ((H.shift b).obj X) := by
  have : t.IsLE (X⟦b⟧) (a-b) := t.isLE_shift _ a b (a-b) (by lia)
  exact IsZero.of_iso (hH.isZero' _ (t.isLE_of_LE (X⟦b⟧) (a - b) (-1) (by lia)))
    (((H.shiftIso b 0 b (add_zero b)).symm ≪≫
      isoWhiskerLeft (shiftFunctor C b) (H.isoShiftZero ℤ)).app X)

end Functor

namespace Triangulated

namespace TStructure

open Abelian.SpectralObject

section

variable (t : TStructure C) (X : C) (H : C ⥤ A) [H.PreservesZeroMorphisms] [H.IsHomological]
  [H.ShiftSequence ℤ]

instance [t.IsGE X 0] [H.VanishesOnGEOne t] :
    ((t.spectralObject X).mapHomologicalFunctor H).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    refine IsZero.of_iso ?_
      ((t.eTruncGE.obj i ⋙ H.shift n).mapIso ((t.isZero_eTruncLT_obj_obj X 0 j hj).isoZero))
    rw [IsZero.iff_id_eq_zero]
    dsimp
    simp only [← Functor.map_id, id_zero,
      (t.eTruncGE.obj i).map_zero, (H.shift n).map_zero]
  isZero₂ i j hij n hi := by
    dsimp
    have := t.isGE_eTruncGE_obj_obj (n + 1) i (by induction i <;> simp_all)
    apply H.isZero_shift_obj_of_vanishesOnGEOne t n (n+1) (by lia)

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

noncomputable def spectralSequenceStronglyConvergesTo [H.VanishesOnGEOne t] [t.IsGE X 0] (n : ℤ) :
    (t.spectralSequence X H).StronglyConvergesToInDegree
      SpectralSequence.cohomologicalStripes n ((H.shift n).obj X) :=
  ((t.spectralObject X).mapHomologicalFunctor H).convergesAt
    mkDataE₂CohomologicalCompatibility n

section

variable [((spectralObject t X).mapHomologicalFunctor H).IsFirstQuadrant]

noncomputable def spectralSequenceNat : E₂CohomologicalSpectralSequenceNat A :=
  ((t.spectralObject X).mapHomologicalFunctor H).E₂SpectralSequenceNat

variable [t.HasHeart] [HasHomology₀ t] [Functor.ShiftSequence (homology₀ t) ℤ]

noncomputable def spectralSequenceNatE₂Iso (pq : ℕ × ℕ) :
    ((t.spectralSequenceNat X H).page 2).X pq ≅
      (t.homology pq.2 ⋙ t.ιHeart ⋙ H.shift (pq.1 : ℤ)).obj X :=
  ((t.spectralObject X).mapHomologicalFunctor H).spectralSequenceFirstPageXIso
      mkDataE₂CohomologicalNat pq _ rfl _ _ rfl rfl ≪≫
    (H.shiftIso _ _ _ (add_comm _ _)).symm.app _ ≪≫
    (H.shift (pq.1 : ℤ)).mapIso (t.shiftSpectralObjectω₁IsoHomologyιHeart X pq.2 _ rfl)

noncomputable def spectralSequenceNatStronglyConvergesTo [t.IsGE X 0] (n : ℕ) :
    (t.spectralSequenceNat X H).StronglyConvergesToInDegree
      CohomologicalSpectralSequenceNat.stripes n ((H.shift (n : ℤ)).obj X) :=
  ((t.spectralObject X).mapHomologicalFunctor H).convergesAt
    mkDataE₂CohomologicalNatCompatibility n

end

end

section

variable (t : TStructure C) (X : C) (H : C ⥤ A) [H.PreservesZeroMorphisms] [H.IsHomological]
  [H.ShiftSequence ℤ] [H.VanishesOnLESubOne t] [t.IsLE X 0]

instance :
    ((t.spectralObject X).mapHomologicalFunctor H).IsThirdQuadrant where
  isZero₁ i j hij hi n :=
    (H.shift n).map_isZero (t.isZero_eTruncGE_obj_obj (((t.eTruncLT).obj j).obj X) 0 i hi)
  isZero₂ i j hij n hj := by
    dsimp
    have := t.isLE_eTruncLT_obj_obj (n - 1) j (by simpa using hj) X
    exact H.isZero_shift_obj_of_vanishesOnLESubOne t (n - 1) n (by lia) _

end

end TStructure

end Triangulated

end CategoryTheory
