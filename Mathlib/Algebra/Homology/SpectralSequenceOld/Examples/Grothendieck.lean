/-import Mathlib.Algebra.Homology.SpectralSequence.Examples.OfTStructure
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

open CategoryTheory Triangulated DerivedCategory DerivedCategory.TStructure

variable {A B C : Type _} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : DerivedCategory A ⥤ DerivedCategory B)
  (G : DerivedCategory B ⥤ DerivedCategory C) [G.CommShift ℤ] [G.IsTriangulated] (X : A)

noncomputable def grothendieckSpectralSequence : E₂CohomologicalSpectralSequence C :=
  TStructure.spectralSequence t (F.obj ((singleFunctor A 0).obj X))
    (G ⋙ DerivedCategory.homologyFunctor C 0)

/-- Computation of `E₂^{p,q}` of the Grothendieck spectral sequence -/
noncomputable def grothendieckSpectralSequenceE₂Iso (pq : ℤ × ℤ) :
  (grothendieckSpectralSequence F G X).page 2 pq ≅
    (singleFunctor A 0 ⋙ F ⋙ homologyFunctor B pq.2 ⋙
      singleFunctor B 0 ⋙ G ⋙ homologyFunctor C pq.1).obj X :=
  TStructure.spectralSequenceE₂Iso t (F.obj ((singleFunctor A 0).obj X))
    (G ⋙ DerivedCategory.homologyFunctor C 0) pq ≪≫
    (isoWhiskerRight (isoWhiskerLeft (singleFunctor A 0 ⋙ F)
      (homologyιHeart B pq.2)) (G ⋙ homologyFunctor C pq.1)).app X

variable [(G ⋙ DerivedCategory.homologyFunctor C 0).VanishesOnGEOne t]
  [t.IsGE (F.obj ((singleFunctor A 0).obj X)) 0]

instance : (grothendieckSpectralSequence F G X).IsFirstQuadrant := by
  dsimp [grothendieckSpectralSequence]
  infer_instance

noncomputable def grothendieckSpectralSequenceStronglyConvergesTo :
    (grothendieckSpectralSequence F G X).StronglyConvergesTo
      (fun n => (singleFunctor A 0 ⋙ F ⋙ G ⋙ homologyFunctor C n).obj X) :=
  TStructure.spectralSequenceStronglyConvergesTo t (F.obj ((singleFunctor A 0).obj X))
    (G ⋙ DerivedCategory.homologyFunctor C 0)

-/
