import Mathlib.Algebra.Homology.SpectralSequence.Examples.OfTStructure
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

namespace DerivedCategory

open CategoryTheory Triangulated DerivedCategory DerivedCategory.TStructure

variable {A B C : Type _} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : DerivedCategory A ⥤ DerivedCategory B)
  (G : DerivedCategory B ⥤ DerivedCategory C) [G.CommShift ℤ] [G.IsTriangulated] (X : A)
  [(G ⋙ DerivedCategory.homologyFunctor C 0).VanishesOnGEOne t]
  [t.IsGE (F.obj ((singleFunctor A 0).obj X)) 0]

noncomputable def grothendieckSpectralSequence : E₂CohomologicalSpectralSequenceNat C :=
  TStructure.spectralSequenceNat t (F.obj ((singleFunctor A 0).obj X))
    (G ⋙ DerivedCategory.homologyFunctor C 0)

/-- Computation of `E₂^{p,q}` of the Grothendieck spectral sequence -/
noncomputable def grothendieckSpectralSequenceE₂Iso (pq : ℕ × ℕ) :
  ((grothendieckSpectralSequence F G X).page 2).X pq ≅
    (singleFunctor A 0 ⋙ F ⋙ homologyFunctor B pq.2 ⋙
      singleFunctor B 0 ⋙ G ⋙ homologyFunctor C pq.1).obj X :=
  TStructure.spectralSequenceNatE₂Iso t (F.obj ((singleFunctor A 0).obj X))
    (G ⋙ DerivedCategory.homologyFunctor C 0) pq

noncomputable def convergesAt (n : ℕ) :
    (grothendieckSpectralSequence F G X).StronglyConvergesToInDegree CohomologicalSpectralSequenceNat.stripes n
      ((singleFunctor A 0 ⋙ F ⋙ G ⋙ homologyFunctor C (n : ℤ)).obj X) := by
  apply TStructure.spectralSequenceNatStronglyConvergesTo

end DerivedCategory
