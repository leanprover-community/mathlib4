/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Examples.OfTStructure
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# The Grothendieck spectral sequence

-/

@[expose] public section

namespace DerivedCategory

open CategoryTheory Triangulated Limits

namespace Plus

open TStructure

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
  (G : B ⥤ C) [G.Additive] [EnoughInjectives B] (X : A)

variable [∀ (I : Injectives A),
  IsIso (G.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj ((Injectives.ι A).obj I))))]

noncomputable example : (F ⋙ G).rightDerivedFunctorPlus ≅
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  asIso (Functor.rightDerivedFunctorPlusCompNatTrans (Iso.refl (F ⋙ G)))

instance : (G.rightDerivedFunctorPlus ⋙ homologyFunctor C 0).VanishesOnGEOne t where
  isZero' K hK := isZero_homology_of_isGE (G.rightDerivedFunctorPlus.obj K) 1 0 (by omega)

noncomputable def grothendieckSpectralSequence : E₂CohomologicalSpectralSequenceNat C :=
  TStructure.spectralSequenceNat t (F.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj X))
    (G.rightDerivedFunctorPlus ⋙ homologyFunctor C 0)

namespace grothendieckSpectralSequence

/-- Computation of `E₂^{p,q}` of the Grothendieck spectral sequence -/
noncomputable def page₂Iso (pq : ℕ × ℕ) :
  ((grothendieckSpectralSequence F G X).page 2).X pq ≅
    (F.rightDerived' pq.2 ⋙ G.rightDerived' pq.1).obj X :=
  t.spectralSequenceNatE₂Iso (F.rightDerivedFunctorPlus.obj ((singleFunctor A 0).obj X))
    (G.rightDerivedFunctorPlus ⋙ homologyFunctor C 0) pq

/-- stronglyConvergesToInDegree' -/
noncomputable def stronglyConvergesToInDegree' (n : ℕ) :
    (grothendieckSpectralSequence F G X).StronglyConvergesToInDegree
      CohomologicalSpectralSequenceNat.stripes n
      ((singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
        G.rightDerivedFunctorPlus ⋙ homologyFunctor C (n : ℤ)).obj X) := by
  apply TStructure.spectralSequenceNatStronglyConvergesTo

noncomputable def stronglyConvergesTo :
    (grothendieckSpectralSequence F G X).StronglyConvergesTo
      CohomologicalSpectralSequenceNat.stripes
      (fun n => (((F ⋙ G).rightDerived' n).obj X)) :=
  fun n => (stronglyConvergesToInDegree' F G X n).ofIso ((homologyFunctor C n).mapIso
      ((asIso (Functor.rightDerivedFunctorPlusCompNatTrans (Iso.refl _))).symm.app _))

end grothendieckSpectralSequence

end Plus

end DerivedCategory
