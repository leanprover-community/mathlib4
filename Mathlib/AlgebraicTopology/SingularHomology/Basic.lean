/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SingularSet

/-!
# Singular homology

In this file, we define the singular chain complex and singular homology of a topological space.
We also calculate the homology of a totally disconnected space as an example.

-/

noncomputable section

namespace AlgebraicTopology

open CategoryTheory

universe w v u

variable (C : Type u) [Category.{v} C] [Limits.HasCoproducts.{0} C]
variable [Preadditive C] [CategoryWithHomology C] (n : ℕ)

/--
The singular chain complex associated to a simplicial set, with coefficients in `X : C`.
One can recover the ordinary singular chain complex when `C := Ab` and `X := ℤ`.
-/
def SSet.singularChainComplexFunctor [Limits.HasCoproducts.{w} C] :
    C ⥤ SSet.{w} ⥤ ChainComplex C ℕ :=
  (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (Limits.sigmaConst ⋙ SimplicialObject.whiskering _ _)

/-- The singular chain complex functor with coefficients in `C`. -/
def singularChainComplexFunctor :
    C ⥤ TopCat.{0} ⥤ ChainComplex C ℕ :=
  SSet.singularChainComplexFunctor.{0} C ⋙ (whiskeringLeft _ _ _).obj TopCat.toSSet

/-- The `n`-th singular homology functor with coefficients in `C`. -/
def singularHomologyFunctor : C ⥤ TopCat.{0} ⥤ C :=
  singularChainComplexFunctor C ⋙
    (whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

section TotallyDisconnectedSpace

variable (R : C) (X : TopCat.{0}) [TotallyDisconnectedSpace X]

/-- If `X` is totally disconnected,
its singular chain complex is given by `R[X] ←0- R[X] ←𝟙- R[X] ←0- R[X] ⋯`,
where `R[X]` is the coproduct of copies of `R` indexed by elements of `X`. -/
noncomputable
def singularChainComplexFunctorIsoOfTotallyDisconnectedSpace :
    ((singularChainComplexFunctor C).obj R).obj X ≅
      (ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R)) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (((SimplicialObject.whiskering _ _).obj _).mapIso
    (TopCat.toSSetIsoConst X) ≪≫ Functor.constComp _ _ _) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _

omit [CategoryWithHomology C] in
lemma singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace [Limits.HasZeroObject C]
    (hn : n ≠ 0) :
    (((singularChainComplexFunctor C).obj R).obj X).ExactAt n :=
  .of_iso (ChainComplex.alternatingConst_exactAt _ _ hn)
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X).symm

lemma isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (hn : n ≠ 0) :
    Limits.IsZero (((singularHomologyFunctor C n).obj R).obj X) :=
  have : Limits.HasZeroObject C := ⟨_, Limits.initialIsInitial.isZero⟩
  (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace C n R X hn).isZero_homology

/-- The zeroth singular homology of a totally disconnected space is the
free `R`-module generated by elements of `X`. -/
noncomputable
def singularHomologyFunctorZeroOfTotallyDisconnectedSpace :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : X ↦ R :=
  have : Limits.HasZeroObject C := ⟨_, Limits.initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

end TotallyDisconnectedSpace

end AlgebraicTopology
