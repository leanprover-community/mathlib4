/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Singular homology

In this file, we define the singular chain complex and singular homology of a topological space.
We also calculate the homology of a totally disconnected space as an example.

-/

@[expose] public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory Limits

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
variable [Preadditive C] (n : ℕ)

/--
The singular chain complex associated to a simplicial set, with coefficients in `X : C`.
One can recover the ordinary singular chain complex when `C := Ab` and `X := ℤ`.
-/
def SSet.singularChainComplexFunctor :
    C ⥤ SSet.{w} ⥤ ChainComplex C ℕ :=
  (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex _)).obj
    (sigmaConst ⋙ SimplicialObject.whiskering _ _)

instance : (SSet.singularChainComplexFunctor C).Additive := by
  dsimp [SSet.singularChainComplexFunctor, SimplicialObject.whiskering]
  infer_instance

/-- The singular chain complex functor with coefficients in `C`. -/
def singularChainComplexFunctor :
    C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ :=
  SSet.singularChainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}

instance : (singularChainComplexFunctor C).Additive := by
  delta singularChainComplexFunctor
  infer_instance

instance [Limits.HasPullbacks C] {X : C} :
    ((singularChainComplexFunctor C).obj X).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

/-- The `n`-th singular homology functor with coefficients in `C`. -/
def singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C :=
  singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

section Adjunction

open Limits _root_.SSet
open scoped Simplicial
open HomologicalComplex (eval)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] SSet.singularChainComplexFunctor in
attribute [local simp←] _root_.SSet.yonedaEquiv_symm_comp in
/-- The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `X : C` and `F : SSet ⥤ C`. -/
def SSet.singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (SSet.singularChainComplexFunctor C) ⊣ (evaluation _ _).obj Δ[n] where
  unit.app R := Sigma.ι (fun _ : Δ[n] _⦋n⦌ ↦ R) (SSet.stdSimplex.objEquiv (n := ⦋n⦌).symm (𝟙 ⦋n⦌))
  counit.app F := { app S := Sigma.desc fun α ↦ F.map (SSet.yonedaEquiv.symm α) }
  right_triangle_components F := by dsimp; simp

/-- The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `X : C` and `F : Top ⥤ C`. -/
def singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (singularChainComplexFunctor C) ⊣ (evaluation _ _).obj (SimplexCategory.toTop.obj ⦋n⦌) :=
  ((SSet.singularChainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

lemma singularChainComplexFunctorAdjunction_unit_app (R : C) :
    (singularChainComplexFunctorAdjunction C n).unit.app R =
      Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n⦌).app (.op ⦋n⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) := by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor,
    SSet.singularChainComplexFunctorAdjunction, SSet.singularChainComplexFunctor]
  simp [stdSimplexToTop]

set_option backward.isDefEq.respectTransparency false in
lemma ι_singularChainComplexFunctorAdjunction_counit_app_app (F : TopCat ⥤ C) (X : TopCat) (i) :
    Sigma.ι _ i ≫ ((singularChainComplexFunctorAdjunction C n).counit.app F).app X =
      F.map i.down := by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChainComplexFunctor, SSet.singularChainComplexFunctor,
      SSet.singularChainComplexFunctorAdjunction]
    simp
  · congr 1
    rw [← reassoc_of% sSetTopAdj_unit_app_app_down]
    exact congr(($(sSetTopAdj.right_triangle_components X).app (.op ⦋n⦌) i).down)

end Adjunction

section TotallyDisconnectedSpace

variable (R : C) (X : TopCat.{w}) [TotallyDisconnectedSpace X]

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

lemma singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
    (hn : n ≠ 0) :
    (((singularChainComplexFunctor C).obj R).obj X).ExactAt n :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  .of_iso (ChainComplex.alternatingConst_exactAt _ _ hn)
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X).symm

lemma isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    [CategoryWithHomology C] (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace C n R X hn).isZero_homology

/-- The zeroth singular homology of a totally disconnected space is the
free `R`-module generated by elements of `X`. -/
noncomputable
def singularHomologyFunctorZeroOfTotallyDisconnectedSpace [CategoryWithHomology C] :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : X ↦ R :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

end TotallyDisconnectedSpace

end AlgebraicTopology
