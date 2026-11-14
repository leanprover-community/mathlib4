/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Adjunction.Whiskering

import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Singular homology

In this file, we define the singular chain complex and singular homology of a topological space.
We also calculate the homology of a totally disconnected space as an example.
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory Limits AlgebraicTopology Simplicial

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

namespace AlgebraicTopology

variable (n : ℕ)

/-- The singular chain complex functor with coefficients in `C`. -/
@[implicit_reducible]
def singularChainComplexFunctor :
    C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}

instance : (singularChainComplexFunctor C).Additive := by
  delta singularChainComplexFunctor
  infer_instance

instance [Limits.HasPullbacks C] {X : C} :
    ((singularChainComplexFunctor C).obj X).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    infer_instance

/-- The `n`-th singular homology functor with coefficients in `C`. -/
@[implicit_reducible]
def singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C :=
  singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

section Adjunction

open Limits _root_.SSet
open scoped Simplicial
open HomologicalComplex (eval)

/-- The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `X : C` and `F : Top ⥤ C`. -/
def singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (singularChainComplexFunctor C) ⊣ (evaluation _ _).obj (SimplexCategory.toTop.obj ⦋n⦌) :=
  ((SSet.chainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

lemma singularChainComplexFunctorAdjunction_unit_app (R : C) :
    (singularChainComplexFunctorAdjunction C n).unit.app R =
      Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n⦌).app (.op ⦋n⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) := by
  simp [singularChainComplexFunctorAdjunction,
    singularChainComplexFunctor,
    SSet.chainComplexFunctorAdjunction, SSet.chainComplexFunctor, stdSimplexToTop]

lemma ι_singularChainComplexFunctorAdjunction_counit_app_app (F : TopCat ⥤ C) (X : TopCat) (i) :
    Sigma.ι _ i ≫ ((singularChainComplexFunctorAdjunction C n).counit.app F).app X =
      F.map i.down := by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChainComplexFunctor, SSet.chainComplexFunctor,
      SSet.chainComplexFunctorAdjunction]
    simp
  · congr 1
    rw [← reassoc_of% sSetTopAdj_unit_app_app_down]
    congrm ($(sSetTopAdj.right_triangle_components X).app (.op ⦋n⦌) i).down

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
  have : HasZeroObject C :=
    have := hasCoproducts_shrink.{0, w} (C := C)
    ⟨_, initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

end TotallyDisconnectedSpace

end AlgebraicTopology

namespace TopCat

variable {C}

/-- The singular chain complex of a topological space with coefficients in `R`. -/
noncomputable abbrev singularChainComplex (X : TopCat.{w}) (R : C) :
    ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

/-- The morphism of singular chain complexes that is induced by a morphism in `TopCat`. -/
noncomputable abbrev singularChainComplexMap {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) :
    X.singularChainComplex R ⟶ Y.singularChainComplex R :=
  ((singularChainComplexFunctor C).obj R).map f

/-- Inclusion of a summand of an object in the singular chain complex of
a topological space. -/
noncomputable abbrev ιSingularChainComplex
    (X : TopCat.{w}) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) :
    R ⟶ (X.singularChainComplex R).X n :=
  Sigma.ι (fun _ ↦ R) x

lemma singularChainComplexX_hom_ext {X : TopCat.{w}} {R : C} {n : ℕ} {T : C}
    {f g : (X.singularChainComplex R).X n ⟶ T}
    (h : ∀ (x : (toSSet.obj X) _⦋n⦌),
      X.ιSingularChainComplex x ≫ f = X.ιSingularChainComplex x ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ h

@[reassoc]
lemma ι_singularChainComplex_d
    (X : TopCat.{w}) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n + 1⦌) :
    X.ιSingularChainComplex (R := R) x ≫ (X.singularChainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1 : ℤ) ^ (i : ℕ) • X.ιSingularChainComplex ((toSSet.obj X).δ i x) := by
  simp [singularChainComplex, singularChainComplexFunctor, SSet.chainComplexFunctor,
    Preadditive.comp_sum]

/-- The universal element in `(toSSet.obj (SimplexCategory.toTop ^⦋n⦌)) _⦋n⦌`. -/
@[simps]
noncomputable def toSSet.univObj (n : ℕ) :
    (toSSet.{w}.obj (SimplexCategory.toTop ^⦋n⦌)) _⦋n⦌ :=
  ULift.up (𝟙 _)

lemma toSSet.δ_univObj {n : ℕ} (i : Fin (n + 2)) :
    (toSSet.{w}.obj (SimplexCategory.toTop ^⦋n + 1⦌)).δ i (univObj.{w} (n + 1)) =
      (toSSet.map (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i))).app _ (univObj.{w} n) :=
  rfl

lemma toSSet.exists_map_app_univObj_eq
    {X : TopCat.{w}} {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    ∃ (f : SimplexCategory.toTop ^⦋n⦌ ⟶ X),
      (toSSet.map f).app _ (univObj n) = s := by
  obtain ⟨s, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
  exact ⟨ofHom (s.comp ⟨ULift.down, by fun_prop⟩), rfl⟩

@[reassoc (attr := simp)]
lemma ι_singularChainComplexMap
    {X Y : TopCat.{w}} (f : X ⟶ Y) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) :
    X.ιSingularChainComplex (R := R) x ≫ (singularChainComplexMap f R).f n =
        Y.ιSingularChainComplex ((toSSet.map f).app _ x) := by
  simp [singularChainComplexFunctor, singularChainComplexMap, ιSingularChainComplex,
    SSet.chainComplexFunctor]

end TopCat
