/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Relative Singular Homology

In this file, we define the relative singular chain complex and relative singular homology of a
pair of topological spaces. They are the groups fitting in the long exact sequence
`⋯ ⟶ Hₙ(U) ⟶ Hₙ(X) ⟶ Hₙ(X, U) ⟶ Hₙ₋₁(U) ⟶ Hₙ₋₁(X) ⟶ ⋯`.
The maps are `map n f R`, `π n f R`, and `δ n (n - 1) _ f R` respectively, and the exactness
are provided via `exact_δ_map`, `exact_map_π`, and `exact_π_δ`
(All in the `AlgebraicTopology.SingularHomology` namespace).

-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (n : ℕ)

/-- The relative singular chain complex functor with coefficients in `C`. -/
def relativeSingularChainComplex :
    C ⥤ Arrow TopCat.{w} ⥤ ChainComplex C ℕ :=
  singularChainComplexFunctor C ⋙ CategoryTheory.Functor.mapArrowFunctor _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (Limits.coker _)

/-- The projection onto the relative singular chain complex as a natural transformation. -/
def relativeSingularChainComplex.π :
    singularChainComplexFunctor C ⋙ (Functor.whiskeringLeft _ _ _).obj Arrow.rightFunc ⟶
    relativeSingularChainComplex C :=
  Functor.whiskerLeft (singularChainComplexFunctor C)
    ((Functor.mapArrowFunctor _ _).whiskerLeft
    ((Functor.whiskeringRight _ _ _).map (Limits.coker.π _)))

/-- The short complex `0 ⟶ C(U) ⟶ C(X) ⟶ C(X)/C(U) ⟶ 0` associated to a continuous map `U ⟶ X`,
as a functor on `Arrow TopCat`. -/
def relativeSingularShortComplex :
    C ⥤ Arrow TopCat.{w} ⥤ ShortComplex (ChainComplex C ℕ) :=
  singularChainComplexFunctor C ⋙ CategoryTheory.Functor.mapArrowFunctor _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (ShortComplex.cokerFunctor _)

/-- The `n`-th relative singular homology functor with coefficients in `C`. -/
def relativeSingularHomologyFunctor : C ⥤ Arrow TopCat.{w} ⥤ C :=
  relativeSingularChainComplex C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

/-- The canonical projection `Hₙ(X) ⟶ Hₙ(X, U)` -/
def singularHomologyFunctor.πNatTrans :
    singularHomologyFunctor C n ⋙ (Functor.whiskeringLeft _ _ _).obj Arrow.rightFunc ⟶
    relativeSingularHomologyFunctor C n :=
  Functor.whiskerRight (relativeSingularChainComplex.π C)
    ((Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n))

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map `Hₙ(X, U) ⟶ Hₙ₊₁(U)` on the category of continuous injections `U ⟶ X`. -/
def singularHomologyFunctor.δNatTrans (m : ℕ) (e : m + 1 = n) :
    relativeSingularHomologyFunctor C n ⋙
      (Functor.whiskeringLeft _ _ _).obj ((ObjectProperty.arrow (.monomorphisms _)).ι) ⟶
    singularHomologyFunctor C m ⋙
      (Functor.whiskeringLeft _ _ _).obj ((ObjectProperty.arrow _).ι ⋙ Arrow.leftFunc) where
  app X :=
  { app f :=
    haveI : Mono (((singularChainComplexFunctor C).obj X).mapArrow.obj f.obj).hom :=
      haveI : Mono f.obj.hom := f.2; by dsimp; infer_instance
    (Limits.shortExact_cokerShortComplex
      (((singularChainComplexFunctor C).obj X).mapArrow.obj f.obj)).δ n m (by simpa)
    naturality {f g} α := (HomologicalComplex.HomologySequence.δ_naturality
      (((relativeSingularShortComplex C).obj X).map _) _ _ _ _ _).symm }
  naturality X Y f := NatTrans.ext <| funext fun α ↦
    (HomologicalComplex.HomologySequence.δ_naturality
      (((relativeSingularShortComplex C).map f).app _) _ _ _ _ _).symm

variable {C}

/-- `H_[n](f; R)` is the `n`-th relative singular homology group of `f : U ⟶ X`
with coefficients in `R`. -/
scoped[SingularHomology] notation3 "H_[" n "](" f "; " R ")" =>
  Functor.obj (Functor.obj (AlgebraicTopology.relativeSingularHomologyFunctor _ n) R) (Arrow.mk f)

open SingularHomology singularHomologyFunctor

/-- The projection `Hₙ(X) ⟶ Hₙ(X, U)` induced by a continuous injection `U ⟶ X`. -/
abbrev SingularHomology.π
    {U X : TopCat} (f : U ⟶ X) (R : C) :
    H_[n](X; R) ⟶ H_[n](f; R) :=
  ((πNatTrans C n).app R).app (.mk f)

/-- The connecting map `Hₘ₊₁(X, U) ⟶ Hₘ(U)` induced by a continuous injection `U ⟶ X`. -/
abbrev SingularHomology.δ
    (m : ℕ) (e : m + 1 = n) {U X : TopCat} (f : U ⟶ X) [Mono f] (R : C) :
    H_[n](f; R) ⟶ H_[m](U; R) :=
  ((δNatTrans C n m e).app R).app ⟨_, ‹_›⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma SingularHomology.map_π {U X : TopCat} (f : U ⟶ X) [Mono f] (R : C) :
    map n f R ≫ π n f R = 0 :=
  (HomologicalComplex.homologyMap_comp ..).symm.trans (by simp [relativeSingularChainComplex.π])

@[reassoc (attr := simp)]
lemma SingularHomology.δ_map
    (m : ℕ) (e : m + 1 = n) {U X : TopCat} (f : U ⟶ X) [Mono f] (R : C) :
    δ n m e f R ≫ map m f R = 0 :=
  @ShortComplex.ShortExact.δ_comp ..

@[reassoc (attr := simp)]
lemma SingularHomology.π_δ
    (m : ℕ) (e : m + 1 = n) {U X : TopCat} (f : U ⟶ X) [Mono f] (R : C) :
    π n f R ≫ δ n m e f R = 0 :=
  haveI : Mono (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f)).hom := by
    dsimp; infer_instance
  (ShortComplex.shortExact_cokerFunctor
    (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f))).comp_δ n m (by simpa)

lemma SingularHomology.exact_δ_map
    (m : ℕ) (e : m + 1 = n) {U X : TopCat} (f : U ⟶ X) [Mono f] (R : C) :
    (ShortComplex.mk (δ n m e f R) (map m f R) (δ_map ..)).Exact :=
  haveI : Mono (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f)).hom := by
    dsimp; infer_instance
  (ShortComplex.shortExact_cokerFunctor
    (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f))).homology_exact₁ n m (by simpa)

lemma SingularHomology.exact_π_δ
    (m : ℕ) (e : m + 1 = n) {U X : TopCat} (f : U ⟶ X) [Mono f] (R : C) :
    (ShortComplex.mk (π n f R) (δ n m e f R) (π_δ ..)).Exact :=
  haveI : Mono (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f)).hom := by
    dsimp; infer_instance
  (ShortComplex.shortExact_cokerFunctor
    (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f))).homology_exact₃ n m (by simpa)

lemma SingularHomology.exact_map_δ {U X : TopCat} (f : U ⟶ X) [Mono f] (R : C) :
    (ShortComplex.mk (map n f R) (π n f R) (map_π ..)).Exact :=
  haveI : Mono (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f)).hom := by
    dsimp; infer_instance
  (ShortComplex.shortExact_cokerFunctor
    (((singularChainComplexFunctor C).obj R).mapArrow.obj (.mk f))).homology_exact₂ n

lemma isZero_relativeSingularChainComplex_of_isIso {U X : TopCat} (f : U ⟶ X) [IsIso f] (R : C) :
    IsZero (((relativeSingularChainComplex C).obj R).obj (.mk f)) := by
  dsimp [relativeSingularChainComplex]
  exact isZero_cokernel_of_epi _

lemma isZero_relativeSingularHomologyFunctor_of_isIso {U X : TopCat} (f : U ⟶ X) [IsIso f] (R : C) :
    IsZero H_[n](f; R) :=
  (HomologicalComplex.homologyFunctor _ _ _).map_isZero
    (isZero_relativeSingularChainComplex_of_isIso ..)

end AlgebraicTopology
