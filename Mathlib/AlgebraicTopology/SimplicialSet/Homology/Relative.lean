/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Relative simplicial homology


-/

@[expose] public section

open Simplicial CategoryTheory Limits Opposite

universe w v u

namespace SSetPair

section

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The bifunctor which sends `R : C` and a pair of simplicial sets `i : X ⟶ Y`
(with `i` a monomorphism) to `X.chainComplex R`, which is the
chain complex of `X` with coefficients in `R` (the usual one is for `C := Ab`
and `R := ℤ`.). -/
noncomputable abbrev chainComplexFunctorLeft :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft ..).obj
    (SSetPair.forget ⋙ Arrow.leftFunc)

/-- The bifunctor which sends `R : C` and a pair of simplicial sets `i : X ⟶ Y`
(with `i` a monomorphism) to `Y.chainComplex R`, which is the
chain complex of `Y` with coefficients in `R` (the usual one is for `C := Ab`
and `R := ℤ`.). -/
noncomputable abbrev chainComplexFunctorRight :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft ..).obj
    (SSetPair.forget ⋙ Arrow.rightFunc)

/-- The map `X.chainComplex R ⟶ Y.chainComplex R` for each pair of simplicial
sets `i : X ⟶ Y` (with `i` a monomorphism), and `R : C`, as a natural transformation of
bifunctors `C ⥤ SSetPair ⥤ ChainComplex C ℕ`. -/
noncomputable abbrev chainComplexFunctorLeftToRight :
    chainComplexFunctorLeft.{w} C ⟶ chainComplexFunctorRight.{w} C :=
  Functor.whiskerLeft _ ((Functor.whiskeringLeft ..).map
    (Functor.whiskerLeft _ Arrow.leftToRight))

instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    Mono ((SSet.chainComplexMap P.hom R).f n) :=
  inferInstanceAs (Mono ((sigmaConst.obj R).map (P.hom.app (op ⦋n⦌))))

set_option backward.defeqAttrib.useBackward true in
instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    dsimp% Mono ((SSet.chainComplexMap P.hom R).f n) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap P.hom R).f n))

instance (R : C) (P : SSetPair.{w}) :
    Mono (SSet.chainComplexMap P.hom R) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

instance (R : C) (P : SSetPair.{w}) :
    dsimp% Mono (SSet.chainComplexMap P.hom R) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

set_option backward.defeqAttrib.useBackward true in
instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    Mono ((((chainComplexFunctorLeftToRight C).app R).app P).f n) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap P.hom R).f n))

instance (R : C) (P : SSetPair.{w}) :
    Mono (((chainComplexFunctorLeftToRight C).app R).app P) :=
  inferInstanceAs (Mono (SSet.chainComplexMap P.hom R))

instance (R : C) : Mono ((chainComplexFunctorLeftToRight C).app R) :=
  NatTrans.mono_of_mono_app _

instance : Mono (chainComplexFunctorLeftToRight C) :=
  NatTrans.mono_of_mono_app _

set_option backward.defeqAttrib.useBackward true in
instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    HasCokernel ((((chainComplexFunctorLeftToRight C).app R).app P).f n) := by
  dsimp [SSet.chainComplexFunctor]
  infer_instance

instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    HasCokernel ((SSet.chainComplexMap P.hom R).f n) :=
  inferInstanceAs (HasCokernel ((((chainComplexFunctorLeftToRight C).app R).app P).f n))

instance (R : C) (P : SSetPair.{w}) :
    HasCokernel (((chainComplexFunctorLeftToRight C).app R).app P) :=
  HomologicalComplex.hasCokernel_of_hasCokernel_f _

instance (R : C) : HasCokernel ((chainComplexFunctorLeftToRight C).app R) :=
  hasCokernel_of_hasCokernel_app _

instance : HasCokernel (chainComplexFunctorLeftToRight.{w} C) :=
  hasCokernel_of_hasCokernel_app _

/--
The chain complex associated to a *pair* of simplicial sets, with coefficients in `R : C`.
It computes the simplicial homology of a pair of simplicial sets with coefficients
in `R`. One can recover the ordinary simplicial chain complex when `C := Ab`
and `R := ℤ`.
-/
@[no_expose]
noncomputable def chainComplexFunctor : C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  cokernel (chainComplexFunctorLeftToRight.{w} C)

/--
For any pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism)
and any `R : C`, this is the map from the chain complex of `Y`
(with coefficients in `R`) to the chain complex of the pair,
as a natural transformation of bifunctors `C ⥤ SSetPair ⥤ ChainComplex C ℕ`.
-/
@[no_expose]
noncomputable def chainComplexFunctorπ :
    chainComplexFunctorRight.{w} C ⟶ chainComplexFunctor.{w} C :=
  cokernel.π _

instance : Epi (chainComplexFunctorπ.{w} C) := coequalizer.π_epi

@[reassoc (attr := simp)]
lemma chainComplexFunctor_condition :
    chainComplexFunctorLeftToRight C ≫ chainComplexFunctorπ.{w} C = 0 :=
  cokernel.condition _

/-- The (colimit) cokernel cofork expressing the bifunctor
`SSetPair.chainComplexFunctor C : C ⥤ SSetPair ⥤ ChainComplex C ℕ`
as a cokernel of `chainComplexFunctorLeftToRight C`. -/
@[no_expose]
noncomputable def cokernelCoforkChainComplexFunctorLeftToRight :
    CokernelCofork (chainComplexFunctorLeftToRight.{w} C) :=
  CokernelCofork.ofπ _ (chainComplexFunctor_condition _)

/-- The bifunctor `SSetPair.chainComplexFunctor C : C ⥤ SSetPair ⥤ ChainComplex C ℕ`
is a cokernel of `chainComplexFunctorLeftToRight C`. -/
@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplexFunctorLeftToRight :
    IsColimit (cokernelCoforkChainComplexFunctorLeftToRight.{w} C) :=
  cokernelIsCokernel _

instance (R : C) :
    PreservesColimit (parallelPair (chainComplexFunctorLeftToRight.{w} C) 0)
      ((evaluation ..).obj R) :=
  evaluation_preservesCokernel_of_hasCokernel_app ..

instance (R : C) (P : SSetPair.{w}) :
    PreservesColimit (parallelPair ((chainComplexFunctorLeftToRight.{w} C).app R) 0)
      ((evaluation ..).obj P) :=
  evaluation_preservesCokernel_of_hasCokernel_app ..

set_option backward.defeqAttrib.useBackward true in
instance (R : C) (P : SSetPair.{w}) :
    PreservesColimit (parallelPair (chainComplexFunctorLeftToRight.{w} C) 0 ⋙
      (evaluation ..).obj R) ((evaluation ..).obj P) :=
  preservesColimit_of_iso_diagram
    (K₁ := parallelPair ((chainComplexFunctorLeftToRight.{w} C).app R) 0) _
      (parallelPair.ext (Iso.refl _) (Iso.refl _))

instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    PreservesColimit (parallelPair (((chainComplexFunctorLeftToRight.{w} C).app R).app P) 0)
      (HomologicalComplex.eval _ _ n) :=
  HomologicalComplex.eval_preservesCokernel_of_hasCokernel_f ..

set_option backward.defeqAttrib.useBackward true in
instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    PreservesColimit (parallelPair (chainComplexFunctorLeftToRight.{w} C) 0 ⋙
      ((evaluation ..).obj R ⋙ (evaluation ..).obj P))
      (HomologicalComplex.eval _ _ n) :=
  preservesColimit_of_iso_diagram
    (K₁ := parallelPair (((chainComplexFunctorLeftToRight.{w} C).app R).app P) 0) _
      (parallelPair.ext (Iso.refl _) (Iso.refl _))

instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    PreservesColimit (parallelPair (chainComplexFunctorLeftToRight.{w} C) 0)
      ((evaluation ..).obj R ⋙ (evaluation ..).obj P ⋙ HomologicalComplex.eval _ _ n) :=
  preservesColimit_of_natIso _ (Functor.associator ..)

instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    PreservesColimit (parallelPair (SSet.chainComplexMap P.hom R) 0)
      (HomologicalComplex.eval C _ n) :=
  HomologicalComplex.eval_preservesCokernel_of_hasCokernel_f ..

variable {C} (P P' P'' : SSetPair.{w}) (f : P ⟶ P') (g : P' ⟶ P'') (R : C)

/-- The chain complex of a pair of simplicial sets
with coefficients in `R : C` (e.g. `C := Ab` and `R := ℤ`.) -/
noncomputable abbrev chainComplex : ChainComplex C ℕ :=
  ((SSetPair.chainComplexFunctor C).obj R).obj P

/-- Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism),
this is the morphism from the chain complex of `Y` to the
chain complex of the pair. -/
noncomputable def chainComplexπ : P.right.chainComplex R ⟶ P.chainComplex R :=
  ((chainComplexFunctorπ.{w} C).app R).app P

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma chainComplex_condition :
    dsimp% SSet.chainComplexMap P.hom R ≫ P.chainComplexπ R = 0 :=
  NatTrans.congr_app (NatTrans.congr_app (chainComplexFunctor_condition C) R) P

@[reassoc (attr := simp)]
lemma chainComplex_condition_f (n : ℕ) :
    dsimp% (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0 := by
  simp [← HomologicalComplex.comp_f]

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism)
and `R : C` (e.g. `C := Ab` and `R := ℤ`), this is the cokernel cofork
expressing the chain complex `SSetPair.chainComplex` of the pair
as a cokernel of the map `X.chainComplex R ⟶ Y.chainComplex R`.
-/
noncomputable def cokernelCoforkChainComplex :
    CokernelCofork (SSet.chainComplexMap P.hom R) :=
  CokernelCofork.ofπ _ (chainComplex_condition ..)

set_option backward.isDefEq.respectTransparency false in
/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism)
and `R : C` (e.g. `C := Ab` and `R := ℤ`), the chain complex
`SSetPair.chainComplex` of the pair is a cokernel of the map
`X.chainComplex R ⟶ Y.chainComplex R`.
-/
@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplex :
    IsColimit (P.cokernelCoforkChainComplex R) :=
  (CokernelCofork.isColimitMapCoconeEquiv
      (cokernelCoforkChainComplexFunctorLeftToRight C)
      ((evaluation ..).obj R ⋙ (evaluation ..).obj P)).1
      (isColimitOfPreserves ((evaluation ..).obj R ⋙ (evaluation ..).obj P)
    (isColimitCokernelCoforkChainComplexFunctorLeftToRight.{w} C))

instance : Epi (P.chainComplexπ R) :=
  Cofork.IsColimit.epi (P.isColimitCokernelCoforkChainComplex R)

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism),
`R : C` (e.g. `C := Ab` and `R := ℤ`) and `n : ℕ`, this is the cokernel cofork
expressing the chain complex `SSetPair.chainComplex` of the pair
in degree `n` as a cokernel of the
map `(X.chainComplex R).X n ⟶ (Y.chainComplex R).X n`.
-/
noncomputable def cokernelCoforkChainComplexX (n : ℕ) :
    CokernelCofork ((SSet.chainComplexMap P.hom R).f n) :=
  CokernelCofork.ofπ _ (chainComplex_condition_f ..)

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism),
`R : C` (e.g. `C := Ab` and `R := ℤ`) and `n : ℕ`,
the chain complex `SSetPair.chainComplex` of the pair in degree `n`
is a cokernel of the map `(X.chainComplex R).X n ⟶ (Y.chainComplex R).X n`.
-/
@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplexX (n : ℕ) :
    IsColimit (P.cokernelCoforkChainComplexX R n) :=
  CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkChainComplex R)
    (HomologicalComplex.eval _ _ n)

instance (n : ℕ) : Epi ((P.chainComplexπ R).f n) :=
  Cofork.IsColimit.epi (P.isColimitCokernelCoforkChainComplexX R n)

/-- Given a pair of simplicial sets corresponding to a monomorphism `i : X ⟶ Y`,
this is the (short exact) short complex which relates
the chain complex of `X`, of `Y` and of the pair. -/
@[simps]
noncomputable def chainComplexShortComplex : ShortComplex (ChainComplex C ℕ) :=
    ShortComplex.mk _ _ (P.chainComplex_condition R)

set_option backward.defeqAttrib.useBackward true in
instance : Mono (P.chainComplexShortComplex R).f := by dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
instance : Epi (P.chainComplexShortComplex R).g := by dsimp; infer_instance

variable {P P'} in
/-- The morphism of simplicial chain complexes induces by a morphism
of simplicial sets. -/
noncomputable abbrev chainComplexMap : P.chainComplex R ⟶ P'.chainComplex R :=
  ((SSetPair.chainComplexFunctor C).obj R).map f

section

variable [CategoryWithHomology C]

/-- The relative simplicial homology with coefficients in `R : C` in degree `n`
of a pair of simplicial sets. -/
protected noncomputable abbrev homology (n : ℕ) : C := (P.chainComplex R).homology n

variable {P P'} in
/-- The morphism in relative simplicial homology that is induced by a morphism
of pairs of simplicial sets. -/
protected noncomputable abbrev homologyMap (n : ℕ) : P.homology R n ⟶ P'.homology R n :=
  HomologicalComplex.homologyMap (chainComplexMap f R) n

@[simp]
lemma homologyMap_id (n : ℕ) : SSetPair.homologyMap (𝟙 P) R n = 𝟙 _ := by
  simp [SSetPair.homologyMap]

variable {P P' P''} in
@[reassoc]
lemma homologyMap_comp (n : ℕ) :
    SSetPair.homologyMap (f ≫ g) R n =
      SSetPair.homologyMap f R n ≫ SSetPair.homologyMap g R n := by
  simp [SSetPair.homologyMap, HomologicalComplex.homologyMap_comp]

attribute [local simp] homologyMap_comp in
/-- The relative simplicial homology functor in degree `n` with coefficients in `R : C`. -/
@[simps]
noncomputable def homologyFunctor (n : ℕ) : SSetPair.{w} ⥤ C where
  obj P := P.homology R n
  map f := SSetPair.homologyMap f R n

/-- Given a pair of simplicial sets corresponding to a monomorphism `i : X ⟶ Y`,
this is the morphism from the homology of `Y` to the relative homology of the pair. -/
noncomputable abbrev homologyπ (n : ℕ) : P.right.homology R n ⟶ P.homology R n :=
  HomologicalComplex.homologyMap (P.chainComplexπ R) n

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma homologyMap_hom_homologyπ (n : ℕ) :
    SSet.homologyMap P.hom R n ≫ P.homologyπ R n = 0 := by
  simp [← HomologicalComplex.homologyMap_comp]

end

end

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  (P : SSetPair.{w}) (R : A)

lemma shortExact_chainComplexShortComplex :
    (P.chainComplexShortComplex R).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _
    (isColimitCokernelCoforkChainComplex ..)

/-- Given a pair of simplicial sets corresponding to a monomorphism `i : X ⟶ Y`,
this is the connecting morphism from the homology of the pair to the homology of `X`. -/
noncomputable def homologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    P.homology R n ⟶ P.left.homology R m :=
  (P.shortExact_chainComplexShortComplex R).δ n m (by simpa)

@[reassoc (attr := simp)]
lemma homologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    P.homologyδ R n m h ≫ SSet.homologyMap P.hom R m = 0 :=
  (P.shortExact_chainComplexShortComplex R).δ_comp n m (by simpa)

@[reassoc (attr := simp)]
lemma comp_homologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    P.homologyπ R n ≫ P.homologyδ R n m h = 0 :=
  (P.shortExact_chainComplexShortComplex R).comp_δ n m (by simpa)

lemma homology_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.homologyδ_comp R n m h)).Exact :=
  (P.shortExact_chainComplexShortComplex R).homology_exact₁ n m h

lemma homology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (P.homologyMap_hom_homologyπ R n)).Exact :=
  (P.shortExact_chainComplexShortComplex R).homology_exact₂ n

lemma homology_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.comp_homologyδ R n m h)).Exact :=
  (P.shortExact_chainComplexShortComplex R).homology_exact₃ n m h

instance : Epi (P.homologyπ R 0) :=
  HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)

end

end SSetPair
