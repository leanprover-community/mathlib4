/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

/-!
# Relative simplicial homology


-/

@[expose] public section

open Simplicial CategoryTheory Limits

universe w v u

namespace SSetPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The bifunctor which sends `R : C` and a pair of simplicial sets `i : X ⟶ Y`
(with `i` a monomorphism) to `X.chainComplex R`, which is the
chain complex of `X` with coefficients in `R` (the usual one is for `C := Ab`
and `R := ℤ`.). -/
noncomputable abbrev chainComplexFunctorLeft :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.leftFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

/-- The bifunctor which sends `R : C` and a pair of simplicial sets `i : X ⟶ Y`
(with `i` a monomorphism) to `Y.chainComplex R`, which is the
chain complex of `Y` with coefficients in `R` (the usual one is for `C := Ab`
and `R := ℤ`.). -/
noncomputable abbrev chainComplexFunctorRight :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.rightFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

/-- The map `X.chainComplex R ⟶ Y.chainComplex R` for each pair of simplicial
sets `i : X ⟶ Y` (with `i` a monomorphism), and `R : C`, as a natural transformation of
bifunctors `C ⥤ SSetPair ⥤ ChainComplex C ℕ`. -/
noncomputable abbrev chainComplexFunctorLeftToRight :
    chainComplexFunctorLeft.{w} C ⟶ chainComplexFunctorRight.{w} C :=
  (flipFunctor ..).map
    (Functor.whiskerLeft SSetPair.forget.{w}
      (Functor.whiskerRight Arrow.leftToRight (SSet.chainComplexFunctor C).flip))

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

example (R : C) (P : SSetPair.{w}) :
    PreservesColimit (parallelPair (chainComplexFunctorLeftToRight.{w} C) 0)
      ((evaluation ..).obj R ⋙ (evaluation ..).obj P) := by
  infer_instance

example (R : C) (P : SSetPair.{w}) (n : ℕ) :
    PreservesColimit (parallelPair (chainComplexFunctorLeftToRight.{w} C) 0)
      (((evaluation ..).obj R ⋙ (evaluation ..).obj P) ⋙ HomologicalComplex.eval _ _ n) := by
  infer_instance

instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    PreservesColimit (parallelPair (chainComplexFunctorLeftToRight.{w} C) 0)
      ((evaluation ..).obj R ⋙ (evaluation ..).obj P ⋙ HomologicalComplex.eval _ _ n) :=
  preservesColimit_of_natIso _ (Functor.associator ..)

instance (R : C) (P : SSetPair.{w}) (n : ℕ) :
    PreservesColimit (parallelPair (SSet.chainComplexMap P.hom R) 0)
      (HomologicalComplex.eval C _ n) :=
  HomologicalComplex.eval_preservesCokernel_of_hasCokernel_f ..

variable {C} (P : SSetPair.{w}) (R : C)

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

end SSetPair
