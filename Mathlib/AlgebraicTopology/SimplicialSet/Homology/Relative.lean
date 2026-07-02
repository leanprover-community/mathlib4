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

noncomputable abbrev chainComplexFunctorLeft :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.leftFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

noncomputable abbrev chainComplexFunctorRight :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.rightFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

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

@[no_expose]
noncomputable def chainComplexFunctor : C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  cokernel (chainComplexFunctorLeftToRight.{w} C)

@[no_expose]
noncomputable def chainComplexFunctorπ :
    chainComplexFunctorRight.{w} C ⟶ chainComplexFunctor.{w} C :=
  cokernel.π _

@[reassoc (attr := simp)]
lemma chainComplexFunctor_condition :
    chainComplexFunctorLeftToRight C ≫ chainComplexFunctorπ.{w} C = 0 :=
  cokernel.condition _

@[no_expose]
noncomputable def cokernelCoforkChainComplexFunctorLeftToRight :
    CokernelCofork (chainComplexFunctorLeftToRight.{w} C) :=
  CokernelCofork.ofπ _ (chainComplexFunctor_condition _)

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

noncomputable abbrev chainComplex : ChainComplex C ℕ :=
  ((SSetPair.chainComplexFunctor C).obj R).obj P

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

noncomputable def cokernelCoforkChainComplex :
    CokernelCofork (SSet.chainComplexMap P.hom R) :=
  CokernelCofork.ofπ _ (chainComplex_condition ..)

set_option backward.isDefEq.respectTransparency false in
@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplex :
    IsColimit (P.cokernelCoforkChainComplex R) :=
  (CokernelCofork.isColimitMapCoconeEquiv
      (cokernelCoforkChainComplexFunctorLeftToRight C)
      ((evaluation ..).obj R ⋙ (evaluation ..).obj P)).1
      (isColimitOfPreserves ((evaluation ..).obj R ⋙ (evaluation ..).obj P)
    (isColimitCokernelCoforkChainComplexFunctorLeftToRight.{w} C))

noncomputable def cokernelCoforkChainComplexX (n : ℕ) :
    CokernelCofork ((SSet.chainComplexMap P.hom R).f n) :=
  CokernelCofork.ofπ _ (chainComplex_condition_f ..)

@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplexX (n : ℕ) :
    IsColimit (P.cokernelCoforkChainComplexX R n) :=
  CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkChainComplex R)
    (HomologicalComplex.eval _ _ n)

end SSetPair
