/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Relative simplicial homology


-/

@[expose] public section

open Simplicial CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] {c : ComplexShape ι} [HasZeroMorphisms C]

lemma hasCokernel_of_hasCokernel_f {K L : HomologicalComplex C c} (f : K ⟶ L)
    [∀ i, HasCokernel (f.f i)] :
    HasCokernel f := sorry

end HomologicalComplex

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* J] [Category* C]
  [HasZeroMorphisms C]

lemma hasCokernel_of_hasCokernel_app {F G : J ⥤ C} (f : F ⟶ G)
    [∀ j, HasCokernel (f.app j)] :
    HasCokernel f := by
  sorry


end CategoryTheory.Limits

universe w v u

namespace SSetPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

noncomputable def chainComplexFunctorNatTransSrc :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.leftFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

noncomputable def chainComplexFunctorNatTransTgt :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.rightFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

noncomputable def chainComplexFunctorNatTrans :
    chainComplexFunctorNatTransSrc.{w} C ⟶ chainComplexFunctorNatTransTgt.{w} C :=
  (flipFunctor _ _ _).map
    (Functor.whiskerLeft SSetPair.forget.{w}
      (Functor.whiskerRight Arrow.leftToRight (SSet.chainComplexFunctor C).flip))

set_option backward.defeqAttrib.useBackward true in
instance : HasCokernel (chainComplexFunctorNatTrans.{w} C) := by
  apply +allowSynthFailures hasCokernel_of_hasCokernel_app
  intro X
  apply +allowSynthFailures hasCokernel_of_hasCokernel_app
  intro P
  apply +allowSynthFailures HomologicalComplex.hasCokernel_of_hasCokernel_f
  intro i
  apply CategoryTheory.Limits.instHasCokernelMap'Id

noncomputable def chainComplexFunctor : C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  cokernel (chainComplexFunctorNatTrans.{w} C)

end SSetPair
