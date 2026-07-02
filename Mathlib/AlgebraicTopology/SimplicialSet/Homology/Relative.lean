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

universe w v u

namespace SSetPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

noncomputable def chainComplexFunctor₁ : C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.leftFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

noncomputable def chainComplexFunctor₂ : C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  (SSetPair.forget ⋙ Arrow.rightFunc ⋙ (SSet.chainComplexFunctor _).flip).flip

noncomputable def chainComplexFunctorTrans :
    chainComplexFunctor₁.{w} C ⟶ chainComplexFunctor₂.{w} C :=
  (flipFunctor ..).map
    (Functor.whiskerLeft  _ (Functor.whiskerRight Arrow.leftToRight _))

instance : HasCokernel (chainComplexFunctorTrans.{w} C) := by
  sorry

noncomputable def chainComplexFunctor : C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  cokernel (chainComplexFunctorTrans.{w} C)

end SSetPair
