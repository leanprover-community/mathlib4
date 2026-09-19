/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# The extension of homological complexes preserves limits and colimits

Given an embedding `e : c.Embedding c'` of complex shapes, we show that the
functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`
preserves limits and colimits when suitable limits and colimits exists
in `C`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits HomologicalComplex

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {C : Type*} [Category* C] [HasZeroObject C] [HasZeroMorphisms C]
  {J : Type*} [Category* J]

instance [HasLimitsOfShape J C] : PreservesLimitsOfShape J (e.extendFunctor C) :=
  preservesLimitsOfShape_of_eval _ (fun i' ↦ by
    by_cases! hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      exact preservesLimitsOfShape_of_natIso (e.extendFunctorCompEvalIso C hi).symm
    · exact Functor.preservesLimitsOfShape_of_isZero _
        (e.isZero_extendFunctor_comp_eval _ _ hi') _)

instance [HasColimitsOfShape J C] : PreservesColimitsOfShape J (e.extendFunctor C) :=
  preservesColimitsOfShape_of_eval _ (fun i' ↦ by
    by_cases! hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      exact preservesColimitsOfShape_of_natIso (e.extendFunctorCompEvalIso C hi).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _
        (e.isZero_extendFunctor_comp_eval _ _ hi') _)

instance [HasFiniteLimits C] : PreservesFiniteLimits (e.extendFunctor C) where
  preservesFiniteLimits _ _ _ := inferInstance

instance [HasFiniteColimits C] : PreservesFiniteColimits (e.extendFunctor C) where
  preservesFiniteColimits _ _ _ := inferInstance

instance [HasLimitsOfSize.{v, u} C] : PreservesLimitsOfSize.{v, u} (e.extendFunctor C) where

instance [HasColimitsOfSize.{v, u} C] : PreservesColimitsOfSize.{v, u} (e.extendFunctor C) where

end ComplexShape.Embedding
