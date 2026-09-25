/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologyCofork
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# The homology functor on a Grothendieck abelian category is accessible

In this file, we show that if `C` is a Grothendieck abelian category,
then the homology functors `ShortComplex C ⥤ C` and `HomologicalComplex C c ⥤ C`
are ℵ₀-accessible (i.e. preserve filtered colimits).

-/

public section

universe w

attribute [local instance] Cardinal.fact_isRegular_aleph0

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace CategoryTheory.ShortComplex

section

variable {J : Type*} [Category* J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

open ObjectProperty

instance : PreservesColimitsOfShape J (ShortComplex.cyclesFunctor C) :=
  (preservesColimitsOfShape J).prop_of_isLimit
    (ShortComplex.isLimitCyclesFunctorFork C) (by
      rintro (_ | _)
      all_goals
        dsimp
        infer_instance)

instance : PreservesColimitsOfShape J (ShortComplex.opcyclesFunctor C) :=
  (preservesColimitsOfShape J).prop_of_isColimit
    (ShortComplex.isColimitOpcyclesFunctorCofork C) (by
      rintro (_ | _)
      all_goals
        dsimp
        infer_instance)

instance : PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) :=
  (preservesColimitsOfShape J).prop_of_isColimit
    (ShortComplex.isColimitHomologyFunctorCofork C) (by
      rintro (_ | _)
      all_goals
        dsimp
        infer_instance)

end

section

variable [IsGrothendieckAbelian.{w} C]

instance : Functor.IsCardinalAccessible.{w} (ShortComplex.cyclesFunctor C) .aleph0 where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
    infer_instance

instance : Functor.IsCardinalAccessible.{w} (ShortComplex.opcyclesFunctor C) .aleph0 where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
    infer_instance

instance : Functor.IsCardinalAccessible.{w} (ShortComplex.homologyFunctor C) .aleph0 where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
    infer_instance

end

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable [IsGrothendieckAbelian.{w} C] {ι : Type*} {c : ComplexShape ι} (i : ι)

instance : Functor.IsCardinalAccessible.{w} (cyclesFunctor C c i) .aleph0 :=
  inferInstanceAs (Functor.IsCardinalAccessible (shortComplexFunctor C c i ⋙
    ShortComplex.cyclesFunctor C) _)

instance : Functor.IsCardinalAccessible.{w} (opcyclesFunctor C c i) .aleph0 :=
  inferInstanceAs (Functor.IsCardinalAccessible (shortComplexFunctor C c i ⋙
    ShortComplex.opcyclesFunctor C) _)

instance : Functor.IsCardinalAccessible.{w} (homologyFunctor C c i) .aleph0 :=
  inferInstanceAs (Functor.IsCardinalAccessible (shortComplexFunctor C c i ⋙
    ShortComplex.homologyFunctor C) _)

end HomologicalComplex
