/-
Copyright (c) 2023 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Data.FunLike.Fintype

/-!
# (Co)limits in the category of finite types

We show that finite (co)limits exist in `FintypeCat` and that they are preserved by the natural
inclusion `FintypeCat.incl`.
-/

open CategoryTheory Limits Functor

namespace CategoryTheory.Limits.FintypeCat

noncomputable def finiteLimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) (_ : (j : J) → Finite (K.obj j)) : Fintype (limit K) := by
  have : Fintype (sections K) := Fintype.ofFinite ↑(sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm

noncomputable instance inclusionCreatesFiniteLimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J FintypeCat.incl where
  CreatesLimit := by
    intro K
    have : Fintype (limit (K ⋙ FintypeCat.incl)) := by
      apply finiteLimitOfFiniteDiagram (K ⋙ FintypeCat.incl)
      intro j
      simp only [comp_obj, FintypeCat.incl_obj]
      exact inferInstance
    exact createsLimitOfFullyFaithfulOfIso (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl)
      (eqToIso rfl)

instance {J : Type} [SmallCategory J] [FinCategory J] : HasLimitsOfShape J FintypeCat where
  has_limit F := hasLimit_of_created F FintypeCat.incl

instance hasFiniteLimits : HasFiniteLimits FintypeCat where
  out _ := inferInstance

noncomputable instance inclusionPreservesFiniteLimits :
    PreservesFiniteLimits FintypeCat.incl where
  preservesFiniteLimits _ :=
    preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape FintypeCat.incl

noncomputable def finiteColimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) (_ : (j : J) → Finite (K.obj j)) : Fintype (colimit K) := by
  have : Finite (Types.Quot K) := Quot.finite (Types.Quot.Rel K)
  have : Fintype (Types.Quot K) := Fintype.ofFinite (Types.Quot K)
  exact Fintype.ofEquiv (Types.Quot K) (Types.colimitEquivQuot K).symm

noncomputable instance inclusionCreatesFiniteColimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J FintypeCat.incl where
  CreatesColimit := by
    intro K
    have : Fintype (colimit (K ⋙ FintypeCat.incl)) := by
      apply finiteColimitOfFiniteDiagram (K ⋙ FintypeCat.incl)
      intro j
      simp
      exact inferInstance
    exact createsColimitOfFullyFaithfulOfIso (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl)
      (eqToIso rfl)

instance {J : Type} [SmallCategory J] [FinCategory J] : HasColimitsOfShape J FintypeCat where
  has_colimit F := hasColimit_of_created F FintypeCat.incl

instance hasFiniteColimits : HasFiniteColimits FintypeCat where
  out _ := inferInstance

noncomputable instance inclusionPreservesFiniteColimits :
    PreservesFiniteColimits FintypeCat.incl where
  preservesFiniteColimits _ :=
    preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape FintypeCat.incl

end CategoryTheory.Limits.FintypeCat
