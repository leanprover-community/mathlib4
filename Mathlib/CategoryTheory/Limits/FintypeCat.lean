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
import Mathlib.Data.Finite.Basic

/-!
# (Co)limits in the category of finite types

We show that finite (co)limits exist in `FintypeCat` and that they are preserved by the natural
inclusion `FintypeCat.incl`.
-/

open CategoryTheory Limits Functor

universe u

namespace CategoryTheory.Limits.FintypeCat

instance {J : Type} [SmallCategory J] (K : J ⥤ FintypeCat.{u}) (j : J) :
    Finite ((K ⋙ FintypeCat.incl.{u}).obj j) := by
  simp only [comp_obj, FintypeCat.incl_obj]
  infer_instance

/-- Any functor from a finite category to Types that only involves finite objects,
has a finite limit. -/
noncomputable instance finiteLimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (limit K) := by
  have : Fintype (sections K) := Fintype.ofFinite (sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm

noncomputable instance inclusionCreatesFiniteLimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J FintypeCat.incl.{u} where
  CreatesLimit {K} := createsLimitOfFullyFaithfulOfIso
    (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/- Help typeclass inference to infer creation of finite limits for the forgtful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteLimits

instance {J : Type} [SmallCategory J] [FinCategory J] : HasLimitsOfShape J FintypeCat.{u} where
  has_limit F := hasLimit_of_created F FintypeCat.incl

instance hasFiniteLimits : HasFiniteLimits FintypeCat.{u} where
  out _ := inferInstance

noncomputable instance inclusionPreservesFiniteLimits :
    PreservesFiniteLimits FintypeCat.incl.{u} where
  preservesFiniteLimits _ :=
    preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape FintypeCat.incl

/- Help typeclass inference to infer preservation of finite limits for the forgtful functor. -/
noncomputable instance : PreservesFiniteLimits (forget FintypeCat) :=
  FintypeCat.inclusionPreservesFiniteLimits

/-- Any functor from a finite category to Types that only involves finite objects,
has a finite colimit. -/
noncomputable instance finiteColimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (colimit K) := by
  have : Finite (Types.Quot K) := Quot.finite (Types.Quot.Rel K)
  have : Fintype (Types.Quot K) := Fintype.ofFinite (Types.Quot K)
  exact Fintype.ofEquiv (Types.Quot K) (Types.colimitEquivQuot K).symm

noncomputable instance inclusionCreatesFiniteColimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J FintypeCat.incl.{u} where
  CreatesColimit {K} := createsColimitOfFullyFaithfulOfIso
    (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/- Help typeclass inference to infer creation of finite colimits for the forgtful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteColimits

instance {J : Type} [SmallCategory J] [FinCategory J] : HasColimitsOfShape J FintypeCat.{u} where
  has_colimit F := hasColimit_of_created F FintypeCat.incl

instance hasFiniteColimits : HasFiniteColimits FintypeCat.{u} where
  out _ := inferInstance

noncomputable instance inclusionPreservesFiniteColimits :
    PreservesFiniteColimits FintypeCat.incl.{u} where
  preservesFiniteColimits _ :=
    preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape FintypeCat.incl

/- Help typeclass inference to infer preservation of finite colimits for the forgtful functor. -/
noncomputable instance : PreservesFiniteColimits (forget FintypeCat) :=
  FintypeCat.inclusionPreservesFiniteColimits

end CategoryTheory.Limits.FintypeCat
