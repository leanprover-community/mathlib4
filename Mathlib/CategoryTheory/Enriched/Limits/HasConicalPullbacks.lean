/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

/-!
TODO: module docstring
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C) (c : Cone F)

/-- `HasPullback f g` represents a particular choice of conical limit cone for the pair
of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` -/
abbrev HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasConicalLimit V (cospan f g)

instance HasConicalPullback_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasConicalPullback V f g] : HasPullback f g :=
  inferInstance

variable (C)

/-- `HasConicalPullbacks` represents a choice of conical pullback for every pair of morphisms -/
abbrev HasConicalPullbacks : Prop := HasConicalLimitsOfShape WalkingCospan V C

instance HasConicalPullbacks_hasPullbacks [hyp : HasConicalPullbacks V C] : HasPullbacks C :=
  inferInstance

end CategoryTheory.Enriched
