/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

/-!
# Existence of conical pullbacks
-/

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- `HasPullback f g` represents the mere existence of a conical limit cone for the pair
of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` -/
abbrev HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasConicalLimit V (cospan f g)

/-- ensure conical pullbacks are pullbacks -/
example {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasConicalPullback V f g] : HasPullback f g :=
  inferInstance

variable (C)

/--
`HasConicalPullbacks` represents the existence of conical pullback for every pair of
morphisms
-/
abbrev HasConicalPullbacks : Prop := HasConicalLimitsOfShape WalkingCospan V C

/-- ensure pullbacks exist of existence of conical pullbacks -/
example [HasConicalPullbacks V C] : HasPullbacks C := inferInstance

end CategoryTheory.Enriched
