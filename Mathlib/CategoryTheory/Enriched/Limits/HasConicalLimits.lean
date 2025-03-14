/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Dagur Asgeirsson, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Existence of conical limits

This file contains different statements about the (non-constructive) existence of conical limits.

The main constructions are the following.

- `HasConicalLimit`: there exists a conical limit for `F : J ⥤ C`.
- `HasConicalLimitsOfShape J`: All functors `F : J ⥤ C` have conical limits.
- `HasConicalLimitsOfSize.{v₁, u₁}`: For all small `J` all functors `F : J ⥤ C` have conical limits.
- `HasConicalLimits `: `C` has all (small) conical limits.

## References

* [Kelly G.M., *Basic concepts of enriched category theory*][kelly2005]:
  See section 3.8 for a similar treatment, although the content of this file is not directly
  adapted from there.

## Implementation notes

It seems that instance inference would work much smoother when `V` would be made
an `(V : outParam <| Type u')` for the `class`es below. However, this might
cause other problems, for example maybe if different `[MonoidalCategory _]` are in scope.
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

section Definitions

-- note: for the classes it seems that instance inference wants `V` to be an `outParam`.
variable {J : Type u₁} [Category.{v₁} J]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

variable {C} in

/--
`HasConicalLimit F` represents the mere existence of a conical limit for `F`.
-/
class HasConicalLimit (F : J ⥤ C) : Prop extends HasLimit F where
  preservesLimit_eCoyoneda (X : C) : PreservesLimit F (eCoyoneda V X) := by infer_instance

attribute [instance] HasConicalLimit.preservesLimit_eCoyoneda

variable (J) in

/--
`C` has conical limits of shape `J` if there exists a conical limit for every functor `F : J ⥤ C`.
-/
class HasConicalLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits. -/
  hasConicalLimit : ∀ F : J ⥤ C, HasConicalLimit V F := by infer_instance

attribute [instance] HasConicalLimitsOfShape.hasConicalLimit

/--
`C` has all conical limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has conical limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
@[pp_with_univ]
class HasConicalLimitsOfSize : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have conical limits -/
  hasConicalLimitsOfShape : ∀ (J : Type u₁) [Category.{v₁} J], HasConicalLimitsOfShape J V C := by
    infer_instance

attribute [instance] HasConicalLimitsOfSize.hasConicalLimitsOfShape

/-- `C` has all (small) conical limits if it has limits of every shape that is as big as its
hom-sets. -/
abbrev HasConicalLimits : Prop := HasConicalLimitsOfSize.{v, v} V C

end Definitions

section Results

variable {J : Type u₁} [Category.{v₁} J]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

variable {C} in

/-- ensure existence of a conical limit implies existence of a limit -/
example {F : J ⥤ C} [HasConicalLimit V F] : HasLimit F := inferInstance

/-- existence of conical limits (of shape) implies existence of limits (of shape) -/
-- TODO: errors if made an `instance`.
def HasConicalLimitsOfShape.hasLimitsOfShape [HasConicalLimitsOfShape J V C] :
    HasLimitsOfShape J C where
  has_limit _ := inferInstance

/-- existence of conical limits (of size) implies existence of limits (of size) -/
-- TODO: errors if made an `instance`.
def HasConicalLimitsOfSize.hasLimitsOfSize [HasConicalLimitsOfSize.{v₁, u₁} V C] :
    HasLimitsOfSize.{v₁, u₁} C where
  has_limits_of_shape _ :=
    -- TODO: use `inferInstance` instead
    HasConicalLimitsOfShape.hasLimitsOfShape V C

/-- ensure existence of (small) conical limits implies existence of (small) limits -/
-- TODO: errors if made an `instance`.
def HasConicalLimits.hasLimits [HasConicalLimits V C] : HasLimits C :=
  -- TODO: use `inferInstance` instead
  HasConicalLimitsOfSize.hasLimitsOfSize V C

end Results

end CategoryTheory.Enriched
