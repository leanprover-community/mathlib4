/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Dagur Asgeirsson, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Limits.Final

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

`V` has been made an `(V : outParam <| Type u')` in the classes below as it seems instance
inference prefers this. Otherwise it failed with
`cannot find synthesization order` on the instances below.
However, it is not fully clear yet whether this could lead to potential issues, for example
if there are multiple `MonoidalCategory _` instances in scope.
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

section Definitions

variable {J : Type u₁} [Category.{v₁} J]
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
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

variable {J : Type u₁} [Category.{v₁} J] {J' : Type u₂} [Category.{v₂} J']
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

namespace HasConicalLimit

variable {C}

variable {F G : J ⥤ C} [HasConicalLimit V F]

/-- ensure existence of a conical limit implies existence of a limit -/
example (F : J ⥤ C) [HasConicalLimit V F] : HasLimit F := inferInstance

/-- If a functor `F` has a conical limit, so does any naturally isomorphic functor. -/
lemma of_iso (e : F ≅ G) :
    HasConicalLimit V G where
  toHasLimit := hasLimit_of_iso e
  preservesLimit_eCoyoneda X :=
    preservesLimit_of_iso_diagram (eCoyoneda V X) e

variable (F)

instance hasConicalLimit_of_equiv (e : J' ≌ J) :
    HasConicalLimit V (e.functor ⋙ F) where
  exists_limit :=
    let cone : Cone (e.functor ⋙ F) := Cone.whisker e.functor (getLimitCone F).cone
    have isLimit : IsLimit cone := IsLimit.whiskerEquivalence (getLimitCone F).isLimit e
    ⟨cone, isLimit⟩
  preservesLimit_eCoyoneda _ := inferInstance

omit [HasConicalLimit V F] in

/-- If a `e ⋙ F` has a limit, and `e` is an equivalence, we can construct a limit of `F`. -/
theorem hasConicalLimit_of_equiv_comp (e : J' ≌ J) [HasConicalLimit V (e.functor ⋙ F)] :
    HasConicalLimit V F := by
  have : HasConicalLimit V (e.inverse ⋙ e.functor ⋙ F) :=
    hasConicalLimit_of_equiv V _ e.symm
  apply HasConicalLimit.of_iso V (e.invFunIdAssoc F)

end HasConicalLimit

namespace HasConicalLimitsOfShape

variable [HasConicalLimitsOfShape J V C]

variable (J) in

/-- existence of conical limits (of shape) implies existence of limits (of shape) -/
instance hasLimitsOfShape :
    HasLimitsOfShape J C where
  has_limit _ := inferInstance

/-- We can transport conical limits of shape `J` along an equivalence `J ≌ J'`. -/
theorem of_equiv (e : J ≌ J') : HasConicalLimitsOfShape J' V C := by
  constructor
  intro F
  apply HasConicalLimit.hasConicalLimit_of_equiv_comp V _ e

end HasConicalLimitsOfShape

namespace HasConicalLimitsOfSize

variable [HasConicalLimitsOfSize.{v₁, u₁} V C]

/-- existence of conical limits (of size) implies existence of limits (of size) -/
instance hasLimitsOfSize :
    HasLimitsOfSize.{v₁, u₁} C where
  has_limits_of_shape _ := inferInstance

/-- A category that has larger conical limits also has smaller conical limits. -/
theorem hasConicalLimitsOfSize_of_univLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}] :
    HasConicalLimitsOfSize.{v₂, u₂} V C where
  hasConicalLimitsOfShape J {_} := HasConicalLimitsOfShape.of_equiv V C
    ((ShrinkHoms.equivalence J).trans (Shrink.equivalence _)).symm

omit [HasConicalLimitsOfSize.{v₁, u₁} V C] in

/-- `HasConicalLimitsOfSize.shrink.{v, u} C` tries to obtain `HasConicalLimitsOfSize.{v, u} C`
from some other `HasConicalLimitsOfSize.{v₁, u₁} C`.
-/
theorem shrink [HasConicalLimitsOfSize.{max v₁ v₂, max u₁ u₂} V C] :
    HasConicalLimitsOfSize.{v₁, u₁} V C :=
  hasConicalLimitsOfSize_of_univLE.{max v₁ v₂, max u₁ u₂} V C

end HasConicalLimitsOfSize

end Results

namespace HasConicalLimits

-- Note that `Category.{v, v} J` is deliberately chosen this way, see `HasConicalLimits`.
variable (J : Type v) [SmallCategory J]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable [HasConicalLimits V C]

/-- ensure existence of (small) conical limits implies existence of (small) limits -/
example [HasConicalLimits V C] : HasLimits C := inferInstance

instance (priority := 100) hasSmallestConicalLimitsOfHasConicalLimits :
    HasConicalLimitsOfSize.{0, 0} V C :=
  HasConicalLimitsOfSize.shrink.{0, 0} V C

instance : HasConicalLimitsOfShape J V C := HasConicalLimitsOfSize.hasConicalLimitsOfShape J

end HasConicalLimits

end CategoryTheory.Enriched
