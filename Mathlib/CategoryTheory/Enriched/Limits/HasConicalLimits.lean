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
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/--
`HasConicalLimit F` represents the mere existence of a conical limit for `F`.
-/
class HasConicalLimit (F : J ⥤ C) : Prop extends HasLimit F where
  preservesLimit_eCoyoneda (X : C) : PreservesLimit F (eCoyoneda V X) := by infer_instance

attribute [instance] HasConicalLimit.preservesLimit_eCoyoneda

/--
Mirrors `LimitCone F`.
-/
structure ConicalLimitCone (F : J ⥤ C) where
  /-- the underlying limit cone of a conical limit cone -/
  limitCone : LimitCone F
  /--
  proof that the cone obtained by applying the coyoneda
  functor `(X ⟶[V] -)` to the ordinary limit cone (`limitCone.cone`) is a limit cone in `V`.
  -/
  isConicalLimit (X : C) : IsLimit <| (eCoyoneda V X).mapCone limitCone.cone

variable (C)

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

variable {C} (F : J ⥤ C) [HasConicalLimit V F]

/-- ensure existence of a conical limit implies existence of a limit -/
example : HasLimit F := inferInstance

variable {F} in
/-- If a functor `F` has a conical limit, so does any naturally isomorphic functor. -/
lemma of_iso {G : J ⥤ C} (e : F ≅ G) :
    HasConicalLimit V G where
  toHasLimit := hasLimit_of_iso e
  preservesLimit_eCoyoneda X := preservesLimit_of_iso_diagram (eCoyoneda V X) e

instance of_equiv (G : J' ⥤ J) [G.IsEquivalence] : HasConicalLimit V (G ⋙ F) where

omit [HasConicalLimit V F] in
/-- If a `G ⋙ F` has a limit, and `G` is an equivalence, we can construct a limit of `F`. -/
lemma of_equiv_comp (G : J' ⥤ J) [G.IsEquivalence]
    [HasConicalLimit V (G ⋙ F)] : HasConicalLimit V F :=
  have e : G.inv ⋙ G ⋙ F ≅ F := G.asEquivalence.invFunIdAssoc F
  HasConicalLimit.of_iso V e

/-- Use the axiom of choice to extract explicit `ConicalLimitCone F` from `HasConicalLimit F`. -/
noncomputable def getConicalLimitCone : ConicalLimitCone V F where
  limitCone := getLimitCone F
  isConicalLimit X := Classical.choice <|
    (preservesLimit_eCoyoneda X).preserves (getLimitCone F).isLimit

/-- An arbitrary choice of conical limit cone for a functor. -/
noncomputable def conicalLimitCone : ConicalLimitCone V F := getConicalLimitCone V F

/-- An arbitrary choice of conical limit object of a functor. -/
noncomputable def conicalLimit : C := (conicalLimitCone V F).limitCone.cone.pt

namespace conicalLimit

/-- The projection from the conical limit object to a value of the functor. -/
protected noncomputable def π (j : J) : conicalLimit V F ⟶ F.obj j :=
  (conicalLimitCone V F).limitCone.cone.π.app j

@[reassoc (attr := simp)]
protected theorem w {j j' : J} (f : j ⟶ j') :
    conicalLimit.π V F j ≫ F.map f = conicalLimit.π V F j' :=
  (conicalLimitCone V F).limitCone.cone.w f

end conicalLimit

end HasConicalLimit

variable (J) in
/-- existence of conical limits (of shape) implies existence of limits (of shape) -/
instance HasConicalLimitsOfShape.hasLimitsOfShape [HasConicalLimitsOfShape J V C] :
    HasLimitsOfShape J C where

/-- We can transport conical limits of shape `J'` along an equivalence `J' ≌ J`. -/
lemma HasConicalLimitsOfShape.of_equiv [HasConicalLimitsOfShape J' V C]
    (G : J' ⥤ J) [G.IsEquivalence] : HasConicalLimitsOfShape J V C where
  hasConicalLimit F := HasConicalLimit.of_equiv_comp V F G

/-- existence of conical limits (of size) implies existence of limits (of size) -/
instance HasConicalLimitsOfSize.hasLimitsOfSize [HasConicalLimitsOfSize.{v₁, u₁} V C] :
    HasLimitsOfSize.{v₁, u₁} C where

/-- ensure existence of (small) conical limits implies existence of (small) limits -/
example [HasConicalLimits V C] : HasLimits C := inferInstance

end Results

end CategoryTheory.Enriched
