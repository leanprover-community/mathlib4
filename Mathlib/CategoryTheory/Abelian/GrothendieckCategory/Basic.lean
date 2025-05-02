/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Grothendieck categories

This file defines Grothendieck categories and proves basic facts about them.

## Definitions

A Grothendieck category according to the Stacks project is an abelian category provided that it
has `AB5` and a separator. However, this definition is not invariant under equivalences of
categories. Therefore, if `C` is an abelian category, the class `IsGrothendieckAbelian.{w} C` has a
weaker definition that is also satisfied for categories that are merely equivalent to a
Grothendieck category in the former strict sense.

## Theorems

The invariance under equivalences of categories is established in
`IsGrothendieckAbelian.of_equivalence`.

In particular, `ShrinkHoms.isGrothendieckAbelian C` shows that `ShrinkHoms C` satisfies our
definition of a Grothendieck category after shrinking its hom sets, which coincides with the strict
definition in this case.

Relevant implications of `IsGrothendieckAbelian` are established in
`IsGrothendieckAbelian.hasLimits` and `IsGrothendieckAbelian.hasColimits`.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits

universe w v u w₂ v₂ u₂
variable (C : Type u) [Category.{v} C] (D : Type u₂) [Category.{v₂} D]

/--
If `C` is an abelian category, we shall say that it satisfies `IsGrothendieckAbelian.{w} C`
if it is locally small (relative to `w`), has exact filtered colimits of size `w` (AB5) and has a
separator.
If `[Category.{v} C]` and `w = v`, this means that `C` satisfies `AB5` and has a separator;
general results about Grothendieck abelian categories can be
reduced to this case using the instance `ShrinkHoms.isGrothendieckAbelian` below.

The introduction of the auxiliary universe `w` shall be needed for certain
applications to categories of sheaves. That the present definition still preserves essential
properties of Grothendieck categories is ensured by `IsGrothendieckAbelian.of_equivalence`,
which shows that every instance for `C` implies an instance for `ShrinkHoms C` with hom sets in
`Type w`.
-/
@[stacks 079B, pp_with_univ]
class IsGrothendieckAbelian [Abelian C] : Prop where
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{w, w} C := by infer_instance
  ab5OfSize : AB5OfSize.{w, w} C := by infer_instance
  hasSeparator : HasSeparator C := by infer_instance

attribute [instance] IsGrothendieckAbelian.locallySmall
  IsGrothendieckAbelian.hasFilteredColimitsOfSize IsGrothendieckAbelian.ab5OfSize
  IsGrothendieckAbelian.hasSeparator

variable {C} {D} in
theorem IsGrothendieckAbelian.of_equivalence [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{w} C] (α : C ≌ D) : IsGrothendieckAbelian.{w} D := by
  have hasFilteredColimits : HasFilteredColimitsOfSize.{w, w, v₂, u₂} D :=
    ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence α.inverse⟩
  refine ⟨?_, hasFilteredColimits, ?_, ?_⟩
  · exact locallySmall_of_faithful α.inverse
  · refine ⟨fun _ _ _ => ?_⟩
    exact HasExactColimitsOfShape.of_codomain_equivalence _ α
  · exact HasSeparator.of_equivalence α

instance ShrinkHoms.isGrothendieckAbelian [Abelian C] [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w, w} (ShrinkHoms C) :=
  IsGrothendieckAbelian.of_equivalence <| ShrinkHoms.equivalence C

section Instances

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

instance IsGrothendieckAbelian.hasColimits : HasColimitsOfSize.{w, w} C :=
  has_colimits_of_finite_and_filtered

instance IsGrothendieckAbelian.hasLimits : HasLimitsOfSize.{w, w} C :=
  have : HasLimits.{w, u} (ShrinkHoms C) := hasLimits_of_hasColimits_of_hasSeparator
  Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence C |>.functor)

instance IsGrothendieckAbelian.wellPowered : WellPowered.{w} C :=
  wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C).symm

instance IsGrothendieckAbelian.ab4OfSize : AB4OfSize.{w} C := by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  apply AB4.of_AB5

end Instances

end CategoryTheory
