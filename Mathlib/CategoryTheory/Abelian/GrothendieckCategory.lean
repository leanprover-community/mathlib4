/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Grothendieck categories

This file defines Grothendieck categories and proves basic facts about them.

## Definitions

A `GrothendieckCategory` is an abelian category provided that it has `AB5` and a separator.

## Theorems

Relevant implications of `GrothendieckCategory` are established in `GrothendieckCategory.hasLimits`
and `GrothendieckCategory.hasColimits`.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits

universe w v u w₂ v₂ u₂
variable (C : Type u) [Category.{v} C] (D : Type u₂) [Category.{v₂} D]

/--
In the literature, an abelian category `C` is called a Grothendieck category provided that it has
`AB5` and a separator (see `HasSeparator`).

`IsGrothendieckAbelian C` is defined such that it holds if and only if `C` is equivalent to a
Grothendieck category -- more concretely, if and only if `ShrinkHoms.{w} C` is a Grothendieck
category.
-/
@[stacks 079B]
class IsGrothendieckAbelian : Prop where
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{w, w} C := by infer_instance
  ab5OfSize : AB5OfSize.{w, w} C := by infer_instance
  hasSeparator : HasSeparator C := by infer_instance

attribute [instance] IsGrothendieckAbelian.locallySmall
  IsGrothendieckAbelian.hasFilteredColimitsOfSize IsGrothendieckAbelian.ab5OfSize
  IsGrothendieckAbelian.hasSeparator

variable {C} {D} in
theorem IsGrothendieckAbelian.of_equivalence
    [IsGrothendieckAbelian.{w} C] (α : C ≌ D) : IsGrothendieckAbelian.{w} D := by
  have hasFilteredColimits : HasFilteredColimitsOfSize.{w, w, v₂, u₂} D :=
    ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence α.inverse⟩
  refine ⟨?_, hasFilteredColimits, ?_, ?_⟩
  · exact locallySmall_of_faithful α.inverse
  · refine ⟨fun _ _ _ => ?_⟩
    exact hasExactColimitsOfShape_obj_of_equiv _ α
  · exact HasSeparator.of_equivalence α

instance IsGrothendieckAbelian.shrinkHoms [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w, w} (ShrinkHoms C) :=
  IsGrothendieckAbelian.of_equivalence <| ShrinkHoms.equivalence C

section Instances

variable [Abelian C] [IsGrothendieckAbelian C]

instance IsGrothendieckAbelian.hasColimits : HasColimits C := has_colimits_of_finite_and_filtered
instance IsGrothendieckAbelian.hasLimits : HasLimits C := hasLimits_of_hasColimits_of_hasSeparator

end Instances

end CategoryTheory
