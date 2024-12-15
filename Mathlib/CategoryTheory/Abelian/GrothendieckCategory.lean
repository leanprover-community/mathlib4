/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Logic.Equiv.TransferInstance

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
    exact HasExactColimitsOfShape.of_codomain_equivalence _ α
  · exact HasSeparator.of_equivalence α

section ShrinkHoms

instance ShrinkHoms.is_grothendieck_abelian [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w, w} (ShrinkHoms C) :=
  IsGrothendieckAbelian.of_equivalence <| ShrinkHoms.equivalence C

noncomputable instance ShrinkHoms.preadditive [LocallySmall.{w} C] [Preadditive C] :
    Preadditive.{w} (ShrinkHoms C) where
  homGroup P Q := Equiv.addCommGroup (equivShrink _).symm
  add_comp _ _ _ _ _ _ := by
    apply congr_arg (equivShrink _)
    conv => congr <;> congr <;> try apply Equiv.symm_apply_apply
    apply Preadditive.add_comp
  comp_add _ _ _ _ _ _ := by
    apply congr_arg (equivShrink _)
    conv => congr <;> congr <;> try apply Equiv.symm_apply_apply
    apply Preadditive.comp_add

-- Alternative? Not sure which is cleaner
-- noncomputable instance ShrinkHoms.preadditive [Preadditive C] : Preadditive (ShrinkHoms C) := by
--   refine ⟨fun _ _ => Equiv.addCommGroup (equivShrink _).symm, ?_, ?_⟩
--   all_goals
--     intros
--     apply congr_arg (equivShrink _)
--     conv => congr <;> congr <;> try apply (equivShrink _).symm_apply_apply
--     first | apply Preadditive.add_comp | apply Preadditive.comp_add

instance ShrinkHoms.has_limits [LocallySmall.{w} C] {J : Type*} [Category J]
    [HasLimitsOfShape J C] : HasLimitsOfShape.{_, _, w} J (ShrinkHoms C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (ShrinkHoms.equivalence C).inverse

instance ShrinkHoms.has_finite_limits [LocallySmall.{w} C] [HasFiniteLimits C] :
    HasFiniteLimits.{w} (ShrinkHoms C) :=
  ⟨fun _ => inferInstance⟩

universe w2 in
noncomputable instance ShrinkHoms.abelian [Abelian C] [LocallySmall.{w} C] :
    Abelian.{w} (ShrinkHoms C) :=
  abelianOfEquivalence (ShrinkHoms.equivalence C |>.inverse)

end ShrinkHoms

section Instances

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

instance IsGrothendieckAbelian.has_colimits : HasColimitsOfSize.{w, w} C :=
  has_colimits_of_finite_and_filtered

instance IsGrothendieckAbelian.has_limits : HasLimitsOfSize.{w, w} C :=
  have : HasLimits.{w, u} (ShrinkHoms C) := hasLimits_of_hasColimits_of_hasSeparator
  Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence C |>.functor)

end Instances

end CategoryTheory
