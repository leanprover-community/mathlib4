/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Transfer
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

noncomputable instance ShrinkHoms.homGroups [Preadditive C] (P Q : ShrinkHoms C) : AddCommGroup (P ⟶ Q) where
  add f g := (equivShrink _ |>.symm) f + (equivShrink _ |>.symm) g |> equivShrink _
  zero := 0 |> equivShrink _
  nsmul n f := magnify f |> AddMonoid.nsmul n |> shrink
  zsmul z f := magnify f |> SubNegMonoid.zsmul z |> shrink
  neg f := - magnify f |> shrink
  zero_add f := by
    unfold HAdd.hAdd instHAdd OfNat.ofNat Zero.toOfNat0 Zero.zero HasZeroMorphisms.zero
      Preadditive.preadditiveHasZeroMorphisms inferInstance NegZeroClass.toZero
      SubNegZeroMonoid.toNegZeroClass AddMonoid.toZero SubNegMonoid.toAddMonoid
      SubNegZeroMonoid.toSubNegMonoid SubtractionMonoid.toSubNegZeroMonoid
      SubtractionMonoid.toSubNegMonoid SubtractionCommMonoid.toSubtractionMonoid
      AddCommGroup.toDivisionAddCommMonoid AddGroup.toSubNegMonoid AddCommGroup.toAddGroup
      Preadditive.homGroup
    dsimp
    simp only [Equiv.symm_apply_apply]
    conv =>
      lhs
      apply congrArg
      simp_rw [zero_add (equivShrink _ |>.symm f)]
    erw [zero_add (equivShrink _ |>.symm f)]
  add_zero := sorry
  neg_add_cancel := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul_zero' := sorry
  zsmul_neg' := sorry
  zsmul_succ' := sorry
  add_comm f g := congrArg _ <| add_comm _ _
  add_assoc f g h := by
    unfold HAdd.hAdd instHAdd
    simp only [Equiv.symm_apply_apply]
    exact congrArg _ <| add_assoc _ _ _
where
  shrink := equivShrink _
  magnify := equivShrink _ |>.symm

instance ShrinkHoms.preadditive [Preadditive C] : Preadditive (ShrinkHoms C) where
  homGroup P Q := by
    addCommGroup

instance ShrinkHoms.abelian [Abelian C] : Abelian (ShrinkHoms C) :=
  abelianOfEquivalence (ShrinkHoms.equivalence C |>.inverse)


section Instances

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

-- instance IsGrothendieckAbelian.hasColimits : HasColimits C := has_colimits_of_finite_and_filtered
-- instance IsGrothendieckAbelian.hasLimits : HasLimits C := hasLimits_of_hasColimits_of_hasSeparator

instance IsGrothendieckAbelian.hasColimitsOfSize' : HasColimitsOfSize.{w, w} C :=
  has_colimits_of_finite_and_filtered

instance IsGrothendieckAbelian.hasLimitsOfSize' : HasLimitsOfSize.{w, w} C := by
  --have : Abelian (ShrinkHoms C) := sorry
  have : HasColimits.{w, u} (ShrinkHoms C) := IsGrothendieckAbelian.hasColimitsOfSize' _
  have : HasLimits.{w, u} (ShrinkHoms C) := hasLimits_of_hasColimits_of_hasSeparator

  done

-- instance IsGrothendieckAbelian.hasColimitsOfSize : HasColimitsOfSize.{w, w} (ShrinkHoms C) := by
--   have : HasColimitsOfSize.{w, w} C := has_colimits_of_finite_and_filtered
--   exact Adjunction.has_colimits_of_equivalence (ShrinkHoms.equivalence C |>.inverse)

instance IsGrothendieckAbelian.hasLimitsOfSize : HasLimitsOfSize.{w, w} (ShrinkHoms C) := by
  -- hasLimits_of_hasColimits_of_hasSeparator
  have : HasLimitsOfSize.{w, w} C := hasLimits_of_hasColimits_of_hasSeparator
  apply Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence C |>.inverse)

end Instances

end CategoryTheory
