/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Final

/-!
# Finally small categories

A category given by `(J : Type u) [Category.{v} J]` is `w`-finally small if there exists a
`FinalModel J : Type w` equipped with `[SmallCategory (FinalModel J)]` and a final functor
`FinalModel J ⥤ J`.

This means that if a category `C` has colimits of size `w` and `J` is `w`-finally small, then
`C` has colimits of shape `J`. In this way, the notion of "finally small" can be seen of a
generalization of the notion of "essentially small" for indexing categories of colimits.

Dually, we have a notion of initially small category.
-/

universe w v v₁ u u₁

open CategoryTheory Functor

namespace CategoryTheory

section FinallySmall

variable (J : Type u) [Category.{v} J]

/-- A category is `FinallySmall.{w}` if there is a final functor from a `w`-small category. -/
class FinallySmall : Prop where
  /-- There is a final functor from a small category. -/
  final_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Final F

/-- Constructor for `FinallySmall C` from an explicit small category witness. -/
theorem FinallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Final F] : FinallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

/-- An arbitrarily chosen small model for a finally small category. -/
def FinalModel [FinallySmall.{w} J] : Type w :=
  Classical.choose (@FinallySmall.final_smallCategory J _ _)

noncomputable instance smallCategoryFinalModel [FinallySmall.{w} J] :
    SmallCategory (FinalModel J) :=
  Classical.choose (Classical.choose_spec (@FinallySmall.final_smallCategory J _ _))

/-- An arbitrarily chosen final functor `FinalModel J ⥤ J`. -/
noncomputable def fromFinalModel [FinallySmall.{w} J] : FinalModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

instance final_fromFinalModel [FinallySmall.{w} J] : Final (fromFinalModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

theorem finallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : FinallySmall.{w} J :=
  FinallySmall.mk' (equivSmallModel.{w} J).inverse

end FinallySmall

section InitiallySmall

variable (J : Type u) [Category.{v} J]

/-- A category is `InitiallySmall.{w}` if there is an initial functor from a `w`-small category. -/
class InitiallySmall : Prop where
  /-- There is an initial functor from a small category. -/
  initial_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Initial F

/-- Constructor for `InitialSmall C` from an explicit small category witness. -/
theorem InitiallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

/-- An arbitrarily chosen small model for an initially small category. -/
def InitialModel [InitiallySmall.{w} J] : Type w :=
  Classical.choose (@InitiallySmall.initial_smallCategory J _ _)

noncomputable instance smallCategoryInitialModel [InitiallySmall.{w} J] :
    SmallCategory (InitialModel J) :=
  Classical.choose (Classical.choose_spec (@InitiallySmall.initial_smallCategory J _ _))

/-- An arbitrarily chosen initial functor `InitialModel J ⥤ J`. -/
noncomputable def fromInitialModel [InitiallySmall.{w} J] : InitialModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

instance initial_fromInitialModel [InitiallySmall.{w} J] : Initial (fromInitialModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

theorem initiallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : InitiallySmall.{w} J :=
  InitiallySmall.mk' (equivSmallModel.{w} J).inverse

end InitiallySmall

namespace Limits

theorem hasColimitsOfShape_of_finallySmall (J : Type u) [Category.{v} J] [FinallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasColimitsOfSize.{w, w} C] : HasColimitsOfShape J C :=
  Final.hasColimitsOfShape_of_final (fromFinalModel J)

theorem hasLimitsOfShape_of_initiallySmall (J : Type u) [Category.{v} J] [InitiallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasLimitsOfSize.{w, w} C] : HasLimitsOfShape J C :=
  Initial.hasLimitsOfShape_of_initial (fromInitialModel J)

end Limits

end CategoryTheory
