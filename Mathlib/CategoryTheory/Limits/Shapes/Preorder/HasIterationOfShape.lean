/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.Order.SuccPred.Limit

/-!
# An assumption for constructions by transfinite induction

In this file, we introduce the typeclass `HasIterationOfShape J C` which is
an assumption in order to do constructions by transfinite induction indexed by
a well-ordered type `J` in a category `C` (see `CategoryTheory.SmallObject`).

-/

universe w v v' u u'

namespace CategoryTheory.Limits

variable (J : Type w) [Preorder J] (C : Type u) [Category.{v} C]
  (K : Type u') [Category.{v'} K]

/-- A category `C` has iterations of shape a preordered type `J`
when certain specific shapes of colimits exists: colimits indexed by `J`,
and by `Set.Iio j` for `j : J`.  -/
class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

attribute [instance] HasIterationOfShape.hasColimitsOfShape

variable [HasIterationOfShape J C]

variable {J} in
lemma hasColimitsOfShape_of_isSuccLimit (j : J)
    (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C :=
  HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

instance : HasIterationOfShape J (Arrow C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance : HasIterationOfShape J (K ⥤ C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

end CategoryTheory.Limits
