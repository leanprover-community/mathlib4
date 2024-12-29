/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.Order.SuccPred.Limit

/-!
# Limits and colimits indexed by preorders

In this file, we consider limits and colimits indexed by a preordered type `J`:
* a least element in `J` implies the existence of all limits indexed by `J`
* a greatest element in `J` implies the existence of all colimits indexed by `J`

We also introduce the typeclass `HasIterationOfShape C J` which is a relevant
assumption in order to do constructions by transfinite induction in a
category `C` (see `CategoryTheory.SmallObject`).

-/

universe v v' u u' w

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C] (J : Type w) [Preorder J]
  (K : Type u') [Category.{v'} K]

namespace Preorder

section OrderBot

variable [OrderBot J]

/-- The least element in a preordered type is initial in the category
associated to this preorder. -/
def isInitialBot : IsInitial (⊥ : J) := IsInitial.ofUnique _

instance : HasInitial J := hasInitial_of_unique ⊥

instance : HasLimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

end OrderBot

section OrderTop

variable [OrderTop J]

/-- The greatest element of a preordered type is terminal in the category
associated to this preorder. -/
def isTerminalBot : IsTerminal (⊤ : J) := IsTerminal.ofUnique _

instance : HasTerminal J := hasTerminal_of_unique ⊤

instance : HasColimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

end OrderTop

end Preorder

namespace CategoryTheory.Limits

/-- A category `C` has iterations of shape of a preordered type `J`
when certain specific hapes of colimits exists: colimits indexed by `J`,
and by `Set.Iio j` for `j : J`. -/
class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

attribute [instance] HasIterationOfShape.hasColimitsOfShape

variable [HasIterationOfShape C J]

variable {J} in
lemma hasColimitsOfShape_of_isSuccLimit  (j : J)
    (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C :=
  HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

instance : HasIterationOfShape (Arrow C) J where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance : HasIterationOfShape (K ⥤ C) J where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

end CategoryTheory.Limits
