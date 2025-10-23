/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Closure of a property of objects under colimits of certain shapes

In this file, given a property `P` of objects in a category `C` and
family of categories `J : α → Type _`, we introduce the closure
`P.colimitsClosure J` of `P` under colimits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that its essentially small.

(We deduce these results about the closure under colimits by dualising the
results in the file `ObjectProperty.LimitsClosure`.)

-/

universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

/-- The closure of a property of objects of a category under colimits of
shape `J a` for a family of categories `J`. -/
inductive colimitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : colimitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : colimitsClosure X) : colimitsClosure Y
  | of_colimitPresentation {X : C} {a : α} (pres : ColimitPresentation (J a) X)
      (h : ∀ j, colimitsClosure (pres.diag.obj j)) : colimitsClosure X

@[simp]
lemma le_colimitsClosure : P ≤ P.colimitsClosure J :=
  fun X hX ↦ .of_mem X hX

instance : (P.colimitsClosure J).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX

instance (a : α) : (P.colimitsClosure J).IsClosedUnderColimitsOfShape (J a) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_colimitPresentation hX.toColimitPresentation hX.prop_diag_obj

variable {P J} in
lemma colimitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [∀ (a : α), Q.IsClosedUnderColimitsOfShape (J a)] (h : P ≤ Q) :
    P.colimitsClosure J ≤ Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_colimitPresentation pres h h' => exact Q.prop_of_isColimit pres.isColimit h'

variable {P} in
lemma colimitsClosure_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.colimitsClosure J ≤ Q.colimitsClosure J :=
  colimitsClosure_le (h.trans (Q.le_colimitsClosure J))

lemma colimitsClosure_isoClosure :
    P.isoClosure.colimitsClosure J = P.colimitsClosure J := by
  refine le_antisymm (colimitsClosure_le ?_)
    (colimitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_colimitsClosure P J

lemma colimitsClosure_eq_unop_limitsClosure :
    P.colimitsClosure J = (P.op.limitsClosure (fun a ↦ (J a)ᵒᵖ)).unop := by
  refine le_antisymm ?_ ?_
  · apply colimitsClosure_le
    rw [← op_monotone_iff, op_unop]
    apply le_limitsClosure
  · rw [← op_monotone_iff, op_unop]
    apply limitsClosure_le
    rw [op_monotone_iff]
    apply le_colimitsClosure

instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.colimitsClosure J) := by
  rw [colimitsClosure_eq_unop_limitsClosure]
  have (a : α) : Small.{w} (J a)ᵒᵖ := Opposite.small
  infer_instance

end CategoryTheory.ObjectProperty
