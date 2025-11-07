/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.Interval.Set.InitialSeg

/-!
# An assumption for constructions by transfinite induction

In this file, we introduce the typeclass `HasIterationOfShape J C` which is
an assumption in order to do constructions by transfinite induction indexed by
a well-ordered type `J` in a category `C` (see `CategoryTheory.SmallObject`).

-/

universe w v v' u u'

namespace CategoryTheory.Limits

variable (J : Type w) [LinearOrder J] (C : Type u) [Category.{v} C]
  (K : Type u') [Category.{v'} K]

/-- A category `C` has iterations of shape a linearly ordered type `J`
when certain specific shapes of colimits exists: colimits indexed by `J`,
and by `Set.Iio j` for `j : J`. -/
class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

attribute [instance] HasIterationOfShape.hasColimitsOfShape

instance [HasColimitsOfSize.{w, w} C] : HasIterationOfShape J C where

variable [HasIterationOfShape J C]

variable {J} in
lemma hasColimitsOfShape_of_isSuccLimit (j : J)
    (hj : Order.IsSuccLimit j) :
    HasColimitsOfShape (Set.Iio j) C :=
  HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj

variable {J} in
lemma hasColimitsOfShape_of_isSuccLimit'
    {α : Type*} [PartialOrder α] (h : α <i J) (hα : Order.IsSuccLimit h.top) :
    HasColimitsOfShape α C := by
  have := hasColimitsOfShape_of_isSuccLimit C h.top hα
  exact hasColimitsOfShape_of_equivalence h.orderIsoIio.equivalence.symm

instance : HasIterationOfShape J (Arrow C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance : HasIterationOfShape J (K ⥤ C) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

variable {J} [SuccOrder J] [WellFoundedLT J]

lemma hasColimitsOfShape_of_initialSeg
    {α : Type*} [PartialOrder α] (f : α ≤i J) [Nonempty α] :
    HasColimitsOfShape α C := by
  by_cases hf : Function.Surjective f
  · exact hasColimitsOfShape_of_equivalence
      (OrderIso.ofRelIsoLT (RelIso.ofSurjective f.toRelEmbedding hf)).equivalence.symm
  · let s := f.toPrincipalSeg hf
    obtain ⟨i, hi₀⟩ : ∃ i, i = s.top := ⟨_, rfl⟩
    induction i using SuccOrder.limitRecOn with
    | isMin i hi =>
      subst hi₀
      exact (hi.not_lt (s.lt_top (Classical.arbitrary _))).elim
    | succ i hi _ =>
      obtain ⟨a, rfl⟩ := (s.mem_range_iff_rel (b := i)).2 (by
        simpa only [← hi₀] using Order.lt_succ_of_not_isMax hi)
      have : OrderTop α :=
        { top := a
          le_top b := by
            rw [← s.le_iff_le]
            exact Order.le_of_lt_succ (by simpa only [hi₀] using s.lt_top b) }
      infer_instance
    | isSuccLimit i hi =>
      subst hi₀
      exact hasColimitsOfShape_of_isSuccLimit' C s hi

lemma hasIterationOfShape_of_initialSeg {α : Type*} [LinearOrder α]
    (h : α ≤i J) [Nonempty α] :
    HasIterationOfShape α C where
  hasColimitsOfShape := hasColimitsOfShape_of_initialSeg C h
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    exact hasColimitsOfShape_of_initialSeg  _
      (InitialSeg.trans (Set.principalSegIio j) h)

instance (j : J) : HasIterationOfShape (Set.Iic j) C :=
  hasIterationOfShape_of_initialSeg C (Set.initialSegIic j)

end CategoryTheory.Limits
