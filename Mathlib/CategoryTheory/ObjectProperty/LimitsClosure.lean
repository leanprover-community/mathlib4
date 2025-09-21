/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.Order.TransfiniteIteration

/-!
# Closure of a property of objects under limits of certain shapes

-/
universe w t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

/-- Given `P : ObjectProperty C` and a family of categories `J : α → Type _`,
this property objects contains `P` and all objects that are equal to `lim F`
for some functor `F : J a ⥤ C` such that `F.obj j` satisfies `P` for any `j`. -/
def strictLimitClosureStep : ObjectProperty C :=
  P ⊔ (⨆ (a : α), P.strictLimitsOfShape (J a))

@[simp]
lemma le_strictLimitClosureStep : P ≤ P.strictLimitClosureStep J := le_sup_left

variable {P} in
lemma strictLimitClosureStep_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictLimitClosureStep J ≤ Q.strictLimitClosureStep J := by
  dsimp [strictLimitClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨h.trans le_sup_left, fun a ↦ (strictLimitsOfShape_monotone (J a) h).trans
    (le_trans (by rfl) ((le_iSup _ a).trans le_sup_right))⟩

/-- Given `P : ObjectProperty C` and a family of categories `J : α → Type _`,
this property objects contains `P.isoClosure` and all objects that are isomorphic to `lim F`
for some functor `F : J a ⥤ C` such that `F.obj j` satisfies `P` for any `j`. -/
def limitClosureStep : ObjectProperty C :=
  P.isoClosure ⊔ (⨆ (a : α), P.limitsOfShape (J a))

@[simp]
lemma isoClosure_le_limitClosureStep : P.isoClosure ≤ P.limitClosureStep J := le_sup_left

@[simp]
lemma le_limitClosureStep : P ≤ P.limitClosureStep J :=
  (le_isoClosure P).trans (P.isoClosure_le_limitClosureStep J)

variable {P} in
lemma limitClosureStep_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.limitClosureStep J ≤ Q.limitClosureStep J := by
  dsimp [limitClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨(monotone_isoClosure h).trans le_sup_left, fun a ↦ (limitsOfShape_monotone (J a) h).trans
    (le_trans (by rfl) ((le_iSup _ a).trans le_sup_right))⟩

instance : (P.limitClosureStep J).IsClosedUnderIsomorphisms := by
  dsimp [limitClosureStep]
  infer_instance

@[simp]
lemma isoClosure_strictLimitClosureStep :
    (P.strictLimitClosureStep J).isoClosure = P.limitClosureStep J := by
  simp [limitClosureStep, strictLimitClosureStep, isoClosure_sup, isoClosure_iSup]

@[simp]
lemma limitClosureStep_isoClosure :
    P.isoClosure.limitClosureStep J = P.limitClosureStep J := by
  refine le_antisymm ?_ (limitClosureStep_monotone _ (P.le_isoClosure))
  simp [limitClosureStep, isoClosure_eq_self]

section

variable {β : Type w} [LinearOrder β] [OrderBot β] [SuccOrder β] [WellFoundedLT β]

/-- Given `P : ObjectProperty C`, a family of categories `J a`, this
is the transfinite iteration of `Q ↦ Q.strictLimitClosureStep J`. -/
abbrev strictLimitClosureIter (b : β) : ObjectProperty C :=
  transfiniteIterate (φ := fun Q ↦ Q.strictLimitClosureStep J) b P

/-- Given `P : ObjectProperty C`, a family of categories `J a`, this
is the transfinite iteration of `Q ↦ Q.limitClosureStep J`. -/
abbrev limitClosureIter (b : β) : ObjectProperty C :=
  transfiniteIterate (φ := fun Q ↦ Q.limitClosureStep J) b P.isoClosure

@[simp]
lemma isoClosure_strictLimitClosureIter (b : β) :
    (P.strictLimitClosureIter J b).isoClosure = P.limitClosureIter J b := by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp
  | succ b hb hb' =>
    dsimp [strictLimitClosureIter, limitClosureIter] at hb' ⊢
    rw [transfiniteIterate_succ _ _ _ hb, transfiniteIterate_succ _ _ _ hb, ← hb',
      isoClosure_strictLimitClosureStep, limitClosureStep_isoClosure]
  | isSuccLimit b hb hb' =>
    dsimp [strictLimitClosureIter, limitClosureIter] at hb' ⊢
    rw [transfiniteIterate_limit _ _ _ hb, transfiniteIterate_limit _ _ _ hb, isoClosure_iSup]
    congr
    ext ⟨c, hc⟩ : 1
    exact hb' c hc

instance (b : β) : (P.limitClosureIter J b).IsClosedUnderIsomorphisms := by
  rw [← isoClosure_strictLimitClosureIter]
  infer_instance

end

end CategoryTheory.ObjectProperty
