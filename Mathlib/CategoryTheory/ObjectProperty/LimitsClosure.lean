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
def strictLimitsClosureStep : ObjectProperty C :=
  P ⊔ (⨆ (a : α), P.strictLimitsOfShape (J a))

@[simp]
lemma le_strictLimitsClosureStep : P ≤ P.strictLimitsClosureStep J := le_sup_left

variable {P} in
lemma strictLimitsClosureStep_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictLimitsClosureStep J ≤ Q.strictLimitsClosureStep J := by
  dsimp [strictLimitsClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨h.trans le_sup_left, fun a ↦ (strictLimitsOfShape_monotone (J a) h).trans
    (le_trans (by rfl) ((le_iSup _ a).trans le_sup_right))⟩

/-- Given `P : ObjectProperty C` and a family of categories `J : α → Type _`,
this property objects contains `P.isoClosure` and all objects that are isomorphic to `lim F`
for some functor `F : J a ⥤ C` such that `F.obj j` satisfies `P` for any `j`. -/
def limitsClosureStep : ObjectProperty C :=
  P.isoClosure ⊔ (⨆ (a : α), P.limitsOfShape (J a))

@[simp]
lemma isoClosure_le_limitsClosureStep : P.isoClosure ≤ P.limitsClosureStep J := le_sup_left

@[simp]
lemma le_limitsClosureStep : P ≤ P.limitsClosureStep J :=
  (le_isoClosure P).trans (P.isoClosure_le_limitsClosureStep J)

variable {P} in
lemma limitsClosureStep_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.limitsClosureStep J ≤ Q.limitsClosureStep J := by
  dsimp [limitsClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨(monotone_isoClosure h).trans le_sup_left, fun a ↦ (limitsOfShape_monotone (J a) h).trans
    (le_trans (by rfl) ((le_iSup _ a).trans le_sup_right))⟩

instance : (P.limitsClosureStep J).IsClosedUnderIsomorphisms := by
  dsimp [limitsClosureStep]
  infer_instance

@[simp]
lemma isoClosure_strictLimitsClosureStep :
    (P.strictLimitsClosureStep J).isoClosure = P.limitsClosureStep J := by
  simp [limitsClosureStep, strictLimitsClosureStep, isoClosure_sup, isoClosure_iSup]

@[simp]
lemma limitsClosureStep_isoClosure :
    P.isoClosure.limitsClosureStep J = P.limitsClosureStep J := by
  refine le_antisymm ?_ (limitsClosureStep_monotone _ (P.le_isoClosure))
  simp [limitsClosureStep, isoClosure_eq_self]

section

variable {β : Type w} [LinearOrder β] [OrderBot β] [SuccOrder β] [WellFoundedLT β]

/-- Given `P : ObjectProperty C`, a family of categories `J a`, this
is the transfinite iteration of `Q ↦ Q.strictLimitsClosureStep J`. -/
abbrev strictLimitsClosureIter (b : β) : ObjectProperty C :=
  transfiniteIterate (φ := fun Q ↦ Q.strictLimitsClosureStep J) b P

/-- Given `P : ObjectProperty C`, a family of categories `J a`, this
is the transfinite iteration of `Q ↦ Q.limitsClosureStep J`. -/
abbrev limitsClosureIter (b : β) : ObjectProperty C :=
  transfiniteIterate (φ := fun Q ↦ Q.limitsClosureStep J) b P.isoClosure

@[simp]
lemma isoClosure_strictLimitsClosureIter (b : β) :
    (P.strictLimitsClosureIter J b).isoClosure = P.limitsClosureIter J b := by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp
  | succ b hb hb' =>
    dsimp [strictLimitsClosureIter, limitsClosureIter] at hb' ⊢
    rw [transfiniteIterate_succ _ _ _ hb, transfiniteIterate_succ _ _ _ hb, ← hb',
      isoClosure_strictLimitsClosureStep, limitsClosureStep_isoClosure]
  | isSuccLimit b hb hb' =>
    dsimp [strictLimitsClosureIter, limitsClosureIter] at hb' ⊢
    rw [transfiniteIterate_limit _ _ _ hb, transfiniteIterate_limit _ _ _ hb, isoClosure_iSup]
    congr
    ext ⟨c, hc⟩ : 1
    exact hb' c hc

instance (b : β) : (P.limitsClosureIter J b).IsClosedUnderIsomorphisms := by
  rw [← isoClosure_strictLimitsClosureIter]
  infer_instance

end

section

variable (κ : Cardinal.{u'}) [Fact κ.IsRegular] (h : ∀ (a : α), HasCardinalLT (J a) κ)

include h

lemma strictLimitsClosureStep_strictLimitsClosureIter_eq_self :
    (P.strictLimitsClosureIter J κ.ord).strictLimitsClosureStep J =
      (P.strictLimitsClosureIter J κ.ord) := by
  have hκ : κ.IsRegular := Fact.out
  refine le_antisymm (fun X hX ↦ ?_) (le_strictLimitsClosureStep _ _)
  simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff] at hX
  obtain (hX | ⟨a, F, hF⟩) := hX
  · exact hX
  · simp only [strictLimitsClosureIter, transfiniteIterate_limit _ _ _
      (Cardinal.isSuccLimit_ord hκ.aleph0_le), prop_iSup_iff,
      Subtype.exists, Set.mem_Iio, exists_prop] at hF
    choose o ho ho' using hF
    obtain ⟨m, hm, hm'⟩ : ∃ (m : Ordinal.{u'}) (hm : m < κ.ord), ∀ (j : J a), o j ≤ m :=
      ⟨⨆ j, o j, Ordinal.iSup_lt_ord
        (lt_of_lt_of_eq ((hasCardinalLT_iff_cardinal_mk_lt _ _).1 (h a)) hκ.cof_eq.symm) ho,
        le_ciSup (Ordinal.bddAbove_range _)⟩
    refine monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) ↦ Q.le_strictLimitsClosureStep J) (Order.succ_le_iff.2 hm) _ ?_
    dsimp
    rw [transfiniteIterate_succ _ _ _ (by simp)]
    simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff]
    exact Or.inr ⟨a, ⟨_, fun j ↦ monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) ↦ Q.le_strictLimitsClosureStep J)  (hm' j) _ (ho' j)⟩⟩

lemma limitsClosureStep_limitsClosureIter_eq_self :
    (P.limitsClosureIter J κ.ord).limitsClosureStep J =
      (P.limitsClosureIter J κ.ord) := by
  refine le_antisymm ?_ (le_limitsClosureStep _ _)
  conv_rhs => rw [← isoClosure_strictLimitsClosureIter,
    ← P.strictLimitsClosureStep_strictLimitsClosureIter_eq_self J κ h]
  rw [isoClosure_strictLimitsClosureStep, ← isoClosure_strictLimitsClosureIter,
    limitsClosureStep_isoClosure]

end

end CategoryTheory.ObjectProperty
