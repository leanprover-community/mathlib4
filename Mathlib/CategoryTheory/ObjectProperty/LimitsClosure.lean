/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Closure of a property of objects under limits of certain shapes

In this file, given a property `P` of objects in a category `C` and
family of categories `J : α → Type _`, we introduce the closure
`P.limitsClosure J` of `P` under limits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that its essentially small.

-/
universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α → Type u') [∀ a, Category.{v'} (J a)]

/-- The closure of property of objects of a category under limits of
shape `J a` for a family of categories `J`. -/
inductive limitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : limitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : limitsClosure X) : limitsClosure Y
  | of_limitPresentation {X : C} {a : α} (pres : LimitPresentation (J a) X)
      (h : ∀ j, limitsClosure (pres.diag.obj j)) : limitsClosure X

@[simp]
lemma le_limitsClosure : P ≤ P.limitsClosure J :=
  fun X hX ↦ .of_mem X hX

instance : (P.limitsClosure J).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX

instance (a : α) : (P.limitsClosure J).IsClosedUnderLimitsOfShape (J a) where
  limitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_limitPresentation hX.toLimitPresentation hX.prop_diag_obj

variable {P J} in
lemma limitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [∀ (a : α), Q.IsClosedUnderLimitsOfShape (J a)] (h : P ≤ Q) :
    P.limitsClosure J ≤ Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_limitPresentation pres h h' => exact Q.prop_of_isLimit pres.isLimit h'

variable {P} in
lemma limitsClosure_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.limitsClosure J ≤ Q.limitsClosure J :=
  limitsClosure_le (h.trans (Q.le_limitsClosure J))

lemma limitsClosure_isoClosure :
    P.isoClosure.limitsClosure J = P.limitsClosure J := by
  refine le_antisymm (limitsClosure_le ?_)
    (limitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_limitsClosure P J

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

section

variable {β : Type w'} [LinearOrder β] [OrderBot β] [SuccOrder β] [WellFoundedLT β]

/-- Given `P : ObjectProperty C`, a family of categories `J a`, this
is the transfinite iteration of `Q ↦ Q.strictLimitsClosureStep J`. -/
abbrev strictLimitsClosureIter (b : β) : ObjectProperty C :=
  transfiniteIterate (φ := fun Q ↦ Q.strictLimitsClosureStep J) b P

lemma le_strictLimitsClosureIter (b : β) :
    P ≤ P.strictLimitsClosureIter J b :=
  le_of_eq_of_le (transfiniteIterate_bot _ _).symm
    (monotone_transfiniteIterate _ _ (fun _ ↦ le_strictLimitsClosureStep _ _) bot_le)

lemma strictLimitsClosureIter_le_limitsClosure (b : β) :
    P.strictLimitsClosureIter J b ≤ P.limitsClosure J := by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp
  | succ b hb hb' =>
    rw [strictLimitsClosureIter, transfiniteIterate_succ _ _ _ hb,
      strictLimitsClosureStep, sup_le_iff, iSup_le_iff]
    exact ⟨hb', fun a ↦ ((strictLimitsOfShape_le_limitsOfShape _ _).trans
      (limitsOfShape_monotone _ hb')).trans (limitsOfShape_le _ _)⟩
  | isSuccLimit b hb hb' =>
    simp only [transfiniteIterate_limit _ _ _ hb,
      iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro c hc
    exact hb' _ hc

instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] (b : β)
    [hb₀ : Small.{w} (Set.Iio b)] :
    ObjectProperty.Small.{w} (P.strictLimitsClosureIter J b) := by
  have H {b c : β} (hbc : b ≤ c) [Small.{w} (Set.Iio c)] : Small.{w} (Set.Iio b) :=
    small_of_injective (f := fun x ↦ (⟨x.1, lt_of_lt_of_le x.2 hbc⟩ : Set.Iio c))
      (fun _ _ _ ↦ by aesop)
  induction b using SuccOrder.limitRecOn generalizing hb₀ with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp only [transfiniteIterate_bot]
    infer_instance
  | succ b hb hb' =>
    have := H (Order.le_succ b)
    rw [strictLimitsClosureIter, transfiniteIterate_succ _ _ _ hb,
      strictLimitsClosureStep]
    infer_instance
  | isSuccLimit b hb hb' =>
    simp only [transfiniteIterate_limit _ _ _ hb]
    have (c : Set.Iio b) : ObjectProperty.Small.{w}
      (transfiniteIterate (fun Q ↦ Q.strictLimitsClosureStep J) c.1 P) := by
      have := H c.2.le
      exact hb' c.1 c.2
    infer_instance

end

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] (h : ∀ (a : α), HasCardinalLT (J a) κ)

include h

lemma strictLimitsClosureStep_strictLimitsClosureIter_eq_self :
    (P.strictLimitsClosureIter J κ.ord).strictLimitsClosureStep J =
      (P.strictLimitsClosureIter J κ.ord) := by
  have hκ : κ.IsRegular := Fact.out
  have (a : α) := (h a).small
  refine le_antisymm (fun X hX ↦ ?_) (le_strictLimitsClosureStep _ _)
  simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff] at hX
  obtain (hX | ⟨a, F, hF⟩) := hX
  · exact hX
  · simp only [strictLimitsClosureIter, transfiniteIterate_limit _ _ _
      (Cardinal.isSuccLimit_ord hκ.aleph0_le), prop_iSup_iff,
      Subtype.exists, Set.mem_Iio, exists_prop] at hF
    choose o ho ho' using hF
    obtain ⟨m, hm, hm'⟩ : ∃ (m : Ordinal.{w}) (hm : m < κ.ord), ∀ (j : J a), o j ≤ m := by
      refine ⟨⨆ j, o ((equivShrink.{w} (J a)).symm j),
          Ordinal.iSup_lt_ord ?_ (fun _ ↦ ho _), fun j ↦ ?_⟩
      · rw [hκ.cof_eq, ← hasCardinalLT_iff_cardinal_mk_lt _ κ,
          ← hasCardinalLT_iff_of_equiv (equivShrink.{w} (J a))]
        exact h a
      · obtain ⟨j, rfl⟩ := (equivShrink.{w} (J a)).symm.surjective j
        exact le_ciSup (Ordinal.bddAbove_range _) _
    refine monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) ↦ Q.le_strictLimitsClosureStep J) (Order.succ_le_iff.2 hm) _ ?_
    dsimp
    rw [transfiniteIterate_succ _ _ _ (by simp)]
    simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff]
    exact Or.inr ⟨a, ⟨_, fun j ↦ monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) ↦ Q.le_strictLimitsClosureStep J)  (hm' j) _ (ho' j)⟩⟩

lemma isoClosure_strictLimitsClosureIter_eq_limitsClosure :
    (P.strictLimitsClosureIter J κ.ord).isoClosure = P.limitsClosure J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictLimitsClosureIter_le_limitsClosure J κ.ord
  · have (a : α) :
        (P.strictLimitsClosureIter J κ.ord).isoClosure.IsClosedUnderLimitsOfShape (J a) := ⟨by
      conv_rhs => rw [← P.strictLimitsClosureStep_strictLimitsClosureIter_eq_self J κ h]
      rw [limitsOfShape_isoClosure, ← isoClosure_strictLimitsOfShape,
        strictLimitsClosureStep]
      exact monotone_isoClosure ((le_trans (by rfl) (le_iSup _ a)).trans le_sup_right)⟩
    refine limitsClosure_le
      ((P.le_strictLimitsClosureIter J κ.ord).trans (le_isoClosure _))

lemma isEssentiallySmall_limitsClosure
    [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsClosure J) := by
  obtain ⟨Q, hQ, hQ₁, hQ₂⟩ := EssentiallySmall.exists_small_le.{w} P
  have : ObjectProperty.EssentiallySmall.{w} (Q.isoClosure.limitsClosure J) := by
    rw [limitsClosure_isoClosure,
      ← Q.isoClosure_strictLimitsClosureIter_eq_limitsClosure J κ h]
    infer_instance
  exact .of_le (limitsClosure_monotone J hQ₂)

end

instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [∀ a, Small.{w} (J a)] [∀ a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsClosure J) := by
  obtain ⟨κ, h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall J
  have : Fact κ.IsRegular := ⟨h₁⟩
  exact isEssentiallySmall_limitsClosure P J κ h₂

end CategoryTheory.ObjectProperty
