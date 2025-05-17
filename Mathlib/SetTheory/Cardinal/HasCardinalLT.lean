/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.SetTheory.Cardinal.Regular

/-!
# The property of being of cardinality less than a cardinal

Given `X : Type u` and `κ : Cardinal.{v}`, we introduce a predicate
`HasCardinalLT X κ` expressing that
`Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ`.

-/

universe w v u u'

/-- The property that the cardinal of a type `X : Type u` is less than `κ : Cardinal.{v}`. -/
def HasCardinalLT (X : Type u) (κ : Cardinal.{v}) : Prop :=
  Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ

lemma hasCardinalLT_iff_cardinal_mk_lt (X : Type u) (κ : Cardinal.{u}) :
    HasCardinalLT X κ ↔ Cardinal.mk X < κ := by
  simp [HasCardinalLT]

namespace HasCardinalLT

section

variable {X : Type u} {κ : Cardinal.{v}} (h : HasCardinalLT X κ)

include h

lemma small : Small.{v} X := by
  dsimp [HasCardinalLT] at h
  rw [← Cardinal.lift_lt.{_, v + 1}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  simpa only [Cardinal.small_iff_lift_mk_lt_univ] using h.trans (Cardinal.lift_lt_univ' κ)

lemma of_le {κ' : Cardinal.{v}} (hκ' : κ ≤ κ') :
    HasCardinalLT X κ' :=
  lt_of_lt_of_le h (by simpa only [Cardinal.lift_le] using hκ')

variable {Y : Type u'}

lemma of_injective (f : Y → X) (hf : Function.Injective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (Function.Injective.comp ULift.up_injective
      (Function.Injective.comp hf ULift.down_injective))) h

lemma of_surjective (f : X → Y) (hf : Function.Surjective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective
    (Function.Surjective.comp ULift.up_surjective (Function.Surjective.comp hf
      ULift.down_surjective))) h

end

end HasCardinalLT

lemma hasCardinalLT_iff_of_equiv {X : Type u} {Y : Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) :
    HasCardinalLT X κ ↔ HasCardinalLT Y κ :=
  ⟨fun h ↦ h.of_injective _ e.symm.injective,
    fun h ↦ h.of_injective _ e.injective⟩

@[simp]
lemma hasCardinalLT_aleph0_iff (X : Type u) :
    HasCardinalLT X Cardinal.aleph0.{v} ↔ Finite X := by
  simpa [HasCardinalLT] using Cardinal.mk_lt_aleph0_iff

lemma hasCardinalLT_sum_iff (X : Type u) (Y : Type u') (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (X ⊕ Y) κ ↔ HasCardinalLT X κ ∧ HasCardinalLT Y κ := by
  constructor
  · intro h
    exact ⟨h.of_injective _ Sum.inl_injective,
      h.of_injective _ Sum.inr_injective⟩
  · rintro ⟨hX, hY⟩
    dsimp [HasCardinalLT] at hX hY ⊢
    rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at hX
    rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift] at hY
    simp only [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift]
    exact Cardinal.add_lt_of_lt (by simpa using hκ) hX hY

lemma hasCardinalLT_option_iff (X : Type u) (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Option X) κ ↔ HasCardinalLT X κ := by
  rw [hasCardinalLT_iff_of_equiv (Equiv.optionEquivSumPUnit.{0} X),
    hasCardinalLT_sum_iff _ _ _ hκ, and_iff_left_iff_imp]
  refine fun _ ↦ HasCardinalLT.of_le ?_ hκ
  rw [hasCardinalLT_aleph0_iff]
  infer_instance

namespace HasCardinalLT

/-- For any `w`-small type `X`, there exists a regular cardinal `κ : Cardinal.{w}`
such that `HasCardinalLT X κ`. -/
lemma exists_regular_cardinal (X : Type u) [Small.{w} X] :
    ∃ (κ : Cardinal.{w}), κ.IsRegular ∧ HasCardinalLT X κ :=
  ⟨Order.succ (max (Cardinal.mk (Shrink.{w} X)) .aleph0),
    Cardinal.isRegular_succ (le_max_right _ _), by
      simp [hasCardinalLT_iff_of_equiv (equivShrink.{w} X),
        hasCardinalLT_iff_cardinal_mk_lt]⟩

/-- For any `w`-small family `X : ι → Type u` of `w`-small types, there exists
a regular cardinal `κ : Cardinal.{w}` such that `HasCardinalLT (X i) κ` for all `i : ι`. -/
lemma exists_regular_cardinal_forall {ι : Type v} {X : ι → Type u} [Small.{w} ι]
    [∀ i, Small.{w} (X i)] :
    ∃ (κ : Cardinal.{w}), κ.IsRegular ∧ ∀ (i : ι), HasCardinalLT (X i) κ := by
  obtain ⟨κ, hκ, h⟩ := exists_regular_cardinal.{w} (Sigma X)
  exact ⟨κ, hκ, fun i ↦ h.of_injective _ sigma_mk_injective⟩

end HasCardinalLT
