/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.SetTheory.Cardinal.Basic

/-!
# The property of being of cardinality less than a cardinal

Given `X : Type u` and `κ : Cardinal.{v}`, we introduce a predicate
`HasCardinalLT X κ` expressing that
`Cardinal.mk (ULift.{v} X) < Cardinal.lift κ`.

-/

universe w v u u'

/-- The property that the cardinal of a type `X : Type u` is less than `κ : Cardinal.{v}`. -/
def HasCardinalLT (X : Type u) (κ : Cardinal.{v}) : Prop :=
  Cardinal.mk (ULift.{v} X) < Cardinal.lift κ

lemma hasCardinalLT_iff_cardinal_mk_lt (X : Type u) (κ : Cardinal.{u}) :
    HasCardinalLT X κ ↔ Cardinal.mk X < κ := by
  simp [HasCardinalLT]

namespace HasCardinalLT

section

variable {X : Type u} {κ : Cardinal.{v}} (h : HasCardinalLT X κ)

include h

lemma small : Small.{v} X := by
  induction' κ using Cardinal.inductionOn  with Y
  replace h := (Cardinal.le_def _ _).1 h.le
  obtain ⟨f, hf⟩ := h
  exact small_of_injective (Function.Injective.comp ULift.down_injective
    (Function.Injective.comp hf ULift.up_injective))

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
