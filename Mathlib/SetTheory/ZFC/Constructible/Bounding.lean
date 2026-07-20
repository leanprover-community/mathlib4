/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Def

/-!
# Stage bounds in the constructible hierarchy

This file collects the external bounding facts used to turn set-indexed
families of constructible sets into constructions inside one level of `L`.
The index type of the members of a `ZFSet` is small, so a family of witnesses
in `Ordinal.{u}` has a supremum in the same universe.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/-- A chosen level at which a constructible set first need not occur, but does occur. -/
noncomputable def stageOf (x : ZFSet.{u}) (hx : x ∈ L) : Ordinal.{u} :=
  Classical.choose hx

theorem mem_LStageZF_stageOf (x : ZFSet.{u}) (hx : x ∈ L) :
    x ∈ LStageZF (stageOf x hx) :=
  Classical.choose_spec hx

/--
All members of an internal set which are constructible occur together in one
level of the constructible hierarchy.
-/
theorem exists_LStage_for_members {a : ZFSet.{u}}
    (ha : ∀ x ∈ a, x ∈ L) :
    ∃ α : Ordinal.{u}, ∀ x ∈ a, x ∈ LStageZF α := by
  let level : a → Ordinal.{u} := fun x => stageOf x.1 (ha x.1 x.2)
  refine ⟨⨆ x : a, level x, ?_⟩
  intro x hx
  let xa : a := ⟨x, hx⟩
  exact LStageZF_mono (Ordinal.le_iSup level xa)
    (mem_LStageZF_stageOf x (ha x hx))

/-- A common level can be required to lie above any prescribed starting level. -/
theorem exists_LStage_for_members_ge {a : ZFSet.{u}}
    (ha : ∀ x ∈ a, x ∈ L) (γ : Ordinal.{u}) :
    ∃ α : Ordinal.{u}, γ ≤ α ∧ ∀ x ∈ a, x ∈ LStageZF α := by
  rcases exists_LStage_for_members ha with ⟨β, hβ⟩
  refine ⟨max γ β, le_max_left _ _, ?_⟩
  intro x hx
  exact LStageZF_mono (le_max_right _ _) (hβ x hx)

/-- Every member of a constructible set is bounded by one constructible level. -/
theorem exists_LStage_for_constructible_members {a : ZFSet.{u}} (ha : a ∈ L) :
    ∃ α : Ordinal.{u}, ∀ x ∈ a, x ∈ LStageZF α :=
  exists_LStage_for_members fun _x hx => mem_L_of_mem hx ha

end ZFC

end Constructible
