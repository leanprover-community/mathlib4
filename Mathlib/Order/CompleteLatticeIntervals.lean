/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module order.complete_lattice_intervals
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Intervals.OrdConnected

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `OrdConnected` set satisfies these conditions.

## TODO

Add appropriate instances for all `Set.Ixx`. This requires a refactor that will allow different
default values for `supₛ` and `infₛ`.
-/


open Classical

open Set

variable {α : Type _} (s : Set α)

section SupSet

variable [SupSet α]

/-- `SupSet` structure on a nonempty subset `s` of an object with `SupSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetSupSet [Inhabited s] : SupSet s where
  supₛ t :=
    if ht : supₛ ((↑) '' t : Set α) ∈ s
    then ⟨supₛ ((↑) '' t : Set α), ht⟩
    else default
#align subset_has_Sup subsetSupSet

attribute [local instance] subsetSupSet

@[simp]
theorem subset_supₛ_def [Inhabited s] :
    @supₛ s _ = fun t =>
      if ht : supₛ ((↑) '' t : Set α) ∈ s
      then ⟨supₛ ((↑) '' t : Set α), ht⟩
      else default :=
  rfl
#align subset_Sup_def subset_supₛ_def

theorem subset_supₛ_of_within [Inhabited s] {t : Set s} (h : supₛ ((↑) '' t : Set α) ∈ s) :
    supₛ ((↑) '' t : Set α) = (@supₛ s _ t : α) := by simp [dif_pos h]
#align subset_Sup_of_within subset_supₛ_of_within

end SupSet

section InfSet

variable [InfSet α]

/-- `InfSet` structure on a nonempty subset `s` of an object with `InfSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetInfSet [Inhabited s] : InfSet s where
  infₛ t :=
    if ht : infₛ ((↑) '' t : Set α) ∈ s
    then ⟨infₛ ((↑) '' t : Set α), ht⟩
    else default
#align subset_has_Inf subsetInfSet

attribute [local instance] subsetInfSet

@[simp]
theorem subset_infₛ_def [Inhabited s] :
    @infₛ s _ = fun t =>
      if ht : infₛ ((↑) '' t : Set α) ∈ s
      then ⟨infₛ ((↑) '' t : Set α), ht⟩ else
      default :=
  rfl
#align subset_Inf_def subset_infₛ_def

theorem subset_infₛ_of_within [Inhabited s] {t : Set s} (h : infₛ ((↑) '' t : Set α) ∈ s) :
    infₛ ((↑) '' t : Set α) = (@infₛ s _ t : α) := by simp [dif_pos h]
#align subset_Inf_of_within subset_infₛ_of_within

end InfSet

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `supₛ` of all its nonempty bounded-above subsets, and
the `infₛ` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), supₛ ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), infₛ ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { -- The following would be a more natural way to finish, but gives a "deep recursion" error:
      -- simpa [subset_Sup_of_within (h_Sup t)] using
      --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
    subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    le_csupₛ := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_supₛ_of_within s (h_Sup ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe _).le_csupₛ_image hct h_bdd
    csupₛ_le := by
      rintro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_supₛ_of_within s (h_Sup ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).csupₛ_image_le ht hB
    le_cinfₛ := by
      intro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_infₛ_of_within s (h_Inf ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).le_cinfₛ_image ht hB
    cinfₛ_le := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_infₛ_of_within s (h_Inf ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe s).cinfₛ_image_le hct h_bdd }
#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrder

section OrdConnected

/-- The `supₛ` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem supₛ_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : supₛ ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine' hs.out c.2 B.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_csupₛ_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe s).csupₛ_image_le ⟨c, hct⟩ hB
#align Sup_within_of_ord_connected supₛ_within_of_ordConnected

/-- The `infₛ` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem infₛ_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : infₛ ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine' hs.out B.2 c.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_cinfₛ_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe s).cinfₛ_image_le hct ⟨B, hB⟩
#align Inf_within_of_ord_connected infₛ_within_of_ordConnected

/-- A nonempty `OrdConnected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s
    (fun h => supₛ_within_of_ordConnected h)
    (fun h => infₛ_within_of_ordConnected h)
#align ord_connected_subset_conditionally_complete_linear_order ordConnectedSubsetConditionallyCompleteLinearOrder

end OrdConnected
