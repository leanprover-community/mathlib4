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

/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetHasSup [Inhabited s] : SupSet s where
  supₛ t :=
    if ht : supₛ (Subtype.val '' t : Set α) ∈ s
    then ⟨supₛ (Subtype.val '' t : Set α), ht⟩
    else default
#align subset_has_Sup subsetHasSup

attribute [local instance] subsetHasSup

@[simp]
theorem subset_Sup_def [Inhabited s] :
    @supₛ s _ = fun t =>
      if ht : supₛ (Subtype.val '' t : Set α) ∈ s
      then ⟨supₛ (Subtype.val '' t : Set α), ht⟩
      else default :=
  rfl
#align subset_Sup_def subset_Sup_def

theorem subset_supₛ_of_within [Inhabited s] {t : Set s} (h : supₛ (Subtype.val '' t : Set α) ∈ s) :
    supₛ (Subtype.val '' t : Set α) = (@supₛ s _ t : α) := by simp [dif_pos h]
#align subset_Sup_of_within subset_supₛ_of_within

end SupSet

section InfSet

variable [InfSet α]

/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetHasInf [Inhabited s] : InfSet s where
  infₛ t :=
    if ht : infₛ (Subtype.val '' t : Set α) ∈ s
    then ⟨infₛ (Subtype.val '' t : Set α), ht⟩
    else default
#align subset_has_Inf subsetHasInf

attribute [local instance] subsetHasInf

@[simp]
theorem subset_Inf_def [Inhabited s] :
    @infₛ s _ = fun t =>
      if ht : infₛ (Subtype.val '' t : Set α) ∈ s
      then ⟨infₛ (Subtype.val '' t : Set α), ht⟩ else
      default :=
  rfl
#align subset_Inf_def subset_Inf_def

theorem subset_infₛ_of_within [Inhabited s] {t : Set s} (h : infₛ (Subtype.val '' t : Set α) ∈ s) :
    infₛ (Subtype.val '' t : Set α) = (@infₛ s _ t : α) := by simp [dif_pos h]
#align subset_Inf_of_within subset_infₛ_of_within

end InfSet

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetHasSup

attribute [local instance] subsetHasInf

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddAbove t), supₛ (Subtype.val '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddBelow t), infₛ (Subtype.val '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { -- The following would be a more natural way to finish, but gives a "deep recursion" error:
      -- simpa [subset_Sup_of_within (h_Sup t)] using
      --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
      subsetHasSup
      s,
    subsetHasInf s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    le_csupₛ := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).le_csupₛ_image hct h_bdd
      erw [subset_supₛ_of_within s (h_Sup ⟨c, hct⟩ h_bdd)] at this
      assumption
    csupₛ_le := by
      rintro t B ht hB
      have := (Subtype.mono_coe s).cSup_image_le ht hB
      rwa [subset_Sup_of_within s (h_Sup ht ⟨B, hB⟩)] at this
    le_cinfₛ := by
      intro t B ht hB
      have := (Subtype.mono_coe s).le_cInf_image ht hB
      rwa [subset_Inf_of_within s (h_Inf ht ⟨B, hB⟩)] at this
    cinfₛ_le := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).cInf_image_le hct h_bdd
      rwa [subset_Inf_of_within s (h_Inf ⟨c, hct⟩ h_bdd)] at this }
#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrder

section OrdConnected

/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem Sup_within_of_ord_connected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : supₛ (coe '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine' hs.out c.2 B.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_cSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe s).cSup_image_le ⟨c, hct⟩ hB
#align Sup_within_of_ord_connected Sup_within_of_ord_connected

/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem Inf_within_of_ord_connected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : infₛ (coe '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine' hs.out B.2 c.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_cInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe s).cInf_image_le hct ⟨B, hB⟩
#align Inf_within_of_ord_connected Inf_within_of_ord_connected

/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s Sup_within_of_ord_connected Inf_within_of_ord_connected
#align
  ord_connected_subset_conditionally_complete_linear_order ordConnectedSubsetConditionallyCompleteLinearOrder

end OrdConnected
