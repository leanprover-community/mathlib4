/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Intervals.OrdConnected

#align_import order.complete_lattice_intervals from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `OrdConnected` set satisfies these conditions.

## TODO

Add appropriate instances for all `Set.Ixx`. This requires a refactor that will allow different
default values for `sSup` and `sInf`.
-/


open Classical

open Set

variable {α : Type*} (s : Set α)

section SupSet

variable [SupSet α]

/-- `SupSet` structure on a nonempty subset `s` of an object with `SupSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetSupSet [Inhabited s] : SupSet s where
  sSup t :=
    if ht : sSup ((↑) '' t : Set α) ∈ s
    then ⟨sSup ((↑) '' t : Set α), ht⟩
    else default
#align subset_has_Sup subsetSupSet

attribute [local instance] subsetSupSet

@[simp]
theorem subset_sSup_def [Inhabited s] :
    @sSup s _ = fun t =>
      if ht : sSup ((↑) '' t : Set α) ∈ s
      then ⟨sSup ((↑) '' t : Set α), ht⟩
      else default :=
  rfl
#align subset_Sup_def subset_sSup_def

theorem subset_sSup_of_within [Inhabited s] {t : Set s} (h : sSup ((↑) '' t : Set α) ∈ s) :
    sSup ((↑) '' t : Set α) = (@sSup s _ t : α) := by simp [dif_pos h]
#align subset_Sup_of_within subset_sSup_of_within

end SupSet

section InfSet

variable [InfSet α]

/-- `InfSet` structure on a nonempty subset `s` of an object with `InfSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetInfSet [Inhabited s] : InfSet s where
  sInf t :=
    if ht : sInf ((↑) '' t : Set α) ∈ s
    then ⟨sInf ((↑) '' t : Set α), ht⟩
    else default
#align subset_has_Inf subsetInfSet

attribute [local instance] subsetInfSet

@[simp]
theorem subset_sInf_def [Inhabited s] :
    @sInf s _ = fun t =>
      if ht : sInf ((↑) '' t : Set α) ∈ s
      then ⟨sInf ((↑) '' t : Set α), ht⟩ else
      default :=
  rfl
#align subset_Inf_def subset_sInf_def

theorem subset_sInf_of_within [Inhabited s] {t : Set s} (h : sInf ((↑) '' t : Set α) ∈ s) :
    sInf ((↑) '' t : Set α) = (@sInf s _ t : α) := by simp [dif_pos h]
#align subset_Inf_of_within subset_sInf_of_within

end InfSet

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

lemma sSup_subtype_eq_sSup_univ_of_not_bddAbove {s : Set α} [Inhabited s]
    (t : Set s) (ht : ¬BddAbove t) : sSup t = sSup univ := by
  have A : ∀ (u : Set s), ¬BddAbove u → BddAbove (Subtype.val '' u) →
      sSup ((↑) '' u : Set α) ∉ s := by
    intro u hu Hu
    contrapose! hu
    refine ⟨⟨_, hu⟩, ?_⟩
    rintro ⟨x, xs⟩ hx
    simp only [Subtype.mk_le_mk]
    apply le_csSup Hu
    exact ⟨⟨x, xs⟩, hx, rfl⟩
  by_cases Ht : BddAbove ((↑) '' t : Set α)
  · have I1 : sSup ((↑) '' t : Set α) ∉ s := A t ht Ht
    have I2 : sSup ((↑) '' (univ : Set s) : Set α) ∉ s := by
      apply A
      · contrapose! ht; exact ht.mono (subset_univ _)
      · refine ⟨sSup ((↑) '' t : Set α), ?_⟩
        rintro - ⟨⟨x, hx⟩, -, rfl⟩
        simp [BddAbove, not_nonempty_iff_eq_empty] at ht
        have : ⟨x, hx⟩ ∉ upperBounds t := by simp [ht]
        obtain ⟨⟨y, ys⟩, yt, hy⟩ : ∃ y, y ∈ t ∧ { val := x, property := hx } < y :=
          by simpa only [Subtype.mk_le_mk, not_forall, not_le, exists_prop, exists_and_right,
            mem_upperBounds]
        refine le_trans (le_of_lt hy) ?_
        exact le_csSup Ht ⟨⟨y, ys⟩, yt, rfl⟩
    simp only [sSup, I1, I2, dite_false]
  · have I : ¬BddAbove ((↑) '' (univ : Set s) : Set α) := by
      contrapose! Ht; exact Ht.mono (image_subset Subtype.val (subset_univ _))
    have X : sSup ((↑) '' t : Set α) = sSup (univ : Set α) :=
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ Ht
    have Y : sSup ((↑) '' (univ : Set s) : Set α) = sSup (univ : Set α) :=
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ I
    simp only [sSup, X, Y]

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `sSup` of all its nonempty bounded-above subsets, and
the `sInf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { -- The following would be a more natural way to finish, but gives a "deep recursion" error:
      -- simpa [subset_Sup_of_within (h_Sup t)] using
      --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
    subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    le_csSup := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_sSup_of_within s (h_Sup ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe _).le_csSup_image hct h_bdd
    csSup_le := by
      rintro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_sSup_of_within s (h_Sup ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).csSup_image_le ht hB
    le_csInf := by
      intro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_sInf_of_within s (h_Inf ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).le_csInf_image ht hB
    csInf_le := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_sInf_of_within s (h_Inf ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe s).csInf_image_le hct h_bdd
    csSup_of_not_bddAbove := sSup_subtype_eq_sSup_univ_of_not_bddAbove
    csInf_of_not_bddBelow := @sSup_subtype_eq_sSup_univ_of_not_bddAbove αᵒᵈ _ _ _ }
#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrder

section OrdConnected

/-- The `sSup` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sSup ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine' hs.out c.2 B.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe s).csSup_image_le ⟨c, hct⟩ hB
#align Sup_within_of_ord_connected sSup_within_of_ordConnected

/-- The `sInf` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : sInf ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine' hs.out B.2 c.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe s).csInf_image_le hct ⟨B, hB⟩
#align Inf_within_of_ord_connected sInf_within_of_ordConnected

/-- A nonempty `OrdConnected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)
#align ord_connected_subset_conditionally_complete_linear_order ordConnectedSubsetConditionallyCompleteLinearOrder

end OrdConnected
