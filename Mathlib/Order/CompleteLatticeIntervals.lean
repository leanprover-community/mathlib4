/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.LatticeIntervals
import Mathlib.Order.Interval.Set.OrdConnected

#align_import order.complete_lattice_intervals from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `OrdConnected` set satisfies these conditions.

## TODO

Add appropriate instances for all `Set.Ixx`. This requires a refactor that will allow different
default values for `sSup` and `sInf`.
-/


open scoped Classical

open Set

variable {ι : Sort*} {α : Type*} (s : Set α)

section SupSet

variable [Preorder α] [SupSet α]

/-- `SupSet` structure on a nonempty subset `s` of a preorder with `SupSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetSupSet [Inhabited s] : SupSet s where
  sSup t :=
    if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else default
#align subset_has_Sup subsetSupSet

attribute [local instance] subsetSupSet

@[simp]
theorem subset_sSup_def [Inhabited s] :
    @sSup s _ = fun t =>
      if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
      then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
      else default :=
  rfl
#align subset_Sup_def subset_sSup_def

theorem subset_sSup_of_within [Inhabited s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddAbove t)  (h : sSup ((↑) '' t : Set α) ∈ s) :
    sSup ((↑) '' t : Set α) = (@sSup s _ t : α) := by simp [dif_pos, h, h', h'']
#align subset_Sup_of_within subset_sSup_of_within

theorem subset_sSup_emptyset [Inhabited s] :
    sSup (∅ : Set s) = default := by
  simp [sSup]

theorem subset_sSup_of_not_bddAbove [Inhabited s] {t : Set s} (ht : ¬BddAbove t) :
    sSup t = default := by
  simp [sSup, ht]

end SupSet

section InfSet

variable [Preorder α] [InfSet α]

/-- `InfSet` structure on a nonempty subset `s` of a preorder with `InfSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
noncomputable def subsetInfSet [Inhabited s] : InfSet s where
  sInf t :=
    if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else default
#align subset_has_Inf subsetInfSet

attribute [local instance] subsetInfSet

@[simp]
theorem subset_sInf_def [Inhabited s] :
    @sInf s _ = fun t =>
      if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
      then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩ else
      default :=
  rfl
#align subset_Inf_def subset_sInf_def

theorem subset_sInf_of_within [Inhabited s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddBelow t) (h : sInf ((↑) '' t : Set α) ∈ s) :
    sInf ((↑) '' t : Set α) = (@sInf s _ t : α) := by simp [dif_pos, h, h', h'']
#align subset_Inf_of_within subset_sInf_of_within

theorem subset_sInf_emptyset [Inhabited s] :
    sInf (∅ : Set s) = default := by
  simp [sInf]

theorem subset_sInf_of_not_bddBelow [Inhabited s] {t : Set s} (ht : ¬BddBelow t) :
    sInf t = default := by
  simp [sInf, ht]

end InfSet

section OrdConnected

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `sSup` of all its nonempty bounded-above subsets, and
the `sInf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
noncomputable abbrev subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    le_csSup := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_sSup_of_within s ⟨c, hct⟩ h_bdd (h_Sup ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe _).le_csSup_image hct h_bdd
    csSup_le := by
      rintro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_sSup_of_within s ht ⟨B, hB⟩ (h_Sup ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).csSup_image_le ht hB
    le_csInf := by
      intro t B ht hB
      rw [← Subtype.coe_le_coe, ← subset_sInf_of_within s ht ⟨B, hB⟩ (h_Inf ht ⟨B, hB⟩)]
      exact (Subtype.mono_coe s).le_csInf_image ht hB
    csInf_le := by
      rintro t c h_bdd hct
      rw [← Subtype.coe_le_coe, ← subset_sInf_of_within s ⟨c, hct⟩ h_bdd (h_Inf ⟨c, hct⟩ h_bdd)]
      exact (Subtype.mono_coe s).csInf_image_le hct h_bdd
    csSup_of_not_bddAbove := fun t ht ↦ by simp [ht]
    csInf_of_not_bddBelow := fun t ht ↦ by simp [ht] }
#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrder

/-- The `sSup` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sSup ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine hs.out c.2 B.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe s).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe s).csSup_image_le ⟨c, hct⟩ hB
#align Sup_within_of_ord_connected sSup_within_of_ordConnected

/-- The `sInf` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : sInf ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine hs.out B.2 c.2 ⟨?_, ?_⟩
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

section Icc

/-- Complete lattice structure on `Set.Icc` -/
noncomputable def Set.Icc.completeLattice [ConditionallyCompleteLattice α]
    {a b : α} (h : a ≤ b) : CompleteLattice (Set.Icc a b) where
  __ := Set.Icc.boundedOrder h
  sSup S := if hS : S = ∅ then ⟨a, le_rfl, h⟩ else ⟨sSup ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine ⟨?_, csSup_le (hS.image (↑)) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.2)⟩
    obtain ⟨c, hc⟩ := hS
    exact c.2.1.trans (le_csSup ⟨b, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩)⟩
  le_sSup S c hc := by
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · simp [hS] at hc
    · exact le_csSup ⟨b, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩
  sSup_le S c hc := by
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · exact c.2.1
    · exact csSup_le ((Set.nonempty_iff_ne_empty.mpr hS).image (↑))
        (fun _ ⟨d, h, hd⟩ ↦ hd ▸ hc d h)
  sInf S := if hS : S = ∅ then ⟨b, h, le_rfl⟩ else ⟨sInf ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine ⟨le_csInf (hS.image (↑)) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.1), ?_⟩
    obtain ⟨c, hc⟩ := hS
    exact le_trans (csInf_le ⟨a, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.1⟩ ⟨c, hc, rfl⟩) c.2.2⟩
  sInf_le S c hc := by
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · simp [hS] at hc
    · exact csInf_le ⟨a, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.1⟩ ⟨c, hc, rfl⟩
  le_sInf S c hc := by
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · exact c.2.2
    · exact le_csInf ((Set.nonempty_iff_ne_empty.mpr hS).image (↑))
        (fun _ ⟨d, h, hd⟩ ↦ hd ▸ hc d h)

/-- Complete linear order structure on `Set.Icc` -/
noncomputable def Set.Icc.completeLinearOrder [ConditionallyCompleteLinearOrder α]
    {a b : α} (h : a ≤ b) : CompleteLinearOrder (Set.Icc a b) :=
  { Set.Icc.completeLattice h, Subtype.instLinearOrder _ with }

lemma Set.Icc.coe_sSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : letI := Set.Icc.completeLattice h
    ↑(sSup S) = sSup ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

lemma Set.Icc.coe_sInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : letI := Set.Icc.completeLattice h
    ↑(sInf S) = sInf ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

lemma Set.Icc.coe_iSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : letI := Set.Icc.completeLattice h
    ↑(iSup S) = (⨆ i, S i : α) :=
  (Set.Icc.coe_sSup h (range_nonempty S)).trans (congrArg sSup (range_comp Subtype.val S).symm)

lemma Set.Icc.coe_iInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : letI := Set.Icc.completeLattice h
    ↑(iInf S) = (⨅ i, S i : α) :=
  (Set.Icc.coe_sInf h (range_nonempty S)).trans (congrArg sInf (range_comp Subtype.val S).symm)

end Icc

namespace Set.Iic

variable [CompleteLattice α] {a : α}

instance instCompleteLattice : CompleteLattice (Iic a) where
  sSup S := ⟨sSup ((↑) '' S), by simpa using fun b hb _ ↦ hb⟩
  sInf S := ⟨a ⊓ sInf ((↑) '' S), by simp⟩
  le_sSup S b hb := le_sSup <| mem_image_of_mem Subtype.val hb
  sSup_le S b hb := sSup_le <| fun c' ⟨c, hc, hc'⟩ ↦ hc' ▸ hb c hc
  sInf_le S b hb := inf_le_of_right_le <| sInf_le <| mem_image_of_mem Subtype.val hb
  le_sInf S b hb := le_inf_iff.mpr ⟨b.property, le_sInf fun d' ⟨d, hd, hd'⟩  ↦ hd' ▸ hb d hd⟩
  le_top := by simp
  bot_le := by simp

variable (S : Set <| Iic a) (f : ι → Iic a) (p : ι → Prop)

@[simp] theorem coe_sSup : (↑(sSup S) : α) = sSup ((↑) '' S) := rfl

@[simp] theorem coe_iSup : (↑(⨆ i, f i) : α) = ⨆ i, (f i : α) := by
  rw [iSup, coe_sSup]; congr; ext; simp

theorem coe_biSup : (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α) := by simp

@[simp] theorem coe_sInf : (↑(sInf S) : α) = a ⊓ sInf ((↑) '' S) := rfl

@[simp] theorem coe_iInf : (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α) := by
  rw [iInf, coe_sInf]; congr; ext; simp

theorem coe_biInf : (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : α) := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [coe_iInf, ← inf_iInf, ← inf_assoc, inf_idem]


end Set.Iic

assert_not_exists Multiset
