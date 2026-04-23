/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.Interval.Set.OrdConnected

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `OrdConnected` set satisfies these conditions.

## TODO

Add appropriate instances for all `Set.Ixx`.
-/

@[expose] public section

assert_not_exists Multiset

open Set

variable {ι : Sort*} {α : Type*} (s : Set α)

section SupSet

variable [Preorder α] [SupSet α]

open Classical in
/-- `SupSet` structure on a nonempty subset `s` of a preorder with `SupSet`.
It should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
@[instance_reducible]
noncomputable def subsetSupSet [Bot s] : SupSet s where
  sSup t :=
    if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else ⊥

attribute [local instance] subsetSupSet

open Classical in
@[simp]
theorem subset_sSup_def [Bot s] :
    @sSup s _ = fun t =>
      if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
      then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
      else ⊥ :=
  rfl

theorem subset_sSup_of_within [Bot s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddAbove t) (h : sSup ((↑) '' t : Set α) ∈ s) :
    sSup ((↑) '' t : Set α) = (@sSup s _ t : α) := by simp [h, h', h'']

theorem subset_sSup_emptyset [Bot s] :
    sSup (∅ : Set s) = ⊥ := by
  simp [sSup]

theorem subset_sSup_of_not_bddAbove [Bot s] {t : Set s} (ht : ¬BddAbove t) :
    sSup t = ⊥ := by
  simp [sSup, ht]

end SupSet

section InfSet

variable [Preorder α] [InfSet α]

open Classical in
/-- `InfSet` structure on a nonempty subset `s` of a preorder with `InfSet`.
It should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
@[instance_reducible]
noncomputable def subsetInfSet [Top s] : InfSet s where
  sInf t :=
    if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else ⊤

attribute [local instance] subsetInfSet

open Classical in
@[simp]
theorem subset_sInf_def [Top s] :
    @sInf s _ = fun t =>
      if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
      then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩ else
      ⊤ :=
  rfl

theorem subset_sInf_of_within [Top s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddBelow t) (h : sInf ((↑) '' t : Set α) ∈ s) :
    sInf ((↑) '' t : Set α) = (@sInf s _ t : α) := by simp [h, h', h'']

theorem subset_sInf_emptyset [Top s] :
    sInf (∅ : Set s) = ⊤ := by
  simp [sInf]

theorem subset_sInf_of_not_bddBelow [Top s] {t : Set s} (ht : ¬BddBelow t) :
    sInf t = ⊤ := by
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
noncomputable abbrev subsetConditionallyCompleteLinearOrder [Bot s] [Top s]
    (hbot : IsBot (⊥ : s) ∨ NoBotOrder s) (htop : IsTop (⊤ : s) ∨ NoTopOrder s)
    (h_Sup : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    isLUB_sSup_of_isLUB t _ h := by
      dsimp [subset_sSup_def]
      obtain rfl | hn := eq_empty_or_nonempty t
      · rw [isLUB_empty_iff] at h ⊢
        rw [dif_neg (by simp)]
        exact hbot.resolve_right fun _ ↦ not_isBot _ h
      · rw [dif_pos ⟨hn, h.bddAbove, h_Sup hn h.bddAbove⟩]
        exact .of_image Subtype.coe_le_coe
          (isLUB_csSup (hn.image _ ) ((Subtype.mono_coe _).map_bddAbove h.bddAbove))
    isGLB_sInf_of_isGLB t _ h := by
      dsimp [subset_sSup_def]
      obtain rfl | hn := eq_empty_or_nonempty t
      · rw [isGLB_empty_iff] at h ⊢
        rw [dif_neg (by simp)]
        exact htop.resolve_right fun _ ↦ not_isTop _ h
      · rw [dif_pos ⟨hn, h.bddBelow, h_Inf hn h.bddBelow⟩]
        exact .of_image Subtype.coe_le_coe
          (isGLB_csInf (hn.image _) ((Subtype.mono_coe _).map_bddBelow h.bddBelow))
    exists_isLUB_cond t ht h_bdd := ⟨sSup t, .of_image Subtype.coe_le_coe <| by
      rw [← subset_sSup_of_within s ht h_bdd (h_Sup ht h_bdd)]
      exact isLUB_csSup (ht.image _) ((Subtype.mono_coe _).map_bddAbove h_bdd)⟩
    exists_isGLB_cond t ht h_bdd := ⟨sInf t, .of_image Subtype.coe_le_coe <| by
      rw [← subset_sInf_of_within s ht h_bdd (h_Inf ht h_bdd)]
      exact isGLB_csInf (ht.image _) ((Subtype.mono_coe _).map_bddBelow h_bdd)⟩
    csSup_of_not_bddAbove := fun t ht ↦ by simp [ht]
    csInf_of_not_bddBelow := fun t ht ↦ by simp [ht] }

/-- The `sSup` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sSup ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine hs.out c.2 B.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· ∈ s)).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe (· ∈ s)).csSup_image_le ⟨c, hct⟩ hB

/-- The `sInf` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : sInf ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine hs.out B.2 c.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· ∈ s)).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe (· ∈ s)).csInf_image_le hct ⟨B, hB⟩

/-- A nonempty `OrdConnected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable abbrev ordConnectedSubsetConditionallyCompleteLinearOrderOfBotTop [Bot s] [Top s]
    (hbot : IsBot (⊥ : s) ∨ NoBotOrder s) (htop : IsTop (⊤ : s) ∨ NoTopOrder s)
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s hbot htop
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

/-- A nonempty `OrdConnected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  letI bot : Bot s := match botOrderOrNoBotOrder s with | .inl h => h.toBot | .inr _ => ⟨default⟩
  letI top : Top s := match topOrderOrNoTopOrder s with | .inl h => h.toTop | .inr _ => ⟨default⟩
  ordConnectedSubsetConditionallyCompleteLinearOrderOfBotTop (s := s)
    (by unfold bot; cases botOrderOrNoBotOrder s; exacts [.inl isBot_bot, .inr ‹_›])
    (by unfold top; cases topOrderOrNoTopOrder s; exacts [.inl isTop_top, .inr ‹_›])

end OrdConnected

section Icc

open Classical in
/-- Complete lattice structure on `Set.Icc` -/
noncomputable instance Set.Icc.completeLattice [ConditionallyCompleteLattice α]
    {a b : α} [Fact (a ≤ b)] : CompleteLattice (Set.Icc a b) where
  __ := (inferInstance : BoundedOrder ↑(Icc a b))
  sSup S := if hS : S = ∅ then ⟨a, le_rfl, Fact.out⟩ else ⟨sSup ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine ⟨?_, csSup_le (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.2)⟩
    obtain ⟨c, hc⟩ := hS
    exact c.2.1.trans (le_csSup ⟨b, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩)⟩
  isLUB_sSup S := by
    split_ifs with hS
    · subst hS; simp only [isLUB_empty_iff, isBot_iff_eq_bot]; rfl
    · exact .of_image Subtype.coe_le_coe <| isLUB_csSup ((Set.nonempty_iff_ne_empty.mpr hS).image _)
        ((Subtype.mono_coe _).map_bddAbove (OrderTop.bddAbove S))
  sInf S := if hS : S = ∅ then ⟨b, Fact.out, le_rfl⟩ else ⟨sInf ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine ⟨le_csInf (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.1), ?_⟩
    obtain ⟨c, hc⟩ := hS
    exact le_trans (csInf_le ⟨a, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.1⟩ ⟨c, hc, rfl⟩) c.2.2⟩
  isGLB_sInf S := by
    split_ifs with hS
    · subst hS; simp only [isGLB_empty_iff, isTop_iff_eq_top]; rfl
    · exact .of_image Subtype.coe_le_coe <| isGLB_csInf ((Set.nonempty_iff_ne_empty.mpr hS).image _)
        ((Subtype.mono_coe _).map_bddBelow (OrderBot.bddBelow S))

/-- Complete linear order structure on `Set.Icc` -/
noncomputable instance [ConditionallyCompleteLinearOrder α] {a b : α} [Fact (a ≤ b)] :
    CompleteLinearOrder (Set.Icc a b) :=
  { Set.Icc.completeLattice, Subtype.instLinearOrder _, LinearOrder.toBiheytingAlgebra _ with }

lemma Set.Icc.coe_sSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a ≤ b) := ⟨h⟩
    ↑(sSup S) = sSup ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

lemma Set.Icc.coe_sInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a ≤ b) := ⟨h⟩
    ↑(sInf S) = sInf ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

lemma Set.Icc.coe_iSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : have : Fact (a ≤ b) := ⟨h⟩
    ↑(iSup S) = (⨆ i, S i : α) :=
  (Set.Icc.coe_sSup h (range_nonempty S)).trans (congrArg sSup (range_comp Subtype.val S).symm)

lemma Set.Icc.coe_iInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : have : Fact (a ≤ b) := ⟨h⟩
    ↑(iInf S) = (⨅ i, S i : α) :=
  (Set.Icc.coe_sInf h (range_nonempty S)).trans (congrArg sInf (range_comp Subtype.val S).symm)

end Icc

namespace Set.Iic

variable [CompleteLattice α] {a : α}

instance instCompleteLattice : CompleteLattice (Iic a) where
  sSup S := ⟨sSup ((↑) '' S), by simpa using fun b hb _ ↦ hb⟩
  sInf S := ⟨a ⊓ sInf ((↑) '' S), by simp⟩
  isLUB_sSup _ := .of_image Subtype.coe_le_coe (isLUB_sSup _)
  isGLB_sInf _ :=
    ⟨fun _ hb ↦ inf_le_of_right_le <| sInf_le <| mem_image_of_mem Subtype.val hb,
      fun b hb ↦ le_inf_iff.mpr ⟨b.property, le_sInf fun _ ⟨_, hd, hd'⟩ ↦ hd' ▸ hb hd⟩⟩
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
