/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Conditionally complete lattice structure on `WithTop` and `WithBot`

This file extends `sSup` and `sInf` from `α` to `WithTop α` and `WithBot α`, and shows that they
are conditionally complete lattices when `α` is. We also show that `WithTop (WithBot α)` and
`WithBot (WithTop α)` are complete lattices.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

namespace WithTop

section LE

/-!
Extension of `sSup` and `sInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [LE α]

open scoped Classical in
@[to_dual]
noncomputable instance instSupSet [SupSet α] : SupSet (WithTop α) :=
  ⟨fun S => if ⊤ ∈ S ∨ ¬BddAbove ((↑) ⁻¹' S : Set α) then ⊤ else ↑(sSup ((↑) ⁻¹' S : Set α))⟩

open scoped Classical in
@[to_dual]
noncomputable instance instInfSet [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α))⟩

@[to_dual]
theorem sSup_eq_top_iff [SupSet α] {s : Set (WithTop α)} :
    sSup s = ⊤ ↔ ⊤ ∈ s ∨ ¬BddAbove ((↑) ⁻¹' s : Set α) := by
  classical exact coe_ne_top.symm.ite_eq_left_iff

@[to_dual]
theorem sSup_eq_coe_iff [SupSet α] {s : Set (WithTop α)} {a : α} :
    sSup s = a ↔ ⊤ ∉ s ∧ BddAbove ((↑) ⁻¹' s : Set α) ∧ sSup ((↑) ⁻¹' s) = a := by
  classical exact ite_eq_iff.trans <| by simp [and_assoc]

@[to_dual]
theorem sInf_eq_top_iff [InfSet α] {s : Set (WithTop α)} :
    sInf s = ⊤ ↔ s ⊆ {⊤} ∨ ¬BddBelow s := by
  classical exact coe_ne_top.symm.ite_eq_left_iff

@[to_dual]
theorem sInf_eq_coe_iff [InfSet α] {s : Set (WithTop α)} {a : α} :
    sInf s = a ↔ ¬s ⊆ {⊤} ∧ BddBelow s ∧ sInf ((↑) ⁻¹' s) = a := by
  classical exact ite_eq_iff.trans <| by simp [and_assoc]

@[to_dual]
theorem sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  sSup_eq_coe_iff.2 ⟨hs, hs', rfl⟩

@[to_dual]
theorem sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) (h's : BddBelow s) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  sInf_eq_coe_iff.2 ⟨hs, h's, rfl⟩

@[to_dual (attr := simp)]
theorem sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
  sInf_eq_top_iff.2 <| .inl <| empty_subset _

@[to_dual (attr := simp)]
theorem sInf_singleton_top [InfSet α] : sInf ({⊤} : Set (WithTop α)) = ⊤ :=
  sInf_eq_top_iff.2 <| .inl subset_rfl

@[to_dual (attr := simp)]
theorem sSup_of_top_mem [SupSet α] {s : Set (WithTop α)} (h : ⊤ ∈ s) : sSup s = ⊤ :=
  sSup_eq_top_iff.2 <| .inl h

@[to_dual]
theorem sSup_singleton_top [SupSet α] : sSup ({⊤} : Set (WithTop α)) = ⊤ := by
  simp

@[to_dual]
theorem sSup_of_not_bddAbove [SupSet α] {s : Set (WithTop α)}
    (h : ¬BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ⊤ :=
  sSup_eq_top_iff.2 <| .inr h

@[to_dual (attr := simp)]
theorem sInf_of_not_bddBelow [InfSet α] {s : Set (WithTop α)} (h : ¬BddBelow s) :
    sInf s = ⊤ :=
  sInf_eq_top_iff.2 <| .inr h

@[to_dual (attr := norm_cast)]
theorem coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  rw [sSup_eq (by simp) (by rwa [preimage_image_eq _ coe_injective]),
    preimage_image_eq _ coe_injective]

@[to_dual (attr := deprecated (since := "2026-10-27"))] alias sSup_empty := sSup_empty

end LE

@[to_dual]
theorem isCompl_range_coe : IsCompl (range ((↑) : α → WithTop α)) {⊤} :=
  eq_compl_iff_isCompl.1 <| Set.ext fun _ ↦ ne_top_iff_exists.symm

section Preorder

variable [Preorder α]

@[to_dual]
theorem lowerBounds_preimage_coe {s : Set (WithTop α)} :
    lowerBounds (((↑) : α → WithTop α) ⁻¹' s) = (↑) ⁻¹' lowerBounds s := by
  ext a; simp [mem_lowerBounds, WithTop.forall]

@[to_dual]
theorem bddBelow_preimage_coe [Nonempty α] {s : Set (WithTop α)} :
    BddBelow (((↑) : α → WithTop α) ⁻¹' s) ↔ BddBelow s := by
  simp only [BddBelow, lowerBounds_preimage_coe, Set.Nonempty, mem_preimage, WithTop.exists,
    iff_or_self]
  exact fun h ↦ ⟨Classical.arbitrary α, lowerBounds_mono_mem le_top h⟩

@[to_dual]
theorem isGLB_coe_iff {s : Set (WithTop α)} {a : α} :
    IsGLB s (a : WithTop α) ↔ ¬s ⊆ {⊤} ∧ IsGLB ((↑) ⁻¹' s) a := by
  simp [isGLB_iff_le_iff, WithTop.forall, mem_lowerBounds, subset_def]

@[to_dual]
theorem isLUB_coe_iff {s : Set (WithTop α)} {a : α} :
    IsLUB s (a : WithTop α) ↔ ⊤ ∉ s ∧ IsLUB ((↑) ⁻¹' s) a := by
  by_cases hs : ⊤ ∈ s
  · simpa [hs] using fun h ↦ not_top_le_coe a (h.1 hs)
  · simp [hs, isLUB_iff_le_iff, WithTop.forall, mem_upperBounds]

@[to_dual]
theorem isGLB_top_iff {s : Set (WithTop α)} :
    IsGLB s ⊤ ↔ s ⊆ {⊤} :=
  ⟨fun h _ hx ↦ WithTop.top_le_iff.mp (h.1 hx),
    fun h ↦ ⟨fun _ hx ↦ le_of_eq (h hx).symm, fun _ _ ↦ le_top⟩⟩

@[to_dual]
theorem isLUB_top_iff {s : Set (WithTop α)} :
    IsLUB s ⊤ ↔ ⊤ ∈ s ∨ ¬BddAbove ((↑) ⁻¹' s : Set α) := by
  simp [isLUB_iff_le_iff, WithTop.forall, mem_upperBounds, BddAbove, Set.Nonempty,
    ← or_iff_not_imp_left, forall_or_left]

@[to_dual]
noncomputable instance instOrderSupSet [OrderSupSet α] :
    OrderSupSet (WithTop α) where
  isLUB_sSup_of_isLUB s a h := by
    cases a with
    | top => rwa [sSup_eq_top_iff.2 (isLUB_top_iff.1 h)]
    | coe a =>
      rw [isLUB_coe_iff] at h
      rw [sSup_eq h.1 h.2.bddAbove, isLUB_coe_iff]
      exact ⟨h.1, h.2.isLUB_sSup⟩

@[to_dual]
noncomputable instance instOrderInfSet [OrderInfSet α] :
    OrderInfSet (WithTop α) where
  isGLB_sInf_of_isGLB s a h := by
    cases a with
    | top => rwa [sInf_eq_top_iff.2 (.inl (isGLB_top_iff.1 h))]
    | coe a =>
      obtain ⟨hs, h'⟩ := isGLB_coe_iff.mp h
      rw [sInf_eq hs ⟨_, h.1⟩, isGLB_coe_iff]
      exact ⟨hs, h'.isGLB_sInf⟩

@[to_dual (attr := norm_cast)]
theorem coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty)
    (h's : BddBelow s) : ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · rcases h with h1 | h2
    · cases h1 (mem_image_of_mem _ hx)
    · exact (h2 (Monotone.map_bddBelow coe_mono h's)).elim
  · rw [preimage_image_eq]
    exact Option.some_injective _

end Preorder

variable [ConditionallyCompleteLinearOrder α] [OrderBot α]

/-- The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
@[to_dual]
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  by_cases h : ⊤ ∈ s ∨ ¬BddAbove ((↑) ⁻¹' s : Set β)
  · rw [sSup_eq_top_iff.2 h]
    exact isLUB_top_iff.2 h
  rw [not_or, not_not] at h
  rw [sSup_eq h.1 h.2, isLUB_coe_iff]
  exact ⟨h.1, isLUB_csSup (hs.preimage' <| by simp [isCompl_range_coe.eq_compl, h.1]) h.2⟩

theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [sSup]
  · exact isLUB_sSup' hs

/-- The `sInf` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
@[to_dual]
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  by_cases h : s ⊆ {⊤}
  · rw [sInf_eq_top_iff.2 (.inl h)]
    exact isGLB_top_iff.2 h
  rw [sInf_eq h hs, isGLB_coe_iff]
  rw [← inter_compl_nonempty_iff, ← isCompl_range_coe.eq_compl, ← nonempty_preimage_iff] at h ⊢
  have := h.nonempty
  exact ⟨h, isGLB_csInf h (bddBelow_preimage_coe.mpr hs)⟩

theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) :=
  isGLB_sInf' (OrderBot.bddBelow _)

noncomputable instance : CompleteLinearOrder (WithTop α) where
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra
  isLUB_sSup := isLUB_sSup
  isGLB_sInf := isGLB_sInf

/-- A version of `WithTop.coe_sSup'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sSup' hb, sSup_image]

/-- A version of `WithTop.coe_sInf'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sInf' hs h's, sInf_image]

end WithTop

section WithTopBot

/-!
### Complete lattice structure on `WithTop (WithBot α)`

If `α` is a `ConditionallyCompleteLattice`, then we show that `WithTop α` and `WithBot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `WithTop (WithBot α)` and `WithBot (WithTop α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `sSup` and `sInf` both return
junk values for sets which are empty or unbounded. The extension of `sSup` to `WithTop α` fixes
the unboundedness problem and the extension to `WithBot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
-/


/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
@[to_dual
/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/]
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) where
  exists_isLUB_cond _ hS _ := ⟨_, WithTop.isLUB_sSup' hS⟩
  exists_isGLB_cond _ _ hS := ⟨_, WithTop.isGLB_sInf' hS⟩

@[to_dual]
noncomputable instance [CompleteLattice α] : CompleteLattice (WithTop α) := inferInstance

noncomputable instance [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrder (WithTop α) where
  le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  csSup_of_not_bddAbove s := absurd <| OrderTop.bddAbove s
  csInf_of_not_bddBelow s h := by simp [h]

noncomputable instance [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrderBot (WithBot α) where
  le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  csSup_of_not_bddAbove s h := by simp [h]
  csInf_of_not_bddBelow s := absurd <| OrderBot.bddBelow s

noncomputable instance [CompleteLinearOrder α] : CompleteLinearOrder (WithBot α) := inferInstance

@[to_dual WithBot.WithTop.completeLattice]
noncomputable instance WithTop.WithBot.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) := inferInstance

noncomputable instance {α : Type*} [ConditionallyCompleteLattice α] :
    CompleteLattice (WithBot (WithTop α)) := inferInstance

noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) :=
  inferInstance

end WithTopBot

section

/-!
Extension of `iSup` and `iInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [Preorder α]

@[to_dual]
theorem WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    ⨅ i, f i = ⊤ := by
  simp

@[to_dual (attr := norm_cast)]
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι → α} (hf : BddBelow (range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf, iInf, WithTop.coe_sInf' (range_nonempty f) hf, ← range_comp, Function.comp_def]

@[to_dual (attr := norm_cast)]
theorem WithTop.coe_iSup [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
  rw [iSup, iSup, WithTop.coe_sSup' h, ← range_comp, Function.comp_def]

@[deprecated (since := "2026-05-04")] alias WithBot.ciSup_empty := WithBot.iSup_empty

@[to_dual]
theorem WithBot.coe_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty)
    {α : Type*} [CompleteLattice α] (f : ι → α) :
    ⨆ i ∈ s, f i = ⨆ i ∈ s, (f i : WithBot α) := by
  rcases hs with ⟨j, hj⟩
  have : Nonempty ι := Nonempty.intro j
  refine le_antisymm ((WithBot.coe_iSup (OrderTop.bddAbove _)).trans_le <|
    iSup_le_iff.mpr fun i ↦ ?_) <| iSup_le_iff.mpr <| fun _ ↦ iSup_le_iff.mpr <|
      fun hi ↦ WithBot.coe_le_coe.mpr (le_biSup _ hi)
  by_cases h : i ∈ s
  · simpa only [iSup_pos h] using by apply le_biSup _ h
  · simpa only [iSup_neg h] using le_trans (by simp) (le_biSup _ hj)

@[to_dual]
theorem WithBot.coe_biInf {ι : Type*} {s : Set ι} {α : Type*} [CompleteLattice α] (f : ι → α) :
    ⨅ i ∈ s, f i = ⨅ i ∈ s, (f i : WithBot α) := by
  simp [coe_iInf]

end

section WithTopBot

namespace WithTop
variable [ConditionallyCompleteLinearOrder α] [OrderBot α] {f : ι → α}

lemma iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f) := by
  rw [iSup_eq_top, not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩

lemma iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f) :=
  lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left

lemma iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι := by simp [isEmpty_iff]

lemma iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι := by
  rw [lt_top_iff_ne_top, Ne, iInf_coe_eq_top, not_isEmpty_iff]

end WithTop

end WithTopBot
