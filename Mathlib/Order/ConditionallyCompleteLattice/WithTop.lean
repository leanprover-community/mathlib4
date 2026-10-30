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

section LE

namespace WithTop

/-!
Extension of `sSup` and `sInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [LE α]

open scoped Classical in
@[to_dual]
noncomputable instance [SupSet α] : SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) ↦ (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

open scoped Classical in
@[to_dual]
noncomputable instance instInfSet [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α))⟩

@[to_dual]
theorem sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  (ite_eq_right hs).trans <| ite_eq_left hs'

@[to_dual]
theorem sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) (h's : BddBelow s) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  ite_eq_right <| by simp [hs, h's]

@[to_dual (attr := simp)]
theorem sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
  ite_eq_left <| by simp

@[to_dual (attr := simp)]
theorem sInf_singleton_top [InfSet α] : sInf ({⊤} : Set (WithTop α)) = ⊤ :=
  ite_eq_left <| .inl subset_rfl

@[to_dual (attr := simp)]
theorem sSup_of_top_mem [SupSet α] {s : Set (WithTop α)} (h : ⊤ ∈ s) : sSup s = ⊤ :=
  ite_eq_left h

@[to_dual]
theorem sSup_singleton_top [SupSet α] : sSup ({⊤} : Set (WithTop α)) = ⊤ := by
  simp

@[to_dual]
theorem sSup_of_not_bddAbove [SupSet α] {s : Set (WithTop α)}
    (h : ¬BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ⊤ := by
  by_cases hmem : ⊤ ∈ s
  · exact sSup_of_top_mem hmem
  · exact ite_eq_right hmem |>.trans <| ite_eq_right h

@[to_dual (attr := simp)]
theorem sInf_of_not_bddBelow [InfSet α] {s : Set (WithTop α)} (h : ¬BddBelow s) :
    sInf s = ⊤ :=
  ite_eq_left <| .inr h

@[to_dual (attr := norm_cast)]
theorem coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  change _ = ite _ _ _
  rw [ite_eq_right, preimage_image_eq, ite_eq_left hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩

@[to_dual]
theorem sSup_empty (α : Type*) [CompleteLattice α] : (sSup ∅ : WithTop α) = ⊥ := by
  rw [sSup_eq (by simp) (OrderTop.bddAbove _), Set.preimage_empty, _root_.sSup_empty, coe_bot]

end WithTop

end LE

section Preorder

variable [Preorder α]

@[to_dual (attr := norm_cast)]
theorem WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty)
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

namespace WithTop

variable [ConditionallyCompleteLinearOrderBot α]

/-- The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
@[to_dual]
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  classical
  constructor
  · change ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply coe_le_coe.2
      exact le_csSup h₂ ha
    · intro _ _
      exact le_top
  · change ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine coe_le_coe.2 (csSup_le ?_ ?_)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact coe_le_coe.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact coe_le_coe.1 (hb ha)

theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [sSup]
  · exact isLUB_sSup' hs

/-- The `sInf` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
@[to_dual]
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  classical
  constructor
  · change ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine coe_le_coe.2 (csInf_le ?_ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff, ← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact coe_le_coe.1 (hb hc)
  · change ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine coe_le_coe.2 (le_csInf ?_ ?_)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (not_nonempty_iff_eq_empty.2 h ⟨a, ha⟩).elim
        · intro b hb
          rw [← coe_le_coe]
          exact ha hb

theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) := by
  by_cases hs : BddBelow s
  · exact isGLB_sInf' hs
  · exact isGLB_sInf' (OrderBot.bddBelow _)

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
  isLUB_csSup _ hS _ := WithTop.isLUB_sSup' hS
  isGLB_csInf _ _ hS := WithTop.isGLB_sInf' hS

@[to_dual]
noncomputable instance [CompleteLattice α] : CompleteLattice (WithTop α) where
  isLUB_sSup s := ⟨fun _ ↦ le_csSup (OrderTop.bddAbove _), fun _ has ↦
    s.eq_empty_or_nonempty.elim (by simp [·, WithTop.sSup_empty]) (csSup_le · has)⟩
  isGLB_sInf s := ⟨fun _ ↦ csInf_le (OrderBot.bddBelow _), fun _ hsa ↦
    s.eq_empty_or_nonempty.elim (by simp [·]) (le_csInf · hsa)⟩

noncomputable instance [CompleteLinearOrder α] : CompleteLinearOrder (WithBot α) where
  __ := WithBot.linearOrder
  __ := WithBot.linearOrder.toBiheytingAlgebra
  __ := show CompleteLattice (WithBot α) from inferInstance

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
  csSup_empty := WithBot.sSup_empty

open scoped Classical in
@[to_dual WithBot.WithTop.completeLattice]
noncomputable instance WithTop.WithBot.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) where
  isLUB_sSup S := ⟨fun a haS ↦ (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS, fun a ha ↦ by
    rcases S.eq_empty_or_nonempty with h | h
    · change ite _ _ _ ≤ a
      simp [h]
    · exact (WithTop.isLUB_sSup' h).2 ha⟩
  isGLB_sInf S := ⟨fun a haS ↦
    show ite _ _ _ ≤ a by
      simp only [OrderBot.bddBelow, not_true_eq_false, or_false]
      split_ifs with h₁
      · cases a
        · exact le_rfl
        cases h₁ haS
      · cases a
        · exact le_top
        · apply WithTop.coe_le_coe.2
          refine csInf_le ?_ haS
          use ⊥
          intro b _
          exact bot_le,
    fun a haS ↦ (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS⟩

noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) where
  __ := completeLattice
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra

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
variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α}

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
