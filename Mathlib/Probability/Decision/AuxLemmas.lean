/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# AuxLemmas
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

lemma Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
    {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
  rw [Set.Finite.lt_ciInf_iff hs]
  simpa

lemma Set.Finite.biInf_eq_bot_iff {α ι : Type*} [CompleteLinearOrder α] {s : Set ι} {f : ι → α}
    (hs : s.Nonempty) (hs' : s.Finite) :
    (⨅ i ∈ s, f i) = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  refine ⟨fun h ↦ ?_, fun ⟨i, his, hi⟩ ↦ le_antisymm ((biInf_le f his).trans_eq hi) bot_le⟩
  by_contra! h'
  simp_rw [← bot_lt_iff_ne_bot] at h'
  rw [← Set.Finite.lt_iInf_iff hs hs'] at h'
  exact h'.ne' h

lemma iInf_eq_bot_iff_of_finite {α ι : Type*} [CompleteLinearOrder α] [Finite ι] [Nonempty ι]
    {f : ι → α} :
    (⨅ i, f i) = ⊥ ↔ ∃ i, f i = ⊥ := by
  rw [← iInf_univ, Set.Finite.biInf_eq_bot_iff (by simp) (by simp)]
  simp
