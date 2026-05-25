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

theorem Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
    {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
  refine ⟨fun h_lt x hx ↦ ?_, fun h_lt ↦ ?_⟩
  · exact h_lt.trans_le (csInf_le (by simp) ⟨x, by simp [hx]⟩)
  · have : ⨅ i ∈ s, f i ∈ f '' s := hs.ciInf_mem_image f (by simpa using h)
    grind

lemma iInf_eq_bot_iff_of_finite {α ι : Type*} [CompleteLinearOrder α] [Finite ι] [Nonempty ι]
    {f : ι → α} : (⨅ i, f i) = ⊥ ↔ ∃ i, f i = ⊥ := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ le_antisymm ((iInf_le _ i).trans_eq hi) bot_le⟩
  by_contra! h'
  simp_rw [← bot_lt_iff_ne_bot] at h'
  have h'' : ∀ i ∈ (Set.univ : Set ι), ⊥ < f i := by simpa
  rw [← Set.Finite.lt_iInf_iff (by simp) Set.finite_univ] at h''
  simp only [Set.mem_univ, iInf_pos] at h''
  exact h''.ne' h
