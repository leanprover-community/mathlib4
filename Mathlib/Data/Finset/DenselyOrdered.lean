/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic

/-!
# Dense orders and finsets

We prove that in a dense order, there's always an element lying in between any two finite sets of
elements.
-/

public section

variable {α : Type*} [LinearOrder α] [DenselyOrdered α]

theorem Finset.exists_between {s t : Finset α}
    (hs : s.Nonempty) (ht : t.Nonempty) (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp

theorem Finset.exists_between' (s t : Finset α) [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · exact s.exists_between hs ht H
  · exact let ⟨p, hp⟩ := exists_gt (s.max' hs); ⟨p, by simp_all⟩
  · exact let ⟨p, hp⟩ := exists_lt (t.min' ht); ⟨p, by simp_all⟩
  · exact Nonempty.elim ‹_› fun p ↦ ⟨p, by simp_all⟩

theorem Set.Finite.exists_between {s t : Set α}
    (hsf : s.Finite) (hs : s.Nonempty) (htf : t.Finite) (ht : t.Nonempty)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert Finset.exists_between (s := hsf.toFinset) (t := htf.toFinset)
    (by simpa) (by simpa) (by simpa) using 1; simp

theorem Set.Finite.exists_between' [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert hs.toFinset.exists_between' ht.toFinset (by simpa) using 1; simp
