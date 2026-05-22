/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.DirSupClosed.Basic

import Mathlib.Data.Nat.Lattice

/-!
# Finite sets are closed under suprema
-/

public section

variable {α : Type*} [PartialOrder α]

theorem Set.Finite.dirSupClosed {s : Set α} (hs : s.Finite) : DirSupClosed s := by
  induction s, hs using induction_on with
  | empty => exact .empty
  | insert has _ hs₁ =>
    rw [Set.insert_eq]
    exact (DirSupClosed.singleton _).union hs₁

theorem dirSupClosed_range_nat {f : ℕ → α} (hf : Monotone f) (hf' : IsCofinal (.range f)) :
    DirSupClosed (.range f) := by
  intro s hs hs₀ hs₁ a ha
  obtain ⟨_, ⟨n, rfl⟩, han⟩ := hf' a
  obtain rfl | han := han.eq_or_lt
  · simp
  have hfb : BddAbove (f ⁻¹' s) := by
    refine ⟨n, fun m hm ↦ ?_⟩
    by_contra! hnm
    exact (ha.1 hm).not_gt (han.trans_le (hf hnm.le))
  refine ⟨sSup (f ⁻¹' s), IsLUB.unique ⟨?_, ?_⟩ ha⟩ <;> intro x hx
  · obtain ⟨m, rfl⟩ := hs hx
    exact hf (le_csSup hfb hx)
  · apply hx (Nat.sSup_mem _ hfb)
    obtain ⟨x, hx⟩ := hs₀
    obtain ⟨m, rfl⟩ := hs hx
    exact ⟨m, hx⟩
