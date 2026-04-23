/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Aesop.BuiltinRules
import Batteries.Tactic.Init
import Batteries.Tactic.Trans
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# List Sub-permutations

This file develops theory about the `List.Subperm` relation.

## Notation

The notation `<+~` is used for sub-permutations.
-/

public section

open Nat

namespace List
variable {α : Type*} {l l₁ l₂ : List α} {a : α}

open Perm

section Subperm

attribute [trans] Subperm.trans

end Subperm

/-- See also `List.subperm_ext_iff`. -/
lemma subperm_iff_count [DecidableEq α] : l₁ <+~ l₂ ↔ ∀ a, count a l₁ ≤ count a l₂ :=
  subperm_ext_iff.trans <| forall_congr' fun a ↦ by
    by_cases ha : a ∈ l₁ <;> simp [ha, count_eq_zero_of_not_mem]

lemma subperm_iff : l₁ <+~ l₂ ↔ ∃ l, l ~ l₂ ∧ l₁ <+ l := by
  refine ⟨?_, fun ⟨l, h₁, h₂⟩ ↦ h₂.subperm.trans h₁.subperm⟩
  rintro ⟨l, h₁, h₂⟩
  obtain ⟨l', h₂⟩ := h₂.exists_perm_append
  exact ⟨l₁ ++ l', (h₂.trans (h₁.append_right _)).symm, (prefix_append _ _).sublist⟩

@[simp] lemma subperm_singleton_iff : l <+~ [a] ↔ l = [] ∨ l = [a] := by
  constructor
  · rw [subperm_iff]
    rintro ⟨s, hla, h⟩
    rwa [perm_singleton.mp hla, sublist_singleton] at h
  · rintro (rfl | rfl)
    exacts [nil_subperm, Subperm.refl _]

lemma subperm_cons_self : l <+~ a :: l := ⟨l, Perm.refl _, sublist_cons_self _ _⟩

protected alias ⟨subperm.of_cons, subperm.cons⟩ := subperm_cons

theorem Subperm.append {l₁ l₂ r₁ r₂ : List α} :
    l₁ <+~ l₂ → r₁ <+~ r₂ → (l₁ ++ r₁) <+~ (l₂ ++ r₂)
  | ⟨l, hl_perm, hl_sub⟩, ⟨r, hr_perm, hr_sub⟩ =>
    ⟨l ++ r, hl_perm.append hr_perm, hl_sub.append hr_sub⟩

theorem map_subperm_map_iff {α β} {l₁ l₂ : List α} {f : α → β} (hf : Function.Injective f) :
    (l₁.map f) <+~ (l₂.map f) ↔ l₁ <+~ l₂ where
  mpr a := by
    obtain ⟨l, hl_perm, hl_sub⟩ := a
    exact ⟨l.map f, hl_perm.map f, hl_sub.map f⟩
  mp a := by
    obtain ⟨w, ⟨perm, sublist⟩⟩ := a
    obtain ⟨x, ⟨sublistₓ, mapₓ⟩⟩ := sublist_map_iff.mp sublist
    use x
    constructor
    · rw [mapₓ] at perm
      exact (map_perm_map_iff hf).mp perm
    · exact sublistₓ

alias ⟨_, Subperm.map⟩ := map_subperm_map_iff

protected theorem Nodup.subperm (d : Nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ :=
  subperm_of_subset d H

end List
