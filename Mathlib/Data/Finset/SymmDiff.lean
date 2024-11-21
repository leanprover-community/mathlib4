/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Set.SymmDiff

/-!
# Symmetric difference of finite sets

This file concerns the symmetric difference operator `s Δ t` on finite sets.

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen
assert_not_exists Multiset.powerset

assert_not_exists CompleteLattice

assert_not_exists OrderedCommMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

/-! ### Symmetric difference -/

section SymmDiff

open scoped symmDiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]

@[simp, norm_cast]
theorem coe_symmDiff : (↑(s ∆ t) : Set α) = (s : Set α) ∆ t :=
  Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]

@[simp] lemma symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t := symmDiff_eq_bot
@[simp] lemma symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

end SymmDiff

end Finset
