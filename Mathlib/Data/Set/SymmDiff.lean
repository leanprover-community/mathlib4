/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.SymmDiff

/-! # Symmetric differences of sets -/

assert_not_exists RelIso

namespace Set

universe u
variable {α : Type u} {a : α} {s t u : Set α}

open scoped symmDiff

theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s :=
  Iff.rfl

protected theorem symmDiff_def (s t : Set α) : s ∆ t = s \ t ∪ t \ s :=
  rfl

theorem symmDiff_subset_union : s ∆ t ⊆ s ∪ t :=
  @symmDiff_le_sup (Set α) _ _ _

@[simp]
theorem symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t :=
  symmDiff_eq_bot

@[simp]
theorem symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

theorem inter_symmDiff_distrib_left (s t u : Set α) : s ∩ t ∆ u = (s ∩ t) ∆ (s ∩ u) :=
  inf_symmDiff_distrib_left _ _ _

theorem inter_symmDiff_distrib_right (s t u : Set α) : s ∆ t ∩ u = (s ∩ u) ∆ (t ∩ u) :=
  inf_symmDiff_distrib_right _ _ _

theorem subset_symmDiff_union_symmDiff_left (h : Disjoint s t) : u ⊆ s ∆ u ∪ t ∆ u :=
  h.le_symmDiff_sup_symmDiff_left

theorem subset_symmDiff_union_symmDiff_right (h : Disjoint t u) : s ⊆ s ∆ t ∪ s ∆ u :=
  h.le_symmDiff_sup_symmDiff_right

end Set
