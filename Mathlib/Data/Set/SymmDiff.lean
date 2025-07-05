/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.SymmDiff

/-! # Symmetric differences of sets -/

public section

assert_not_exists RelIso

open Function

namespace Set
variable {α β : Type*} {a : α} {s t u : Set α} {f : α → β}

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

lemma image_symmDiff (hf : Injective f) (s t : Set α) : f '' s ∆ t = (f '' s) ∆ (f '' t) := by
  simp_rw [Set.symmDiff_def, image_union, image_diff hf]

lemma subset_image_symmDiff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
  (union_subset_union (subset_image_diff _ _ _) <| subset_image_diff _ _ _).trans
    (image_union _ _ _).superset

@[simp]
lemma preimage_symmDiff {f : α → β} (s t : Set β) : f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) := rfl

end Set
