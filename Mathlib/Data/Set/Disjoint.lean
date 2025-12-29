/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Theorems about the `Disjoint` and `Codisjoint relations on `Set`.
-/

@[expose] public section

assert_not_exists HeytingAlgebra RelIso

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t u s₁ s₂ t₁ t₂ : Set α}


/-! ### Disjointness -/

protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  disjoint_iff_inf_le

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

theorem _root_.Disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot

@[grind =]
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  disjoint_iff_inf_le.trans <| forall_congr' fun _ => not_and

alias ⟨_root_.Disjoint.notMem_of_mem_left, _⟩ := disjoint_left

@[deprecated (since := "2025-05-23")]
alias _root_.Disjoint.not_mem_of_mem_left := Disjoint.notMem_of_mem_left

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right, _⟩ := disjoint_right

@[deprecated (since := "2025-05-23")]
alias _root_.Disjoint.not_mem_of_mem_right := Disjoint.notMem_of_mem_right

lemma not_disjoint_iff : ¬Disjoint s t ↔ ∃ x, x ∈ s ∧ x ∈ t := by grind

lemma not_disjoint_iff_nonempty_inter : ¬ Disjoint s t ↔ (s ∩ t).Nonempty := not_disjoint_iff

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

lemma disjoint_or_nonempty_inter (s t : Set α) : Disjoint s t ∨ (s ∩ t).Nonempty :=
  (em _).imp_right not_disjoint_iff_nonempty_inter.1

lemma disjoint_iff_forall_ne : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ t → a ≠ b := by grind

alias ⟨_root_.Disjoint.ne_of_mem, _⟩ := disjoint_iff_forall_ne

lemma disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t := d.mono_left h
lemma disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t := d.mono_right h

@[gcongr high]
lemma disjoint_of_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁ :=
  h.mono hs ht

@[simp]
lemma disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := disjoint_sup_left

@[simp]
lemma disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right

@[simp] lemma disjoint_empty (s : Set α) : Disjoint s ∅ := disjoint_bot_right
@[simp] lemma empty_disjoint (s : Set α) : Disjoint ∅ s := disjoint_bot_left

@[simp] lemma univ_disjoint : Disjoint univ s ↔ s = ∅ := top_disjoint
@[simp] lemma disjoint_univ : Disjoint s univ ↔ s = ∅ := disjoint_top

theorem disjoint_range_iff {β γ : Sort*} {x : β → α} {y : γ → α} :
    Disjoint (range x) (range y) ↔ ∀ i j, x i ≠ y j := by
  simp [Set.disjoint_iff_forall_ne]

/-! # Codisjointness -/

-- TODO goes in `Mathlib.Data.Set.Disjoint`
protected theorem codisjoint_iff {α} {s t : Set α} :
    Codisjoint s t ↔ s ∪ t = univ := by rw [_root_.codisjoint_iff]; rfl

@[grind =]
theorem codisjoint_left : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t :=
  codisjoint_iff_le_sup.trans <| forall_congr' fun _ => by simpa using by tauto

alias ⟨_root_.Codisjoint.mem_of_notMem_left, _⟩ := codisjoint_left

theorem codisjoint_right : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s := by
  rw [codisjoint_comm, codisjoint_left]

alias ⟨_root_.Codisjoint.mem_of_notMem_right, _⟩ := disjoint_right

lemma not_codisjoint_iff : ¬Codisjoint s t ↔ ∃ x, x ∉ s ∧ x ∉ t := by grind

alias codisjoint_iff_union_eq_univ := Set.codisjoint_iff

alias ⟨_root_.Codisjoint.union_eq, _⟩ := Set.codisjoint_iff_union_eq_univ

lemma codisjoint_iff_forall_ne : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → ∀ ⦃b⦄, b ∉ t → a ≠ b := by grind

alias ⟨_root_.Codisjoint.ne_of_notMem, _⟩ := disjoint_iff_forall_ne

lemma codisjoint_of_subset_left (h : s ⊆ u) (c : Codisjoint s t) : Codisjoint u t := c.mono_left h

lemma codisjoint_of_subset_right (h : t ⊆ u) (c : Codisjoint s t) : Codisjoint s u :=
  c.mono_right h

@[gcongr high]
lemma codisjoint_of_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (h : Codisjoint s₁ t₁) :
    Codisjoint s₂ t₂ := h.mono hs ht

@[simp]
lemma codisjoint_inter_left : Codisjoint (s ∩ t) u ↔ Codisjoint s u ∧ Codisjoint t u :=
  codisjoint_inf_left

@[simp]
lemma codisjoint_inter_right : Codisjoint s (t ∩ u) ↔ Codisjoint s t ∧ Codisjoint s u :=
  codisjoint_inf_right

@[simp] lemma codisjoint_univ (s : Set α) : Codisjoint s univ := codisjoint_top_right
@[simp] lemma univ_codisjoint (s : Set α) : Codisjoint univ s := codisjoint_top_left

@[simp] lemma empty_codisjoint : Codisjoint ∅ s ↔ s = univ := bot_codisjoint
@[simp] lemma codisjoint_empty : Codisjoint s ∅ ↔ s = univ := codisjoint_bot

theorem codisjoint_range_iff {β γ : Sort*} {x : β → α} {y : γ → α} :
    Codisjoint (range x) (range y) ↔ ∀ a, (∃ i, x i = a) ∨ (∃ j, y j = a) := by
  contrapose!; simp [Set.codisjoint_iff_forall_ne]

end Set


/-! ### Disjoint sets -/

variable {α : Type*} {s t u : Set α}

namespace Disjoint

theorem union_left (hs : Disjoint s u) (ht : Disjoint t u) : Disjoint (s ∪ t) u :=
  hs.sup_left ht

theorem union_right (ht : Disjoint s t) (hu : Disjoint s u) : Disjoint s (t ∪ u) :=
  ht.sup_right hu

theorem inter_left (u : Set α) (h : Disjoint s t) : Disjoint (s ∩ u) t :=
  h.inf_left _

theorem inter_left' (u : Set α) (h : Disjoint s t) : Disjoint (u ∩ s) t :=
  h.inf_left' _

theorem inter_right (u : Set α) (h : Disjoint s t) : Disjoint s (t ∩ u) :=
  h.inf_right _

theorem inter_right' (u : Set α) (h : Disjoint s t) : Disjoint s (u ∩ t) :=
  h.inf_right' _

theorem subset_left_of_subset_union (h : s ⊆ t ∪ u) (hac : Disjoint s u) : s ⊆ t :=
  hac.left_le_of_le_sup_right h

theorem subset_right_of_subset_union (h : s ⊆ t ∪ u) (hab : Disjoint s t) : s ⊆ u :=
  hab.left_le_of_le_sup_left h

end Disjoint

namespace Set

theorem mem_union_of_disjoint (h : Disjoint s t) {x : α} : x ∈ s ∪ t ↔ Xor' (x ∈ s) (x ∈ t) := by
  grind [Xor']

end Set
