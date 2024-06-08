/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

#align_import data.list.pairwise from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable {α β : Type*} {R S T : α → α → Prop} {a : α} {l : List α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff
#align list.pairwise_iff List.pairwise_iff

/-! ### Pairwise -/

#align list.pairwise.nil List.Pairwise.nil
#align list.pairwise.cons List.Pairwise.cons

#align list.rel_of_pairwise_cons List.rel_of_pairwise_cons

#align list.pairwise.of_cons List.Pairwise.of_cons

#align list.pairwise.tail List.Pairwise.tail

#align list.pairwise.drop List.Pairwise.drop

#align list.pairwise.imp_of_mem List.Pairwise.imp_of_mem

#align list.pairwise.imp List.Pairwise.impₓ -- Implicits Order

#align list.pairwise_and_iff List.pairwise_and_iff

#align list.pairwise.and List.Pairwise.and

#align list.pairwise.imp₂ List.Pairwise.imp₂

#align list.pairwise.iff_of_mem List.Pairwise.iff_of_mem

#align list.pairwise.iff List.Pairwise.iff

#align list.pairwise_of_forall List.pairwise_of_forall

#align list.pairwise.and_mem List.Pairwise.and_mem

#align list.pairwise.imp_mem List.Pairwise.imp_mem

#align list.pairwise.sublist List.Pairwise.sublistₓ -- Implicits order

#align list.pairwise.forall_of_forall_of_flip List.Pairwise.forall_of_forall_of_flip

theorem Pairwise.forall_of_forall (H : Symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [H.flip_eq]
#align list.pairwise.forall_of_forall List.Pairwise.forall_of_forall

theorem Pairwise.forall (hR : Symmetric R) (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  apply Pairwise.forall_of_forall
  · exact fun a b h hne => hR (h hne.symm)
  · exact fun _ _ hx => (hx rfl).elim
  · exact hl.imp (@fun a b h _ => by exact h)
#align list.pairwise.forall List.Pairwise.forall

theorem Pairwise.set_pairwise (hl : Pairwise R l) (hr : Symmetric R) : { x | x ∈ l }.Pairwise R :=
  hl.forall hr
#align list.pairwise.set_pairwise List.Pairwise.set_pairwise

#align list.pairwise_singleton List.pairwise_singleton

#align list.pairwise_pair List.pairwise_pair

#align list.pairwise_append List.pairwise_append

#align list.pairwise_append_comm List.pairwise_append_comm

#align list.pairwise_middle List.pairwise_middle

-- Porting note: Duplicate of `pairwise_map` but with `f` explicit.
@[deprecated] theorem pairwise_map' (f : β → α) : -- 2024-02-25
    ∀ {l : List β}, Pairwise R (map f l) ↔ Pairwise (fun a b : β => R (f a) (f b)) l
  | [] => by simp only [map, Pairwise.nil]
  | b :: l => by
    simp only [map, pairwise_cons, mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, pairwise_map]
#align list.pairwise_map List.pairwise_map'

#align list.pairwise.of_map List.Pairwise.of_map

#align list.pairwise.map List.Pairwise.map

#align list.pairwise_filter_map List.pairwise_filterMap

#align list.pairwise.filter_map List.Pairwise.filter_map

#align list.pairwise_filter List.pairwise_filter

#align list.pairwise.filter List.Pairwise.filterₓ

theorem pairwise_pmap {p : β → Prop} {f : ∀ b, p b → α} {l : List β} (h : ∀ x ∈ l, p x) :
    Pairwise R (l.pmap f h) ↔
      Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l := by
  induction' l with a l ihl
  · simp
  obtain ⟨_, hl⟩ : p a ∧ ∀ b, b ∈ l → p b := by simpa using h
  simp only [ihl hl, pairwise_cons, exists₂_imp, pmap, and_congr_left_iff, mem_pmap]
  refine fun _ => ⟨fun H b hb _ hpb => H _ _ hb rfl, ?_⟩
  rintro H _ b hb rfl
  exact H b hb _ _
#align list.pairwise_pmap List.pairwise_pmap

theorem Pairwise.pmap {l : List α} (hl : Pairwise R l) {p : α → Prop} {f : ∀ a, p a → β}
    (h : ∀ x ∈ l, p x) {S : β → β → Prop}
    (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) :
    Pairwise S (l.pmap f h) := by
  refine (pairwise_pmap h).2 (Pairwise.imp_of_mem ?_ hl)
  intros; apply hS; assumption
#align list.pairwise.pmap List.Pairwise.pmap

#align list.pairwise_join List.pairwise_join

#align list.pairwise_bind List.pairwise_bind

#align list.pairwise_reverse List.pairwise_reverse

#align list.pairwise_of_reflexive_on_dupl_of_forall_ne List.pairwise_of_reflexive_on_dupl_of_forall_ne

theorem pairwise_of_forall_mem_list {l : List α} {r : α → α → Prop} (h : ∀ a ∈ l, ∀ b ∈ l, r a b) :
    l.Pairwise r := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  apply h <;> (apply hab.subset; simp)
#align list.pairwise_of_forall_mem_list List.pairwise_of_forall_mem_list

theorem pairwise_of_reflexive_of_forall_ne {l : List α} {r : α → α → Prop} (hr : Reflexive r)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply hr
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq
#align list.pairwise_of_reflexive_of_forall_ne List.pairwise_of_reflexive_of_forall_ne

set_option linter.deprecated false in
@[deprecated pairwise_iff_get (since := "2023-01-10")]
theorem pairwise_iff_nthLe {R} {l : List α} : Pairwise R l ↔
    ∀ (i j) (h₁ : j < length l) (h₂ : i < j), R (nthLe l i (lt_trans h₂ h₁)) (nthLe l j h₁) :=
  pairwise_iff_get.trans
    ⟨fun h i j _ h₂ => h ⟨i, _⟩ ⟨j, _⟩ h₂,
     fun h i j hij => h i j _ hij⟩
#align list.pairwise_iff_nth_le List.pairwise_iff_nthLe

#align list.pairwise_replicate List.pairwise_replicate

/-! ### Pairwise filtering -/


variable [DecidableRel R]

#align list.pw_filter_nil List.pwFilter_nil

#align list.pw_filter_cons_of_pos List.pwFilter_cons_of_pos

#align list.pw_filter_cons_of_neg List.pwFilter_cons_of_neg

#align list.pw_filter_map List.pwFilter_map

#align list.pw_filter_sublist List.pwFilter_sublist

#align list.pw_filter_subset List.pwFilter_subset

#align list.pairwise_pw_filter List.pairwise_pwFilter

#align list.pw_filter_eq_self List.pwFilter_eq_self

alias ⟨_, Pairwise.pwFilter⟩ := pwFilter_eq_self
#align list.pairwise.pw_filter List.Pairwise.pwFilter

-- Porting note: commented out
-- attribute [protected] List.Pairwise.pwFilter

#align list.pw_filter_idempotent List.pwFilter_idem

#align list.forall_mem_pw_filter List.forall_mem_pwFilter

end List
