/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.List.Pairwise
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Relation

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise R [a 0, ..., a (n - 1)]` means `∀ i j, i < j → R (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter R l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise R l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable {α β : Type*} {R : α → α → Prop} {l : List α} {a : α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff

/-! ### Pairwise -/

theorem Pairwise.forall_of_forall (H : Symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [H.flip_eq]

theorem Pairwise.forall (hR : Symmetric R) (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  apply Pairwise.forall_of_forall
  · exact fun a b h hne => hR (h hne.symm)
  · exact fun _ _ hx => (hx rfl).elim
  · exact hl.imp (@fun a b h _ => by exact h)

theorem Pairwise.set_pairwise (hl : Pairwise R l) (hr : Symmetric R) : { x | x ∈ l }.Pairwise R :=
  hl.forall hr

theorem pairwise_of_reflexive_of_forall_ne (hr : Reflexive R)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) : l.Pairwise R := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply hr
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

theorem Pairwise.rel_head_tail (h₁ : l.Pairwise R) (ha : a ∈ l.tail) :
    R (l.head <| ne_nil_of_mem <| mem_of_mem_tail ha) a := by
  cases l with
  | nil => simp at ha
  | cons b l => exact (pairwise_cons.1 h₁).1 a ha

theorem Pairwise.rel_head_of_rel_head_head (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hhead : R (l.head <| ne_nil_of_mem ha) (l.head <| ne_nil_of_mem ha)) :
    R (l.head <| ne_nil_of_mem ha) a := by
  cases l with
  | nil => simp at ha
  | cons b l => exact (mem_cons.mp ha).elim (· ▸ hhead) ((pairwise_cons.1 h₁).1 _)

theorem Pairwise.rel_head [IsRefl α R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R (l.head <| ne_nil_of_mem ha) a :=
  h₁.rel_head_of_rel_head_head ha (refl_of ..)

theorem Pairwise.rel_dropLast_getLast (h : l.Pairwise R) (ha : a ∈ l.dropLast) :
    R a (l.getLast <| ne_nil_of_mem <| dropLast_subset _ ha) := by
  rw [← pairwise_reverse] at h
  rw [getLast_eq_head_reverse]
  exact h.rel_head_tail (by rwa [tail_reverse, mem_reverse])

theorem Pairwise.rel_getLast_of_rel_getLast_getLast (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hlast : R (l.getLast <| ne_nil_of_mem ha) (l.getLast <| ne_nil_of_mem ha)) :
    R a (l.getLast <| ne_nil_of_mem ha) := by
  rw [← dropLast_concat_getLast (ne_nil_of_mem ha), mem_append, List.mem_singleton] at ha
  exact ha.elim h₁.rel_dropLast_getLast (· ▸ hlast)

theorem Pairwise.rel_getLast [IsRefl α R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R a (l.getLast <| ne_nil_of_mem ha) :=
  h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

protected alias ⟨Pairwise.of_reverse, Pairwise.reverse⟩ := pairwise_reverse

theorem Pairwise.head!_le [Inhabited α] [IsRefl α R] (h : l.Pairwise R)
    (ha : a ∈ l) : R l.head! a := by
  cases l
  · contradiction
  · cases ha with
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)

@[deprecated (since := "2025-10-11")]
alias Sorted.head!_le := Pairwise.head!_le

@[deprecated (since := "2025-10-11")]
alias Sorted.le_head! := Pairwise.head!_le

theorem pairwise_replicate_of_refl {n} [IsRefl α R] : (replicate n a).Pairwise R :=
  pairwise_replicate.mpr  (Or.inr <| refl_of ..)

@[deprecated (since := "2025-10-11")]
alias sorted_replicate := pairwise_replicate_of_refl

/-! ### Pairwise filtering -/

protected alias ⟨_, Pairwise.pwFilter⟩ := pwFilter_eq_self

theorem pairwise_cons_cons_iff_of_trans [IsTrans α R] {l : List α} {a b : α} :
    Pairwise R (a :: b :: l) ↔ R a b ∧ Pairwise R (b :: l) := by
  simp_rw [← isChain_iff_pairwise, isChain_cons_cons]

@[deprecated (since := "2025-10-11")]
alias sorted_cons_cons := pairwise_cons_cons_iff_of_trans

theorem Pairwise.cons_cons_of_trans [IsTrans α R] {l : List α} {a b : α} :
    R a b → Pairwise R (b :: l) → Pairwise R (a :: b :: l) := by
  simp_rw [pairwise_cons_cons_iff_of_trans]
  exact And.intro

@[deprecated (since := "2025-10-11")]
alias Sorted.cons := Pairwise.cons_cons_of_trans

theorem Pairwise.rel_get_of_lt {l : List α} (h : l.Pairwise R) {a b : Fin l.length} (hab : a < b) :
    R (l.get a) (l.get b) :=
  List.pairwise_iff_get.1 h _ _ hab

@[deprecated (since := "2025-10-11")]
alias Sorted.rel_get_of_lt := Pairwise.rel_get_of_lt

theorem Pairwise.rel_get_of_le [IsRefl α R] {l : List α} (h : l.Pairwise R) {a b : Fin l.length}
    (hab : a ≤ b) : R (l.get a) (l.get b) := by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hab; exacts [refl _, (pairwise_iff_get.1 h) _ _ hlt]

@[deprecated (since := "2025-10-11")]
alias Sorted.rel_get_of_le := Pairwise.rel_get_of_le

theorem Pairwise.decide [DecidableRel R] (l : List α) (h : Pairwise R l) :
    Pairwise (fun a b => decide (R a b) = true) l := by
  refine h.imp fun {a b} h => by simpa using h

@[deprecated (since := "2025-10-11")]
alias Sorted.decide := Pairwise.decide

end List
