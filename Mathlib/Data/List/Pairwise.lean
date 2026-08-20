/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.List.Lemmas
public import Batteries.Data.List.Pairwise
public import Mathlib.Data.List.TFAE
public import Mathlib.Logic.Pairwise
public import Mathlib.Logic.Relation

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

public section


open Nat

namespace List

variable {α : Type*} {R : α → α → Prop} {l l₁ l₂ : List α} {a b : α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff

/-! ### Pairwise -/

theorem pairwise_iff_forall_infix {α : Type*} {l : List α} {R : α → α → Prop} :
    l.Pairwise R ↔
      ∀ l', (h : 1 < l'.length) → l' <:+: l → R (l'.head <| by grind) (l'.getLast <| by grind) := by
  refine l.pairwise_iff_getElem.trans ⟨fun h l' hne ⟨l₁, l₂, hl⟩ ↦ ?_, fun h i j hi hj hij ↦ ?_⟩
  · grind [getElem_append_left', getElem_append_right']
  · grind [h _ _ <| List.drop_suffix i _ |>.isInfix.trans <| l.take_prefix (j + 1) |>.isInfix]

theorem Pairwise.forall_of_forall [Std.Symm R] (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [Std.Symm.flip_eq]

theorem Pairwise.forall [Std.Symm R] (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  have : Std.Symm fun x y ↦ x ≠ y → R x y := { symm a b h hne := symm <| h hne.symm }
  apply Pairwise.forall_of_forall
  · exact fun _ _ ↦ absurd rfl
  · exact hl.imp @fun a b h _ ↦ by exact h

theorem Pairwise.set_pairwise (hl : Pairwise R l) [Std.Symm R] : { x | x ∈ l }.Pairwise R :=
  hl.forall

theorem pairwise_of_reflexive_of_forall_ne [Std.Refl R] (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) :
    l.Pairwise R := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply refl
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

theorem pairwise_append_of_mem [Std.Symm R] [IsTrans α R] (ha : a ∈ l₁) (hb : b ∈ l₂) :
    (l₁ ++ l₂).Pairwise R ↔ R a b ∧ l₁.Pairwise R ∧ l₂.Pairwise R := by
  rw [pairwise_append, ← and_rotate, and_congr_left_iff, and_imp]
  refine fun h₁ h₂ ↦ ⟨fun h ↦ h a ha b hb, fun hab x hx y hy ↦ ?_⟩
  have : R a y := eq_or_ne b y |>.elim (· ▸ hab) (trans_of R hab <| h₂.forall hb hy ·)
  exact eq_or_ne x a |>.elim (· ▸ this) fun hne ↦ trans_of R (h₁.forall hx ha hne) this

theorem pairwise_cons_of_mem [Std.Symm R] [IsTrans α R] (h : b ∈ l) :
    (a :: l).Pairwise R ↔ R a b ∧ l.Pairwise R := by
  simpa using pairwise_append_of_mem (l₁ := [a]) (by simp) h

theorem Pairwise.rel_head_tail (h₁ : l.Pairwise R) (ha : a ∈ l.tail) :
    R (l.head <| ne_nil_of_mem <| mem_of_mem_tail ha) a := by
  grind +splitIndPred

theorem Pairwise.rel_head_of_rel_head_head (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hhead : R (l.head <| ne_nil_of_mem ha) (l.head <| ne_nil_of_mem ha)) :
    R (l.head <| ne_nil_of_mem ha) a := by
  grind +splitIndPred

theorem Pairwise.rel_head [Std.Refl R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
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

theorem Pairwise.rel_getLast [Std.Refl R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R a (l.getLast <| ne_nil_of_mem ha) :=
  h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

protected alias ⟨Pairwise.of_reverse, Pairwise.reverse⟩ := pairwise_reverse

theorem Pairwise.head!_le [Inhabited α] [Std.Refl R] (h : l.Pairwise R)
    (ha : a ∈ l) : R l.head! a := by
  cases l
  · contradiction
  · cases ha with
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)

theorem pairwise_replicate_of_refl {n} [Std.Refl R] : (replicate n a).Pairwise R :=
  pairwise_replicate.mpr (Or.inr <| refl_of ..)

/-! ### Pairwise filtering -/

protected alias ⟨_, Pairwise.pwFilter⟩ := pwFilter_eq_self

theorem pairwise_cons_cons_iff_of_trans [IsTrans α R] {l : List α} {a b : α} :
    Pairwise R (a :: b :: l) ↔ R a b ∧ Pairwise R (b :: l) := by
  simp_rw [← isChain_iff_pairwise, isChain_cons_cons]

theorem Pairwise.cons_cons_of_trans [IsTrans α R] {l : List α} {a b : α} :
    R a b → Pairwise R (b :: l) → Pairwise R (a :: b :: l) := by
  simp_rw [pairwise_cons_cons_iff_of_trans]
  exact And.intro

theorem Pairwise.rel_get_of_lt {l : List α} (h : l.Pairwise R) {a b : Fin l.length} (hab : a < b) :
    R (l.get a) (l.get b) :=
  List.pairwise_iff_get.1 h _ _ hab

theorem Pairwise.rel_get_of_le [Std.Refl R] {l : List α} (h : l.Pairwise R) {a b : Fin l.length}
    (hab : a ≤ b) : R (l.get a) (l.get b) := by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hab; exacts [refl _, (pairwise_iff_get.1 h) _ _ hlt]

theorem Pairwise.decide [DecidableRel R] (l : List α) (h : Pairwise R l) :
    Pairwise (fun a b => decide (R a b) = true) l := by
  refine h.imp fun {a b} h => by simpa using h

/-! ## TFAE -/

section TFAE

variable {a b : Prop} {l l₁ l₂ : List Prop}

theorem tfae_iff_pairwise : TFAE l ↔ l.Pairwise (· ↔ ·) :=
  ⟨pairwise_of_forall_mem_list, Pairwise.forall_of_forall fun _ _ ↦ .rfl⟩

theorem tfae_append :
    TFAE (l₁ ++ l₂) ↔ TFAE l₁ ∧ TFAE l₂ ∧ (∀ a ∈ l₁, ∀ b ∈ l₂, a ↔ b) := by
  simp [tfae_iff_pairwise, pairwise_append]

theorem tfae_append_of_mem (ha : a ∈ l₁) (hb : b ∈ l₂) :
    TFAE (l₁ ++ l₂) ↔ (a ↔ b) ∧ TFAE l₁ ∧ TFAE l₂ := by
  simp [tfae_iff_pairwise, pairwise_append_of_mem ha hb]

theorem tfae_cons (h : b ∈ l) : TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l := by
  simp [tfae_iff_pairwise, pairwise_cons_of_mem h]

@[simp]
theorem tfae_cons_of_mem (h : a ∈ l) : TFAE (a :: l) ↔ TFAE l := by
  simp [tfae_iff_pairwise, pairwise_cons_of_mem h]

theorem tfae_concat (h : b ∈ l) : TFAE (l ++ [a]) ↔ (a ↔ b) ∧ TFAE l := by
  simp [tfae_append_of_mem (l₁ := l) (l₂ := [a]) (b := a) h, iff_comm]

@[simp]
theorem tfae_concat_of_mem (h : a ∈ l) : TFAE (l ++ [a]) ↔ TFAE l := by
  simp [tfae_concat h]

theorem tfae_cons_cons : TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l) :=
  tfae_cons (Mem.head _)

@[deprecated tfae_cons_of_mem +typeChanged (since := "2026-08-14")]
theorem tfae_cons_self : TFAE (a :: a :: l) ↔ TFAE (a :: l) := by simp

theorem tfae_of_cycle (h_chain : List.IsChain (· → ·) (a :: b :: l))
    (h_last : getLastD l b → a) : TFAE (a :: b :: l) := by
  induction l generalizing a b with
  | nil => simp_all [iff_def]
  | cons c l IH =>
    simp only [tfae_cons_cons, getLastD_cons, isChain_cons_cons] at *
    rcases h_chain with ⟨ab, ⟨bc, ch⟩⟩
    have := IH ⟨bc, ch⟩ (ab ∘ h_last)
    exact ⟨⟨ab, h_last ∘ (this.2 c (.head _) _ getLastD_mem_cons).1 ∘ bc⟩, this⟩

end TFAE

end List
