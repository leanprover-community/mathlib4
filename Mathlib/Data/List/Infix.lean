/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic

#align_import data.list.infix from "leanprover-community/mathlib"@"26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2"

/-!
# Prefixes, suffixes, infixes

This file proves properties about
* `List.isPrefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `List.isSuffix`: `l₁` is a suffix of `l₂` if `l₂` ends with `l₁`.
* `List.isInfix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some suffix of `l₂`.
* `List.inits`: The list of prefixes of a list.
* `List.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `Mathlib.Data.List.Defs`.

## Notation

* `l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
* `l₁ <:+ l₂`: `l₁` is a suffix of `l₂`.
* `l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/

open Nat

variable {α β : Type*}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α} {m n : ℕ}

/-! ### prefix, suffix, infix -/


section Fix


theorem prefix_rfl : l <+: l :=
  prefix_refl _

theorem suffix_rfl : l <:+ l :=
  suffix_refl _

theorem infix_rfl : l <:+: l :=
  infix_refl _


theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp


alias ⟨_, isSuffix.reverse⟩ := reverse_prefix

alias ⟨_, isPrefix.reverse⟩ := reverse_suffix

alias ⟨_, isInfix.reverse⟩ := reverse_infix


alias ⟨eq_nil_of_infix_nil, _⟩ := infix_nil

alias ⟨eq_nil_of_prefix_nil, _⟩ := prefix_nil

alias ⟨eq_nil_of_suffix_nil, _⟩ := suffix_nil


theorem eq_of_infix_of_length_eq (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem eq_of_prefix_of_length_eq (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem eq_of_suffix_of_length_eq (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length


lemma dropSlice_sublist (n m : ℕ) (l : List α) : l.dropSlice n m <+ l :=
  calc l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, add_comm]
  _ <+ take n l ++ drop n l := (Sublist.refl _).append (drop_sublist _ _)
  _ = _ := take_append_drop _ _

lemma dropSlice_subset (n m : ℕ) (l : List α) : l.dropSlice n m ⊆ l :=
  (dropSlice_sublist n m l).subset

lemma mem_of_mem_dropSlice {n m : ℕ} {l : List α} {a : α} (h : a ∈ l.dropSlice n m) : a ∈ l :=
  dropSlice_subset n m l h

theorem takeWhile_prefix (p : α → Bool) : l.takeWhile p <+: l :=
  ⟨l.dropWhile p, takeWhile_append_dropWhile p l⟩

theorem dropWhile_suffix (p : α → Bool) : l.dropWhile p <:+ l :=
  ⟨l.takeWhile p, takeWhile_append_dropWhile p l⟩

theorem dropLast_prefix : ∀ l : List α, l.dropLast <+: l
  | [] => ⟨nil, by rw [dropLast, List.append_nil]⟩
  | a :: l => ⟨_, dropLast_append_getLast (cons_ne_nil a l)⟩

theorem tail_suffix (l : List α) : tail l <:+ l := by rw [← drop_one]; apply drop_suffix

theorem dropLast_sublist (l : List α) : l.dropLast <+ l :=
  (dropLast_prefix l).sublist

theorem tail_sublist (l : List α) : l.tail <+ l :=
  (tail_suffix l).sublist

theorem dropLast_subset (l : List α) : l.dropLast ⊆ l :=
  (dropLast_sublist l).subset

theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).subset

theorem mem_of_mem_dropLast (h : a ∈ l.dropLast) : a ∈ l :=
  dropLast_subset l h

theorem mem_of_mem_tail (h : a ∈ l.tail) : a ∈ l :=
  tail_subset l h

theorem prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; rw [drop_left], fun e => ⟨_, e⟩⟩

theorem suffix_iff_eq_append : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; simp only [length_append, add_tsub_cancel_right, take_left], fun e =>
    ⟨_, e⟩⟩

theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
  ⟨fun h => append_right_cancel <| (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ take_prefix _ _⟩

theorem suffix_iff_eq_drop : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
  ⟨fun h => append_left_cancel <| (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ drop_suffix _ _⟩

instance decidablePrefix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+: l₂)
  | [], l₂ => isTrue ⟨l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨t, te⟩ => List.noConfusion te
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      @decidable_of_decidable_of_iff _ _ (decidablePrefix l₁ l₂) (by rw [← h, prefix_cons_inj])
    else
      isFalse fun ⟨t, te⟩ => h <| by injection te

-- Alternatively, use mem_tails
instance decidableSuffix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+ l₂)
  | [], l₂ => isTrue ⟨l₂, append_nil _⟩
  | a :: l₁, [] => isFalse <| mt (Sublist.length_le ∘ IsSuffix.sublist) (by simp)
  | l₁, b :: l₂ =>
    @decidable_of_decidable_of_iff _ _
      (@instDecidableOr _ _ _ (l₁.decidableSuffix l₂))
      suffix_cons_iff.symm
termination_by decidableSuffix l₁ l₂ => (l₁, l₂)

instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ => by simp at te
  | l₁, b :: l₂ =>
    @decidable_of_decidable_of_iff _ _
      (@instDecidableOr _ _ (l₁.decidablePrefix (b :: l₂)) (l₁.decidableInfix l₂))
      infix_cons_iff.symm
termination_by decidableInfix l₁ l₂ => (l₁, l₂)

theorem prefix_take_le_iff {L : List (List (Option α))} (hm : m < L.length) :
    L.take m <+: L.take n ↔ m ≤ n := by
  simp only [prefix_iff_eq_take, length_take]
  induction m generalizing L n with
  | zero => simp [min_eq_left, eq_self_iff_true, Nat.zero_le, take]
  | succ m IH =>
    cases L with
    | nil => exact (not_lt_bot hm).elim
    | cons l ls =>
      cases n with
      | zero =>
        refine' iff_of_false _ (zero_lt_succ _).not_le
        rw [take_zero, take_nil]
        simp only [take]
      | succ n =>
        simp only [length] at hm
        have specializedIH := @IH n ls (Nat.lt_of_succ_lt_succ hm)
        simp only [le_of_lt (Nat.lt_of_succ_lt_succ hm), min_eq_left] at specializedIH
        simp only [take, length, ge_iff_le, le_of_lt hm, min_eq_left, take_cons_succ, cons.injEq,
          specializedIH, true_and]
        exact ⟨Nat.succ_le_succ, Nat.le_of_succ_le_succ⟩

theorem cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ := by
  constructor
  · rintro ⟨L, hL⟩
    simp only [cons_append] at hL
    injection hL with hLLeft hLRight
    exact ⟨hLLeft, ⟨L, hLRight⟩⟩
  · rintro ⟨rfl, h⟩
    rwa [prefix_cons_inj]

theorem IsPrefix.map (h : l₁ <+: l₂) (f : α → β) : l₁.map f <+: l₂.map f := by
  induction' l₁ with hd tl hl generalizing l₂
  · simp only [nil_prefix, map_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h
      simp only [List.map_cons, h, prefix_cons_inj, hl, map]

theorem IsPrefix.filter_map (h : l₁ <+: l₂) (f : α → Option β) :
    l₁.filterMap f <+: l₂.filterMap f := by
  induction' l₁ with hd₁ tl₁ hl generalizing l₂
  · simp only [nil_prefix, filterMap_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h
      rw [← @singleton_append _ hd₁ _, ← @singleton_append _ hd₂ _, filterMap_append,
        filterMap_append, h.left, prefix_append_right_inj]
      exact hl h.right

theorem IsPrefix.reduceOption {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filter_map id


instance : IsPartialOrder (List α) (· <+: ·) where
  refl := prefix_refl
  trans _ _ _ := IsPrefix.trans
  antisymm _ _ h₁ h₂ := eq_of_prefix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+ ·) where
  refl := suffix_refl
  trans _ _ _ := IsSuffix.trans
  antisymm _ _ h₁ h₂ := eq_of_suffix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+: ·) where
  refl := infix_refl
  trans _ _ _ := IsInfix.trans
  antisymm _ _ h₁ h₂ := eq_of_infix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

@[simp]
theorem mem_inits : ∀ s t : List α, s ∈ inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by simpa only [inits, mem_singleton]
    ⟨fun h => h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t by simpa
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        rw [← hs, ← ht]; exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion hr) fun ba (st : s ++ r = t) =>
          Or.inr <| by rw [ba]; exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩⟩

@[simp]
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton, suffix_nil]
  | s, a :: t => by
    simp only [tails, mem_cons, mem_tails s t];
    exact
      show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
        ⟨fun o =>
          match s, t, o with
          | _, t, Or.inl rfl => suffix_rfl
          | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
          fun e =>
          match s, t, e with
          | _, t, ⟨[], rfl⟩ => Or.inl rfl
          | s, t, ⟨b :: l, he⟩ => List.noConfusion he fun _ lt => Or.inr ⟨l, lt⟩⟩

theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp

theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp

@[simp]
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
  | [], a :: t => by simp[· ∘ ·]
  | a :: s, t => by simp [inits_append s t, · ∘ ·]

@[simp]
theorem tails_append :
    ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [tails_append s t]

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
  | a :: l => by simp [inits_eq_tails l, map_eq_map_iff, reverse_map]

theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
  | a :: l => by simp [tails_eq_inits l, append_left_inj]

theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self, reverse_map]

theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self, reverse_map]

theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self, reverse_map]

theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self, reverse_map]

@[simp]
theorem length_tails (l : List α) : length (tails l) = length l + 1 := by
  induction' l with x l IH
  · simp
  · simpa using IH

@[simp]
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]

section deprecated
set_option linter.deprecated false -- TODO(Henrik): make replacements for theorems in this section

@[simp]
theorem nth_le_tails (l : List α) (n : ℕ) (hn : n < length (tails l)) :
    nthLe (tails l) n hn = l.drop n := by
  induction' l with x l IH generalizing n
  · simp
  · cases n
    · simp[nthLe_cons]
    · simpa[nthLe_cons] using IH _ _

@[simp]
theorem nth_le_inits (l : List α) (n : ℕ) (hn : n < length (inits l)) :
    nthLe (inits l) n hn = l.take n := by
  induction' l with x l IH generalizing n
  · simp
  · cases n
    · simp[nthLe_cons]
    · simpa[nthLe_cons] using IH _ _
end deprecated

end InitsTails

/-! ### insert -/


section Insert

variable [DecidableEq α]

@[simp]
theorem insert_nil (a : α) : insert a nil = [a] :=
  rfl

theorem insert.def (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l :=
  rfl


@[simp]
theorem suffix_insert (a : α) (l : List α) : l <:+ l.insert a := by
  by_cases h : a ∈ l
  · simp only [insert_of_mem h, insert, suffix_refl]
  · simp only [insert_of_not_mem h, suffix_cons, insert]

theorem infix_insert (a : α) (l : List α) : l <:+: l.insert a :=
  (suffix_insert a l).isInfix

theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).sublist

theorem subset_insert (a : α) (l : List α) : l ⊆ l.insert a :=
  (sublist_insert a l).subset


end Insert

theorem mem_of_mem_suffix (hx : a ∈ l₁) (hl : l₁ <:+ l₂) : a ∈ l₂ :=
  hl.subset hx

end List
