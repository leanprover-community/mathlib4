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

`l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
`l₁ <:+ l₂`: `l₁` is a suffix of `l₂`.
`l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/

open Nat

variable {α β : Type*}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α} {m n : ℕ}

/-! ### prefix, suffix, infix -/


section Fix

#align list.prefix_append List.prefix_append
#align list.suffix_append List.suffix_append
#align list.infix_append List.infix_append
#align list.infix_append' List.infix_append'
#align list.is_prefix.is_infix List.isPrefix.isInfix
#align list.is_suffix.is_infix List.isSuffix.isInfix
#align list.nil_prefix List.nil_prefix
#align list.nil_suffix List.nil_suffix
#align list.nil_infix List.nil_infix
#align list.prefix_refl List.prefix_refl
#align list.suffix_refl List.suffix_refl
#align list.infix_refl List.infix_refl

theorem prefix_rfl : l <+: l :=
  prefix_refl _
#align list.prefix_rfl List.prefix_rfl

theorem suffix_rfl : l <:+ l :=
  suffix_refl _
#align list.suffix_rfl List.suffix_rfl

theorem infix_rfl : l <:+: l :=
  infix_refl _
#align list.infix_rfl List.infix_rfl

#align list.suffix_cons List.suffix_cons

theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp
                                                           -- 🎉 no goals
#align list.prefix_concat List.prefix_concat

#align list.infix_cons List.infix_cons
#align list.infix_concat List.infix_concat
#align list.is_prefix.trans List.isPrefix.trans
#align list.is_suffix.trans List.isSuffix.trans
#align list.is_infix.trans List.isInfix.trans
#align list.is_infix.sublist List.isInfix.sublist
#align list.is_infix.subset List.isInfix.subset
#align list.is_prefix.sublist List.isPrefix.sublist
#align list.is_prefix.subset List.isPrefix.subset
#align list.is_suffix.sublist List.isSuffix.sublist
#align list.is_suffix.subset List.isSuffix.subset
#align list.reverse_suffix List.reverse_suffix
#align list.reverse_prefix List.reverse_prefix
#align list.reverse_infix List.reverse_infix

alias ⟨_, isSuffix.reverse⟩ := reverse_prefix
#align list.is_suffix.reverse List.isSuffix.reverse

alias ⟨_, isPrefix.reverse⟩ := reverse_suffix
#align list.is_prefix.reverse List.isPrefix.reverse

alias ⟨_, isInfix.reverse⟩ := reverse_infix
#align list.is_infix.reverse List.isInfix.reverse

#align list.is_infix.length_le List.isInfix.length_le
#align list.is_prefix.length_le List.isPrefix.length_le
#align list.is_suffix.length_le List.isSuffix.length_le
#align list.infix_nil_iff List.infix_nil
#align list.prefix_nil_iff List.prefix_nil
#align list.suffix_nil_iff List.suffix_nil

alias ⟨eq_nil_of_infix_nil, _⟩ := infix_nil
#align list.eq_nil_of_infix_nil List.eq_nil_of_infix_nil

alias ⟨eq_nil_of_prefix_nil, _⟩ := prefix_nil
#align list.eq_nil_of_prefix_nil List.eq_nil_of_prefix_nil

alias ⟨eq_nil_of_suffix_nil, _⟩ := suffix_nil
#align list.eq_nil_of_suffix_nil List.eq_nil_of_suffix_nil

#align list.infix_iff_prefix_suffix List.infix_iff_prefix_suffix

theorem eq_of_infix_of_length_eq (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length
#align list.eq_of_infix_of_length_eq List.eq_of_infix_of_length_eq

theorem eq_of_prefix_of_length_eq (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length
#align list.eq_of_prefix_of_length_eq List.eq_of_prefix_of_length_eq

theorem eq_of_suffix_of_length_eq (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length
#align list.eq_of_suffix_of_length_eq List.eq_of_suffix_of_length_eq

#align list.prefix_of_prefix_length_le List.prefix_of_prefix_length_le
#align list.prefix_or_prefix_of_prefix List.prefix_or_prefix_of_prefix
#align list.suffix_of_suffix_length_le List.suffix_of_suffix_length_le
#align list.suffix_or_suffix_of_suffix List.suffix_or_suffix_of_suffix
#align list.suffix_cons_iff List.suffix_cons_iff
#align list.infix_cons_iff List.infix_cons_iff
#align list.infix_of_mem_join List.infix_of_mem_join
#align list.prefix_append_right_inj List.prefix_append_right_inj
#align list.prefix_cons_inj List.prefix_cons_inj
#align list.take_prefix List.take_prefix
#align list.drop_suffix List.drop_suffix
#align list.take_sublist List.take_sublist
#align list.drop_sublist List.drop_sublist
#align list.take_subset List.take_subset
#align list.drop_subset List.drop_subset
#align list.mem_of_mem_take List.mem_of_mem_take
#align list.mem_of_mem_drop List.mem_of_mem_drop

lemma dropSlice_sublist (n m : ℕ) (l : List α) : l.dropSlice n m <+ l :=
  calc l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, add_comm]
                                                             -- 🎉 no goals
  _ <+ take n l ++ drop n l := (Sublist.refl _).append (drop_sublist _ _)
  _ = _ := take_append_drop _ _
#align list.slice_sublist List.dropSlice_sublist

lemma dropSlice_subset (n m : ℕ) (l : List α) : l.dropSlice n m ⊆ l :=
  (dropSlice_sublist n m l).subset
#align list.slice_subset List.dropSlice_subset

lemma mem_of_mem_dropSlice {n m : ℕ} {l : List α} {a : α} (h : a ∈ l.dropSlice n m) : a ∈ l :=
  dropSlice_subset n m l h
#align list.mem_of_mem_slice List.mem_of_mem_dropSlice

theorem takeWhile_prefix (p : α → Bool) : l.takeWhile p <+: l :=
  ⟨l.dropWhile p, takeWhile_append_dropWhile p l⟩
#align list.take_while_prefix List.takeWhile_prefix

theorem dropWhile_suffix (p : α → Bool) : l.dropWhile p <:+ l :=
  ⟨l.takeWhile p, takeWhile_append_dropWhile p l⟩
#align list.drop_while_suffix List.dropWhile_suffix

theorem dropLast_prefix : ∀ l : List α, l.dropLast <+: l
  | [] => ⟨nil, by rw [dropLast, List.append_nil]⟩
                   -- 🎉 no goals
  | a :: l => ⟨_, dropLast_append_getLast (cons_ne_nil a l)⟩
#align list.init_prefix List.dropLast_prefix

theorem tail_suffix (l : List α) : tail l <:+ l := by rw [← drop_one]; apply drop_suffix
                                                      -- ⊢ drop 1 l <:+ l
                                                                       -- 🎉 no goals
#align list.tail_suffix List.tail_suffix

theorem dropLast_sublist (l : List α) : l.dropLast <+ l :=
  (dropLast_prefix l).sublist
#align list.init_sublist List.dropLast_sublist

theorem tail_sublist (l : List α) : l.tail <+ l :=
  (tail_suffix l).sublist
#align list.tail_sublist List.tail_sublist

theorem dropLast_subset (l : List α) : l.dropLast ⊆ l :=
  (dropLast_sublist l).subset
#align list.init_subset List.dropLast_subset

theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).subset
#align list.tail_subset List.tail_subset

theorem mem_of_mem_dropLast (h : a ∈ l.dropLast) : a ∈ l :=
  dropLast_subset l h
#align list.mem_of_mem_init List.mem_of_mem_dropLast

theorem mem_of_mem_tail (h : a ∈ l.tail) : a ∈ l :=
  tail_subset l h
#align list.mem_of_mem_tail List.mem_of_mem_tail

theorem prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; rw [drop_left], fun e => ⟨_, e⟩⟩
      -- ⊢ l₁ ++ drop (length l₁) (l₁ ++ r) = l₁ ++ r
                       -- 🎉 no goals
#align list.prefix_iff_eq_append List.prefix_iff_eq_append

theorem suffix_iff_eq_append : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; simp only [length_append, add_tsub_cancel_right, take_left], fun e =>
      -- ⊢ take (length (r ++ l₁) - length l₁) (r ++ l₁) ++ l₁ = r ++ l₁
                       -- 🎉 no goals
    ⟨_, e⟩⟩
#align list.suffix_iff_eq_append List.suffix_iff_eq_append

theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
  ⟨fun h => append_right_cancel <| (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ take_prefix _ _⟩
#align list.prefix_iff_eq_take List.prefix_iff_eq_take

theorem suffix_iff_eq_drop : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
  ⟨fun h => append_left_cancel <| (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ drop_suffix _ _⟩
#align list.suffix_iff_eq_drop List.suffix_iff_eq_drop

instance decidablePrefix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+: l₂)
  | [], l₂ => isTrue ⟨l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨t, te⟩ => List.noConfusion te
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      @decidable_of_decidable_of_iff _ _ (decidablePrefix l₁ l₂) (by rw [← h, prefix_cons_inj])
                                                                     -- 🎉 no goals
    else
      isFalse fun ⟨t, te⟩ => h <| by injection te
                                     -- 🎉 no goals
#align list.decidable_prefix List.decidablePrefix

-- Alternatively, use mem_tails
instance decidableSuffix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+ l₂)
  | [], l₂ => isTrue ⟨l₂, append_nil _⟩
  | a :: l₁, [] => isFalse <| mt (Sublist.length_le ∘ isSuffix.sublist) (by simp)
                                                                            -- 🎉 no goals
  | l₁, b :: l₂ =>
    @decidable_of_decidable_of_iff _ _
      (@instDecidableOr _ _ _ (l₁.decidableSuffix l₂))
      suffix_cons_iff.symm
termination_by decidableSuffix l₁ l₂ => (l₁, l₂)
#align list.decidable_suffix List.decidableSuffix

instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ => by simp at te
                                                -- 🎉 no goals
  | l₁, b :: l₂ =>
    @decidable_of_decidable_of_iff _ _
      (@instDecidableOr _ _ (l₁.decidablePrefix (b :: l₂)) (l₁.decidableInfix l₂))
      infix_cons_iff.symm
termination_by decidableInfix l₁ l₂ => (l₁, l₂)
#align list.decidable_infix List.decidableInfix

theorem prefix_take_le_iff {L : List (List (Option α))} (hm : m < L.length) :
    L.take m <+: L.take n ↔ m ≤ n := by
  simp only [prefix_iff_eq_take, length_take]
  -- ⊢ take m L = take (min m (length L)) (take n L) ↔ m ≤ n
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
        simp [le_of_lt hm, specializedIH, true_and_iff, min_eq_left, eq_self_iff_true, length, take]
        exact ⟨Nat.succ_le_succ, Nat.le_of_succ_le_succ⟩
#align list.prefix_take_le_iff List.prefix_take_le_iff

theorem cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ := by
  constructor
  -- ⊢ a :: l₁ <+: b :: l₂ → a = b ∧ l₁ <+: l₂
  · rintro ⟨L, hL⟩
    -- ⊢ a = b ∧ l₁ <+: l₂
    simp only [cons_append] at hL
    -- ⊢ a = b ∧ l₁ <+: l₂
    injection hL with hLLeft hLRight
    -- ⊢ a = b ∧ l₁ <+: l₂
    exact ⟨hLLeft, ⟨L, hLRight⟩⟩
    -- 🎉 no goals
  · rintro ⟨rfl, h⟩
    -- ⊢ a :: l₁ <+: a :: l₂
    rwa [prefix_cons_inj]
    -- 🎉 no goals
#align list.cons_prefix_iff List.cons_prefix_iff

theorem isPrefix.map (h : l₁ <+: l₂) (f : α → β) : l₁.map f <+: l₂.map f := by
  induction' l₁ with hd tl hl generalizing l₂
  -- ⊢ List.map f [] <+: List.map f l₂
  · simp only [nil_prefix, map_nil]
    -- 🎉 no goals
  · cases' l₂ with hd₂ tl₂
    -- ⊢ List.map f (hd :: tl) <+: List.map f []
    · simpa only using eq_nil_of_prefix_nil h
      -- 🎉 no goals
    · rw [cons_prefix_iff] at h
      -- ⊢ List.map f (hd :: tl) <+: List.map f (hd₂ :: tl₂)
      simp only [List.map_cons, h, prefix_cons_inj, hl, map]
      -- 🎉 no goals
#align list.is_prefix.map List.isPrefix.map

theorem isPrefix.filter_map (h : l₁ <+: l₂) (f : α → Option β) :
    l₁.filterMap f <+: l₂.filterMap f := by
  induction' l₁ with hd₁ tl₁ hl generalizing l₂
  -- ⊢ filterMap f [] <+: filterMap f l₂
  · simp only [nil_prefix, filterMap_nil]
    -- 🎉 no goals
  · cases' l₂ with hd₂ tl₂
    -- ⊢ filterMap f (hd₁ :: tl₁) <+: filterMap f []
    · simpa only using eq_nil_of_prefix_nil h
      -- 🎉 no goals
    · rw [cons_prefix_iff] at h
      -- ⊢ filterMap f (hd₁ :: tl₁) <+: filterMap f (hd₂ :: tl₂)
      rw [← @singleton_append _ hd₁ _, ← @singleton_append _ hd₂ _, filterMap_append,
        filterMap_append, h.left, prefix_append_right_inj]
      exact hl h.right
      -- 🎉 no goals
#align list.is_prefix.filter_map List.isPrefix.filter_map

theorem isPrefix.reduceOption {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filter_map id
#align list.is_prefix.reduce_option List.isPrefix.reduceOption

#align list.is_prefix.filter List.isPrefix.filter
#align list.is_suffix.filter List.isSuffix.filter
#align list.is_infix.filter List.isInfix.filter

instance : IsPartialOrder (List α) (· <+: ·) where
  refl := prefix_refl
  trans _ _ _ := isPrefix.trans
  antisymm _ _ h₁ h₂ := eq_of_prefix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+ ·) where
  refl := suffix_refl
  trans _ _ _ := isSuffix.trans
  antisymm _ _ h₁ h₂ := eq_of_suffix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+: ·) where
  refl := infix_refl
  trans _ _ _ := isInfix.trans
  antisymm _ _ h₁ h₂ := eq_of_infix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

@[simp]
theorem mem_inits : ∀ s t : List α, s ∈ inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by simpa only [inits, mem_singleton]
                                    -- 🎉 no goals
    ⟨fun h => h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t by simpa
                                                                     -- 🎉 no goals
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        -- ⊢ s✝ <+: a :: t
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        -- ⊢ a :: r <+: a :: (r ++ s)
                         -- 🎉 no goals
        rw [← hs, ← ht]; exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion hr) fun ba (st : s ++ r = t) =>
                       -- ⊢ ∃ l, l ∈ inits t ∧ a :: l = a :: s
                                -- 🎉 no goals
          Or.inr <| by rw [ba]; exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩⟩
#align list.mem_inits List.mem_inits

@[simp]
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton, suffix_nil]
    -- 🎉 no goals
  | s, a :: t => by
    simp only [tails, mem_cons, mem_tails s t];
    -- ⊢ s = a :: t ∨ s <:+ t ↔ s <:+ a :: t
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
#align list.mem_tails List.mem_tails

theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp
  -- 🎉 no goals
#align list.inits_cons List.inits_cons

theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp
                                                                                     -- 🎉 no goals
#align list.tails_cons List.tails_cons

@[simp]
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
                 -- 🎉 no goals
  | [], a :: t => by simp[· ∘ ·]
                     -- 🎉 no goals
  | a :: s, t => by simp [inits_append s t, · ∘ ·]
                    -- 🎉 no goals
#align list.inits_append List.inits_append

@[simp]
theorem tails_append :
    ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
                 -- 🎉 no goals
  | [], a :: t => by simp
                     -- 🎉 no goals
  | a :: s, t => by simp [tails_append s t]
                    -- 🎉 no goals
#align list.tails_append List.tails_append

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
             -- 🎉 no goals
  | a :: l => by simp [inits_eq_tails l, map_eq_map_iff, reverse_map]
                 -- 🎉 no goals
#align list.inits_eq_tails List.inits_eq_tails

theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
             -- 🎉 no goals
  | a :: l => by simp [tails_eq_inits l, append_left_inj]
                 -- 🎉 no goals
#align list.tails_eq_inits List.tails_eq_inits

theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]
  -- ⊢ inits (reverse l) = reverse (map reverse (reverse (map reverse (inits (rever …
  simp [reverse_involutive.comp_self, reverse_map]
  -- 🎉 no goals
#align list.inits_reverse List.inits_reverse

theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]
  -- ⊢ tails (reverse l) = reverse (map reverse (reverse (map reverse (tails (rever …
  simp [reverse_involutive.comp_self, reverse_map]
  -- 🎉 no goals
#align list.tails_reverse List.tails_reverse

theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]
  -- ⊢ map reverse (reverse (map reverse (tails (reverse l)))) = reverse (tails (re …
  simp [reverse_involutive.comp_self, reverse_map]
  -- 🎉 no goals
#align list.map_reverse_inits List.map_reverse_inits

theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]
  -- ⊢ map reverse (reverse (map reverse (inits (reverse l)))) = reverse (inits (re …
  simp [reverse_involutive.comp_self, reverse_map]
  -- 🎉 no goals
#align list.map_reverse_tails List.map_reverse_tails

@[simp]
theorem length_tails (l : List α) : length (tails l) = length l + 1 := by
  induction' l with x l IH
  -- ⊢ length (tails []) = length [] + 1
  · simp
    -- 🎉 no goals
  · simpa using IH
    -- 🎉 no goals
#align list.length_tails List.length_tails

@[simp]
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]
                                                                          -- 🎉 no goals
#align list.length_inits List.length_inits

section deprecated
set_option linter.deprecated false -- TODO(Henrik): make replacements for theorems in this section

@[simp]
theorem nth_le_tails (l : List α) (n : ℕ) (hn : n < length (tails l)) :
    nthLe (tails l) n hn = l.drop n := by
  induction' l with x l IH generalizing n
  -- ⊢ nthLe (tails []) n hn = drop n []
  · simp
    -- 🎉 no goals
  · cases n
    -- ⊢ nthLe (tails (x :: l)) zero hn = drop zero (x :: l)
    · simp[nthLe_cons]
      -- 🎉 no goals
    · simpa[nthLe_cons] using IH _ _
      -- 🎉 no goals
#align list.nth_le_tails List.nth_le_tails

@[simp]
theorem nth_le_inits (l : List α) (n : ℕ) (hn : n < length (inits l)) :
    nthLe (inits l) n hn = l.take n := by
  induction' l with x l IH generalizing n
  -- ⊢ nthLe (inits []) n hn = take n []
  · simp
    -- 🎉 no goals
  · cases n
    -- ⊢ nthLe (inits (x :: l)) zero hn = take zero (x :: l)
    · simp[nthLe_cons]
      -- 🎉 no goals
    · simpa[nthLe_cons] using IH _ _
      -- 🎉 no goals
#align list.nth_le_inits List.nth_le_inits
end deprecated

end InitsTails

/-! ### insert -/


section Insert

variable [DecidableEq α]

@[simp]
theorem insert_nil (a : α) : insert a nil = [a] :=
  rfl
#align list.insert_nil List.insert_nil

theorem insert.def (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l :=
  rfl
#align list.insert.def List.insert.def

#align list.insert_of_mem List.insert_of_mem
#align list.insert_of_not_mem List.insert_of_not_mem
#align list.mem_insert_iff List.mem_insert_iff

@[simp]
theorem suffix_insert (a : α) (l : List α) : l <:+ l.insert a := by
  by_cases h : a ∈ l
  -- ⊢ l <:+ List.insert a l
  · simp only [insert_of_mem h, insert, suffix_refl]
    -- 🎉 no goals
  · simp only [insert_of_not_mem h, suffix_cons, insert]
    -- 🎉 no goals
#align list.suffix_insert List.suffix_insert

theorem infix_insert (a : α) (l : List α) : l <:+: l.insert a :=
  (suffix_insert a l).isInfix
#align list.infix_insert List.infix_insert

theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).sublist
#align list.sublist_insert List.sublist_insert

theorem subset_insert (a : α) (l : List α) : l ⊆ l.insert a :=
  (sublist_insert a l).subset
#align list.subset_insert List.subset_insert

#align list.mem_insert_self List.mem_insert_self
#align list.mem_insert_of_mem List.mem_insert_of_mem
#align list.eq_or_mem_of_mem_insert List.eq_or_mem_of_mem_insert
#align list.length_insert_of_mem List.length_insert_of_mem
#align list.length_insert_of_not_mem List.length_insert_of_not_mem

end Insert

theorem mem_of_mem_suffix (hx : a ∈ l₁) (hl : l₁ <:+ l₂) : a ∈ l₂ :=
  hl.subset hx
#align list.mem_of_mem_suffix List.mem_of_mem_suffix

end List
