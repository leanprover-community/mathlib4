/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.infix
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Basic

/-!
# Prefixes, subfixes, infixes

This file proves properties about
* `List.prefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `List.subfix`: `l₁` is a subfix of `l₂` if `l₂` ends with `l₁`.
* `List.infix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some subfix of `l₂`.
* `List.inits`: The list of prefixes of a list.
* `List.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `Mathlib.Data.List.Defs`.

## Notation

`l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
`l₁ <:+ l₂`: `l₁` is a subfix of `l₂`.
`l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/

open Nat

variable {α β : Type _}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α} {m n : ℕ}

/-! ### prefix, suffix, infix -/


section Fix

@[simp]
theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ :=
  ⟨l₂, rfl⟩
#align list.prefix_append List.prefix_append

@[simp]
theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ :=
  ⟨l₁, rfl⟩
#align list.suffix_append List.suffix_append

theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ :=
  ⟨l₁, l₃, rfl⟩
#align list.infix_append List.infix_append

@[simp]
theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc]; apply infix_append
#align list.infix_append' List.infix_append'

theorem isPrefix.isInfix : l₁ <+: l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨[], t, h⟩
#align list.is_prefix.is_infix List.isPrefix.isInfix

theorem isSuffix.isInfix : l₁ <:+ l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨t, [], by rw [h, append_nil]⟩
#align list.is_suffix.is_infix List.isSuffix.isInfix

theorem nil_prefix (l : List α) : [] <+: l :=
  ⟨l, rfl⟩
#align list.nil_prefix List.nil_prefix

theorem nil_suffix (l : List α) : [] <:+ l :=
  ⟨l, append_nil _⟩
#align list.nil_suffix List.nil_suffix

theorem nil_infix (l : List α) : [] <:+: l :=
  (nil_prefix _).isInfix
#align list.nil_infix List.nil_infix

@[refl]
theorem prefix_refl (l : List α) : l <+: l :=
  ⟨[], append_nil _⟩
#align list.prefix_refl List.prefix_refl

@[refl]
theorem suffix_refl (l : List α) : l <:+ l :=
  ⟨[], rfl⟩
#align list.suffix_refl List.suffix_refl

@[refl]
theorem infix_refl (l : List α) : l <:+: l :=
  (prefix_refl l).isInfix
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

@[simp]
theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l :=
  suffix_append [a]
#align list.suffix_cons List.suffix_cons

theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp
#align list.prefix_concat List.prefix_concat

theorem infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := fun ⟨L₁, L₂, h⟩ => ⟨a :: L₁, L₂, h ▸ rfl⟩
#align list.infix_cons List.infix_cons

theorem infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a := fun ⟨L₁, L₂, h⟩ =>
  ⟨L₁, concat L₂ a, by simp_rw [← h, concat_eq_append, append_assoc]⟩
#align list.infix_concat List.infix_concat

@[trans]
theorem isPrefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
  | _, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩
#align list.is_prefix.trans List.isPrefix.trans

@[trans]
theorem isSuffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
  | _, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩
#align list.is_suffix.trans List.isSuffix.trans

@[trans]
theorem isInfix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
  | l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ => ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩
#align list.is_infix.trans List.isInfix.trans

protected theorem isInfix.sublist : l₁ <:+: l₂ → l₁ <+ l₂ := fun ⟨s, t, h⟩ => by
  rw [← h]
  exact (sublist_append_right _ _).trans (sublist_append_left _ _)
#align list.is_infix.sublist List.isInfix.sublist

protected theorem isInfix.subset (hl : l₁ <:+: l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset
#align list.is_infix.subset List.isInfix.subset

protected theorem isPrefix.sublist (h : l₁ <+: l₂) : l₁ <+ l₂ :=
  h.isInfix.sublist
#align list.is_prefix.sublist List.isPrefix.sublist

protected theorem isPrefix.subset (hl : l₁ <+: l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset
#align list.is_prefix.subset List.isPrefix.subset

protected theorem isSuffix.sublist (h : l₁ <:+ l₂) : l₁ <+ l₂ :=
  h.isInfix.sublist
#align list.is_suffix.sublist List.isSuffix.sublist

protected theorem isSuffix.subset (hl : l₁ <:+ l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset
#align list.is_suffix.subset List.isSuffix.subset

@[simp]
theorem reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
    fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_append, e]⟩⟩
#align list.reverse_suffix List.reverse_suffix

@[simp]
theorem reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix]; simp only [reverse_reverse]
#align list.reverse_prefix List.reverse_prefix

@[simp]
theorem reverse_infix : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ :=
  ⟨fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by
      rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e,
        reverse_reverse]⟩,
    fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by rw [append_assoc, ← reverse_append, ← reverse_append, e]⟩⟩
#align list.reverse_infix List.reverse_infix

alias reverse_prefix ↔ _ isSuffix.reverse
#align list.is_suffix.reverse List.isSuffix.reverse

alias reverse_suffix ↔ _ isPrefix.reverse
#align list.is_prefix.reverse List.isPrefix.reverse

alias reverse_infix ↔ _ isInfix.reverse
#align list.is_infix.reverse List.isInfix.reverse

theorem isInfix.length_le (h : l₁ <:+: l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le
#align list.is_infix.length_le List.isInfix.length_le

theorem isPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le
#align list.is_prefix.length_le List.isPrefix.length_le

theorem isSuffix.length_le (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le
#align list.is_suffix.length_le List.isSuffix.length_le

theorem eq_nil_of_infix_nil (h : l <:+: []) : l = [] :=
  eq_nil_of_sublist_nil h.sublist
#align list.eq_nil_of_infix_nil List.eq_nil_of_infix_nil

@[simp]
theorem infix_nil_iff : l <:+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_sublist_nil h.sublist, fun h => h ▸ infix_rfl⟩
#align list.infix_nil_iff List.infix_nil_iff

@[simp]
theorem prefix_nil_iff : l <+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.isInfix, fun h => h ▸ prefix_rfl⟩
#align list.prefix_nil_iff List.prefix_nil_iff

@[simp]
theorem suffix_nil_iff : l <:+ [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.isInfix, fun h => h ▸ suffix_rfl⟩
#align list.suffix_nil_iff List.suffix_nil_iff

alias prefix_nil_iff ↔ eq_nil_of_prefix_nil _
#align list.eq_nil_of_prefix_nil List.eq_nil_of_prefix_nil

alias suffix_nil_iff ↔ eq_nil_of_suffix_nil _
#align list.eq_nil_of_suffix_nil List.eq_nil_of_suffix_nil

theorem infix_iff_prefix_suffix (l₁ l₂ : List α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
  ⟨fun ⟨s, t, e⟩ => ⟨l₁ ++ t, ⟨_, rfl⟩, by rw [← e, append_assoc]; exact ⟨_, rfl⟩⟩,
    fun ⟨_, ⟨t, rfl⟩, s, e⟩ => ⟨s, t, by rw [append_assoc]; exact e⟩⟩
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

theorem prefix_of_prefix_length_le : ∀ { l₁ l₂ l₃ : List α } ,
  l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
| [] , l₂ , _, _, _, _ => nil_prefix _
| a :: l₁ , b :: l₂ , _ , ⟨ r₁ , rfl ⟩ , ⟨ r₂ , e ⟩ , ll => by
  injection e with _ e'
  subst b
  rcases prefix_of_prefix_length_le ⟨ _ , rfl ⟩ ⟨ _ , e' ⟩
    (le_of_succ_le_succ ll) with ⟨ r₃ , rfl ⟩
  exact ⟨ r₃ , rfl ⟩
#align list.prefix_of_prefix_length_le List.prefix_of_prefix_length_le

theorem prefix_or_prefix_of_prefix (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  (le_total (length l₁) (length l₂)).imp (prefix_of_prefix_length_le h₁ h₂)
    (prefix_of_prefix_length_le h₂ h₁)
#align list.prefix_or_prefix_of_prefix List.prefix_or_prefix_of_prefix

theorem suffix_of_suffix_length_le (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) :
    l₁ <:+ l₂ :=
  reverse_prefix.1 <|
    prefix_of_prefix_length_le (reverse_prefix.2 h₁) (reverse_prefix.2 h₂) (by simp [ll])
#align list.suffix_of_suffix_length_le List.suffix_of_suffix_length_le

theorem suffix_or_suffix_of_suffix (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  (prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp reverse_prefix.1
    reverse_prefix.1
#align list.suffix_or_suffix_of_suffix List.suffix_or_suffix_of_suffix

theorem suffix_cons_iff : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, hl₄⟩
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
    · exact hl₁.trans (l₂.suffix_cons _)
#align list.suffix_cons_iff List.suffix_cons_iff

theorem infix_cons_iff : l₁ <:+: a :: l₂ ↔ l₁ <+: a :: l₂ ∨ l₁ <:+: l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, t, hl₃⟩
    · exact Or.inl ⟨t, hl₃⟩
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, t, hl₄⟩
  · rintro (h | hl₁)
    · exact h.isInfix
    · exact infix_cons hl₁
#align list.infix_cons_iff List.infix_cons_iff

theorem infix_of_mem_join : ∀ {L : List (List α)}, l ∈ L → l <:+: join L
  | l' :: _, h =>
    match h with
    | List.Mem.head .. => infix_append [] _ _
    | List.Mem.tail _ hlMemL =>
      isInfix.trans (infix_of_mem_join hlMemL) <| (suffix_append _ _).isInfix
#align list.infix_of_mem_join List.infix_of_mem_join

theorem prefix_append_right_inj (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
  exists_congr fun r => by rw [append_assoc, append_right_inj]
#align list.prefix_append_right_inj List.prefix_append_right_inj

theorem prefix_cons_inj (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]
#align list.prefix_cons_inj List.prefix_cons_inj

theorem take_prefix (n) (l : List α) : take n l <+: l :=
  ⟨_, take_append_drop _ _⟩
#align list.take_prefix List.take_prefix

theorem drop_suffix (n) (l : List α) : drop n l <:+ l :=
  ⟨_, take_append_drop _ _⟩
#align list.drop_suffix List.drop_suffix

theorem take_sublist (n) (l : List α) : take n l <+ l :=
  (take_prefix n l).sublist
#align list.take_sublist List.take_sublist

theorem drop_sublist (n) (l : List α) : drop n l <+ l :=
  (drop_suffix n l).sublist
#align list.drop_sublist List.drop_sublist

theorem take_subset (n) (l : List α) : take n l ⊆ l :=
  (take_sublist n l).subset
#align list.take_subset List.take_subset

theorem drop_subset (n) (l : List α) : drop n l ⊆ l :=
  (drop_sublist n l).subset
#align list.drop_subset List.drop_subset

theorem mem_of_mem_take (h : a ∈ l.take n) : a ∈ l :=
  take_subset n l h
#align list.mem_of_mem_take List.mem_of_mem_take

#align list.mem_of_mem_drop List.mem_of_mem_drop

lemma dropSlice_sublist (n m : ℕ) (l : List α) : l.dropSlice n m <+ l :=
  calc l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, add_comm]
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
  ⟨l.dropWhile p, takeWhile_append_drop p l⟩
#align list.take_while_prefix List.takeWhile_prefix

theorem dropWhile_suffix (p : α → Bool) : l.dropWhile p <:+ l :=
  ⟨l.takeWhile p, takeWhile_append_drop p l⟩
#align list.drop_while_suffix List.dropWhile_suffix

theorem dropLast_prefix : ∀ l : List α, l.dropLast <+: l
  | [] => ⟨nil, by rw [dropLast, List.append_nil]⟩
  | a :: l => ⟨_, dropLast_append_getLast (cons_ne_nil a l)⟩
#align list.init_prefix List.dropLast_prefix

theorem tail_suffix (l : List α) : tail l <:+ l := by rw [← drop_one]; apply drop_suffix
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
#align list.prefix_iff_eq_append List.prefix_iff_eq_append

theorem suffix_iff_eq_append : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; simp only [length_append, add_tsub_cancel_right, take_left], fun e =>
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
    else
      isFalse fun ⟨t, te⟩ => h <| by injection te
#align list.decidable_prefix List.decidablePrefix

-- Alternatively, use mem_tails
instance decidableSuffix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+ l₂)
  | [], l₂ => isTrue ⟨l₂, append_nil _⟩
  | a :: l₁, [] => isFalse <| mt (Sublist.length_le ∘ isSuffix.sublist) (by simp)
  | l₁, b :: l₂ =>
    @decidable_of_decidable_of_iff _ _
      (@instDecidableOr _ _ _ (l₁.decidableSuffix l₂))
      suffix_cons_iff.symm
termination_by decidableSuffix l₁ l₂ => (l₁, l₂)
#align list.decidable_suffix List.decidableSuffix

instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ => by simp at te
  | l₁, b :: l₂ =>
    @decidable_of_decidable_of_iff _ _
      (@instDecidableOr _ _ (l₁.decidablePrefix (b :: l₂)) (l₁.decidableInfix l₂))
      infix_cons_iff.symm
termination_by decidableInfix l₁ l₂ => (l₁, l₂)
#align list.decidable_infix List.decidableInfix

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
        simp [le_of_lt hm, specializedIH, true_and_iff, min_eq_left, eq_self_iff_true, length, take]
        exact ⟨Nat.succ_le_succ, Nat.le_of_succ_le_succ⟩
#align list.prefix_take_le_iff List.prefix_take_le_iff

theorem cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ := by
  constructor
  · rintro ⟨L, hL⟩
    simp only [cons_append] at hL
    injection hL with hLLeft hLRight
    exact ⟨hLLeft, ⟨L, hLRight⟩⟩
  · rintro ⟨rfl, h⟩
    rwa [prefix_cons_inj]
#align list.cons_prefix_iff List.cons_prefix_iff

theorem isPrefix.map (h : l₁ <+: l₂) (f : α → β) : l₁.map f <+: l₂.map f := by
  induction' l₁ with hd tl hl generalizing l₂
  · simp only [nil_prefix, map_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h
      simp only [List.map_cons, h, prefix_cons_inj, hl, map]
#align list.is_prefix.map List.isPrefix.map

theorem isPrefix.filter_map (h : l₁ <+: l₂) (f : α → Option β) :
    l₁.filterMap f <+: l₂.filterMap f := by
  induction' l₁ with hd₁ tl₁ hl generalizing l₂
  · simp only [nil_prefix, filterMap_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h
      rw [← @singleton_append _ hd₁ _, ← @singleton_append _ hd₂ _, filterMap_append,
        filterMap_append, h.left, prefix_append_right_inj]
      exact hl h.right
#align list.is_prefix.filter_map List.isPrefix.filter_map

theorem isPrefix.reduceOption {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filter_map id
#align list.is_prefix.reduce_option List.isPrefix.reduceOption

theorem isPrefix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact prefix_append _ _
#align list.is_prefix.filter List.isPrefix.filter

theorem isSuffix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    l₁.filter p <:+ l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact suffix_append _ _
#align list.is_suffix.filter List.isSuffix.filter

theorem isInfix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]
  exact infix_append _ _ _
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
#align list.mem_inits List.mem_inits

@[simp]
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_suffix_nil⟩
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
#align list.mem_tails List.mem_tails

theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp
#align list.inits_cons List.inits_cons

theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp
#align list.tails_cons List.tails_cons

@[simp]
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
  | [], a :: t => by simp[· ∘ ·]
  | a :: s, t => by simp [inits_append s t, · ∘ ·]
#align list.inits_append List.inits_append

@[simp]
theorem tails_append :
    ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [tails_append s t]
#align list.tails_append List.tails_append

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
  | a :: l => by simp [inits_eq_tails l, map_eq_map_iff, reverse_map]
#align list.inits_eq_tails List.inits_eq_tails

theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
  | a :: l => by simp [tails_eq_inits l, append_left_inj]
#align list.tails_eq_inits List.tails_eq_inits

theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self, reverse_map]
#align list.inits_reverse List.inits_reverse

theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self, reverse_map]
#align list.tails_reverse List.tails_reverse

theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self, reverse_map]
#align list.map_reverse_inits List.map_reverse_inits

theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self, reverse_map]
#align list.map_reverse_tails List.map_reverse_tails

@[simp]
theorem length_tails (l : List α) : length (tails l) = length l + 1 := by
  induction' l with x l IH
  · simp
  · simpa using IH
#align list.length_tails List.length_tails

@[simp]
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]
#align list.length_inits List.length_inits

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
#align list.nth_le_tails List.nth_le_tails

@[simp]
theorem nth_le_inits (l : List α) (n : ℕ) (hn : n < length (inits l)) :
    nthLe (inits l) n hn = l.take n := by
  induction' l with x l IH generalizing n
  · simp
  · cases n
    · simp[nthLe_cons]
    · simpa[nthLe_cons] using IH _ _
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
  · simp only [insert_of_mem h, insert, suffix_refl]
  · simp only [insert_of_not_mem h, suffix_cons, insert]
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
