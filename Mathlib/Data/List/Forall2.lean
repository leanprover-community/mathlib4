/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module data.list.forall2
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Infix

/-!
# Double universal quantification on a list

This file provides an API for `list.forall₂` (definition in `data.list.defs`).
`forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length, and whenever `a` is the nth element
of `l₁`, and `b` is the nth element of `l₂`, then `R a b` is satisfied.
-/


open Nat Function

namespace List

variable {α β γ δ : Type _} {R S : α → β → Prop} {P : γ → δ → Prop} {Rₐ : α → α → Prop}

open Relator

mk_iff_of_inductive_prop List.Forall₂ List.forall₂_iff

@[simp]
theorem forall₂_cons {a b l₁ l₂} : Forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ Forall₂ R l₁ l₂ :=
  ⟨fun h => by cases' h with h₁ h₂ <;> constructor <;> assumption, fun ⟨h₁, h₂⟩ =>
    Forall₂.cons h₁ h₂⟩
#align list.forall₂_cons List.forall₂_cons

theorem Forall₂.imp (H : ∀ a b, R a b → S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> solve_by_elim
#align list.forall₂.imp List.Forall₂.imp

theorem Forall₂.mp {Q : α → β → Prop} (h : ∀ a b, Q a b → R a b → S a b) :
    ∀ {l₁ l₂}, Forall₂ Q l₁ l₂ → Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | [], [], forall₂.nil, forall₂.nil => Forall₂.nil
  | a :: l₁, b :: l₂, forall₂.cons hr hrs, forall₂.cons hq hqs =>
    Forall₂.cons (h a b hr hq) (forall₂.mp hrs hqs)
#align list.forall₂.mp List.Forall₂.mp

theorem Forall₂.flip : ∀ {a b}, Forall₂ (flip R) b a → Forall₂ R a b
  | _, _, forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => Forall₂.cons h₁ h₂.flip
#align list.forall₂.flip List.Forall₂.flip

@[simp]
theorem forall₂_same : ∀ {l : List α}, Forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x
  | [] => by simp
  | a :: l => by simp [@forall₂_same l]
#align list.forall₂_same List.forall₂_same

theorem forall₂_refl [IsRefl α Rₐ] (l : List α) : Forall₂ Rₐ l l :=
  forall₂_same.2 fun a h => refl _
#align list.forall₂_refl List.forall₂_refl

@[simp]
theorem forall₂_eq_eq_eq : Forall₂ ((· = ·) : α → α → Prop) = (· = ·) :=
  by
  funext a b; apply propext
  constructor
  · intro h
    induction h
    · rfl
    simp only [*] <;> constructor <;> rfl
  · rintro rfl
    exact forall₂_refl _
#align list.forall₂_eq_eq_eq List.forall₂_eq_eq_eq

@[simp]
theorem forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H <;> rfl, by rintro rfl <;> exact forall₂.nil⟩
#align list.forall₂_nil_left_iff List.forall₂_nil_left_iff

@[simp]
theorem forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H <;> rfl, by rintro rfl <;> exact forall₂.nil⟩
#align list.forall₂_nil_right_iff List.forall₂_nil_right_iff

theorem forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨b, u', h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂
#align list.forall₂_cons_left_iff List.forall₂_cons_left_iff

theorem forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨b, u', h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂
#align list.forall₂_cons_right_iff List.forall₂_cons_right_iff

theorem forall₂_and_left {p : α → Prop} :
    ∀ l u, Forall₂ (fun a b => p a ∧ R a b) l u ↔ (∀ a ∈ l, p a) ∧ Forall₂ R l u
  | [], u => by
    simp only [forall₂_nil_left_iff, forall_prop_of_false (not_mem_nil _), imp_true_iff,
      true_and_iff]
  | a :: l, u => by
    simp only [forall₂_and_left l, forall₂_cons_left_iff, forall_mem_cons, and_assoc', and_comm',
      and_left_comm, exists_and_distrib_left.symm]
#align list.forall₂_and_left List.forall₂_and_left

@[simp]
theorem forall₂_map_left_iff {f : γ → α} :
    ∀ {l u}, Forall₂ R (map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u
  | [], _ => by simp only [map, forall₂_nil_left_iff]
  | a :: l, _ => by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]
#align list.forall₂_map_left_iff List.forall₂_map_left_iff

@[simp]
theorem forall₂_map_right_iff {f : γ → β} :
    ∀ {l u}, Forall₂ R l (map f u) ↔ Forall₂ (fun a c => R a (f c)) l u
  | _, [] => by simp only [map, forall₂_nil_right_iff]
  | _, b :: u => by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]
#align list.forall₂_map_right_iff List.forall₂_map_right_iff

theorem left_unique_forall₂' (hr : LeftUnique R) : ∀ {a b c}, Forall₂ R a c → Forall₂ R b c → a = b
  | a₀, nil, a₁, forall₂.nil, forall₂.nil => rfl
  | a₀ :: l₀, b :: l, a₁ :: l₁, forall₂.cons ha₀ h₀, forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ left_unique_forall₂' h₀ h₁ ▸ rfl
#align list.left_unique_forall₂' List.left_unique_forall₂'

theorem Relator.LeftUnique.forall₂ (hr : LeftUnique R) : LeftUnique (Forall₂ R) :=
  @left_unique_forall₂' _ _ _ hr
#align relator.left_unique.forall₂ Relator.LeftUnique.forall₂

theorem right_unique_forall₂' (hr : RightUnique R) :
    ∀ {a b c}, Forall₂ R a b → Forall₂ R a c → b = c
  | nil, a₀, a₁, forall₂.nil, forall₂.nil => rfl
  | b :: l, a₀ :: l₀, a₁ :: l₁, forall₂.cons ha₀ h₀, forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ right_unique_forall₂' h₀ h₁ ▸ rfl
#align list.right_unique_forall₂' List.right_unique_forall₂'

theorem Relator.RightUnique.forall₂ (hr : RightUnique R) : RightUnique (Forall₂ R) :=
  @right_unique_forall₂' _ _ _ hr
#align relator.right_unique.forall₂ Relator.RightUnique.forall₂

theorem Relator.BiUnique.forall₂ (hr : BiUnique R) : BiUnique (Forall₂ R) :=
  ⟨hr.left.forall₂, hr.right.forall₂⟩
#align relator.bi_unique.forall₂ Relator.BiUnique.forall₂

theorem Forall₂.length_eq : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → length l₁ = length l₂
  | _, _, forall₂.nil => rfl
  | _, _, forall₂.cons h₁ h₂ => congr_arg succ (forall₂.length_eq h₂)
#align list.forall₂.length_eq List.Forall₂.length_eq

theorem Forall₂.nth_le :
    ∀ {x : List α} {y : List β} (h : Forall₂ R x y) ⦃i : ℕ⦄ (hx : i < x.length) (hy : i < y.length),
      R (x.nthLe i hx) (y.nthLe i hy)
  | a₁ :: l₁, a₂ :: l₂, forall₂.cons ha hl, 0, hx, hy => ha
  | a₁ :: l₁, a₂ :: l₂, forall₂.cons ha hl, succ i, hx, hy => hl.nthLe _ _
#align list.forall₂.nth_le List.Forall₂.nth_le

theorem forall₂_of_length_eq_of_nth_le :
    ∀ {x : List α} {y : List β},
      x.length = y.length → (∀ i h₁ h₂, R (x.nthLe i h₁) (y.nthLe i h₂)) → Forall₂ R x y
  | [], [], hl, h => Forall₂.nil
  | a₁ :: l₁, a₂ :: l₂, hl, h =>
    Forall₂.cons (h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
      (forall₂_of_length_eq_of_nth_le (succ.inj hl) fun i h₁ h₂ =>
        h i.succ (succ_lt_succ h₁) (succ_lt_succ h₂))
#align list.forall₂_of_length_eq_of_nth_le List.forall₂_of_length_eq_of_nth_le

theorem forall₂_iff_nth_le {l₁ : List α} {l₂ : List β} :
    Forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧ ∀ i h₁ h₂, R (l₁.nthLe i h₁) (l₂.nthLe i h₂) :=
  ⟨fun h => ⟨h.length_eq, h.nthLe⟩, And.ndrec forall₂_of_length_eq_of_nth_le⟩
#align list.forall₂_iff_nth_le List.forall₂_iff_nth_le

theorem forall₂_zip : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b
  | _, _, forall₂.cons h₁ h₂, x, y, Or.inl rfl => h₁
  | _, _, forall₂.cons h₁ h₂, x, y, Or.inr h₃ => forall₂_zip h₂ h₃
#align list.forall₂_zip List.forall₂_zip

theorem forall₂_iff_zip {l₁ l₂} :
    Forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b :=
  ⟨fun h => ⟨Forall₂.length_eq h, @forall₂_zip _ _ _ _ _ h⟩, fun h =>
    by
    cases' h with h₁ h₂
    induction' l₁ with a l₁ IH generalizing l₂
    · cases length_eq_zero.1 h₁.symm
      constructor
    · cases' l₂ with b l₂ <;> injection h₁ with h₁
      exact forall₂.cons (h₂ <| Or.inl rfl) ((IH h₁) fun a b h => h₂ <| Or.inr h)⟩
#align list.forall₂_iff_zip List.forall₂_iff_zip

theorem forall₂_take : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (take n l₁) (take n l₂)
  | 0, _, _, _ => by simp only [forall₂.nil, take]
  | n + 1, _, _, forall₂.nil => by simp only [forall₂.nil, take]
  | n + 1, _, _, forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_take n]
#align list.forall₂_take List.forall₂_take

theorem forall₂_drop : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (drop n l₁) (drop n l₂)
  | 0, _, _, h => by simp only [drop, h]
  | n + 1, _, _, forall₂.nil => by simp only [forall₂.nil, drop]
  | n + 1, _, _, forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_drop n]
#align list.forall₂_drop List.forall₂_drop

theorem forall₂_take_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.take (length l₁) l) l₁ :=
  by
  have h' : Forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)) :=
    forall₂_take (length l₁) h
  rwa [take_left] at h'
#align list.forall₂_take_append List.forall₂_take_append

theorem forall₂_drop_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.drop (length l₁) l) l₂ :=
  by
  have h' : Forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)) :=
    forall₂_drop (length l₁) h
  rwa [drop_left] at h'
#align list.forall₂_drop_append List.forall₂_drop_append

theorem rel_mem (hr : BiUnique R) : (R ⇒ Forall₂ R ⇒ Iff) (· ∈ ·) (· ∈ ·)
  | a, b, h, [], [], forall₂.nil => by simp only [not_mem_nil]
  | a, b, h, a' :: as, b' :: bs, forall₂.cons h₁ h₂ => rel_or (rel_eq hr h h₁) (rel_mem h h₂)
#align list.rel_mem List.rel_mem

theorem rel_map : ((R ⇒ P) ⇒ Forall₂ R ⇒ Forall₂ P) map map
  | f, g, h, [], [], forall₂.nil => Forall₂.nil
  | f, g, h, a :: as, b :: bs, forall₂.cons h₁ h₂ => Forall₂.cons (h h₁) (rel_map (@h) h₂)
#align list.rel_map List.rel_map

theorem rel_append : (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) append append
  | [], [], h, l₁, l₂, hl => hl
  | a :: as, b :: bs, forall₂.cons h₁ h₂, l₁, l₂, hl => Forall₂.cons h₁ (rel_append h₂ hl)
#align list.rel_append List.rel_append

theorem rel_reverse : (Forall₂ R ⇒ Forall₂ R) reverse reverse
  | [], [], forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ =>
    by
    simp only [reverse_cons]
    exact rel_append (rel_reverse h₂) (forall₂.cons h₁ forall₂.nil)
#align list.rel_reverse List.rel_reverse

@[simp]
theorem forall₂_reverse_iff {l₁ l₂} : Forall₂ R (reverse l₁) (reverse l₂) ↔ Forall₂ R l₁ l₂ :=
  Iff.intro
    (fun h => by
      rw [← reverse_reverse l₁, ← reverse_reverse l₂]
      exact rel_reverse h)
    fun h => rel_reverse h
#align list.forall₂_reverse_iff List.forall₂_reverse_iff

theorem rel_join : (Forall₂ (Forall₂ R) ⇒ Forall₂ R) join join
  | [], [], forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => rel_append h₁ (rel_join h₂)
#align list.rel_join List.rel_join

theorem rel_bind : (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P) List.bind List.bind :=
  fun a b h₁ f g h₂ => rel_join (rel_map (@h₂) h₁)
#align list.rel_bind List.rel_bind

theorem rel_foldl : ((P ⇒ R ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldl foldl
  | f, g, hfg, _, _, h, _, _, forall₂.nil => h
  | f, g, hfg, x, y, hxy, _, _, forall₂.cons hab hs => rel_foldl (@hfg) (hfg hxy hab) hs
#align list.rel_foldl List.rel_foldl

theorem rel_foldr : ((R ⇒ P ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldr foldr
  | f, g, hfg, _, _, h, _, _, forall₂.nil => h
  | f, g, hfg, x, y, hxy, _, _, forall₂.cons hab hs => hfg hab (rel_foldr (@hfg) hxy hs)
#align list.rel_foldr List.rel_foldr

theorem rel_filter {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : (R ⇒ (· ↔ ·)) p q) : (Forall₂ R ⇒ Forall₂ R) (filter p) (filter q)
  | _, _, forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => by
    by_cases p a
    · have : q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_pos _ h, filter_cons_of_pos _ this, forall₂_cons, h₁, rel_filter h₂,
        and_true_iff]
    · have : ¬q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_neg _ h, filter_cons_of_neg _ this, rel_filter h₂]
#align list.rel_filter List.rel_filter

theorem rel_filter_map : ((R ⇒ Option.Rel P) ⇒ Forall₂ R ⇒ Forall₂ P) filterMap filterMap
  | f, g, hfg, _, _, forall₂.nil => Forall₂.nil
  | f, g, hfg, a :: as, b :: bs, forall₂.cons h₁ h₂ => by
    rw [filter_map_cons, filter_map_cons] <;>
      exact
        match f a, g b, hfg h₁ with
        | _, _, Option.Rel.none => rel_filter_map (@hfg) h₂
        | _, _, Option.Rel.some h => forall₂.cons h (rel_filter_map (@hfg) h₂)
#align list.rel_filter_map List.rel_filter_map

@[to_additive]
theorem rel_prod [Monoid α] [Monoid β] (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)) :
    (Forall₂ R ⇒ R) prod prod :=
  rel_foldl hf h
#align list.rel_prod List.rel_prod

/-- Given a relation `R`, `sublist_forall₂ r l₁ l₂` indicates that there is a sublist of `l₂` such
  that `forall₂ r l₁ l₂`. -/
inductive SublistForall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil {l} : sublist_forall₂ [] l
  | cons {a₁ a₂ l₁ l₂} : R a₁ a₂ → sublist_forall₂ l₁ l₂ → sublist_forall₂ (a₁ :: l₁) (a₂ :: l₂)
  | cons_right {a l₁ l₂} : sublist_forall₂ l₁ l₂ → sublist_forall₂ l₁ (a :: l₂)
#align list.sublist_forall₂ List.SublistForall₂

theorem sublist_forall₂_iff {l₁ : List α} {l₂ : List β} :
    SublistForall₂ R l₁ l₂ ↔ ∃ l, Forall₂ R l₁ l ∧ l <+ l₂ :=
  by
  constructor <;> intro h
  · induction' h with _ a b l1 l2 rab rll ih b l1 l2 hl ih
    · exact ⟨nil, forall₂.nil, nil_sublist _⟩
    · obtain ⟨l, hl1, hl2⟩ := ih
      refine' ⟨b :: l, forall₂.cons rab hl1, hl2.cons_cons b⟩
    · obtain ⟨l, hl1, hl2⟩ := ih
      exact ⟨l, hl1, hl2.trans (sublist.cons _ _ _ (sublist.refl _))⟩
  · obtain ⟨l, hl1, hl2⟩ := h
    revert l₁
    induction' hl2 with _ _ _ _ ih _ _ _ _ ih <;> intro l₁ hl1
    · rw [forall₂_nil_right_iff.1 hl1]
      exact sublist_forall₂.nil
    · exact sublist_forall₂.cons_right (ih hl1)
    · cases' hl1 with _ _ _ _ hr hl _
      exact sublist_forall₂.cons hr (ih hl)
#align list.sublist_forall₂_iff List.sublist_forall₂_iff

instance SublistForall₂.is_refl [IsRefl α Rₐ] : IsRefl (List α) (SublistForall₂ Rₐ) :=
  ⟨fun l => sublist_forall₂_iff.2 ⟨l, forall₂_refl l, Sublist.refl l⟩⟩
#align list.sublist_forall₂.is_refl List.SublistForall₂.is_refl

instance SublistForall₂.is_trans [IsTrans α Rₐ] : IsTrans (List α) (SublistForall₂ Rₐ) :=
  ⟨fun a b c => by
    revert a b
    induction' c with _ _ ih
    · rintro _ _ h1 (_ | _ | _)
      exact h1
    · rintro a b h1 h2
      cases' h2 with _ _ _ _ _ hbc tbc _ _ y1 btc
      · cases h1
        exact sublist_forall₂.nil
      · cases' h1 with _ _ _ _ _ hab tab _ _ _ atb
        · exact sublist_forall₂.nil
        · exact sublist_forall₂.cons (trans hab hbc) (ih _ _ tab tbc)
        · exact sublist_forall₂.cons_right (ih _ _ atb tbc)
      · exact sublist_forall₂.cons_right (ih _ _ h1 btc)⟩
#align list.sublist_forall₂.is_trans List.SublistForall₂.is_trans

theorem Sublist.sublist_forall₂ {l₁ l₂ : List α} (h : l₁ <+ l₂) [IsRefl α Rₐ] :
    SublistForall₂ Rₐ l₁ l₂ :=
  sublist_forall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩
#align list.sublist.sublist_forall₂ List.Sublist.sublist_forall₂

theorem tail_sublist_forall₂_self [IsRefl α Rₐ] (l : List α) : SublistForall₂ Rₐ l.tail l :=
  l.tail_sublist.SublistForall₂
#align list.tail_sublist_forall₂_self List.tail_sublist_forall₂_self

end List

