/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Mathlib.Data.List.Forall2
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Init.Data.Fin.Basic

#align_import data.list.nodup from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-!
# Lists with no duplicates

`List.Nodup` is defined in `Data/List/Basic`. In this file we prove various properties of this
predicate.
-/


universe u v

open Nat Function

variable {α : Type u} {β : Type v} {l l₁ l₂ : List α} {r : α → α → Prop} {a b : α}

namespace List

@[simp]
theorem forall_mem_ne {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩
#align list.forall_mem_ne List.forall_mem_ne

@[simp]
theorem nodup_nil : @Nodup α [] :=
  Pairwise.nil
#align list.nodup_nil List.nodup_nil

@[simp]
theorem nodup_cons {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]
#align list.nodup_cons List.nodup_cons

protected theorem Pairwise.nodup {l : List α} {r : α → α → Prop} [IsIrrefl α r] (h : Pairwise r l) :
    Nodup l :=
  h.imp ne_of_irrefl
#align list.pairwise.nodup List.Pairwise.nodup

theorem rel_nodup {r : α → β → Prop} (hr : Relator.BiUnique r) : (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup
  | _, _, Forall₂.nil => by simp only [nodup_nil]
  | _, _, Forall₂.cons hab h => by
    simpa only [nodup_cons] using
      Relator.rel_and (Relator.rel_not (rel_mem hr hab h)) (rel_nodup hr h)
#align list.rel_nodup List.rel_nodup

protected theorem Nodup.cons (ha : a ∉ l) (hl : Nodup l) : Nodup (a :: l) :=
  nodup_cons.2 ⟨ha, hl⟩
#align list.nodup.cons List.Nodup.cons

theorem nodup_singleton (a : α) : Nodup [a] :=
  pairwise_singleton _ _
#align list.nodup_singleton List.nodup_singleton

theorem Nodup.of_cons (h : Nodup (a :: l)) : Nodup l :=
  (nodup_cons.1 h).2
#align list.nodup.of_cons List.Nodup.of_cons

theorem Nodup.not_mem (h : (a :: l).Nodup) : a ∉ l :=
  (nodup_cons.1 h).1
#align list.nodup.not_mem List.Nodup.not_mem

theorem not_nodup_cons_of_mem : a ∈ l → ¬Nodup (a :: l) :=
  imp_not_comm.1 Nodup.not_mem
#align list.not_nodup_cons_of_mem List.not_nodup_cons_of_mem

protected theorem Nodup.sublist : l₁ <+ l₂ → Nodup l₂ → Nodup l₁ :=
  Pairwise.sublist
#align list.nodup.sublist List.Nodup.sublist

theorem not_nodup_pair (a : α) : ¬Nodup [a, a] :=
  not_nodup_cons_of_mem <| mem_singleton_self _
#align list.not_nodup_pair List.not_nodup_pair

theorem nodup_iff_sublist {l : List α} : Nodup l ↔ ∀ a, ¬[a, a] <+ l :=
  ⟨fun d a h => not_nodup_pair a (d.sublist h),
    by
      induction' l with a l IH <;> intro h; · exact nodup_nil
      exact (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons fun al =>
        h a <| (singleton_sublist.2 al).cons_cons _⟩
#align list.nodup_iff_sublist List.nodup_iff_sublist

theorem nodup_iff_injective_getElem {l : List α} :
    Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1]) :=
  pairwise_iff_getElem.trans
    ⟨fun h i j hg => by
      cases' i with i hi; cases' j with j hj
      rcases lt_trichotomy i j with (hij | rfl | hji)
      · exact (h i j hi hj hij hg).elim
      · rfl
      · exact (h j i hj hi hji hg.symm).elim,
      fun hinj i j hi hj hij h => Nat.ne_of_lt hij (Fin.val_eq_of_eq (@hinj ⟨i, hi⟩ ⟨j, hj⟩ h))⟩

-- Porting note (#10756): new theorem
theorem nodup_iff_injective_get {l : List α} :
    Nodup l ↔ Function.Injective l.get := by
  rw [nodup_iff_injective_getElem]
  change _ ↔ Injective (fun i => l.get i)
  simp

set_option linter.deprecated false in
@[deprecated nodup_iff_injective_get (since := "2023-01-10")]
theorem nodup_iff_nthLe_inj {l : List α} :
    Nodup l ↔ ∀ i j h₁ h₂, nthLe l i h₁ = nthLe l j h₂ → i = j :=
  nodup_iff_injective_get.trans
    ⟨fun hinj _ _ _ _ h => congr_arg Fin.val (hinj h),
     fun hinj i j h => Fin.eq_of_veq (hinj i j i.2 j.2 h)⟩
#align list.nodup_iff_nth_le_inj List.nodup_iff_nthLe_inj

theorem Nodup.get_inj_iff {l : List α} (h : Nodup l) {i j : Fin l.length} :
    l.get i = l.get j ↔ i = j :=
  (nodup_iff_injective_get.1 h).eq_iff

theorem Nodup.getElem_inj_iff {l : List α} (h : Nodup l)
    {i : Nat} {hi : i < l.length} {j : Nat} {hj : j < l.length} :
    l[i] = l[j] ↔ i = j := by
  have := @Nodup.get_inj_iff _ _ h ⟨i, hi⟩ ⟨j, hj⟩
  simpa

set_option linter.deprecated false in
@[deprecated Nodup.get_inj_iff (since := "2023-01-10")]
theorem Nodup.nthLe_inj_iff {l : List α} (h : Nodup l) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) : l.nthLe i hi = l.nthLe j hj ↔ i = j :=
  ⟨nodup_iff_nthLe_inj.mp h _ _ _ _, by simp (config := { contextual := true })⟩
#align list.nodup.nth_le_inj_iff List.Nodup.nthLe_inj_iff

theorem nodup_iff_getElem?_ne_getElem? {l : List α} :
    l.Nodup ↔ ∀ i j : ℕ, i < j → j < l.length → l[i]? ≠ l[j]? := by
  rw [Nodup, pairwise_iff_getElem]
  constructor
  · intro h i j hij hj
    rw [getElem?_eq_getElem (lt_trans hij hj), getElem?_eq_getElem hj, Ne, Option.some_inj]
    exact h _ _ _ _ hij
  · intro h i j hi hj hij
    rw [Ne, ← Option.some_inj, ← getElem?_eq_getElem, ← getElem?_eq_getElem]
    exact h i j hij hj

theorem nodup_iff_get?_ne_get? {l : List α} :
    l.Nodup ↔ ∀ i j : ℕ, i < j → j < l.length → l.get? i ≠ l.get? j := by
  simp [nodup_iff_getElem?_ne_getElem?]
#align list.nodup_iff_nth_ne_nth List.nodup_iff_get?_ne_get?

theorem Nodup.ne_singleton_iff {l : List α} (h : Nodup l) (x : α) :
    l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x := by
  induction' l with hd tl hl
  · simp
  · specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · suffices ∃ y ∈ hd :: tl, y ≠ x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩
#align list.nodup.ne_singleton_iff List.Nodup.ne_singleton_iff

theorem not_nodup_of_get_eq_of_ne (xs : List α) (n m : Fin xs.length)
    (h : xs.get n = xs.get m) (hne : n ≠ m) : ¬Nodup xs := by
  rw [nodup_iff_injective_get]
  exact fun hinj => hne (hinj h)
#align list.nth_le_eq_of_ne_imp_not_nodup List.not_nodup_of_get_eq_of_ne

theorem indexOf_getElem [DecidableEq α] {l : List α} (H : Nodup l) (i : Nat) (h : i < l.length) :
    indexOf l[i] l = i :=
  suffices (⟨indexOf l[i] l, indexOf_lt_length.2 (get_mem _ _ _)⟩ : Fin l.length) = ⟨i, h⟩
    from Fin.val_eq_of_eq this
  nodup_iff_injective_get.1 H (by simp)

-- This is incorrectly named and should be `indexOf_get`;
-- this already exists, so will require a deprecation dance.
theorem get_indexOf [DecidableEq α] {l : List α} (H : Nodup l) (i : Fin l.length) :
    indexOf (get l i) l = i := by
  simp [indexOf_getElem, H]

#align list.nth_le_index_of List.get_indexOf

theorem nodup_iff_count_le_one [DecidableEq α] {l : List α} : Nodup l ↔ ∀ a, count a l ≤ 1 :=
  nodup_iff_sublist.trans <|
    forall_congr' fun a =>
      have : replicate 2 a <+ l ↔ 1 < count a l := (le_count_iff_replicate_sublist ..).symm
      (not_congr this).trans not_lt
#align list.nodup_iff_count_le_one List.nodup_iff_count_le_one

theorem nodup_iff_count_eq_one [DecidableEq α] : Nodup l ↔ ∀ a ∈ l, count a l = 1 :=
  nodup_iff_count_le_one.trans <| forall_congr' fun _ =>
    ⟨fun H h => H.antisymm (count_pos_iff_mem.mpr h),
     fun H => if h : _ then (H h).le else (count_eq_zero.mpr h).trans_le (Nat.zero_le 1)⟩

theorem nodup_replicate (a : α) : ∀ {n : ℕ}, Nodup (replicate n a) ↔ n ≤ 1
  | 0 => by simp [Nat.zero_le]
  | 1 => by simp
  | n + 2 =>
    iff_of_false
      (fun H => nodup_iff_sublist.1 H a ((replicate_sublist_replicate _).2 (Nat.le_add_left 2 n)))
      (not_le_of_lt <| Nat.le_add_left 2 n)
#align list.nodup_replicate List.nodup_replicate

@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {l : List α} (d : Nodup l) (h : a ∈ l) :
    count a l = 1 :=
  _root_.le_antisymm (nodup_iff_count_le_one.1 d a) (Nat.succ_le_of_lt (count_pos_iff_mem.2 h))
#align list.count_eq_one_of_mem List.count_eq_one_of_mem

theorem count_eq_of_nodup [DecidableEq α] {a : α} {l : List α} (d : Nodup l) :
    count a l = if a ∈ l then 1 else 0 := by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_not_mem h
#align list.count_eq_of_nodup List.count_eq_of_nodup

theorem Nodup.of_append_left : Nodup (l₁ ++ l₂) → Nodup l₁ :=
  Nodup.sublist (sublist_append_left l₁ l₂)
#align list.nodup.of_append_left List.Nodup.of_append_left

theorem Nodup.of_append_right : Nodup (l₁ ++ l₂) → Nodup l₂ :=
  Nodup.sublist (sublist_append_right l₁ l₂)
#align list.nodup.of_append_right List.Nodup.of_append_right

theorem nodup_append {l₁ l₂ : List α} :
    Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂ := by
  simp only [Nodup, pairwise_append, disjoint_iff_ne]
#align list.nodup_append List.nodup_append

theorem disjoint_of_nodup_append {l₁ l₂ : List α} (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂ :=
  (nodup_append.1 d).2.2
#align list.disjoint_of_nodup_append List.disjoint_of_nodup_append

theorem Nodup.append (d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂) : Nodup (l₁ ++ l₂) :=
  nodup_append.2 ⟨d₁, d₂, dj⟩
#align list.nodup.append List.Nodup.append

theorem nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁) := by
  simp only [nodup_append, and_left_comm, disjoint_comm]
#align list.nodup_append_comm List.nodup_append_comm

theorem nodup_middle {a : α} {l₁ l₂ : List α} :
    Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :: (l₁ ++ l₂)) := by
  simp only [nodup_append, not_or, and_left_comm, and_assoc, nodup_cons, mem_append,
    disjoint_cons_right]
#align list.nodup_middle List.nodup_middle

theorem Nodup.of_map (f : α → β) {l : List α} : Nodup (map f l) → Nodup l :=
  (Pairwise.of_map f) fun _ _ => mt <| congr_arg f
#align list.nodup.of_map List.Nodup.of_mapₓ -- Porting note: different universe order

theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : Nodup l) :
    (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)
#align list.nodup.map_on List.Nodup.map_onₓ -- Porting note: different universe order

theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : Nodup (map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y := by
  induction' l with hd tl ih
  · simp
  · simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃
#align list.inj_on_of_nodup_map List.inj_on_of_nodup_map

theorem nodup_map_iff_inj_on {f : α → β} {l : List α} (d : Nodup l) :
    Nodup (map f l) ↔ ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩
#align list.nodup_map_iff_inj_on List.nodup_map_iff_inj_on

protected theorem Nodup.map {f : α → β} (hf : Injective f) : Nodup l → Nodup (map f l) :=
  Nodup.map_on fun _ _ _ _ h => hf h
#align list.nodup.map List.Nodup.map -- Porting note: different universe order

theorem nodup_map_iff {f : α → β} {l : List α} (hf : Injective f) : Nodup (map f l) ↔ Nodup l :=
  ⟨Nodup.of_map _, Nodup.map hf⟩
#align list.nodup_map_iff List.nodup_map_iff

@[simp]
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_val l ▸ h.map fun _ _ => Subtype.eq, fun h =>
    Nodup.of_map Subtype.val ((attach_map_val l).symm ▸ h)⟩
#align list.nodup_attach List.nodup_attach

alias ⟨Nodup.of_attach, Nodup.attach⟩ := nodup_attach
#align list.nodup.attach List.Nodup.attach
#align list.nodup.of_attach List.Nodup.of_attach

-- Porting note: commented out
--attribute [protected] nodup.attach

theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : Nodup l) : Nodup (pmap f l H) := by
  rw [pmap_eq_map_attach]
  exact h.attach.map fun ⟨a, ha⟩ ⟨b, hb⟩ h => by congr; exact hf a (H _ ha) b (H _ hb) h
#align list.nodup.pmap List.Nodup.pmap

theorem Nodup.filter (p : α → Bool) {l} : Nodup l → Nodup (filter p l) := by
  simpa using Pairwise.filter (fun a ↦ p a)
#align list.nodup.filter List.Nodup.filter

@[simp]
theorem nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l :=
  pairwise_reverse.trans <| by simp only [Nodup, Ne, eq_comm]
#align list.nodup_reverse List.nodup_reverse

theorem Nodup.erase_eq_filter [DecidableEq α] {l} (d : Nodup l) (a : α) :
    l.erase a = l.filter (· ≠ a) := by
  induction' d with b l m _ IH; · rfl
  by_cases h : b = a
  · subst h
    rw [erase_cons_head, filter_cons_of_neg _ (by simp)]
    symm
    rw [filter_eq_self]
    simpa [@eq_comm α] using m
  · rw [erase_cons_tail _ (not_beq_of_ne h), filter_cons_of_pos, IH]
    simp [h]
#align list.nodup.erase_eq_filter List.Nodup.erase_eq_filter

theorem Nodup.erase [DecidableEq α] (a : α) : Nodup l → Nodup (l.erase a) :=
  Nodup.sublist <| erase_sublist _ _
#align list.nodup.erase List.Nodup.erase

theorem Nodup.erase_getElem [DecidableEq α] {l : List α} (hl : l.Nodup)
    (i : Nat) (h : i < l.length) : l.erase l[i] = l.eraseIdx ↑i := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH =>
    cases i with
    | zero => simp
    | succ i =>
      rw [nodup_cons] at hl
      rw [erase_cons_tail]
      · simp [IH hl.2]
      · rw [beq_iff_eq]
        simp only [getElem_cons_succ]
        simp only [length_cons, succ_eq_add_one, Nat.add_lt_add_iff_right] at h
        exact mt (· ▸ l.getElem_mem i h) hl.1

theorem Nodup.erase_get [DecidableEq α] {l : List α} (hl : l.Nodup) (i : Fin l.length) :
    l.erase (l.get i) = l.eraseIdx ↑i := by
  simp [erase_getElem, hl]

theorem Nodup.diff [DecidableEq α] : l₁.Nodup → (l₁.diff l₂).Nodup :=
  Nodup.sublist <| diff_sublist _ _
#align list.nodup.diff List.Nodup.diff

theorem Nodup.mem_erase_iff [DecidableEq α] (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [d.erase_eq_filter, mem_filter, and_comm, decide_eq_true_iff]
#align list.nodup.mem_erase_iff List.Nodup.mem_erase_iff

theorem Nodup.not_mem_erase [DecidableEq α] (h : Nodup l) : a ∉ l.erase a := fun H =>
  (h.mem_erase_iff.1 H).1 rfl
#align list.nodup.not_mem_erase List.Nodup.not_mem_erase

theorem nodup_join {L : List (List α)} :
    Nodup (join L) ↔ (∀ l ∈ L, Nodup l) ∧ Pairwise Disjoint L := by
  simp only [Nodup, pairwise_join, disjoint_left.symm, forall_mem_ne]
#align list.nodup_join List.nodup_join

theorem nodup_bind {l₁ : List α} {f : α → List β} :
    Nodup (l₁.bind f) ↔
      (∀ x ∈ l₁, Nodup (f x)) ∧ Pairwise (fun a b : α => Disjoint (f a) (f b)) l₁ := by
  simp only [List.bind, nodup_join, pairwise_map, and_comm, and_left_comm, mem_map, exists_imp,
      and_imp]
  rw [show (∀ (l : List β) (x : α), f x = l → x ∈ l₁ → Nodup l) ↔ ∀ x : α, x ∈ l₁ → Nodup (f x)
      from forall_swap.trans <| forall_congr' fun _ => forall_eq']
#align list.nodup_bind List.nodup_bind

protected theorem Nodup.product {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) :
    (l₁ ×ˢ l₂).Nodup :=
  nodup_bind.2
    ⟨fun a _ => d₂.map <| LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
#align list.nodup.product List.Nodup.product

theorem Nodup.sigma {σ : α → Type*} {l₂ : ∀ a , List (σ a)} (d₁ : Nodup l₁)
    (d₂ : ∀ a , Nodup (l₂ a)) : (l₁.sigma l₂).Nodup :=
  nodup_bind.2
    ⟨fun a _ => (d₂ a).map fun b b' h => by injection h with _ h,
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
#align list.nodup.sigma List.Nodup.sigma

protected theorem Nodup.filterMap {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup l → Nodup (filterMap f l) :=
  (Pairwise.filter_map f) @fun a a' n b bm b' bm' e => n <| h a a' b' (by rw [← e]; exact bm) bm'
#align list.nodup.filter_map List.Nodup.filterMap

protected theorem Nodup.concat (h : a ∉ l) (h' : l.Nodup) : (l.concat a).Nodup := by
  rw [concat_eq_append]; exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)
#align list.nodup.concat List.Nodup.concat

protected theorem Nodup.insert [DecidableEq α] (h : l.Nodup) : (l.insert a).Nodup :=
  if h' : a ∈ l then by rw [insert_of_mem h']; exact h
  else by rw [insert_of_not_mem h', nodup_cons]; constructor <;> assumption
#align list.nodup.insert List.Nodup.insert

theorem Nodup.union [DecidableEq α] (l₁ : List α) (h : Nodup l₂) : (l₁ ∪ l₂).Nodup := by
  induction' l₁ with a l₁ ih generalizing l₂
  · exact h
  · exact (ih h).insert
#align list.nodup.union List.Nodup.union

theorem Nodup.inter [DecidableEq α] (l₂ : List α) : Nodup l₁ → Nodup (l₁ ∩ l₂) :=
  Nodup.filter _
#align list.nodup.inter List.Nodup.inter

theorem Nodup.diff_eq_filter [DecidableEq α] :
    ∀ {l₁ l₂ : List α} (_ : l₁.Nodup), l₁.diff l₂ = l₁.filter (· ∉ l₂)
  | l₁, [], _ => by simp
  | l₁, a :: l₂, hl₁ => by
    rw [diff_cons, (hl₁.erase _).diff_eq_filter, hl₁.erase_eq_filter, filter_filter]
    simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not, ne_eq, and_comm,
      Bool.decide_and, find?, mem_cons, not_or]
#align list.nodup.diff_eq_filter List.Nodup.diff_eq_filter

theorem Nodup.mem_diff_iff [DecidableEq α] (hl₁ : l₁.Nodup) : a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ := by
  rw [hl₁.diff_eq_filter, mem_filter, decide_eq_true_iff]
#align list.nodup.mem_diff_iff List.Nodup.mem_diff_iff

protected theorem Nodup.set :
    ∀ {l : List α} {n : ℕ} {a : α} (_ : l.Nodup) (_ : a ∉ l), (l.set n a).Nodup
  | [], _, _, _, _ => nodup_nil
  | _ :: _, 0, _, hl, ha => nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
  | _ :: _, _ + 1, _, hl, ha =>
    nodup_cons.2
      ⟨fun h =>
        (mem_or_eq_of_mem_set h).elim (nodup_cons.1 hl).1 fun hba => ha (hba ▸ mem_cons_self _ _),
        hl.of_cons.set (mt (mem_cons_of_mem _) ha)⟩
#align list.nodup.update_nth List.Nodup.set

theorem Nodup.map_update [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → β) (x : α) (y : β) :
    l.map (Function.update f x y) =
      if x ∈ l then (l.map f).set (l.indexOf x) y else l.map f := by
  induction' l with hd tl ihl; · simp
  rw [nodup_cons] at hl
  simp only [mem_cons, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [set, hl.1]
  · simp [Ne.symm H, H, set, ← apply_ite (cons (f hd))]
#align list.nodup.map_update List.Nodup.map_update

theorem Nodup.pairwise_of_forall_ne {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; have := nodup_iff_sublist.mp hl _ hab; contradiction
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq
#align list.nodup.pairwise_of_forall_ne List.Nodup.pairwise_of_forall_ne

theorem Nodup.pairwise_of_set_pairwise {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : { x | x ∈ l }.Pairwise r) : l.Pairwise r :=
  hl.pairwise_of_forall_ne h
#align list.nodup.pairwise_of_set_pairwise List.Nodup.pairwise_of_set_pairwise

@[simp]
theorem Nodup.pairwise_coe [IsSymm α r] (hl : l.Nodup) :
    { a | a ∈ l }.Pairwise r ↔ l.Pairwise r := by
  induction' l with a l ih
  · simp
  rw [List.nodup_cons] at hl
  have : ∀ b ∈ l, ¬a = b → r a b ↔ r a b := fun b hb =>
    imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm
  simp [Set.setOf_or, Set.pairwise_insert_of_symmetric (@symm_of _ r _), ih hl.2, and_comm,
    forall₂_congr this]
#align list.nodup.pairwise_coe List.Nodup.pairwise_coe

theorem Nodup.take_eq_filter_mem [DecidableEq α] :
    ∀ {l : List α} {n : ℕ} (_ : l.Nodup), l.take n = l.filter (l.take n).elem
  | [], n, _ => by simp
  | b::l, 0, _ => by simp
  | b::l, n+1, hl => by
    rw [take_cons, Nodup.take_eq_filter_mem (Nodup.of_cons hl), List.filter_cons_of_pos _ (by simp)]
    congr 1
    refine List.filter_congr ?_
    intro x hx
    have : x ≠ b := fun h => (nodup_cons.1 hl).1 (h ▸ hx)
    simp (config := {contextual := true}) [List.mem_filter, this, hx]
end List

theorem Option.toList_nodup : ∀ o : Option α, o.toList.Nodup
  | none => List.nodup_nil
  | some x => List.nodup_singleton x
#align option.to_list_nodup Option.toList_nodup
