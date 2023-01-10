/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau

! This file was ported from Lean 3 source module data.list.nodup
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Lattice
import Mathbin.Data.List.Pairwise
import Mathbin.Data.List.Forall2
import Mathbin.Data.Set.Pairwise

/-!
# Lists with no duplicates

`list.nodup` is defined in `data/list/defs`. In this file we prove various properties of this
predicate.
-/


universe u v

open Nat Function

variable {α : Type u} {β : Type v} {l l₁ l₂ : List α} {r : α → α → Prop} {a b : α}

namespace List

@[simp]
theorem forall_mem_ne {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h a' m e => h (e.symm ▸ m)⟩
#align list.forall_mem_ne List.forall_mem_ne

@[simp]
theorem nodup_nil : @Nodup α [] :=
  pairwise.nil
#align list.nodup_nil List.nodup_nil

@[simp]
theorem nodup_cons {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [nodup, pairwise_cons, forall_mem_ne]
#align list.nodup_cons List.nodup_cons

protected theorem Pairwise.nodup {l : List α} {r : α → α → Prop} [IsIrrefl α r] (h : Pairwise r l) :
    Nodup l :=
  h.imp fun a b => ne_of_irrefl
#align list.pairwise.nodup List.Pairwise.nodup

theorem rel_nodup {r : α → β → Prop} (hr : Relator.BiUnique r) : (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup
  | _, _, forall₂.nil => by simp only [nodup_nil]
  | _, _, forall₂.cons hab h => by
    simpa only [nodup_cons] using Relator.rel_and (Relator.rel_not (rel_mem hr hab h)) (rel_nodup h)
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
  pairwise.sublist
#align list.nodup.sublist List.Nodup.sublist

theorem not_nodup_pair (a : α) : ¬Nodup [a, a] :=
  not_nodup_cons_of_mem <| mem_singleton_self _
#align list.not_nodup_pair List.not_nodup_pair

theorem nodup_iff_sublist {l : List α} : Nodup l ↔ ∀ a, ¬[a, a] <+ l :=
  ⟨fun d a h => not_nodup_pair a (d.Sublist h),
    by
    induction' l with a l IH <;> intro h; · exact nodup_nil
    exact
      (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons fun al =>
        h a <| (singleton_sublist.2 al).cons_cons _⟩
#align list.nodup_iff_sublist List.nodup_iff_sublist

theorem nodup_iff_nth_le_inj {l : List α} :
    Nodup l ↔ ∀ i j h₁ h₂, nthLe l i h₁ = nthLe l j h₂ → i = j :=
  pairwise_iff_nth_le.trans
    ⟨fun H i j h₁ h₂ h =>
      ((lt_trichotomy _ _).resolve_left fun h' => H _ _ h₂ h' h).resolve_right fun h' =>
        H _ _ h₁ h' h.symm,
      fun H i j h₁ h₂ h => ne_of_lt h₂ (H _ _ _ _ h)⟩
#align list.nodup_iff_nth_le_inj List.nodup_iff_nth_le_inj

theorem Nodup.nth_le_inj_iff {l : List α} (h : Nodup l) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) : l.nthLe i hi = l.nthLe j hj ↔ i = j :=
  ⟨nodup_iff_nth_le_inj.mp h _ _ _ _, by simp (config := { contextual := true })⟩
#align list.nodup.nth_le_inj_iff List.Nodup.nth_le_inj_iff

theorem nodup_iff_nth_ne_nth {l : List α} :
    l.Nodup ↔ ∀ i j : ℕ, i < j → j < l.length → l.nth i ≠ l.nth j :=
  by
  rw [nodup_iff_nth_le_inj]
  simp only [nth_le_eq_iff, some_nth_le_eq]
  constructor <;> rintro h i j h₁ h₂
  · exact mt (h i j (h₁.trans h₂) h₂) (ne_of_lt h₁)
  · intro h₃
    by_contra h₄
    cases' lt_or_gt_of_ne h₄ with h₅ h₅
    · exact h i j h₅ h₂ h₃
    · exact h j i h₅ h₁ h₃.symm
#align list.nodup_iff_nth_ne_nth List.nodup_iff_nth_ne_nth

theorem Nodup.ne_singleton_iff {l : List α} (h : Nodup l) (x : α) :
    l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x :=
  by
  induction' l with hd tl hl
  · simp
  · specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne.def, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · have : tl ≠ [] := ne_nil_of_mem hy
        suffices ∃ (y : α)(H : y ∈ hd :: tl), y ≠ x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩
#align list.nodup.ne_singleton_iff List.Nodup.ne_singleton_iff

theorem nth_le_eq_of_ne_imp_not_nodup (xs : List α) (n m : ℕ) (hn : n < xs.length)
    (hm : m < xs.length) (h : xs.nthLe n hn = xs.nthLe m hm) (hne : n ≠ m) : ¬Nodup xs :=
  by
  rw [nodup_iff_nth_le_inj]
  simp only [exists_prop, exists_and_right, not_forall]
  exact ⟨n, m, ⟨hn, hm, h⟩, hne⟩
#align list.nth_le_eq_of_ne_imp_not_nodup List.nth_le_eq_of_ne_imp_not_nodup

@[simp]
theorem nth_le_index_of [DecidableEq α] {l : List α} (H : Nodup l) (n h) :
    indexOf (nthLe l n h) l = n :=
  nodup_iff_nth_le_inj.1 H _ _ _ h <| index_of_nth_le <| indexOf_lt_length.2 <| nthLe_mem _ _ _
#align list.nth_le_index_of List.nth_le_index_of

theorem nodup_iff_count_le_one [DecidableEq α] {l : List α} : Nodup l ↔ ∀ a, count a l ≤ 1 :=
  nodup_iff_sublist.trans <|
    forall_congr' fun a =>
      have : [a, a] <+ l ↔ 1 < count a l := (@le_count_iff_repeat_sublist _ _ a l 2).symm
      (not_congr this).trans not_lt
#align list.nodup_iff_count_le_one List.nodup_iff_count_le_one

theorem nodup_repeat (a : α) : ∀ {n : ℕ}, Nodup (repeat a n) ↔ n ≤ 1
  | 0 => by simp [Nat.zero_le]
  | 1 => by simp
  | n + 2 =>
    iff_of_false
      (fun H => nodup_iff_sublist.1 H a ((repeat_sublist_repeat _).2 (Nat.le_add_left 2 n)))
      (not_le_of_lt <| Nat.le_add_left 2 n)
#align list.nodup_repeat List.nodup_repeat

@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {l : List α} (d : Nodup l) (h : a ∈ l) :
    count a l = 1 :=
  le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos.2 h)
#align list.count_eq_one_of_mem List.count_eq_one_of_mem

theorem count_eq_of_nodup [DecidableEq α] {a : α} {l : List α} (d : Nodup l) :
    count a l = if a ∈ l then 1 else 0 :=
  by
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

theorem nodup_append {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂ :=
  by simp only [nodup, pairwise_append, disjoint_iff_ne]
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

theorem nodup_middle {a : α} {l₁ l₂ : List α} : Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :: (l₁ ++ l₂)) :=
  by
  simp only [nodup_append, not_or, and_left_comm, and_assoc', nodup_cons, mem_append,
    disjoint_cons_right]
#align list.nodup_middle List.nodup_middle

/- warning: list.nodup.of_map -> List.Nodup.of_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) {l : List.{u1} α}, (List.Nodup.{u2} β (List.map.{u1, u2} α β f l)) -> (List.Nodup.{u1} α l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) {l : List.{u2} α}, (List.Nodup.{u1} β (List.map.{u2, u1} α β f l)) -> (List.Nodup.{u2} α l)
Case conversion may be inaccurate. Consider using '#align list.nodup.of_map List.Nodup.of_mapₓ'. -/
theorem Nodup.of_map (f : α → β) {l : List α} : Nodup (map f l) → Nodup l :=
  (Pairwise.of_map f) fun a b => mt <| congr_arg f
#align list.nodup.of_map List.Nodup.of_map

/- warning: list.nodup.map_on -> List.Nodup.map_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : List.{u1} α} {f : α -> β}, (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (forall (y : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) y l) -> (Eq.{succ u2} β (f x) (f y)) -> (Eq.{succ u1} α x y))) -> (List.Nodup.{u1} α l) -> (List.Nodup.{u2} β (List.map.{u1, u2} α β f l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : List.{u2} α} {f : α -> β}, (forall (x : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) x l) -> (forall (y : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) y l) -> (Eq.{succ u1} β (f x) (f y)) -> (Eq.{succ u2} α x y))) -> (List.Nodup.{u2} α l) -> (List.Nodup.{u1} β (List.map.{u2, u1} α β f l))
Case conversion may be inaccurate. Consider using '#align list.nodup.map_on List.Nodup.map_onₓ'. -/
theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : Nodup l) :
    (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)
#align list.nodup.map_on List.Nodup.map_on

theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : Nodup (map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y :=
  by
  induction' l with hd tl ih
  · simp
  · simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.def] at d
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

/- warning: list.nodup.map -> List.Nodup.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : List.{u1} α} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (List.Nodup.{u1} α l) -> (List.Nodup.{u2} β (List.map.{u1, u2} α β f l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : List.{u2} α} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (List.Nodup.{u2} α l) -> (List.Nodup.{u1} β (List.map.{u2, u1} α β f l))
Case conversion may be inaccurate. Consider using '#align list.nodup.map List.Nodup.mapₓ'. -/
protected theorem Nodup.map {f : α → β} (hf : Injective f) : Nodup l → Nodup (map f l) :=
  Nodup.map_on fun x _ y _ h => hf h
#align list.nodup.map List.Nodup.map

theorem nodup_map_iff {f : α → β} {l : List α} (hf : Injective f) : Nodup (map f l) ↔ Nodup l :=
  ⟨Nodup.of_map _, Nodup.map hf⟩
#align list.nodup_map_iff List.nodup_map_iff

#print List.nodup_attach /-
@[simp]
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_val l ▸ h.map fun a b => Subtype.eq, fun h =>
    Nodup.of_map Subtype.val ((attach_map_val l).symm ▸ h)⟩
#align list.nodup_attach List.nodup_attach
-/

alias nodup_attach ↔ nodup.of_attach nodup.attach

attribute [protected] nodup.attach

/- warning: list.nodup.pmap -> List.Nodup.pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {l : List.{u1} α} {H : forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a)}, (forall (a : α) (ha : p a) (b : α) (hb : p b), (Eq.{succ u2} β (f a ha) (f b hb)) -> (Eq.{succ u1} α a b)) -> (List.Nodup.{u1} α l) -> (List.Nodup.{u2} β (List.pmap.{u1, u2} α β (fun (a : α) => p a) f l H))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {l : List.{u2} α} {H : forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (p a)}, (forall (a : α) (ha : p a) (b : α) (hb : p b), (Eq.{succ u1} β (f a ha) (f b hb)) -> (Eq.{succ u2} α a b)) -> (List.Nodup.{u2} α l) -> (List.Nodup.{u1} β (List.pmap.{u2, u1} α β (fun (a : α) => p a) f l H))
Case conversion may be inaccurate. Consider using '#align list.nodup.pmap List.Nodup.pmapₓ'. -/
theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : Nodup l) : Nodup (pmap f l H) := by
  rw [pmap_eq_map_attach] <;>
    exact h.attach.map fun ⟨a, ha⟩ ⟨b, hb⟩ h => by congr <;> exact hf a (H _ ha) b (H _ hb) h
#align list.nodup.pmap List.Nodup.pmap

theorem Nodup.filter (p : α → Prop) [DecidablePred p] {l} : Nodup l → Nodup (filter p l) :=
  Pairwise.filter p
#align list.nodup.filter List.Nodup.filter

@[simp]
theorem nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l :=
  pairwise_reverse.trans <| by simp only [nodup, Ne.def, eq_comm]
#align list.nodup_reverse List.nodup_reverse

theorem Nodup.erase_eq_filter [DecidableEq α] {l} (d : Nodup l) (a : α) :
    l.erase a = filter (· ≠ a) l :=
  by
  induction' d with b l m d IH; · rfl
  by_cases b = a
  · subst h
    rw [erase_cons_head, filter_cons_of_neg]
    symm
    rw [filter_eq_self]
    simpa only [Ne.def, eq_comm] using m
    exact not_not_intro rfl
  · rw [erase_cons_tail _ h, filter_cons_of_pos, IH]
    exact h
#align list.nodup.erase_eq_filter List.Nodup.erase_eq_filter

theorem Nodup.erase [DecidableEq α] (a : α) : Nodup l → Nodup (l.erase a) :=
  nodup.sublist <| erase_sublist _ _
#align list.nodup.erase List.Nodup.erase

theorem Nodup.diff [DecidableEq α] : l₁.Nodup → (l₁.diff l₂).Nodup :=
  nodup.sublist <| diff_sublist _ _
#align list.nodup.diff List.Nodup.diff

theorem Nodup.mem_erase_iff [DecidableEq α] (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [d.erase_eq_filter, mem_filter, and_comm']
#align list.nodup.mem_erase_iff List.Nodup.mem_erase_iff

theorem Nodup.not_mem_erase [DecidableEq α] (h : Nodup l) : a ∉ l.erase a := fun H =>
  (h.mem_erase_iff.1 H).1 rfl
#align list.nodup.not_mem_erase List.Nodup.not_mem_erase

theorem nodup_join {L : List (List α)} :
    Nodup (join L) ↔ (∀ l ∈ L, Nodup l) ∧ Pairwise Disjoint L := by
  simp only [nodup, pairwise_join, disjoint_left.symm, forall_mem_ne]
#align list.nodup_join List.nodup_join

theorem nodup_bind {l₁ : List α} {f : α → List β} :
    Nodup (l₁.bind f) ↔
      (∀ x ∈ l₁, Nodup (f x)) ∧ Pairwise (fun a b : α => Disjoint (f a) (f b)) l₁ :=
  by
  simp only [List.bind, nodup_join, pairwise_map, and_comm', and_left_comm, mem_map, exists_imp,
      and_imp] <;>
    rw [show (∀ (l : List β) (x : α), f x = l → x ∈ l₁ → nodup l) ↔ ∀ x : α, x ∈ l₁ → nodup (f x)
        from forall_swap.trans <| forall_congr' fun _ => forall_eq']
#align list.nodup_bind List.nodup_bind

protected theorem Nodup.product {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) :
    (l₁.product l₂).Nodup :=
  nodup_bind.2
    ⟨fun a ma => d₂.map <| left_inverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun a₁ a₂ n x h₁ h₂ =>
        by
        rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
#align list.nodup.product List.Nodup.product

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Nodup.sigma [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`σ]
         [":" (Term.arrow `α "→" (Term.type "Type" [(Level.hole "_")]))]
         "}")
        (Term.implicitBinder
         "{"
         [`l₂]
         [":" (Term.forall "∀" [`a] [] "," (Term.app `List [(Term.app `σ [`a])]))]
         "}")
        (Term.explicitBinder "(" [`d₁] [":" (Term.app `Nodup [`l₁])] [] ")")
        (Term.explicitBinder
         "("
         [`d₂]
         [":" (Term.forall "∀" [`a] [] "," (Term.app `Nodup [(Term.app `l₂ [`a])]))]
         []
         ")")]
       (Term.typeSpec ":" (Term.proj (Term.app (Term.proj `l₁ "." `Sigma) [`l₂]) "." `Nodup)))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `nodup_bind "." (fieldIdx "2"))
        [(Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`a `ma]
             []
             "=>"
             (Term.app
              (Term.proj (Term.app `d₂ [`a]) "." `map)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`b `b' `h]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.injection "injection" `h ["with" ["_" `h]])
                      "<;>"
                      (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))])))))])))
           ","
           (Term.app
            (Term.proj `d₁ "." `imp)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a₁ `a₂ `n `x `h₁ `h₂]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget
                      []
                      (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₁)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₁)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                           [])]
                         "⟩")])
                      [])])
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget
                      []
                      (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₂)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₂)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                           [])]
                         "⟩")])
                      [])])
                   []
                   (Tactic.exact "exact" (Term.app `n [`rfl]))])))))])]
          "⟩")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `nodup_bind "." (fieldIdx "2"))
       [(Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`a `ma]
            []
            "=>"
            (Term.app
             (Term.proj (Term.app `d₂ [`a]) "." `map)
             [(Term.fun
               "fun"
               (Term.basicFun
                [`b `b' `h]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.injection "injection" `h ["with" ["_" `h]])
                     "<;>"
                     (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))])))))])))
          ","
          (Term.app
           (Term.proj `d₁ "." `imp)
           [(Term.fun
             "fun"
             (Term.basicFun
              [`a₁ `a₂ `n `x `h₁ `h₂]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget
                     []
                     (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₁)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₁)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget
                     []
                     (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂]))]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₂)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₂)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.exact "exact" (Term.app `n [`rfl]))])))))])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `ma]
          []
          "=>"
          (Term.app
           (Term.proj (Term.app `d₂ [`a]) "." `map)
           [(Term.fun
             "fun"
             (Term.basicFun
              [`b `b' `h]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.injection "injection" `h ["with" ["_" `h]])
                   "<;>"
                   (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))])))))])))
        ","
        (Term.app
         (Term.proj `d₁ "." `imp)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`a₁ `a₂ `n `x `h₁ `h₂]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₁)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₁)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₂)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₂)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.exact "exact" (Term.app `n [`rfl]))])))))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `d₁ "." `imp)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a₁ `a₂ `n `x `h₁ `h₂]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₂)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₂)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.exact "exact" (Term.app `n [`rfl]))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a₁ `a₂ `n `x `h₁ `h₂]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₂)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₂)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.exact "exact" (Term.app `n [`rfl]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact "exact" (Term.app `n [`rfl]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `n [`rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `n [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `mem_map "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `mb₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `mem_map "." (fieldIdx "1")) [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `mem_map "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `d₁ "." `imp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `d₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `ma]
        []
        "=>"
        (Term.app
         (Term.proj (Term.app `d₂ [`a]) "." `map)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`b `b' `h]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.injection "injection" `h ["with" ["_" `h]])
                 "<;>"
                 (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `d₂ [`a]) "." `map)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`b `b' `h]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.injection "injection" `h ["with" ["_" `h]])
               "<;>"
               (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b `b' `h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.injection "injection" `h ["with" ["_" `h]])
             "<;>"
             (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.injection "injection" `h ["with" ["_" `h]])
           "<;>"
           (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.injection "injection" `h ["with" ["_" `h]])
       "<;>"
       (Tactic.exact "exact" (Term.app `eq_of_heq [`h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `eq_of_heq [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_of_heq [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_of_heq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.injection "injection" `h ["with" ["_" `h]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '_', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '_', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Nodup.sigma
  { σ : α → Type _ } { l₂ : ∀ a , List σ a } ( d₁ : Nodup l₁ ) ( d₂ : ∀ a , Nodup l₂ a )
    : l₁ . Sigma l₂ . Nodup
  :=
    nodup_bind . 2
      ⟨
        fun a ma => d₂ a . map fun b b' h => by injection h with _ h <;> exact eq_of_heq h
          ,
          d₁ . imp
            fun
              a₁ a₂ n x h₁ h₂
                =>
                by
                  rcases mem_map . 1 h₁ with ⟨ b₁ , mb₁ , rfl ⟩
                    rcases mem_map . 1 h₂ with ⟨ b₂ , mb₂ , ⟨ ⟩ ⟩
                    exact n rfl
        ⟩
#align list.nodup.sigma List.Nodup.sigma

protected theorem Nodup.filter_map {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup l → Nodup (filterMap f l) :=
  (Pairwise.filter_map f) fun a a' n b bm b' bm' e => n <| h a a' b' (e ▸ bm) bm'
#align list.nodup.filter_map List.Nodup.filter_map

protected theorem Nodup.concat (h : a ∉ l) (h' : l.Nodup) : (l.concat a).Nodup := by
  rw [concat_eq_append] <;> exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)
#align list.nodup.concat List.Nodup.concat

theorem Nodup.insert [DecidableEq α] (h : l.Nodup) : (insert a l).Nodup :=
  if h' : a ∈ l then by rw [insert_of_mem h'] <;> exact h
  else by rw [insert_of_not_mem h', nodup_cons] <;> constructor <;> assumption
#align list.nodup.insert List.Nodup.insert

theorem Nodup.union [DecidableEq α] (l₁ : List α) (h : Nodup l₂) : (l₁ ∪ l₂).Nodup :=
  by
  induction' l₁ with a l₁ ih generalizing l₂
  · exact h
  · exact (ih h).insert
#align list.nodup.union List.Nodup.union

theorem Nodup.inter [DecidableEq α] (l₂ : List α) : Nodup l₁ → Nodup (l₁ ∩ l₂) :=
  Nodup.filter _
#align list.nodup.inter List.Nodup.inter

theorem Nodup.diff_eq_filter [DecidableEq α] :
    ∀ {l₁ l₂ : List α} (hl₁ : l₁.Nodup), l₁.diff l₂ = l₁.filter (· ∉ l₂)
  | l₁, [], hl₁ => by simp
  | l₁, a :: l₂, hl₁ =>
    by
    rw [diff_cons, (hl₁.erase _).diff_eq_filter, hl₁.erase_eq_filter, filter_filter]
    simp only [mem_cons_iff, not_or, and_comm]
#align list.nodup.diff_eq_filter List.Nodup.diff_eq_filter

theorem Nodup.mem_diff_iff [DecidableEq α] (hl₁ : l₁.Nodup) : a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ := by
  rw [hl₁.diff_eq_filter, mem_filter]
#align list.nodup.mem_diff_iff List.Nodup.mem_diff_iff

protected theorem Nodup.update_nth :
    ∀ {l : List α} {n : ℕ} {a : α} (hl : l.Nodup) (ha : a ∉ l), (l.updateNth n a).Nodup
  | [], n, a, hl, ha => nodup_nil
  | b :: l, 0, a, hl, ha => nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
  | b :: l, n + 1, a, hl, ha =>
    nodup_cons.2
      ⟨fun h =>
        (mem_or_eq_of_mem_set h).elim (nodup_cons.1 hl).1 fun hba => ha (hba ▸ mem_cons_self _ _),
        hl.of_cons.updateNth (mt (mem_cons_of_mem _) ha)⟩
#align list.nodup.update_nth List.Nodup.update_nth

theorem Nodup.map_update [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → β) (x : α) (y : β) :
    l.map (Function.update f x y) =
      if x ∈ l then (l.map f).updateNth (l.indexOf x) y else l.map f :=
  by
  induction' l with hd tl ihl; · simp
  rw [nodup_cons] at hl
  simp only [mem_cons_iff, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [update_nth, hl.1]
  · simp [Ne.symm H, H, update_nth, ← apply_ite (cons (f hd))]
#align list.nodup.map_update List.Nodup.map_update

theorem Nodup.pairwise_of_forall_ne {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  classical
    refine' pairwise_of_reflexive_on_dupl_of_forall_ne _ h
    intro x hx
    rw [nodup_iff_count_le_one] at hl
    exact absurd (hl x) hx.not_le
#align list.nodup.pairwise_of_forall_ne List.Nodup.pairwise_of_forall_ne

theorem Nodup.pairwise_of_set_pairwise {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : { x | x ∈ l }.Pairwise r) : l.Pairwise r :=
  hl.pairwise_of_forall_ne h
#align list.nodup.pairwise_of_set_pairwise List.Nodup.pairwise_of_set_pairwise

@[simp]
theorem Nodup.pairwise_coe [IsSymm α r] (hl : l.Nodup) : { a | a ∈ l }.Pairwise r ↔ l.Pairwise r :=
  by
  induction' l with a l ih
  · simp
  rw [List.nodup_cons] at hl
  have : ∀ b ∈ l, ¬a = b → r a b ↔ r a b := fun b hb =>
    imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm
  simp [Set.setOf_or, Set.pairwise_insert_of_symmetric (@symm_of _ r _), ih hl.2, and_comm',
    forall₂_congr this]
#align list.nodup.pairwise_coe List.Nodup.pairwise_coe

end List

theorem Option.to_list_nodup {α} : ∀ o : Option α, o.toList.Nodup
  | none => List.nodup_nil
  | some x => List.nodup_singleton x
#align option.to_list_nodup Option.to_list_nodup

