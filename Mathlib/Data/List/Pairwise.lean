/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.pairwise
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Lex
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Relation

/-!
# Pairwise relations on a list

This file provides basic results about `list.pairwise` and `list.pw_filter` (definitions are in
`data.list.defs`).
`pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`pairwise (≠) l` means that all elements of `l` are distinct, and `pairwise (<) l` means that `l`
is strictly increasing.
`pw_filter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable {α β : Type _} {R S T : α → α → Prop} {a : α} {l : List α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff

/-! ### Pairwise -/

theorem rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  (pairwise_cons.1 p).1 _
#align list.rel_of_pairwise_cons List.rel_of_pairwise_cons

theorem Pairwise.of_cons (p : (a :: l).Pairwise R) : Pairwise R l :=
  (pairwise_cons.1 p).2
#align list.pairwise.of_cons List.Pairwise.of_cons

theorem Pairwise.tail : ∀ {l : List α} (_p : Pairwise R l), Pairwise R l.tail
  | [], h => h
  | _ :: _, h => h.of_cons
#align list.pairwise.tail List.Pairwise.tail

theorem Pairwise.drop : ∀ {l : List α} {n : ℕ}, List.Pairwise R l → List.Pairwise R (l.drop n)
  | _, 0, h => h
  | [], _ + 1, _ => List.Pairwise.nil
  | a :: l, n + 1, h => by rw [List.drop]; exact Pairwise.drop (pairwise_cons.mp h).right
#align list.pairwise.drop List.Pairwise.drop

theorem Pairwise.imp_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l := by
  induction p with
  | nil => constructor
  | @cons a l r _ ih =>
    constructor
    · exact BAll.imp_right (fun x h ↦ H (mem_cons_self _ _) (mem_cons_of_mem _ h)) r
    · exact ih fun {a b} m m' ↦ H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')
#align list.pairwise.imp_of_mem List.Pairwise.imp_of_mem

#align list.pairwise.imp List.Pairwise.impₓ -- Implicits Order

theorem pairwise_and_iff : (l.Pairwise fun a b => R a b ∧ S a b) ↔ l.Pairwise R ∧ l.Pairwise S :=
  ⟨fun h => ⟨h.imp @fun a b h => h.1, h.imp @fun a b h => h.2⟩, fun ⟨hR, hS⟩ =>
    by induction' hR with a l R1 R2 IH <;> simp only [Pairwise.nil, pairwise_cons] at *
       exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH ⟨R2, hS.2⟩ hS.2⟩⟩
#align list.pairwise_and_iff List.pairwise_and_iff

theorem Pairwise.and (hR : l.Pairwise R) (hS : l.Pairwise S) :
    l.Pairwise fun a b => R a b ∧ S a b :=
  pairwise_and_iff.2 ⟨hR, hS⟩
#align list.pairwise.and List.Pairwise.and

theorem Pairwise.imp₂ (H : ∀ a b, R a b → S a b → T a b) (hR : l.Pairwise R) (hS : l.Pairwise S) :
    l.Pairwise T :=
  (hR.and hS).imp fun h => (H _ _ h.1 h.2)
#align list.pairwise.imp₂ List.Pairwise.imp₂

theorem Pairwise.iff_of_mem {S : α → α → Prop} {l : List α}
    (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : Pairwise R l ↔ Pairwise S l :=
  ⟨Pairwise.imp_of_mem fun {_ _} m m' ↦ (H m m').1,
   Pairwise.imp_of_mem fun {_ _} m m' ↦ (H m m').2⟩
#align list.pairwise.iff_of_mem List.Pairwise.iff_of_mem

theorem Pairwise.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    Pairwise R l ↔ Pairwise S l :=
  Pairwise.iff_of_mem fun a b _ _ => H a b
#align list.pairwise.iff List.Pairwise.iff

theorem pairwise_of_forall {l : List α} (H : ∀ x y, R x y) : Pairwise R l := by
  induction l <;> [exact pairwise.nil, simp only [*, pairwise_cons, forall₂_true_iff, and_true_iff]]
#align list.pairwise_of_forall List.pairwise_of_forall

#print List.Pairwise.and_mem /-
theorem Pairwise.and_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  Pairwise.iff_of_mem
    (by simp (config := { contextual := true }) only [true_and_iff, iff_self_iff, forall₂_true_iff])
#align list.pairwise.and_mem List.Pairwise.and_mem
-/

theorem Pairwise.imp_mem {l : List α} :
    Pairwise R l ↔ Pairwise (fun x y => x ∈ l → y ∈ l → R x y) l :=
  Pairwise.iff_of_mem
    (by
      simp (config := { contextual := true }) only [forall_prop_of_true, iff_self_iff,
        forall₂_true_iff])
#align list.pairwise.imp_mem List.Pairwise.imp_mem

/- warning: list.pairwise.sublist -> List.Pairwise.sublist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : α -> α -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (List.Pairwise.{u1} α R l₂) -> (List.Pairwise.{u1} α R l₁)
but is expected to have type
  forall {α : Type.{u1}} {R : List.{u1} α} {l₁ : List.{u1} α} {l₂ : α -> α -> Prop}, (List.Sublist.{u1} α R l₁) -> (List.Pairwise.{u1} α l₂ l₁) -> (List.Pairwise.{u1} α l₂ R)
Case conversion may be inaccurate. Consider using '#align list.pairwise.sublist List.Pairwise.sublistₓ'. -/
protected theorem Pairwise.sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → Pairwise R l₂ → Pairwise R l₁
  | _, _, sublist.slnil, h => h
  | _, _, sublist.cons l₁ l₂ a s, pairwise.cons i h => h.Sublist s
  | _, _, sublist.cons2 l₁ l₂ a s, pairwise.cons i h =>
    (h.Sublist s).cons (BAll.imp_left s.Subset i)
#align list.pairwise.sublist List.Pairwise.sublist

theorem Pairwise.forall_of_forall_of_flip (h₁ : ∀ x ∈ l, R x x) (h₂ : l.Pairwise R)
    (h₃ : l.Pairwise (flip R)) : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  by
  induction' l with a l ih
  · exact forall_mem_nil _
  rw [pairwise_cons] at h₂ h₃
  rintro x (rfl | hx) y (rfl | hy)
  · exact h₁ _ (l.mem_cons_self _)
  · exact h₂.1 _ hy
  · exact h₃.1 _ hx
  · exact ih (fun x hx => h₁ _ <| mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy
#align list.pairwise.forall_of_forall_of_flip List.Pairwise.forall_of_forall_of_flip

theorem Pairwise.forall_of_forall (H : Symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [H.flip_eq]
#align list.pairwise.forall_of_forall List.Pairwise.forall_of_forall

theorem Pairwise.forall (hR : Symmetric R) (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b :=
  Pairwise.forall_of_forall (fun a b h hne => hR (h hne.symm)) (fun _ _ h => (h rfl).elim)
    (hl.imp fun _ _ h _ => h)
#align list.pairwise.forall List.Pairwise.forall

theorem Pairwise.set_pairwise (hl : Pairwise R l) (hr : Symmetric R) : { x | x ∈ l }.Pairwise R :=
  hl.forall hr
#align list.pairwise.set_pairwise List.Pairwise.set_pairwise

#print List.pairwise_singleton /-
theorem pairwise_singleton (R) (a : α) : Pairwise R [a] := by
  simp only [pairwise_cons, mem_singleton, forall_prop_of_false (not_mem_nil _), forall_true_iff,
    pairwise.nil, and_true_iff]
#align list.pairwise_singleton List.pairwise_singleton
-/

theorem pairwise_pair {a b : α} : Pairwise R [a, b] ↔ R a b := by
  simp only [pairwise_cons, mem_singleton, forall_eq, forall_prop_of_false (not_mem_nil _),
    forall_true_iff, pairwise.nil, and_true_iff]
#align list.pairwise_pair List.pairwise_pair

#print List.pairwise_append /-
theorem pairwise_append {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R l₁ ∧ Pairwise R l₂ ∧ ∀ x ∈ l₁, ∀ y ∈ l₂, R x y := by
  induction' l₁ with x l₁ IH <;>
    [simp only [List.Pairwise.nil, forall_prop_of_false (not_mem_nil _), forall_true_iff,
      and_true_iff, true_and_iff, nil_append],
    simp only [cons_append, pairwise_cons, forall_mem_append, IH, forall_mem_cons, forall_and,
      and_assoc', and_left_comm]]
#align list.pairwise_append List.pairwise_append
-/

#print List.pairwise_append_comm /-
theorem pairwise_append_comm (s : Symmetric R) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) :=
  by
  have :
    ∀ l₁ l₂ : List α,
      (∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y) → ∀ x : α, x ∈ l₂ → ∀ y : α, y ∈ l₁ → R x y :=
    fun l₁ l₂ a x xm y ym => s (a y ym x xm)
  simp only [pairwise_append, and_left_comm] <;> rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]
#align list.pairwise_append_comm List.pairwise_append_comm
-/

#print List.pairwise_middle /-
theorem pairwise_middle (s : Symmetric R) {a : α} {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) :=
  show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂) by
    rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁),
        pairwise_append_comm s] <;>
      simp only [mem_append, or_comm']
#align list.pairwise_middle List.pairwise_middle
-/

/- warning: list.pairwise_map -> List.pairwise_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> α -> Prop} (f : β -> α) {l : List.{u2} β}, Iff (List.Pairwise.{u1} α R (List.map.{u2, u1} β α f l)) (List.Pairwise.{u2} β (fun (a : β) (b : β) => R (f a) (f b)) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β} {f : β -> β -> Prop} {l : List.{u2} α}, Iff (List.Pairwise.{u1} β f (List.map.{u2, u1} α β R l)) (List.Pairwise.{u2} α (fun (a : α) (b : α) => f (R a) (R b)) l)
Case conversion may be inaccurate. Consider using '#align list.pairwise_map List.pairwise_mapₓ'. -/
theorem pairwise_map (f : β → α) :
    ∀ {l : List β}, Pairwise R (map f l) ↔ Pairwise (fun a b : β => R (f a) (f b)) l
  | [] => by simp only [map, pairwise.nil]
  | b :: l =>
    by
    have : (∀ a b', b' ∈ l → f b' = a → R (f b) a) ↔ ∀ b' : β, b' ∈ l → R (f b) (f b') :=
      forall_swap.trans <| forall_congr' fun a => forall_swap.trans <| by simp only [forall_eq']
    simp only [map, pairwise_cons, mem_map, exists_imp, and_imp, this, pairwise_map]
#align list.pairwise_map List.pairwise_map

#print List.Pairwise.of_map /-
theorem Pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    (p : Pairwise S (map f l)) : Pairwise R l :=
  ((pairwise_map f).1 p).imp H
#align list.pairwise.of_map List.Pairwise.of_map
-/

/- warning: list.pairwise.map -> List.Pairwise.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> α -> Prop} {l : List.{u1} α} {S : β -> β -> Prop} (f : α -> β), (forall (a : α) (b : α), (R a b) -> (S (f a) (f b))) -> (List.Pairwise.{u1} α R l) -> (List.Pairwise.{u2} β S (List.map.{u1, u2} α β f l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> α -> Prop} {l : List.{u2} α} {S : β -> β -> Prop} (f : α -> β), (forall (a : α) (b : α), (R a b) -> (S (f a) (f b))) -> (List.Pairwise.{u2} α R l) -> (List.Pairwise.{u1} β S (List.map.{u2, u1} α β f l))
Case conversion may be inaccurate. Consider using '#align list.pairwise.map List.Pairwise.mapₓ'. -/
theorem Pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    (p : Pairwise R l) : Pairwise S (map f l) :=
  (pairwise_map f).2 <| p.imp H
#align list.pairwise.map List.Pairwise.map

theorem pairwise_filter_map (f : β → Option α) {l : List β} :
    Pairwise R (filterMap f l) ↔ Pairwise (fun a a' : β => ∀ b ∈ f a, ∀ b' ∈ f a', R b b') l :=
  by
  let S (a a' : β) := ∀ b ∈ f a, ∀ b' ∈ f a', R b b'
  simp only [Option.mem_def]; induction' l with a l IH
  · simp only [filter_map, pairwise.nil]
  cases' e : f a with b
  · rw [filter_map_cons_none _ _ e, IH, pairwise_cons]
    simp only [e, forall_prop_of_false not_false, forall₃_true_iff, true_and_iff]
  rw [filter_map_cons_some _ _ _ e]
  simp only [pairwise_cons, mem_filter_map, exists_imp, and_imp, IH, e, forall_eq']
  show
    (∀ (a' : α) (x : β), x ∈ l → f x = some a' → R b a') ∧ Pairwise S l ↔
      (∀ a' : β, a' ∈ l → ∀ b' : α, f a' = some b' → R b b') ∧ Pairwise S l
  exact and_congr ⟨fun h b mb a ma => h a b mb ma, fun h a b mb ma => h b mb a ma⟩ Iff.rfl
#align list.pairwise_filter_map List.pairwise_filter_map

theorem Pairwise.filter_map {S : β → β → Prop} (f : α → Option β)
    (H : ∀ a a' : α, R a a' → ∀ b ∈ f a, ∀ b' ∈ f a', S b b') {l : List α} (p : Pairwise R l) :
    Pairwise S (filterMap f l) :=
  (pairwise_filter_map _).2 <| p.imp H
#align list.pairwise.filter_map List.Pairwise.filter_map

theorem pairwise_filter (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l :=
  by
  rw [← filter_map_eq_filter, pairwise_filter_map]
  apply pairwise.iff; intros ; simp only [Option.mem_def, Option.guard_eq_some, and_imp, forall_eq']
#align list.pairwise_filter List.pairwise_filter

theorem Pairwise.filter (p : α → Prop) [DecidablePred p] : Pairwise R l → Pairwise R (filter p l) :=
  Pairwise.sublist (filter_sublist _)
#align list.pairwise.filter List.Pairwise.filter

theorem pairwise_pmap {p : β → Prop} {f : ∀ b, p b → α} {l : List β} (h : ∀ x ∈ l, p x) :
    Pairwise R (l.pmap f h) ↔
      Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l :=
  by
  induction' l with a l ihl
  · simp
  obtain ⟨ha, hl⟩ : p a ∧ ∀ b, b ∈ l → p b := by simpa using h
  simp only [ihl hl, pairwise_cons, bex_imp, pmap, and_congr_left_iff, mem_pmap]
  refine' fun _ => ⟨fun H b hb hpa hpb => H _ _ hb rfl, _⟩
  rintro H _ b hb rfl
  exact H b hb _ _
#align list.pairwise_pmap List.pairwise_pmap

theorem Pairwise.pmap {l : List α} (hl : Pairwise R l) {p : α → Prop} {f : ∀ a, p a → β}
    (h : ∀ x ∈ l, p x) {S : β → β → Prop}
    (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) : Pairwise S (l.pmap f h) :=
  by
  refine' (pairwise_pmap h).2 (pairwise.imp_of_mem _ hl)
  intros ; apply hS; assumption
#align list.pairwise.pmap List.Pairwise.pmap

theorem pairwise_join {L : List (List α)} :
    Pairwise R (join L) ↔
      (∀ l ∈ L, Pairwise R l) ∧ Pairwise (fun l₁ l₂ => ∀ x ∈ l₁, ∀ y ∈ l₂, R x y) L :=
  by
  induction' L with l L IH
  · simp only [join, pairwise.nil, forall_prop_of_false (not_mem_nil _), forall_const, and_self_iff]
  have :
    (∀ x : α, x ∈ l → ∀ (y : α) (x_1 : List α), x_1 ∈ L → y ∈ x_1 → R x y) ↔
      ∀ a' : List α, a' ∈ L → ∀ x : α, x ∈ l → ∀ y : α, y ∈ a' → R x y :=
    ⟨fun h a b c d e => h c d e a b, fun h c d e a b => h a b c d e⟩
  simp only [join, pairwise_append, IH, mem_join, exists_imp, and_imp, this, forall_mem_cons,
    pairwise_cons]
  simp only [and_assoc', and_comm', and_left_comm]
#align list.pairwise_join List.pairwise_join

theorem pairwise_bind {R : β → β → Prop} {l : List α} {f : α → List β} :
    List.Pairwise R (l.bind f) ↔
      (∀ a ∈ l, Pairwise R (f a)) ∧ Pairwise (fun a₁ a₂ => ∀ x ∈ f a₁, ∀ y ∈ f a₂, R x y) l :=
  by simp [List.bind, List.pairwise_join, List.mem_map', List.pairwise_map]
#align list.pairwise_bind List.pairwise_bind

#print List.pairwise_reverse /-
@[simp]
theorem pairwise_reverse :
    ∀ {R} {l : List α}, Pairwise R (reverse l) ↔ Pairwise (fun x y => R y x) l :=
  suffices ∀ {R l}, @Pairwise α R l → Pairwise (fun x y => R y x) (reverse l) from fun R l =>
    ⟨fun p => reverse_reverse l ▸ this p, this⟩
  fun R l p => by
  induction' p with a l h p IH <;> [apply pairwise.nil,
    simpa only [reverse_cons, pairwise_append, IH, pairwise_cons,
      forall_prop_of_false (not_mem_nil _), forall_true_iff, pairwise.nil, mem_reverse,
      mem_singleton, forall_eq, true_and_iff] using h]
#align list.pairwise_reverse List.pairwise_reverse
-/

theorem pairwise_of_reflexive_on_dupl_of_forall_ne [DecidableEq α] {l : List α} {r : α → α → Prop}
    (hr : ∀ a, 1 < count a l → r a a) (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r :=
  by
  induction' l with hd tl IH
  · simp
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      by_cases H : hd = x
      · rw [H]
        refine' hr _ _
        simpa [count_cons, H, Nat.succ_lt_succ_iff, count_pos] using hx
      · exact h hd (mem_cons_self _ _) x (mem_cons_of_mem _ hx) H
    · refine' IH _ _
      · intro x hx
        refine' hr _ _
        rw [count_cons]
        split_ifs
        · exact hx.trans (Nat.lt_succ_self _)
        · exact hx
      · intro x hx y hy
        exact h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy)
#align
  list.pairwise_of_reflexive_on_dupl_of_forall_ne List.pairwise_of_reflexive_on_dupl_of_forall_ne

theorem pairwise_of_forall_mem_list {l : List α} {r : α → α → Prop} (h : ∀ a ∈ l, ∀ b ∈ l, r a b) :
    l.Pairwise r := by
  classical
    refine'
      pairwise_of_reflexive_on_dupl_of_forall_ne (fun a ha' => _) fun a ha b hb _ => h a ha b hb
    have ha := List.one_le_count_iff_mem.1 ha'.le
    exact h a ha a ha
#align list.pairwise_of_forall_mem_list List.pairwise_of_forall_mem_list

theorem pairwise_of_reflexive_of_forall_ne {l : List α} {r : α → α → Prop} (hr : Reflexive r)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  classical exact pairwise_of_reflexive_on_dupl_of_forall_ne (fun _ _ => hr _) h
#align list.pairwise_of_reflexive_of_forall_ne List.pairwise_of_reflexive_of_forall_ne

theorem pairwise_iff_nth_le {R} :
    ∀ {l : List α},
      Pairwise R l ↔
        ∀ (i j) (h₁ : j < length l) (h₂ : i < j), R (nthLe l i (lt_trans h₂ h₁)) (nthLe l j h₁)
  | [] => by
    simp only [pairwise.nil, true_iff_iff] <;> exact fun i j h => (Nat.not_lt_zero j).elim h
  | a :: l => by
    rw [pairwise_cons, pairwise_iff_nth_le]
    refine'
      ⟨fun H i j h₁ h₂ => _, fun H =>
        ⟨fun a' m => _, fun i j h₁ h₂ => H _ _ (succ_lt_succ h₁) (succ_lt_succ h₂)⟩⟩
    · cases' j with j
      · exact (Nat.not_lt_zero _).elim h₂
      cases' i with i
      · exact H.1 _ (nth_le_mem l _ _)
      · exact H.2 _ _ (lt_of_succ_lt_succ h₁) (lt_of_succ_lt_succ h₂)
    · rcases nth_le_of_mem m with ⟨n, h, rfl⟩
      exact H _ _ (succ_lt_succ h) (succ_pos _)
#align list.pairwise_iff_nth_le List.pairwise_iff_nth_le

theorem pairwise_repeat {α : Type _} {r : α → α → Prop} {x : α} (hx : r x x) :
    ∀ n : ℕ, Pairwise r (repeat x n)
  | 0 => by simp
  | n + 1 => by simp [hx, mem_repeat, pairwise_repeat n]
#align list.pairwise_repeat List.pairwise_repeat

/-! ### Pairwise filtering -/


variable [DecidableRel R]

@[simp]
theorem pw_filter_nil : pwFilter R [] = [] :=
  rfl
#align list.pw_filter_nil List.pw_filter_nil

@[simp]
theorem pw_filter_cons_of_pos {a : α} {l : List α} (h : ∀ b ∈ pwFilter R l, R a b) :
    pwFilter R (a :: l) = a :: pwFilter R l :=
  if_pos h
#align list.pw_filter_cons_of_pos List.pw_filter_cons_of_pos

@[simp]
theorem pw_filter_cons_of_neg {a : α} {l : List α} (h : ¬∀ b ∈ pwFilter R l, R a b) :
    pwFilter R (a :: l) = pwFilter R l :=
  if_neg h
#align list.pw_filter_cons_of_neg List.pw_filter_cons_of_neg

theorem pw_filter_map (f : β → α) :
    ∀ l : List β, pwFilter R (map f l) = map f (pwFilter (fun x y => R (f x) (f y)) l)
  | [] => rfl
  | x :: xs =>
    if h : ∀ b ∈ pwFilter R (map f xs), R (f x) b then
      by
      have h' : ∀ b : β, b ∈ pwFilter (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) :=
        fun b hb => h _ (by rw [pw_filter_map] <;> apply mem_map_of_mem _ hb)
      rw [map, pw_filter_cons_of_pos h, pw_filter_cons_of_pos h', pw_filter_map, map]
    else
      by
      have h' : ¬∀ b : β, b ∈ pwFilter (fun x y : β => R (f x) (f y)) xs → R (f x) (f b) :=
        fun hh =>
        h fun a ha => by
          rw [pw_filter_map, mem_map] at ha
          rcases ha with ⟨b, hb₀, hb₁⟩
          subst a
          exact hh _ hb₀
      rw [map, pw_filter_cons_of_neg h, pw_filter_cons_of_neg h', pw_filter_map]
#align list.pw_filter_map List.pw_filter_map

theorem pw_filter_sublist : ∀ l : List α, pwFilter R l <+ l
  | [] => nil_sublist _
  | x :: l => by
    by_cases ∀ y ∈ pw_filter R l, R x y
    · rw [pw_filter_cons_of_pos h]
      exact (pw_filter_sublist l).cons_cons _
    · rw [pw_filter_cons_of_neg h]
      exact sublist_cons_of_sublist _ (pw_filter_sublist l)
#align list.pw_filter_sublist List.pw_filter_sublist

theorem pw_filter_subset (l : List α) : pwFilter R l ⊆ l :=
  (pw_filter_sublist _).Subset
#align list.pw_filter_subset List.pw_filter_subset

theorem pairwise_pw_filter : ∀ l : List α, Pairwise R (pwFilter R l)
  | [] => Pairwise.nil
  | x :: l => by
    by_cases ∀ y ∈ pw_filter R l, R x y
    · rw [pw_filter_cons_of_pos h]
      exact pairwise_cons.2 ⟨h, pairwise_pw_filter l⟩
    · rw [pw_filter_cons_of_neg h]
      exact pairwise_pw_filter l
#align list.pairwise_pw_filter List.pairwise_pw_filter

theorem pw_filter_eq_self {l : List α} : pwFilter R l = l ↔ Pairwise R l :=
  ⟨fun e => e ▸ pairwise_pw_filter l, fun p =>
    by
    induction' l with x l IH; · rfl
    cases' pairwise_cons.1 p with al p
    rw [pw_filter_cons_of_pos (BAll.imp_left (pw_filter_subset l) al), IH p]⟩
#align list.pw_filter_eq_self List.pw_filter_eq_self

alias pw_filter_eq_self ↔ _ pairwise.pw_filter

attribute [protected] pairwise.pw_filter

@[simp]
theorem pw_filter_idempotent : pwFilter R (pwFilter R l) = pwFilter R l :=
  (pairwise_pw_filter l).pwFilter
#align list.pw_filter_idempotent List.pw_filter_idempotent

theorem forall_mem_pw_filter (neg_trans : ∀ {x y z}, R x z → R x y ∨ R y z) (a : α) (l : List α) :
    (∀ b ∈ pwFilter R l, R a b) ↔ ∀ b ∈ l, R a b :=
  ⟨by
    induction' l with x l IH; · exact fun _ _ => False.elim
    simp only [forall_mem_cons]
    by_cases ∀ y ∈ pw_filter R l, R x y <;> dsimp at h
    · simp only [pw_filter_cons_of_pos h, forall_mem_cons, and_imp]
      exact fun r H => ⟨r, IH H⟩
    · rw [pw_filter_cons_of_neg h]
      refine' fun H => ⟨_, IH H⟩
      cases' e : find (fun y => ¬R x y) (pw_filter R l) with k
      · refine' h.elim (BAll.imp_right _ (find_eq_none.1 e))
        exact fun y _ => not_not.1
      · have := find_some e
        exact (neg_trans (H k (find_mem e))).resolve_right this, BAll.imp_left (pw_filter_subset l)⟩
#align list.forall_mem_pw_filter List.forall_mem_pw_filter

end List



-- /-
-- Copyright (c) 2018 Mario Carneiro. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro
-- -/
-- import Mathlib.Data.List.Basic

-- /-!
-- # Pairwise relations on a list
-- -/

-- namespace List

-- variable {α β : Type _} {R S T : α → α → Prop} {a : α} {l : List α}

-- theorem pairwise_append_comm (s : Symmetric R) {l₁ l₂ : List α} :
--     Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
--   have : ∀ l₁ l₂ : List α, (∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y) →
--     ∀ x : α, x ∈ l₂ → ∀ y : α, y ∈ l₁ → R x y := fun l₁ l₂ a x xm y ym ↦ s (a y ym x xm)
--   simp only [pairwise_append, and_left_comm]; rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

-- theorem pairwise_middle (s : Symmetric R) {a : α} {l₁ l₂ : List α} :
--     Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) :=
--   show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂) by
--     rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s]
--     simp only [mem_append, or_comm]

-- theorem pairwise_singleton (R) (a : α) : Pairwise R [a] := by
--   simp [Pairwise.nil]

-- theorem Pairwise.of_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
--     (p : Pairwise S (map f l)) : Pairwise R l :=
--   (pairwise_map.1 p).imp (H _ _)

-- theorem Pairwise.map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
--     (p : Pairwise R l) : Pairwise S (map f l) :=
--   pairwise_map.2 <| p.imp (H _ _)

-- theorem Pairwise.and_mem {l : List α} :
--     Pairwise R l ↔ Pairwise (fun x y ↦ x ∈ l ∧ y ∈ l ∧ R x y) l :=
--   Pairwise.iff_of_mem (by simp (config := { contextual := true }))
