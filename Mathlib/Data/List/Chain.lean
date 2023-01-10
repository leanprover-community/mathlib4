/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov

! This file was ported from Lean 3 source module data.list.chain
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Pairwise
import Mathlib.Logic.Relation

/-!
# Relation chain

This file provides basic results about `List.Chain` (definition in `Data.List.Defs`).
A list `[a₂, ..., aₙ]` is a `Chain` starting at `a₁` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `Chain r a₁ [a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/


universe u v

open Nat

namespace List

variable {α : Type u} {β : Type v} {R r : α → α → Prop} {l l₁ l₂ : List α} {a b : α}

mk_iff_of_inductive_prop List.Chain List.chain_iff

--Porting note: attribute in Lean3, but not in Lean4 Std so added here instead
attribute [simp] Chain.nil

#align list.chain.nil List.Chain.nil
#align list.chain.cons List.Chain.cons

theorem rel_of_chain_cons {a b : α} {l : List α} (p : Chain R a (b :: l)) : R a b :=
  (chain_cons.1 p).1
#align list.rel_of_chain_cons List.rel_of_chain_cons

theorem chain_of_chain_cons {a b : α} {l : List α} (p : Chain R a (b :: l)) : Chain R b l :=
  (chain_cons.1 p).2
#align list.chain_of_chain_cons List.chain_of_chain_cons

theorem Chain.imp' {R S : α → α → Prop} (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α}
    (Hab : ∀ ⦃c⦄, R a c → S b c) {l : List α} (p : Chain R a l) : Chain S b l := by
  induction p generalizing b with
  | nil => constructor
  | cons r _ ih =>
    constructor
    · exact Hab r
    · exact ih (@HRS _)
#align list.chain.imp' List.Chain.imp'

theorem Chain.imp {R S : α → α → Prop} (H : ∀ a b, R a b → S a b) {a : α} {l : List α}
    (p : Chain R a l) : Chain S a l :=
  p.imp' H (H a)
#align list.chain.imp List.Chain.imp

theorem Chain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {a : α} {l : List α} :
    Chain R a l ↔ Chain S a l :=
  ⟨Chain.imp fun a b => (H a b).1, Chain.imp fun a b => (H a b).2⟩
#align list.chain.iff List.Chain.iff

theorem Chain.iff_mem {a : α} {l : List α} :
    Chain R a l ↔ Chain (fun x y => x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
  ⟨fun p => by
    induction' p with _ a b l r _ IH <;> constructor <;>
      [exact ⟨mem_cons_self _ _, mem_cons_self _ _, r⟩,
      exact IH.imp fun a b ⟨am, bm, h⟩ => ⟨mem_cons_of_mem _ am, mem_cons_of_mem _ bm, h⟩],
    Chain.imp fun a b h => h.2.2⟩
#align list.chain.iff_mem List.Chain.iff_mem

theorem chain_singleton {a b : α} : Chain R a [b] ↔ R a b := by
  simp only [chain_cons, Chain.nil, and_true_iff]
#align list.chain_singleton List.chain_singleton

theorem chain_split {a b : α} {l₁ l₂ : List α} :
    Chain R a (l₁ ++ b :: l₂) ↔ Chain R a (l₁ ++ [b]) ∧ Chain R b l₂ := by
  induction' l₁ with x l₁ IH generalizing a <;>
    simp only [*, nil_append, cons_append, Chain.nil, chain_cons, and_true_iff, and_assoc]
#align list.chain_split List.chain_split

@[simp]
theorem chain_append_cons_cons {a b c : α} {l₁ l₂ : List α} :
    Chain R a (l₁ ++ b :: c :: l₂) ↔ Chain R a (l₁ ++ [b]) ∧ R b c ∧ Chain R c l₂ := by
  rw [chain_split, chain_cons]
#align list.chain_append_cons_cons List.chain_append_cons_cons

theorem chain_iff_forall₂ :
    ∀ {a : α} {l : List α}, Chain R a l ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l
  | a, [] => by simp
  | a, b :: l => by
    by_cases h : l = [] <;>
    simp [@chain_iff_forall₂ b l, *]
#align list.chain_iff_forall₂ List.chain_iff_forall₂

theorem chain_append_singleton_iff_forall₂ : Chain R a (l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b]) :=
  by simp [chain_iff_forall₂]
#align list.chain_append_singleton_iff_forall₂ List.chain_append_singleton_iff_forall₂

theorem chain_map (f : β → α) {b : β} {l : List β} :
    Chain R (f b) (map f l) ↔ Chain (fun a b : β => R (f a) (f b)) b l := by
  induction l generalizing b <;> simp only [map, Chain.nil, chain_cons, *]
#align list.chain_map List.chain_map

theorem chain_of_chain_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    {a : α} {l : List α} (p : Chain S (f a) (map f l)) : Chain R a l :=
  ((chain_map f).1 p).imp H
#align list.chain_of_chain_map List.chain_of_chain_map

theorem chain_map_of_chain {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    {a : α} {l : List α} (p : Chain R a l) : Chain S (f a) (map f l) :=
  (chain_map f).2 <| p.imp H
#align list.chain_map_of_chain List.chain_map_of_chain

theorem chain_pmap_of_chain {S : β → β → Prop} {p : α → Prop} {f : ∀ a, p a → β}
    (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb)) {a : α} {l : List α} (hl₁ : Chain R a l)
    (ha : p a) (hl₂ : ∀ a ∈ l, p a) : Chain S (f a ha) (List.pmap f l hl₂) :=
  by
  induction' l with lh lt l_ih generalizing a
  · simp
  · simp [H _ _ _ _ (rel_of_chain_cons hl₁), l_ih (chain_of_chain_cons hl₁)]
#align list.chain_pmap_of_chain List.chain_pmap_of_chain

theorem chain_of_chain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl₁ : ∀ a ∈ l, p a) {a : α} (ha : p a) (hl₂ : Chain S (f a ha) (List.pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : Chain R a l :=
  by
  induction' l with lh lt l_ih generalizing a
  · simp
  · simp [H _ _ _ _ (rel_of_chain_cons hl₂), l_ih _ _ (chain_of_chain_cons hl₂)]
#align list.chain_of_chain_pmap List.chain_of_chain_pmap

/- warning: list.pairwise.chain -> List.Pairwise.chain is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : α -> α -> Prop} {l : List.{u1} α} {a : α}, (List.Pairwise.{u1} α R (List.cons.{u1} α a l)) -> (List.Chain.{u1} α R a l)
but is expected to have type
  forall {α : Type.{u1}} {R : α -> α -> Prop} {l : α} {a : List.{u1} α}, (List.Pairwise.{u1} α R (List.cons.{u1} α l a)) -> (List.Chain.{u1} α R l a)
Case conversion may be inaccurate. Consider using '#align list.pairwise.chain List.Pairwise.chainₓ'. -/
protected theorem Pairwise.chain (p : Pairwise R (a :: l)) : Chain R a l :=
  by
  cases' pairwise_cons.1 p with r p'; clear p
  induction' p' with b l r' _ IH generalizing a; · exact Chain.nil
  simp only [chain_cons, forall_mem_cons] at r
  exact chain_cons.2 ⟨r.1, IH r'⟩
#align list.pairwise.chain List.Pairwise.chain

/- warning: list.chain.pairwise -> List.Chain.pairwise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : α -> α -> Prop} [_inst_1 : IsTrans.{u1} α R] {a : α} {l : List.{u1} α}, (List.Chain.{u1} α R a l) -> (List.Pairwise.{u1} α R (List.cons.{u1} α a l))
but is expected to have type
  forall {α : Type.{u1}} {R : α -> α -> Prop} [_inst_1 : Trans.{0, 0, 0, succ u1, succ u1, succ u1} α α α R R R] {a : α} {l : List.{u1} α}, (List.Chain.{u1} α R a l) -> (List.Pairwise.{u1} α R (List.cons.{u1} α a l))
Case conversion may be inaccurate. Consider using '#align list.chain.pairwise List.Chain.pairwiseₓ'. -/
protected theorem Chain.pairwise [IsTrans α R] :
    ∀ {a : α} {l : List α}, Chain R a l → Pairwise R (a :: l)
  | a, [], Chain.nil => pairwise_singleton _ _
  | a, _, @Chain.cons _ _ _ b l h hb =>
    hb.pairwise.cons
      (by
        simp only [mem_cons, forall_eq_or_imp, h, true_and_iff]
        exact fun c hc => trans h (rel_of_pairwise_cons hb.pairwise hc))
#align list.chain.pairwise List.Chain.pairwise

/- warning: list.chain_iff_pairwise -> List.chain_iff_pairwise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : α -> α -> Prop} [_inst_1 : IsTrans.{u1} α R] {a : α} {l : List.{u1} α}, Iff (List.Chain.{u1} α R a l) (List.Pairwise.{u1} α R (List.cons.{u1} α a l))
but is expected to have type
  forall {α : Type.{u1}} {R : α -> α -> Prop} [_inst_1 : Trans.{0, 0, 0, succ u1, succ u1, succ u1} α α α R R R] {a : α} {l : List.{u1} α}, Iff (List.Chain.{u1} α R a l) (List.Pairwise.{u1} α R (List.cons.{u1} α a l))
Case conversion may be inaccurate. Consider using '#align list.chain_iff_pairwise List.chain_iff_pairwiseₓ'. -/
theorem chain_iff_pairwise [IsTrans α R] {a : α} {l : List α} : Chain R a l ↔ Pairwise R (a :: l) :=
  ⟨Chain.pairwise, Pairwise.chain⟩
#align list.chain_iff_pairwise List.chain_iff_pairwise

protected theorem Chain.sublist [IsTrans α R] (hl : l₂.Chain R a) (h : l₁ <+ l₂) : l₁.Chain R a :=
  by
  rw [chain_iff_pairwise] at hl⊢
  exact hl.sublist (h.cons_cons a)
#align list.chain.sublist List.Chain.sublist

protected theorem Chain.rel [IsTrans α R] (hl : l.Chain R a) (hb : b ∈ l) : R a b :=
  by
  rw [chain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb
#align list.chain.rel List.Chain.rel

theorem chain_iff_nth_le {R} :
    ∀ {a : α} {l : List α},
      Chain R a l ↔
        (∀ h : 0 < length l, R a (nthLe l 0 h)) ∧
          ∀ (i) (h : i < length l - 1),
            R (nthLe l i (lt_of_lt_pred h)) (nthLe l (i + 1) (lt_pred_iff.mp h))
  | a, [] => by simp
  | a, b :: t => by
    rw [chain_cons, chain_iff_nth_le]
    constructor
    · rintro ⟨R, ⟨h0, h⟩⟩
      constructor
      · intro w
        exact R
      intro i w
      cases i
      · apply h0
      convert h i _ using 1
      simp only [succ_eq_add_one, add_succ_sub_one, add_zero, length, add_lt_add_iff_right] at w
      exact lt_pred_iff.mpr w
    rintro ⟨h0, h⟩; constructor
    · apply h0
      simp
    constructor
    · apply h 0
    intro i w; convert h (i + 1) _ using 1
    exact lt_pred_iff.mp w
#align list.chain_iff_nth_le List.chain_iff_nth_le

theorem Chain'.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b) {l : List α} (p : Chain' R l) :
    Chain' S l := by cases l <;> [trivial, exact p.imp H]
#align list.chain'.imp List.Chain'.imp

theorem Chain'.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    Chain' R l ↔ Chain' S l :=
  ⟨Chain'.imp fun a b => (H a b).1, Chain'.imp fun a b => (H a b).2⟩
#align list.chain'.iff List.Chain'.iff

theorem Chain'.iff_mem : ∀ {l : List α}, Chain' R l ↔ Chain' (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
  | [] => Iff.rfl
  | x :: l =>
    ⟨fun h => (Chain.iff_mem.1 h).imp fun a b ⟨h₁, h₂, h₃⟩ => ⟨h₁, Or.inr h₂, h₃⟩,
      chain'.imp fun a b h => h.2.2⟩
#align list.chain'.iff_mem List.Chain'.iff_mem

@[simp]
theorem chain'_nil : Chain' R [] :=
  trivial
#align list.chain'_nil List.chain'_nil

@[simp]
theorem chain'_singleton (a : α) : Chain' R [a] :=
  chain.nil
#align list.chain'_singleton List.chain'_singleton

@[simp]
theorem chain'_cons {x y l} : Chain' R (x :: y :: l) ↔ R x y ∧ Chain' R (y :: l) :=
  chain_cons
#align list.chain'_cons List.chain'_cons

theorem chain'_is_infix : ∀ l : List α, Chain' (fun x y => [x, y] <:+: l) l
  | [] => chain'_nil
  | [a] => chain'_singleton _
  | a :: b :: l =>
    chain'_cons.2
      ⟨⟨[], l, by simp⟩, (chain'_is_infix (b :: l)).imp fun x y h => h.trans ⟨[a], [], by simp⟩⟩
#align list.chain'_is_infix List.chain'_is_infix

theorem chain'_split {a : α} :
    ∀ {l₁ l₂ : List α}, Chain' R (l₁ ++ a :: l₂) ↔ Chain' R (l₁ ++ [a]) ∧ Chain' R (a :: l₂)
  | [], l₂ => (and_iff_right (chain'_singleton a)).symm
  | b :: l₁, l₂ => chain_split
#align list.chain'_split List.chain'_split

@[simp]
theorem chain'_append_cons_cons {b c : α} {l₁ l₂ : List α} :
    Chain' R (l₁ ++ b :: c :: l₂) ↔ Chain' R (l₁ ++ [b]) ∧ R b c ∧ Chain' R (c :: l₂) := by
  rw [chain'_split, chain'_cons]
#align list.chain'_append_cons_cons List.chain'_append_cons_cons

theorem chain'_map (f : β → α) {l : List β} :
    Chain' R (map f l) ↔ Chain' (fun a b : β => R (f a) (f b)) l := by
  cases l <;> [rfl, exact chain_map _]
#align list.chain'_map List.chain'_map

theorem chain'_of_chain'_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    {l : List α} (p : Chain' S (map f l)) : Chain' R l :=
  ((chain'_map f).1 p).imp H
#align list.chain'_of_chain'_map List.chain'_of_chain'_map

theorem chain'_map_of_chain' {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (p : Chain' R l) : Chain' S (map f l) :=
  (chain'_map f).2 <| p.imp H
#align list.chain'_map_of_chain' List.chain'_map_of_chain'

theorem Pairwise.chain' : ∀ {l : List α}, Pairwise R l → Chain' R l
  | [], _ => trivial
  | a :: l, h => Pairwise.chain h
#align list.pairwise.chain' List.Pairwise.chain'

theorem chain'_iff_pairwise [IsTrans α R] : ∀ {l : List α}, Chain' R l ↔ Pairwise R l
  | [] => (iff_true_intro Pairwise.nil).symm
  | a :: l => chain_iff_pairwise
#align list.chain'_iff_pairwise List.chain'_iff_pairwise

protected theorem Chain'.sublist [IsTrans α R] (hl : l₂.Chain' R) (h : l₁ <+ l₂) : l₁.Chain' R :=
  by
  rw [chain'_iff_pairwise] at hl⊢
  exact hl.sublist h
#align list.chain'.sublist List.Chain'.sublist

theorem Chain'.cons {x y l} (h₁ : R x y) (h₂ : Chain' R (y :: l)) : Chain' R (x :: y :: l) :=
  chain'_cons.2 ⟨h₁, h₂⟩
#align list.chain'.cons List.Chain'.cons

theorem Chain'.tail : ∀ {l} (h : Chain' R l), Chain' R l.tail
  | [], _ => trivial
  | [x], _ => trivial
  | x :: y :: l, h => (chain'_cons.mp h).right
#align list.chain'.tail List.Chain'.tail

theorem Chain'.rel_head {x y l} (h : Chain' R (x :: y :: l)) : R x y :=
  rel_of_chain_cons h
#align list.chain'.rel_head List.Chain'.rel_head

theorem Chain'.rel_head' {x l} (h : Chain' R (x :: l)) ⦃y⦄ (hy : y ∈ head? l) : R x y :=
  by
  rw [← cons_head'_tail hy] at h
  exact h.rel_head
#align list.chain'.rel_head' List.Chain'.rel_head'

theorem Chain'.cons' {x} : ∀ {l : List α}, Chain' R l → (∀ y ∈ l.head', R x y) → Chain' R (x :: l)
  | [], _, _ => chain'_singleton x
  | a :: l, hl, H => hl.cons <| H _ rfl
#align list.chain'.cons' List.Chain'.cons'

theorem chain'_cons' {x l} : Chain' R (x :: l) ↔ (∀ y ∈ head? l, R x y) ∧ Chain' R l :=
  ⟨fun h => ⟨h.rel_head', h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons' h₁⟩
#align list.chain'_cons' List.chain'_cons'

theorem chain'_append :
    ∀ {l₁ l₂ : List α},
      Chain' R (l₁ ++ l₂) ↔ Chain' R l₁ ∧ Chain' R l₂ ∧ ∀ x ∈ l₁.last', ∀ y ∈ l₂.head', R x y
  | [], l => by simp
  | [a], l => by simp [chain'_cons', and_comm']
  | a :: b :: l₁, l₂ => by
    rw [cons_append, cons_append, chain'_cons, chain'_cons, ← cons_append, chain'_append, last',
      and_assoc]
#align list.chain'_append List.chain'_append

theorem Chain'.append (h₁ : Chain' R l₁) (h₂ : Chain' R l₂)
    (h : ∀ x ∈ l₁.last', ∀ y ∈ l₂.head', R x y) : Chain' R (l₁ ++ l₂) :=
  chain'_append.2 ⟨h₁, h₂, h⟩
#align list.chain'.append List.Chain'.append

theorem Chain'.left_of_append (h : Chain' R (l₁ ++ l₂)) : Chain' R l₁ :=
  (chain'_append.1 h).1
#align list.chain'.left_of_append List.Chain'.left_of_append

theorem Chain'.right_of_append (h : Chain' R (l₁ ++ l₂)) : Chain' R l₂ :=
  (chain'_append.1 h).2.1
#align list.chain'.right_of_append List.Chain'.right_of_append

theorem Chain'.infix (h : Chain' R l) (h' : l₁ <:+: l) : Chain' R l₁ :=
  by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append
#align list.chain'.infix List.Chain'.infix

theorem Chain'.suffix (h : Chain' R l) (h' : l₁ <:+ l) : Chain' R l₁ :=
  h.infix h'.isInfix
#align list.chain'.suffix List.Chain'.suffix

theorem Chain'.prefix (h : Chain' R l) (h' : l₁ <+: l) : Chain' R l₁ :=
  h.infix h'.isInfix
#align list.chain'.prefix List.Chain'.prefix

theorem Chain'.drop (h : Chain' R l) (n : ℕ) : Chain' R (drop n l) :=
  h.suffix (drop_suffix _ _)
#align list.chain'.drop List.Chain'.drop

theorem Chain'.init (h : Chain' R l) : Chain' R l.init :=
  h.prefix l.init_prefix
#align list.chain'.init List.Chain'.init

theorem Chain'.take (h : Chain' R l) (n : ℕ) : Chain' R (take n l) :=
  h.prefix (take_prefix _ _)
#align list.chain'.take List.Chain'.take

theorem chain'_pair {x y} : Chain' R [x, y] ↔ R x y := by
  simp only [chain'_singleton, chain'_cons, and_true_iff]
#align list.chain'_pair List.chain'_pair

theorem Chain'.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : Chain' R (x :: l)) :
    Chain' R (y :: l) :=
  hl.tail.cons' fun z hz => h <| hl.rel_head' hz
#align list.chain'.imp_head List.Chain'.imp_head

theorem chain'_reverse : ∀ {l}, Chain' R (reverse l) ↔ Chain' (flip R) l
  | [] => Iff.rfl
  | [a] => by simp only [chain'_singleton, reverse_singleton]
  | a :: b :: l => by
    rw [chain'_cons, reverse_cons, reverse_cons, append_assoc, cons_append, nil_append,
      chain'_split, ← reverse_cons, @chain'_reverse (b :: l), and_comm', chain'_pair, flip]
#align list.chain'_reverse List.chain'_reverse

theorem chain'_iff_nth_le {R} :
    ∀ {l : List α},
      Chain' R l ↔
        ∀ (i) (h : i < length l - 1),
          R (nthLe l i (lt_of_lt_pred h)) (nthLe l (i + 1) (lt_pred_iff.mp h))
  | [] => by simp
  | [a] => by simp
  | a :: b :: t => by
    rw [← and_forall_succ, chain'_cons, chain'_iff_nth_le]
    simp only [length, nth_le, add_tsub_cancel_right, add_lt_add_iff_right, tsub_pos_iff_lt,
      one_lt_succ_succ, true_imp_iff]
    rfl
#align list.chain'_iff_nth_le List.chain'_iff_nth_le

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `chain' R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
theorem Chain'.append_overlap {l₁ l₂ l₃ : List α} (h₁ : Chain' R (l₁ ++ l₂))
    (h₂ : Chain' R (l₂ ++ l₃)) (hn : l₂ ≠ []) : Chain' R (l₁ ++ l₂ ++ l₃) :=
  h₁.append h₂.right_of_append <| by
    simpa only [last'_append_of_ne_nil _ hn] using (chain'_append.1 h₂).2.2
#align list.chain'.append_overlap List.Chain'.append_overlap

/-- If `a` and `b` are related by the reflexive transitive closure of `r`, then there is a `r`-chain
starting from `a` and ending on `b`.
The converse of `relation_refl_trans_gen_of_exists_chain`.
-/
theorem exists_chain_of_relation_refl_trans_gen (h : Relation.ReflTransGen r a b) :
    ∃ l, Chain r a l ∧ getLast (a :: l) (cons_ne_nil _ _) = b :=
  by
  apply Relation.ReflTransGen.head_induction_on h
  · exact ⟨[], chain.nil, rfl⟩
  · intro c d e t ih
    obtain ⟨l, hl₁, hl₂⟩ := ih
    refine' ⟨d :: l, chain.cons e hl₁, _⟩
    rwa [last_cons_cons]
#align list.exists_chain_of_relation_refl_trans_gen List.exists_chain_of_relation_refl_trans_gen

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem Chain.induction (p : α → Prop) (l : List α) (h : Chain r a l)
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : ∀ i ∈ a :: l, p i :=
  by
  induction l generalizing a
  · cases hb
    simp [final]
  · rw [chain_cons] at h
    rintro _ (rfl | _)
    apply carries h.1 (l_ih h.2 hb _ (Or.inl rfl))
    apply l_ih h.2 hb _ H
#align list.chain.induction List.Chain.induction

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
@[elab_as_elim]
theorem Chain.induction_head (p : α → Prop) (l : List α) (h : Chain r a l)
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : p a :=
  (Chain.induction p l h hb carries final) _ (mem_cons_self _ _)
#align list.chain.induction_head List.Chain.induction_head

/--
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` are related by the
reflexive transitive closure of `r`. The converse of `exists_chain_of_relation_refl_trans_gen`.
-/
theorem relation_refl_trans_gen_of_exists_chain (l) (hl₁ : Chain r a l)
    (hl₂ : getLast (a :: l) (cons_ne_nil _ _) = b) : Relation.ReflTransGen r a b :=
  Chain.induction_head _ l hl₁ hl₂ (fun x y => Relation.ReflTransGen.head)
    Relation.ReflTransGen.refl
#align list.relation_refl_trans_gen_of_exists_chain List.relation_refl_trans_gen_of_exists_chain

end List


-- /-
-- Copyright (c) 2018 Mario Carneiro. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-- -/
-- import Std.Data.List.Basic
-- import Mathlib.Init.Logic
-- import Mathlib.Data.List.Defs
-- import Mathlib.Data.List.Pairwise

-- /-!
-- # Relation chain

-- This file provides basic results about `List.Chain` (definition in `Std.Data.List.Defs`).
-- A list `[a₂, ..., aₙ]` is a `Chain` starting at `a₁` with respect to the relation `r` if `r a₁ a₂`
-- and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `Chain r a₁ [a₂, ..., aₙ]`.
-- A graph-specialized version is in development and will hopefully be added under `combinatorics.`
-- sometime soon.
-- -/

-- namespace List





-- protected theorem Pairwise.chain (p : Pairwise R (a :: l)) : Chain R a l := by
--   rcases pairwise_cons.1 p with ⟨r,p'⟩
--   clear p
--   induction p' generalizing a with
--   | nil => exact Chain.nil
--   | cons r' _ ih =>
--     simp only [chain_cons, forall_mem_cons] at r
--     exact chain_cons.2 ⟨r.1, ih r'⟩

-- protected theorem Chain.pairwise {R : α → α → Prop} [Trans R R R] :
--     ∀ {a : α} {l : List α}, Chain R a l → Pairwise R (a :: l)
--   | a, [], .nil => pairwise_singleton _ _
--   | a, _, .cons h hb =>
--     hb.pairwise.cons (by
--       simp only [mem_cons, forall_eq_or_imp, h, true_and]
--       exact fun c hc ↦ trans h (rel_of_pairwise_cons hb.pairwise hc))

-- theorem chain_iff_pairwise {R : α → α → Prop} [Trans R R R] {a : α} {l : List α} :
--     Chain R a l ↔ Pairwise R (a :: l) :=
--   ⟨Chain.pairwise, Pairwise.chain⟩
