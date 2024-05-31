/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import Mathlib.Logic.Relation
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Infix

#align_import data.list.chain from "leanprover-community/mathlib"@"dd71334db81d0bd444af1ee339a29298bef40734"

/-!
# Relation chain

This file provides basic results about `List.Chain` (definition in `Data.List.Defs`).
A list `[a₂, ..., aₙ]` is a `Chain` starting at `a₁` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `Chain r a₁ [a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

-- Make sure we haven't imported `Data.Nat.Order.Basic`
assert_not_exists OrderedSub

universe u v

open Nat

namespace List

variable {α : Type u} {β : Type v} {R r : α → α → Prop} {l l₁ l₂ : List α} {a b : α}

mk_iff_of_inductive_prop List.Chain List.chain_iff
#align list.chain_iff List.chain_iff

#align list.chain.nil List.Chain.nil
#align list.chain.cons List.Chain.cons
#align list.rel_of_chain_cons List.rel_of_chain_cons
#align list.chain_of_chain_cons List.chain_of_chain_cons
#align list.chain.imp' List.Chain.imp'
#align list.chain.imp List.Chain.imp

theorem Chain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {a : α} {l : List α} :
    Chain R a l ↔ Chain S a l :=
  ⟨Chain.imp fun a b => (H a b).1, Chain.imp fun a b => (H a b).2⟩
#align list.chain.iff List.Chain.iff

theorem Chain.iff_mem {a : α} {l : List α} :
    Chain R a l ↔ Chain (fun x y => x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
  ⟨fun p => by
    induction' p with _ a b l r _ IH <;> constructor <;>
      [exact ⟨mem_cons_self _ _, mem_cons_self _ _, r⟩;
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
    simp [@chain_iff_forall₂ b l, dropLast, *]
#align list.chain_iff_forall₂ List.chain_iff_forall₂

theorem chain_append_singleton_iff_forall₂ :
    Chain R a (l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b]) := by simp [chain_iff_forall₂]
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
    (ha : p a) (hl₂ : ∀ a ∈ l, p a) : Chain S (f a ha) (List.pmap f l hl₂) := by
  induction' l with lh lt l_ih generalizing a
  · simp
  · simp [H _ _ _ _ (rel_of_chain_cons hl₁), l_ih (chain_of_chain_cons hl₁)]
#align list.chain_pmap_of_chain List.chain_pmap_of_chain

theorem chain_of_chain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl₁ : ∀ a ∈ l, p a) {a : α} (ha : p a) (hl₂ : Chain S (f a ha) (List.pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : Chain R a l := by
  induction' l with lh lt l_ih generalizing a
  · simp
  · simp [H _ _ _ _ (rel_of_chain_cons hl₂), l_ih _ _ (chain_of_chain_cons hl₂)]
#align list.chain_of_chain_pmap List.chain_of_chain_pmap

#align list.pairwise.chain List.Pairwise.chain

protected theorem Chain.pairwise [IsTrans α R] :
    ∀ {a : α} {l : List α}, Chain R a l → Pairwise R (a :: l)
  | a, [], Chain.nil => pairwise_singleton _ _
  | a, _, @Chain.cons _ _ _ b l h hb =>
    hb.pairwise.cons
      (by
        simp only [mem_cons, forall_eq_or_imp, h, true_and_iff]
        exact fun c hc => _root_.trans h (rel_of_pairwise_cons hb.pairwise hc))
#align list.chain.pairwise List.Chain.pairwise

theorem chain_iff_pairwise [IsTrans α R] {a : α} {l : List α} : Chain R a l ↔ Pairwise R (a :: l) :=
  ⟨Chain.pairwise, Pairwise.chain⟩
#align list.chain_iff_pairwise List.chain_iff_pairwise

protected theorem Chain.sublist [IsTrans α R] (hl : l₂.Chain R a) (h : l₁ <+ l₂) :
    l₁.Chain R a := by
  rw [chain_iff_pairwise] at hl ⊢
  exact hl.sublist (h.cons_cons a)
#align list.chain.sublist List.Chain.sublist

protected theorem Chain.rel [IsTrans α R] (hl : l.Chain R a) (hb : b ∈ l) : R a b := by
  rw [chain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb
#align list.chain.rel List.Chain.rel

theorem chain_iff_get {R} : ∀ {a : α} {l : List α}, Chain R a l ↔
    (∀ h : 0 < length l, R a (get l ⟨0, h⟩)) ∧
      ∀ (i : ℕ) (h : i < l.length - 1),
        R (get l ⟨i, by omega⟩) (get l ⟨i+1, by omega⟩)
  | a, [] => iff_of_true (by simp) ⟨fun h => by simp at h, fun _ h => by simp at h⟩
  | a, b :: t => by
    rw [chain_cons, @chain_iff_get _ _ t]
    constructor
    · rintro ⟨R, ⟨h0, h⟩⟩
      constructor
      · intro _
        exact R
      intro i w
      cases' i with i
      · apply h0
      · exact h i (by simp only [length_cons] at w; omega)
    rintro ⟨h0, h⟩; constructor
    · apply h0
      simp
    constructor
    · apply h 0
    intro i w
    exact h (i+1) (by simp only [length_cons]; omega)

set_option linter.deprecated false in
@[deprecated chain_iff_get] -- 2023-01-10
theorem chain_iff_nthLe {R} {a : α} {l : List α} : Chain R a l ↔
    (∀ h : 0 < length l, R a (nthLe l 0 h)) ∧
    ∀ (i) (h : i < length l - 1),
    R (nthLe l i (by omega)) (nthLe l (i + 1) (by omega)) := by
  rw [chain_iff_get]; simp [nthLe]
#align list.chain_iff_nth_le List.chain_iff_nthLe

theorem Chain'.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b) {l : List α} (p : Chain' R l) :
    Chain' S l := by cases l <;> [trivial; exact Chain.imp H p]
#align list.chain'.imp List.Chain'.imp

theorem Chain'.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    Chain' R l ↔ Chain' S l :=
  ⟨Chain'.imp fun a b => (H a b).1, Chain'.imp fun a b => (H a b).2⟩
#align list.chain'.iff List.Chain'.iff

theorem Chain'.iff_mem : ∀ {l : List α}, Chain' R l ↔ Chain' (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
  | [] => Iff.rfl
  | _ :: _ =>
    ⟨fun h => (Chain.iff_mem.1 h).imp fun _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, mem_cons.2 (Or.inr h₂), h₃⟩,
      Chain'.imp fun _ _ h => h.2.2⟩
#align list.chain'.iff_mem List.Chain'.iff_mem

@[simp]
theorem chain'_nil : Chain' R [] :=
  trivial
#align list.chain'_nil List.chain'_nil

@[simp]
theorem chain'_singleton (a : α) : Chain' R [a] :=
  Chain.nil
#align list.chain'_singleton List.chain'_singleton

@[simp]
theorem chain'_cons {x y l} : Chain' R (x :: y :: l) ↔ R x y ∧ Chain' R (y :: l) :=
  chain_cons
#align list.chain'_cons List.chain'_cons

theorem chain'_isInfix : ∀ l : List α, Chain' (fun x y => [x, y] <:+: l) l
  | [] => chain'_nil
  | [a] => chain'_singleton _
  | a :: b :: l =>
    chain'_cons.2
      ⟨⟨[], l, by simp⟩, (chain'_isInfix (b :: l)).imp fun x y h => h.trans ⟨[a], [], by simp⟩⟩
#align list.chain'_is_infix List.chain'_isInfix

theorem chain'_split {a : α} :
    ∀ {l₁ l₂ : List α}, Chain' R (l₁ ++ a :: l₂) ↔ Chain' R (l₁ ++ [a]) ∧ Chain' R (a :: l₂)
  | [], _ => (and_iff_right (chain'_singleton a)).symm
  | _ :: _, _ => chain_split
#align list.chain'_split List.chain'_split

@[simp]
theorem chain'_append_cons_cons {b c : α} {l₁ l₂ : List α} :
    Chain' R (l₁ ++ b :: c :: l₂) ↔ Chain' R (l₁ ++ [b]) ∧ R b c ∧ Chain' R (c :: l₂) := by
  rw [chain'_split, chain'_cons]
#align list.chain'_append_cons_cons List.chain'_append_cons_cons

theorem chain'_map (f : β → α) {l : List β} :
    Chain' R (map f l) ↔ Chain' (fun a b : β => R (f a) (f b)) l := by
  cases l <;> [rfl; exact chain_map _]
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
  | _ :: _, h => Pairwise.chain h
#align list.pairwise.chain' List.Pairwise.chain'

theorem chain'_iff_pairwise [IsTrans α R] : ∀ {l : List α}, Chain' R l ↔ Pairwise R l
  | [] => (iff_true_intro Pairwise.nil).symm
  | _ :: _ => chain_iff_pairwise
#align list.chain'_iff_pairwise List.chain'_iff_pairwise

protected theorem Chain'.sublist [IsTrans α R] (hl : l₂.Chain' R) (h : l₁ <+ l₂) : l₁.Chain' R := by
  rw [chain'_iff_pairwise] at hl ⊢
  exact hl.sublist h
#align list.chain'.sublist List.Chain'.sublist

theorem Chain'.cons {x y l} (h₁ : R x y) (h₂ : Chain' R (y :: l)) : Chain' R (x :: y :: l) :=
  chain'_cons.2 ⟨h₁, h₂⟩
#align list.chain'.cons List.Chain'.cons

theorem Chain'.tail : ∀ {l}, Chain' R l → Chain' R l.tail
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => (chain'_cons.mp h).right
#align list.chain'.tail List.Chain'.tail

theorem Chain'.rel_head {x y l} (h : Chain' R (x :: y :: l)) : R x y :=
  rel_of_chain_cons h
#align list.chain'.rel_head List.Chain'.rel_head

theorem Chain'.rel_head? {x l} (h : Chain' R (x :: l)) ⦃y⦄ (hy : y ∈ head? l) : R x y := by
  rw [← cons_head?_tail hy] at h
  exact h.rel_head
#align list.chain'.rel_head' List.Chain'.rel_head?

theorem Chain'.cons' {x} : ∀ {l : List α}, Chain' R l → (∀ y ∈ l.head?, R x y) → Chain' R (x :: l)
  | [], _, _ => chain'_singleton x
  | _ :: _, hl, H => hl.cons <| H _ rfl
#align list.chain'.cons' List.Chain'.cons'

theorem chain'_cons' {x l} : Chain' R (x :: l) ↔ (∀ y ∈ head? l, R x y) ∧ Chain' R l :=
  ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons' h₁⟩
#align list.chain'_cons' List.chain'_cons'

theorem chain'_append :
    ∀ {l₁ l₂ : List α},
      Chain' R (l₁ ++ l₂) ↔ Chain' R l₁ ∧ Chain' R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y
  | [], l => by simp
  | [a], l => by simp [chain'_cons', and_comm]
  | a :: b :: l₁, l₂ => by
    rw [cons_append, cons_append, chain'_cons, chain'_cons, ← cons_append, chain'_append,
      and_assoc]
    simp
#align list.chain'_append List.chain'_append

theorem Chain'.append (h₁ : Chain' R l₁) (h₂ : Chain' R l₂)
    (h : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) : Chain' R (l₁ ++ l₂) :=
  chain'_append.2 ⟨h₁, h₂, h⟩
#align list.chain'.append List.Chain'.append

theorem Chain'.left_of_append (h : Chain' R (l₁ ++ l₂)) : Chain' R l₁ :=
  (chain'_append.1 h).1
#align list.chain'.left_of_append List.Chain'.left_of_append

theorem Chain'.right_of_append (h : Chain' R (l₁ ++ l₂)) : Chain' R l₂ :=
  (chain'_append.1 h).2.1
#align list.chain'.right_of_append List.Chain'.right_of_append

theorem Chain'.infix (h : Chain' R l) (h' : l₁ <:+: l) : Chain' R l₁ := by
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

theorem Chain'.init (h : Chain' R l) : Chain' R l.dropLast :=
  h.prefix l.dropLast_prefix
#align list.chain'.init List.Chain'.init

theorem Chain'.take (h : Chain' R l) (n : ℕ) : Chain' R (take n l) :=
  h.prefix (take_prefix _ _)
#align list.chain'.take List.Chain'.take

theorem chain'_pair {x y} : Chain' R [x, y] ↔ R x y := by
  simp only [chain'_singleton, chain'_cons, and_true_iff]
#align list.chain'_pair List.chain'_pair

theorem Chain'.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : Chain' R (x :: l)) :
    Chain' R (y :: l) :=
  hl.tail.cons' fun _ hz => h <| hl.rel_head? hz
#align list.chain'.imp_head List.Chain'.imp_head

theorem chain'_reverse : ∀ {l}, Chain' R (reverse l) ↔ Chain' (flip R) l
  | [] => Iff.rfl
  | [a] => by simp only [chain'_singleton, reverse_singleton]
  | a :: b :: l => by
    rw [chain'_cons, reverse_cons, reverse_cons, append_assoc, cons_append, nil_append,
      chain'_split, ← reverse_cons, @chain'_reverse (b :: l), and_comm, chain'_pair, flip]
#align list.chain'_reverse List.chain'_reverse

theorem chain'_iff_get {R} : ∀ {l : List α}, Chain' R l ↔
    ∀ (i : ℕ) (h : i < length l - 1),
      R (get l ⟨i, by omega⟩) (get l ⟨i + 1, by omega⟩)
  | [] => iff_of_true (by simp) (fun _ h => by simp at h)
  | [a] => iff_of_true (by simp) (fun _ h => by simp at h)
  | a :: b :: t => by
    rw [← and_forall_succ, chain'_cons, chain'_iff_get]
    simp only [length_cons, get_cons_succ, Fin.zero_eta, get_cons_zero, Nat.zero_add, Fin.mk_one,
      get_cons_cons_one, succ_sub_succ_eq_sub, Nat.le_zero, Nat.add_eq_zero_iff, and_false,
      Nat.sub_zero, Nat.add_pos_iff_pos_or_pos, Nat.zero_lt_one, or_true, forall_true_left,
      and_congr_right_iff]
    dsimp [succ_sub_one]
    exact fun _ => ⟨fun h i hi => h i (Nat.lt_of_succ_lt_succ hi),
                    fun h i hi => h i (Nat.succ_lt_succ hi)⟩

set_option linter.deprecated false in
@[deprecated chain'_iff_get] -- 2023-01-10
theorem chain'_iff_nthLe {R} {l : List α} : Chain' R l ↔
    ∀ (i) (h : i < length l - 1),
      R (nthLe l i (by omega)) (nthLe l (i + 1) (by omega)) :=
  chain'_iff_get.trans <| by simp [nthLe]
#align list.chain'_iff_nth_le List.chain'_iff_nthLe

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `Chain' R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
theorem Chain'.append_overlap {l₁ l₂ l₃ : List α} (h₁ : Chain' R (l₁ ++ l₂))
    (h₂ : Chain' R (l₂ ++ l₃)) (hn : l₂ ≠ []) : Chain' R (l₁ ++ l₂ ++ l₃) :=
  h₁.append h₂.right_of_append <| by
    simpa only [getLast?_append_of_ne_nil _ hn] using (chain'_append.1 h₂).2.2
#align list.chain'.append_overlap List.Chain'.append_overlap

-- Porting note (#10756): new lemma
lemma chain'_join : ∀ {L : List (List α)}, [] ∉ L →
    (Chain' R L.join ↔ (∀ l ∈ L, Chain' R l) ∧
    L.Chain' (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), R x y))
| [], _ => by simp
| [l], _ => by simp [join]
| (l₁ :: l₂ :: L), hL => by
    rw [mem_cons, not_or, ← Ne] at hL
    rw [join, chain'_append, chain'_join hL.2, forall_mem_cons, chain'_cons]
    rw [mem_cons, not_or, ← Ne] at hL
    simp only [forall_mem_cons, and_assoc, join, head?_append_of_ne_nil _ hL.2.1.symm]
    exact Iff.rfl.and (Iff.rfl.and <| Iff.rfl.and and_comm)

/-- If `a` and `b` are related by the reflexive transitive closure of `r`, then there is an
`r`-chain starting from `a` and ending on `b`.
The converse of `relationReflTransGen_of_exists_chain`.
-/
theorem exists_chain_of_relationReflTransGen (h : Relation.ReflTransGen r a b) :
    ∃ l, Chain r a l ∧ getLast (a :: l) (cons_ne_nil _ _) = b := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[], Chain.nil, rfl⟩
  · intro c d e _ ih
    obtain ⟨l, hl₁, hl₂⟩ := ih
    refine ⟨d :: l, Chain.cons e hl₁, ?_⟩
    rwa [getLast_cons_cons]
#align list.exists_chain_of_relation_refl_trans_gen List.exists_chain_of_relationReflTransGen

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem Chain.induction (p : α → Prop) (l : List α) (h : Chain r a l)
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : ∀ i ∈ a :: l, p i := by
  induction' l with _ _ l_ih generalizing a
  · cases hb
    simpa using final
  · rw [chain_cons] at h
    simp only [mem_cons]
    rintro _ (rfl | H)
    · apply carries h.1 (l_ih h.2 hb _ (mem_cons.2 (Or.inl rfl)))
    · apply l_ih h.2 hb _ (mem_cons.2 H)
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
reflexive transitive closure of `r`. The converse of `exists_chain_of_relationReflTransGen`.
-/
theorem relationReflTransGen_of_exists_chain (l : List α) (hl₁ : Chain r a l)
    (hl₂ : getLast (a :: l) (cons_ne_nil _ _) = b) : Relation.ReflTransGen r a b :=
-- Porting note: `p` behaves like an implicit argument to `Chain.induction_head` but it is explicit.
  Chain.induction_head l hl₁ hl₂ (fun _ _ => Relation.ReflTransGen.head)
    Relation.ReflTransGen.refl
#align list.relation_refl_trans_gen_of_exists_chain List.relationReflTransGen_of_exists_chain

theorem Chain'.cons_of_le [LinearOrder α] {a : α} {as m : List α}
    (ha : List.Chain' (· > ·) (a :: as)) (hm : List.Chain' (· > ·) m) (hmas : m ≤ as) :
    List.Chain' (· > ·) (a :: m) := by
  cases m with
  | nil => simp only [List.chain'_singleton]
  | cons b bs =>
    apply hm.cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, or_false] at hmas
      exact (List.Lex.not_nil_right (·<·) _ hmas).elim
    | cons a' as =>
      rw [List.chain'_cons] at ha
      refine gt_of_gt_of_ge ha.1 ?_
      rw [le_iff_lt_or_eq] at hmas
      cases' hmas with hmas hmas
      · by_contra! hh
        rw [← not_le] at hmas
        apply hmas
        apply le_of_lt
        exact (List.lt_iff_lex_lt _ _).mp (List.lt.head _ _ hh)
      · simp only [List.cons.injEq] at hmas
        rw [ge_iff_le, le_iff_lt_or_eq]
        exact Or.inr hmas.1

end List


/-! In this section, we consider the type of `r`-decreasing chains (`List.Chain' (flip r)`)
  equipped with lexicographic order `List.Lex r`. -/

variable {α : Type*} (r : α → α → Prop)

/-- The type of `r`-decreasing chains -/
abbrev List.chains := { l : List α // l.Chain' (flip r) }

/-- The lexicographic order on the `r`-decreasing chains -/
abbrev List.lex_chains (l m : List.chains r) : Prop := List.Lex r l.val m.val

variable {r}

/-- If an `r`-decreasing chain `l` is empty or its head is accessible by `r`, then
  `l` is accessible by the lexicographic order `List.Lex r`. -/
theorem Acc.list_chain' {l : List.chains r} (acc : ∀ a ∈ l.val.head?, Acc r a) :
    Acc (List.lex_chains r) l := by
  obtain ⟨_ | ⟨a, l⟩, hl⟩ := l
  · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
  specialize acc a _
  · rw [List.head?_cons, Option.mem_some_iff]
  /- For an r-decreasing chain of the form a :: l, apply induction on a -/
  induction acc generalizing l with
  | intro a _ ih =>
    /- Bundle l with a proof that it is r-decreasing to form l' -/
    have hl' := (List.chain'_cons'.1 hl).2
    let l' : List.chains r := ⟨l, hl'⟩
    have : Acc (List.lex_chains r) l' := by
      cases' l with b l
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      /- l' is accessible by induction hypothesis -/
      · apply ih b (List.chain'_cons.1 hl).1
    /- make l' a free variable and induct on l' -/
    revert hl
    rw [(by rfl : l = l'.1)]
    clear_value l'
    induction this with
    | intro l _ ihl =>
      intro hl
      apply Acc.intro
      rintro ⟨_ | ⟨b, m⟩, hm⟩ (_ | hr | hr)
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      · apply ihl ⟨m, (List.chain'_cons'.1 hm).2⟩ hr
      · apply ih b hr

/-- If `r` is well-founded, the lexicographic order on `r`-decreasing chains is also. -/
theorem WellFounded.list_chain' (hwf : WellFounded r) :
    WellFounded (List.lex_chains r) :=
  ⟨fun _ ↦ Acc.list_chain' (fun _ _ => hwf.apply _)⟩

instance [hwf : IsWellFounded α r] :
    IsWellFounded (List.chains r) (List.lex_chains r) :=
  ⟨hwf.wf.list_chain'⟩
