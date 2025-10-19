/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Lex
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

/-!
# Relation chain

This file provides basic results about `List.IsChain` from betteries.
A list `[a₁, a₂, ..., aₙ]` satifies `IsChain` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `IsChain r [a₁, a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

assert_not_imported Mathlib.Algebra.Order.Group.Nat

universe u v

open Nat

namespace List

variable {α : Type u} {β : Type v} {R r : α → α → Prop} {l l₁ l₂ : List α} {a b : α}

mk_iff_of_inductive_prop List.IsChain List.isChain_iff

theorem isChain_nil : IsChain R [] := .nil
theorem isChain_singleton (a : α) : IsChain R [a] := .singleton _

@[deprecated (since := "2025-09-24")] alias chain'_nil := isChain_nil
@[deprecated (since := "2025-09-24")] alias chain'_singleton := isChain_singleton
@[deprecated (since := "2025-09-24")] alias chain'_cons_cons := isChain_cons_cons
@[deprecated (since := "2025-08-12")] alias chain'_cons := isChain_cons_cons

@[deprecated (since := "2025-09-24"), nolint defLemma] alias Chain'.cons_cons := IsChain.cons_cons
@[deprecated (since := "2025-09-24"), nolint defLemma] alias Chain'.cons := IsChain.cons_cons

theorem isChain_cons_iff (R : α → α → Prop) (a : α) (l : List α) :
    IsChain R (a :: l) ↔ l = [] ∨
      ∃ (b : α) (l' : List α), R a b ∧ IsChain R (b :: l') ∧ l = b :: l' :=
  (isChain_iff _ _).trans <| by
    simp only [cons_ne_nil, List.cons_eq_cons, exists_and_right,
      exists_eq', true_and, exists_and_left, false_or]
    grind

@[deprecated (since := "2025-09-24")] alias chain_iff := isChain_cons_iff

theorem IsChain.imp_of_mem_tail_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l.tail → R a b → S a b) (p : IsChain R l) : IsChain S l := by
  induction p with grind

theorem IsChain.imp_of_mem_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l → R a b → S a b) (p : IsChain R l) : IsChain S l :=
  p.imp_of_mem_tail_imp (H · · · <| mem_of_mem_tail ·)

theorem IsChain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp fun a b => (H a b).1, IsChain.imp fun a b => (H a b).2⟩

@[deprecated (since := "2025-09-24")] alias Chain.iff := IsChain.iff
@[deprecated (since := "2025-09-24")] alias Chain'.imp := IsChain.imp
@[deprecated (since := "2025-09-24")] alias Chain'.iff := IsChain.iff

theorem IsChain.iff_of_mem_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l → (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_imp (Iff.mp <| H · · · ·), IsChain.imp_of_mem_imp (Iff.mpr <| H · · · ·)⟩

theorem IsChain.iff_of_mem_tail_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l.tail → (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_tail_imp (Iff.mp <| H · · · ·),
  IsChain.imp_of_mem_tail_imp (Iff.mpr <| H · · · ·)⟩

theorem IsChain.iff_mem {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  IsChain.iff_of_mem_imp <| by grind

theorem IsChain.iff_mem_mem_tail {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l.tail ∧ R x y) l :=
  IsChain.iff_of_mem_tail_imp <| by grind

@[deprecated (since := "2025-09-24")] alias Chain'.iff_mem := IsChain.iff_mem
@[deprecated (since := "2025-09-24")] alias Chain.iff_mem := IsChain.iff_mem_mem_tail

theorem isChain_pair {x y} : IsChain R [x, y] ↔ R x y := by
  simp only [IsChain.singleton, isChain_cons_cons, and_true]

@[deprecated (since := "2025-09-24")] alias chain_singleton := isChain_pair
@[deprecated (since := "2025-09-24")] alias chain'_pair := isChain_pair

theorem isChain_isInfix : ∀ l : List α, IsChain (fun x y => [x, y] <:+: l) l
  | [] => .nil
  | [_] => .singleton _
  | a :: b :: l => .cons_cons ⟨[], l, by simp⟩
    ((isChain_isInfix (b :: l)).imp fun _ _ h => h.trans ⟨[a], [], by simp⟩)

@[deprecated (since := "2025-09-24")] alias chain'_isInfix := isChain_isInfix

theorem isChain_split {c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂) := by
  induction l₁ using twoStepInduction generalizing l₂ with grind

@[deprecated (since := "2025-09-24")]
alias chain'_split := isChain_split

theorem isChain_cons_split {c : α} {l₁ l₂ : List α} :
    IsChain R (a :: (l₁ ++ c :: l₂)) ↔ IsChain R (a :: (l₁ ++ [c])) ∧ IsChain R (c :: l₂) := by
  simp_rw [← cons_append, isChain_split (l₂ := l₂)]

@[deprecated (since := "2025-09-19")]
alias chain_split := isChain_cons_split

@[simp]
theorem isChain_append_cons_cons {b c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ b :: c :: l₂) ↔ IsChain R (l₁ ++ [b]) ∧ R b c ∧ IsChain R (c :: l₂) := by
  rw [isChain_split, isChain_cons_cons]

@[deprecated (since := "2025-09-24")]
alias chain'_append_cons_cons := isChain_append_cons_cons

@[simp]
theorem isChain_cons_append_cons_cons {a b c : α} {l₁ l₂ : List α} :
    IsChain R (a :: (l₁ ++ b :: c :: l₂)) ↔
    IsChain R (a :: (l₁ ++ [b])) ∧ R b c ∧ IsChain R (c :: l₂) := by
  rw [isChain_cons_split, isChain_cons_cons]

@[deprecated (since := "2025-09-19")]
alias chain_append_cons_cons := isChain_cons_append_cons_cons

theorem isChain_iff_forall_rel_of_append_cons_cons {l : List α} :
    IsChain R l ↔ ∀ ⦃a b l₁ l₂⦄, l = l₁ ++ a :: b :: l₂ → R a b := by
  refine ⟨fun h _ _ _ _ eq => (isChain_append_cons_cons.mp (eq ▸ h)).2.1, ?_⟩
  induction l using twoStepInduction with
  | nil | singleton => grind
  | cons_cons head head' tail _ ih =>
    refine fun h ↦ isChain_cons_cons.mpr ⟨h (nil_append _).symm, ih _ fun ⦃a b l₁ l₂⦄ eq => ?_⟩
    apply h
    rw [eq, cons_append]

@[deprecated (since := "2025-09-24")]
alias chain'_iff_forall_rel_of_append_cons_cons := isChain_append_cons_cons

theorem isChain_iff_forall₂ {l : List α} :
    IsChain R l ↔ Forall₂ R l.dropLast l.tail := by
  induction l using twoStepInduction <;> simp_all

theorem isChain_cons_iff_forall₂ : IsChain R (a :: l) ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l := by
  cases l <;> simp [isChain_iff_forall₂]

@[deprecated (since := "2025-09-24")] alias chain_iff_forall₂ := isChain_cons_iff_forall₂

theorem isChain_cons_append_singleton_iff_forall₂ :
    IsChain R (a :: l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b]) := by
  simp_rw [isChain_iff_forall₂, dropLast_concat, cons_append, tail_cons]

@[deprecated (since := "2025-09-24")]
alias chain_append_singleton_iff_forall₂ := isChain_cons_append_singleton_iff_forall₂

theorem isChain_map (f : β → α) {l : List β} :
    IsChain R (map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l := by
  induction l using twoStepInduction <;> grind

@[deprecated (since := "2025-09-24")] alias chain'_map := isChain_map

theorem isChain_of_isChain_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    {l : List α} (p : IsChain S (map f l)) : IsChain R l :=
  ((isChain_map f).1 p).imp H

@[deprecated (since := "2025-09-24")] alias chain'_of_chain'_map := isChain_of_isChain_map

theorem isChain_map_of_isChain {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (p : IsChain R l) : IsChain S (map f l) :=
  (isChain_map f).2 <| p.imp H

@[deprecated (since := "2025-09-24")] alias chain'_map_of_chain' := isChain_map_of_isChain

theorem isChain_cons_map (f : β → α) {l : List β} {b : β} :
    IsChain R (f b :: map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l) :=
  isChain_map f (l := b :: l)

theorem isChain_cons_of_isChain_cons_map {S : β → β → Prop} (f : α → β)
    (H : ∀ a b : α, S (f a) (f b) → R a b)
    {l : List α} (p : IsChain S (f a :: map f l)) : IsChain R (a :: l) :=
  ((isChain_cons_map f).1 p).imp H

theorem isChain_cons_map_of_isChain_cons {S : β → β → Prop} (f : α → β)
    (H : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (p : IsChain R (a :: l)) : IsChain S (f a :: map f l) :=
  (isChain_cons_map f).2 <| p.imp H

@[deprecated (since := "2025-09-19")]
alias chain_map := isChain_cons_map

@[deprecated (since := "2025-09-19")]
alias chain_of_chain_map := isChain_cons_of_isChain_cons_map

@[deprecated (since := "2025-09-19")]
alias chain_map_of_chain := isChain_cons_map_of_isChain_cons

theorem isChain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl : ∀ a ∈ l, p a) : IsChain S (pmap f l hl) ↔
    IsChain (fun a b => ∃ ha, ∃ hb, S (f a ha) (f b hb)) l := by
  induction l using twoStepInduction <;> grind

theorem isChain_pmap_of_isChain {S : β → β → Prop} {p : α → Prop} {f : ∀ a, p a → β}
    (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb)) {l : List α} (hl₁ : IsChain R l)
    (hl₂ : ∀ a ∈ l, p a) : IsChain S (pmap f l hl₂) := (isChain_pmap f _).2 <|
  hl₁.imp_of_mem_imp (by grind)

theorem isChain_of_isChain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : IsChain S (pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : IsChain R l :=
  ((isChain_pmap f _).1 hl₂).imp (by grind)

theorem isChain_cons_pmap {p : β → Prop} (f : ∀ b, p b → α) {l : List β} (hl : ∀ b ∈ l, p b)
    {a} (ha) : IsChain R (f a ha :: pmap f l hl) ↔
    IsChain (fun a b => ∃ ha, ∃ hb, R (f a ha) (f b hb)) (a :: l) :=
  isChain_pmap (l := a :: _) f (by grind)

theorem isChain_cons_pmap_of_isChain_cons {S : β → β → Prop} {p : α → Prop} {f : ∀ a, p a → β}
    (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb)) {l : List α} {a} (ha)
    (hl₁ : IsChain R (a :: l)) (hl₂ : ∀ a ∈ l, p a) : IsChain S (f a ha :: pmap f l hl₂) :=
    (isChain_cons_pmap f _ _).2 <| hl₁.imp_of_mem_imp (by grind)

theorem isChain_cons_of_isChain_cons_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β)
    {l : List α} (hl₁ : ∀ a ∈ l, p a) {a} (ha) (hl₂ : IsChain S (f a ha :: pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : IsChain R (a :: l) :=
  ((isChain_cons_pmap f _ _).1 hl₂).imp (by grind)

@[deprecated (since := "2025-09-19")]
alias chain_pmap_of_chain := isChain_cons_pmap_of_isChain_cons

@[deprecated (since := "2025-09-19")]
alias chain_of_chain_pmap := isChain_cons_of_isChain_cons_pmap

@[deprecated (since := "2025-09-19")]
alias Chain.pairwise := IsChain.pairwise

@[deprecated (since := "2025-09-24")]
alias Pairwise.chain' := Pairwise.isChain

@[deprecated (since := "2025-09-19")]
alias chain_iff_pairwise := isChain_iff_pairwise

@[deprecated (since := "2025-09-24")]
alias chain'_iff_pairwise := isChain_iff_pairwise

protected theorem IsChain.sublist [Trans R R R] (hl : l₂.IsChain R) (h : l₁ <+ l₂) :
    l₁.IsChain R := by
  rw [isChain_iff_pairwise] at hl ⊢
  exact hl.sublist h

@[deprecated "Use `IsChain.sublist` combined with `Sublist.cons_cons`" (since := "2025-09-19")]
alias Chain.sublist := IsChain.sublist

@[deprecated (since := "2025-09-24")]
alias Chain'.sublist := IsChain.sublist

protected theorem IsChain.rel_cons [Trans R R R] (hl : (a :: l).IsChain R) (hb : b ∈ l) :
    R a b := by
  rw [isChain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb

@[deprecated (since := "2025-09-19")]
alias Chain.rel := IsChain.rel_cons

theorem IsChain.of_cons {x} : ∀ {l : List α}, IsChain R (x :: l) → IsChain R l
  | [] => fun _ => IsChain.nil
  | _ :: _ => fun | .cons_cons _ h => h

theorem IsChain.tail {l : List α} (h : IsChain R l) : IsChain R l.tail := by
  cases l
  · exact IsChain.nil
  · exact h.of_cons

@[deprecated (since := "2025-09-24")] alias Chain'.tail := IsChain.tail

theorem IsChain.rel_head {x y l} (h : IsChain R (x :: y :: l)) : R x y :=
  List.rel_of_isChain_cons_cons h

@[deprecated (since := "2025-09-24")] alias Chain'.rel_head := IsChain.rel_head

theorem IsChain.rel_head? {x l} (h : IsChain R (x :: l)) ⦃y⦄ (hy : y ∈ head? l) : R x y := by
  rw [← cons_head?_tail hy] at h
  exact h.rel_head

@[deprecated (since := "2025-09-24")] alias Chain'.rel_head? := IsChain.rel_head?

theorem IsChain.cons {x} : ∀ {l : List α}, IsChain R l → (∀ y ∈ l.head?, R x y) →
    IsChain R (x :: l)
  | [], _, _ => .singleton x
  | _ :: _, hl, H => hl.cons_cons <| H _ rfl

@[deprecated (since := "2025-10-16")] alias IsChain.cons' := IsChain.cons
@[deprecated (since := "2025-09-24")] alias Chain'.cons' := IsChain.cons

lemma IsChain.cons_of_ne_nil {x : α} {l : List α} (l_ne_nil : l ≠ [])
    (hl : IsChain R l) (h : R x (l.head l_ne_nil)) : IsChain R (x :: l) := by
  refine hl.cons fun y hy ↦ ?_
  convert h
  simpa [l.head?_eq_head l_ne_nil] using hy.symm

@[deprecated (since := "2025-09-24")] alias Chain'.cons_of_ne_nil := IsChain.cons_of_ne_nil

theorem isChain_cons {x l} : IsChain R (x :: l) ↔ (∀ y ∈ head? l, R x y) ∧ IsChain R l :=
  ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩

@[deprecated (since := "2025-10-16")] alias isChain_cons' := isChain_cons
@[deprecated (since := "2025-09-24")] alias chain'_cons' := isChain_cons

theorem isChain_append :
    ∀ {l₁ l₂ : List α},
      IsChain R (l₁ ++ l₂) ↔ IsChain R l₁ ∧ IsChain R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y
  | [], l => by simp
  | [a], l => by simp [isChain_cons, and_comm]
  | a :: b :: l₁, l₂ => by
    rw [cons_append, cons_append, isChain_cons_cons, isChain_cons_cons,
      ← cons_append, isChain_append, and_assoc]
    simp

@[deprecated (since := "2025-09-24")] alias chain'_append := isChain_append

theorem IsChain.append (h₁ : IsChain R l₁) (h₂ : IsChain R l₂)
    (h : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) : IsChain R (l₁ ++ l₂) :=
  isChain_append.2 ⟨h₁, h₂, h⟩

theorem IsChain.left_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₁ :=
  (isChain_append.1 h).1

theorem IsChain.right_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₂ :=
  (isChain_append.1 h).2.1

@[deprecated (since := "2025-09-24")] alias Chain'.append := isChain_append

@[deprecated (since := "2025-09-24")] alias Chain'.left_of_append := IsChain.left_of_append

@[deprecated (since := "2025-09-24")] alias Chain'.right_of_append := IsChain.right_of_append

theorem IsChain.infix (h : IsChain R l) (h' : l₁ <:+: l) : IsChain R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append

@[deprecated (since := "2025-09-24")] alias Chain'.infix := IsChain.infix

theorem IsChain.suffix (h : IsChain R l) (h' : l₁ <:+ l) : IsChain R l₁ :=
  h.infix h'.isInfix

@[deprecated (since := "2025-09-24")] alias Chain'.suffix := IsChain.suffix

theorem IsChain.prefix (h : IsChain R l) (h' : l₁ <+: l) : IsChain R l₁ :=
  h.infix h'.isInfix

@[deprecated (since := "2025-09-24")] alias Chain'.prefix := IsChain.prefix

theorem IsChain.drop (h : IsChain R l) (n : ℕ) : IsChain R (drop n l) :=
  h.suffix (drop_suffix _ _)

@[deprecated (since := "2025-09-24")] alias Chain'.drop := IsChain.drop

theorem IsChain.dropLast (h : IsChain R l) : IsChain R l.dropLast :=
  h.prefix l.dropLast_prefix

@[deprecated (since := "2025-09-24")] alias Chain'.init := IsChain.dropLast

theorem IsChain.take (h : IsChain R l) (n : ℕ) : IsChain R (take n l) :=
  h.prefix (take_prefix _ _)

@[deprecated (since := "2025-09-24")] alias Chain'.take := IsChain.take

theorem IsChain.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : IsChain R (x :: l)) :
    IsChain R (y :: l) :=
  IsChain.cons_of_imp_of_cons @h hl

@[deprecated (since := "2025-09-24")] alias Chain'.getElem := IsChain.getElem

theorem isChain_iff_get {R} : ∀ {l : List α}, IsChain R l ↔
    ∀ (i : ℕ) (h : i + 1 < l.length), R (get l ⟨i, by cutsat⟩) (get l ⟨i + 1, h⟩) := by
  simp [isChain_iff_getElem]

@[deprecated (since := "2025-09-24")] alias chain'_iff_forall_getElem := isChain_iff_getElem
@[deprecated (since := "2025-09-24")] alias chain'_iff_get := isChain_iff_get

theorem isChain_cons_iff_get {R} {a : α} {l : List α} : IsChain R (a :: l) ↔
    (∀ h : 0 < length l, R a (get l ⟨0, h⟩)) ∧
      ∀ (i : ℕ) (h : i < l.length - 1),
        R (get l ⟨i, by cutsat⟩) (get l ⟨i+1, by cutsat⟩) := by
  cases l <;> grind [isChain_iff_get]

theorem exists_not_getElem_of_not_isChain (h : ¬List.IsChain R l) :
    ∃ n : ℕ, ∃ h : n + 1 < l.length, ¬R l[n] l[n + 1] := by simp_all [isChain_iff_getElem]

@[deprecated (since := "2025-09-19")] alias chain'_of_not := exists_not_getElem_of_not_isChain

@[deprecated (since := "2025-09-19")] alias chain_iff_get := isChain_cons_iff_get

theorem isChain_reverse {l : List α} : IsChain R (reverse l) ↔ IsChain (flip R) l := by
  induction l using twoStepInduction with
  | nil => grind
  | singleton a => grind
  | cons_cons a b l IH IH2 =>
    rw [isChain_cons_cons, reverse_cons, reverse_cons, append_assoc, cons_append, nil_append,
      isChain_split, ← reverse_cons, IH2, and_comm, isChain_pair, flip]

@[deprecated (since := "2025-09-24")] alias chain'_reverse := isChain_reverse

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `IsChain R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
theorem IsChain.append_overlap {l₁ l₂ l₃ : List α} (h₁ : IsChain R (l₁ ++ l₂))
    (h₂ : IsChain R (l₂ ++ l₃)) (hn : l₂ ≠ []) : IsChain R (l₁ ++ l₂ ++ l₃) :=
  h₁.append h₂.right_of_append <| by
    simpa only [getLast?_append_of_ne_nil _ hn] using (isChain_append.1 h₂).2.2

@[deprecated (since := "2025-09-24")] alias Chain'.append_overlap := IsChain.append_overlap

lemma isChain_flatten : ∀ {L : List (List α)}, [] ∉ L →
    (IsChain R L.flatten ↔ (∀ l ∈ L, IsChain R l) ∧
    L.IsChain (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), R x y))
| [], _ => by simp
| [l], _ => by simp [flatten]
| (l₁ :: l₂ :: L), hL => by
    rw [mem_cons, not_or, ← Ne] at hL
    rw [flatten, isChain_append, isChain_flatten hL.2, forall_mem_cons, isChain_cons_cons]
    rw [mem_cons, not_or, ← Ne] at hL
    simp only [forall_mem_cons, and_assoc, flatten, head?_append_of_ne_nil _ hL.2.1.symm]
    exact Iff.rfl.and (Iff.rfl.and <| Iff.rfl.and and_comm)

@[deprecated (since := "2025-09-24")] alias chain'_flatten := isChain_flatten

theorem isChain_attachWith {l : List α} {p : α → Prop} (h : ∀ x ∈ l, p x)
    {r : {a // p a} → {a // p a} → Prop} :
    (l.attachWith p h).IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction l with
  | nil => grind
  | cons a l IH =>
    rw [attachWith_cons, isChain_cons, isChain_cons, IH, and_congr_left]
    simp_rw [head?_attachWith]
    intros
    constructor <;>
    intro hc b (hb : _ = _)
    · simp_rw [hb, Option.pbind_some] at hc
      have hb' := h b (mem_cons_of_mem a (mem_of_mem_head? hb))
      exact ⟨h a mem_cons_self, hb', hc ⟨b, hb'⟩ rfl⟩
    · cases l <;> aesop

@[deprecated (since := "2025-09-24")] alias chain'_attachWith := isChain_attachWith

theorem isChain_attach {l : List α} {r : {a // a ∈ l} → {a // a ∈ l} → Prop} :
    l.attach.IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ :=
  isChain_attachWith fun _ ↦ id

@[deprecated (since := "2025-09-24")] alias chain'_attach := isChain_attach

/-- If `a` and `b` are related by the reflexive transitive closure of `r`, then there is an
`r`-chain starting from `a` and ending on `b`.
-/
theorem exists_isChain_cons_of_relationReflTransGen (h : Relation.ReflTransGen r a b) :
    ∃ l, IsChain r (a :: l) ∧ getLast (a :: l) (cons_ne_nil _ _) = b := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[], .singleton _, rfl⟩
  · intro c d e _ ih
    obtain ⟨l, hl₁, hl₂⟩ := ih
    refine ⟨d :: l, .cons_cons e hl₁, ?_⟩
    rwa [getLast_cons_cons]

@[deprecated (since := "2025-09-22")]
alias exists_chain_of_relationReflTransGen := exists_isChain_cons_of_relationReflTransGen

/-- If `a` and `b` are related by the reflexive transitive closure of `r`, then there is an
`r`-chain starting from `a` and ending on `b`.
-/
theorem exists_isChain_ne_nil_of_relationReflTransGen (h : Relation.ReflTransGen r a b) :
    ∃ l, ∃ (hl : l ≠ []), IsChain r l ∧ l.head hl = a ∧ getLast l hl = b := by
  rcases exists_isChain_cons_of_relationReflTransGen h with ⟨l, _⟩; use (a :: l); grind

/-- Given a chain `l`, such that a predicate `p` holds for its head if it is nonempty,
and if `r x y → p x → p y`, then the predicate is true everywhere in the chain.
That is, we can propagate the predicate down the chain.
-/
theorem IsChain.induction (p : α → Prop) (l : List α) (h : IsChain r l)
    (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (initial : (lne : l ≠ []) → p (l.head lne)) :
    ∀ i ∈ l, p i := by
  induction l using twoStepInduction with
  | nil => grind [not_mem_nil]
  | singleton => grind
  | cons_cons a b l IH IH2 =>
    grind

@[deprecated (since := "2025-09-24")] alias Chain'.induction := IsChain.induction

/-- Given a chain from `a` to `b`, and a predicate true at `a`, if `r x y → p x → p y` then
the predicate is true everywhere in the chain.
That is, we can propagate the predicate down the chain.
-/
theorem IsChain.cons_induction (p : α → Prop) (l : List α) (h : IsChain r (a :: l))
    (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (initial : p a) : ∀ i ∈ l, p i := fun _ hi =>
  h.induction _ _ carries (fun _ => initial) _ (mem_cons_of_mem _ hi)

@[deprecated (since := "2025-09-24")] alias Chain.induction := IsChain.cons_induction

theorem IsChain.concat_induction (p : α → Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (hb : head (l ++ [b]) (concat_ne_nil _ _) = a) (carries : ∀ ⦃x y : α⦄, r x y → p x → p y)
    (initial : p a) : ∀ i ∈ l ++ [b], p i :=
  h.induction _ _ carries (fun _ => hb ▸ initial)

@[elab_as_elim]
theorem IsChain.concat_induction_head (p : α → Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (hb : head (l ++ [b]) (concat_ne_nil _ _) = a) (carries : ∀ ⦃x y : α⦄, r x y → p x → p y)
    (initial : p a) : p b :=
  (IsChain.concat_induction p l h hb carries initial) _ mem_concat_self

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem IsChain.backwards_induction (p : α → Prop) (l : List α) (h : IsChain r l)
    (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : (lne : l ≠ []) → p (getLast l lne)) :
    ∀ i ∈ l, p i := by
  have H : IsChain (flip (flip r)) l := h
  replace H := (isChain_reverse.mpr H).induction _ _ (fun _ _ h ↦ carries h)
  grind

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem IsChain.backwards_concat_induction (p : α → Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : p b) : ∀ i ∈ l, p i := fun _ hi =>
  h.backwards_induction _ _ carries (fun _ => getLast_concat ▸ final) _ (mem_append_left _ hi)

theorem IsChain.backwards_cons_induction (p : α → Prop) (l : List α) (h : IsChain r (a :: l))
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : ∀ i ∈ a :: l, p i :=
  h.backwards_induction _ _ carries (fun _ => hb ▸ final)

@[deprecated (since := "2025-09-24")]
alias Chain.backwards_induction := IsChain.backwards_cons_induction

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
@[elab_as_elim]
theorem IsChain.backwards_cons_induction_head (p : α → Prop) (l : List α) (h : IsChain r (a :: l))
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : p a :=
  (IsChain.backwards_cons_induction p l h hb carries final) _ mem_cons_self

@[deprecated (since := "2025-09-24")]
alias Chain.backwards_induction_head := IsChain.backwards_cons_induction_head

/--
If there is an non-empty `r`-chain, its head and last element are related by the
reflexive transitive closure of `r`.
-/
theorem relationReflTransGen_of_exists_isChain (l : List α) (hl₁ : IsChain r l) (hne : l ≠ []) :
    Relation.ReflTransGen r (head l hne) (getLast l hne) :=
  IsChain.induction (Relation.ReflTransGen r (head l hne) ·) l hl₁
  (fun _ _ h₁ h₂ => Trans.trans h₂ h₁) (fun _ => Relation.ReflTransGen.refl) _ (getLast_mem _)

/--
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` are related by the
reflexive transitive closure of `r`.
-/
theorem relationReflTransGen_of_exists_isChain_cons (l : List α) (hl₁ : IsChain r (a :: l))
    (hl₂ : getLast (a :: l) (cons_ne_nil _ _) = b) : Relation.ReflTransGen r a b :=
  IsChain.backwards_cons_induction_head _ l hl₁ hl₂ (fun _ _ => Relation.ReflTransGen.head)
  Relation.ReflTransGen.refl

@[deprecated (since := "2025-09-24")]
alias relationReflTransGen_of_exists_chain_cons := relationReflTransGen_of_exists_isChain_cons

theorem IsChain.cons_of_le [LinearOrder α] {a : α} {as m : List α}
    (ha : List.IsChain (· > ·) (a :: as)) (hm : List.IsChain (· > ·) m) (hmas : m ≤ as) :
    List.IsChain (· > ·) (a :: m) := by
  cases m with
  | nil => grind
  | cons b bs =>
    apply hm.cons_cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, reduceCtorEq, or_false] at hmas
      exact (List.not_lt_nil _ hmas).elim
    | cons a' as =>
      rw [List.isChain_cons_cons] at ha
      refine lt_of_le_of_lt ?_ ha.1
      rw [le_iff_lt_or_eq] at hmas
      rcases hmas with hmas | hmas
      · by_contra! hh
        rw [← not_le] at hmas
        apply hmas
        apply le_of_lt
        exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel hh)
      · simp_all only [List.cons.injEq, le_refl]

@[deprecated (since := "2025-09-24")] alias Chain'.cons_of_le := IsChain.cons_of_le

lemma IsChain.isChain_cons {α : Type*} {R : α → α → Prop} {l : List α} {v : α}
    (hl : l.IsChain R) (hv : (lne : l ≠ []) → R v (l.head lne)) : (v :: l).IsChain R := by
  cases l <;> grind

@[deprecated (since := "2025-09-24")] alias Chain'.chain := IsChain.isChain_cons

lemma IsChain.iterate_eq_of_apply_eq {α : Type*} {f : α → α} {l : List α}
    (hl : l.IsChain (fun x y ↦ f x = y)) (i : ℕ) (hi : i < l.length) :
    f^[i] l[0] = l[i] := by
  induction i with
  | zero => rfl
  | succ i h =>
    rw [Function.iterate_succ', Function.comp_apply, h (by cutsat)]
    rw [List.isChain_iff_get] at hl
    apply hl

@[deprecated (since := "2025-09-24")]
alias Chain'.iterate_eq_of_apply_eq := IsChain.iterate_eq_of_apply_eq

theorem isChain_replicate_of_rel (n : ℕ) {a : α} (h : r a a) : IsChain r (replicate n a) := by
  induction n using Nat.twoStepInduction <;> grind

@[deprecated "Use `isChain_replicate_of_rel` with `n + 1` instead" (since := "2025-09-19")]
alias chain_replicate_of_rel := isChain_replicate_of_rel

theorem isChain_eq_iff_eq_replicate {l : List α} :
    IsChain (· = ·) l ↔ ∀ a ∈ l.head?, l = replicate l.length a := by
  induction l using twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b l IH IH2 =>
    simp +contextual [isChain_cons_cons, eq_comm, IH2, replicate_succ]

@[deprecated (since := "2025-09-19")]
alias chain'_eq_iff_eq_replicate := isChain_eq_iff_eq_replicate

theorem isChain_cons_eq_iff_eq_replicate {a : α} {l : List α} :
    IsChain (· = ·) (a :: l) ↔ l = replicate l.length a := by
  simp [isChain_eq_iff_eq_replicate, replicate_succ]

@[deprecated (since := "2025-09-19")]
alias chain_eq_iff_eq_replicate := isChain_cons_eq_iff_eq_replicate

end List


/-! In this section, we consider the type of `r`-decreasing chains (`List.IsChain (flip r)`)
  equipped with lexicographic order `List.Lex r`. -/

variable {α : Type*} (r : α → α → Prop)

/-- The type of `r`-decreasing chains -/
abbrev List.chains := { l : List α // l.IsChain (flip r) }

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
    have hl' := (List.isChain_cons.1 hl).2
    let l' : List.chains r := ⟨l, hl'⟩
    have : Acc (List.lex_chains r) l' := by
      rcases l with - | ⟨b, l⟩
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      /- l' is accessible by induction hypothesis -/
      · apply ih b (List.isChain_cons_cons.1 hl).1
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
      · apply ih b hr
      · apply ihl ⟨m, (List.isChain_cons.1 hm).2⟩ hr

/-- If `r` is well-founded, the lexicographic order on `r`-decreasing chains is also. -/
theorem WellFounded.list_chain' (hwf : WellFounded r) :
    WellFounded (List.lex_chains r) :=
  ⟨fun _ ↦ Acc.list_chain' (fun _ _ => hwf.apply _)⟩

instance [hwf : IsWellFounded α r] :
    IsWellFounded (List.chains r) (List.lex_chains r) :=
  ⟨hwf.wf.list_chain'⟩
