/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Lex
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

/-!
# Relation chain

This file provides basic results about `List.Chain` (definition in `Data.List.Defs`).
A list `[a₂, ..., aₙ]` is a `Chain` starting at `a₁` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `Chain r a₁ [a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

assert_not_imported Mathlib.Algebra.Order.Group.Nat

universe u v

open Nat

namespace List

variable {α : Type u} {β : Type v} {R r : α → α → Prop} {l l₁ l₂ : List α} {a b : α}

mk_iff_of_inductive_prop List.Chain List.chain_iff

theorem Chain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {a : α} {l : List α} :
    Chain R a l ↔ Chain S a l :=
  ⟨Chain.imp fun a b => (H a b).1, Chain.imp fun a b => (H a b).2⟩

theorem Chain.iff_mem {a : α} {l : List α} :
    Chain R a l ↔ Chain (fun x y => x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
  ⟨fun p => by
    induction p with
    | nil => exact nil
    | @cons _ _ _ r _ IH =>
      constructor
      · exact ⟨mem_cons_self, mem_cons_self, r⟩
      · exact IH.imp fun a b ⟨am, bm, h⟩ => ⟨mem_cons_of_mem _ am, mem_cons_of_mem _ bm, h⟩,
    Chain.imp fun _ _ h => h.2.2⟩

theorem chain_singleton {a b : α} : Chain R a [b] ↔ R a b := by
  simp only [chain_cons, Chain.nil, and_true]

theorem chain_split {a b : α} {l₁ l₂ : List α} :
    Chain R a (l₁ ++ b :: l₂) ↔ Chain R a (l₁ ++ [b]) ∧ Chain R b l₂ := by
  induction l₁ generalizing a <;>
    simp only [*, nil_append, cons_append, Chain.nil, chain_cons, and_true, and_assoc]

@[simp]
theorem chain_append_cons_cons {a b c : α} {l₁ l₂ : List α} :
    Chain R a (l₁ ++ b :: c :: l₂) ↔ Chain R a (l₁ ++ [b]) ∧ R b c ∧ Chain R c l₂ := by
  rw [chain_split, chain_cons]

theorem chain_iff_forall₂ :
    ∀ {a : α} {l : List α}, Chain R a l ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l
  | a, [] => by simp
  | a, b :: l => by
    by_cases h : l = [] <;>
    simp [@chain_iff_forall₂ b l, dropLast, *]

theorem chain_append_singleton_iff_forall₂ :
    Chain R a (l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b]) := by simp [chain_iff_forall₂]

theorem chain_map (f : β → α) {b : β} {l : List β} :
    Chain R (f b) (map f l) ↔ Chain (fun a b : β => R (f a) (f b)) b l := by
  induction l generalizing b <;> simp only [map, Chain.nil, chain_cons, *]

theorem chain_of_chain_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    {a : α} {l : List α} (p : Chain S (f a) (map f l)) : Chain R a l :=
  ((chain_map f).1 p).imp H

theorem chain_map_of_chain {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    {a : α} {l : List α} (p : Chain R a l) : Chain S (f a) (map f l) :=
  (chain_map f).2 <| p.imp H

theorem chain_pmap_of_chain {S : β → β → Prop} {p : α → Prop} {f : ∀ a, p a → β}
    (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb)) {a : α} {l : List α} (hl₁ : Chain R a l)
    (ha : p a) (hl₂ : ∀ a ∈ l, p a) : Chain S (f a ha) (List.pmap f l hl₂) := by
  induction l generalizing a with
  | nil => simp
  | cons lh lt l_ih => simp [H _ _ _ _ (rel_of_chain_cons hl₁), l_ih (chain_of_chain_cons hl₁)]

theorem chain_of_chain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl₁ : ∀ a ∈ l, p a) {a : α} (ha : p a) (hl₂ : Chain S (f a ha) (List.pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : Chain R a l := by
  induction l generalizing a with
  | nil => simp
  | cons lh lt l_ih => simp [H _ _ _ _ (rel_of_chain_cons hl₂), l_ih _ _ (chain_of_chain_cons hl₂)]

protected theorem Chain.pairwise [IsTrans α R] :
    ∀ {a : α} {l : List α}, Chain R a l → Pairwise R (a :: l)
  | _, [], Chain.nil => pairwise_singleton _ _
  | a, _, @Chain.cons _ _ _ b l h hb =>
    hb.pairwise.cons
      (by
        simp only [mem_cons, forall_eq_or_imp, h, true_and]
        exact fun c hc => _root_.trans h (rel_of_pairwise_cons hb.pairwise hc))

theorem chain_iff_pairwise [IsTrans α R] {a : α} {l : List α} : Chain R a l ↔ Pairwise R (a :: l) :=
  ⟨Chain.pairwise, Pairwise.chain⟩

protected theorem Chain.sublist [IsTrans α R] (hl : l₂.Chain R a) (h : l₁ <+ l₂) :
    l₁.Chain R a := by
  rw [chain_iff_pairwise] at hl ⊢
  exact hl.sublist (h.cons_cons a)

protected theorem Chain.rel [IsTrans α R] (hl : l.Chain R a) (hb : b ∈ l) : R a b := by
  rw [chain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb

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
      rcases i with - | i
      · apply h0
      · exact h i (by simp only [length_cons] at w; omega)
    rintro ⟨h0, h⟩; constructor
    · apply h0
      simp
    constructor
    · apply h 0
    intro i w
    exact h (i+1) (by simp only [length_cons]; omega)

theorem chain_replicate_of_rel (n : ℕ) {a : α} (h : r a a) : Chain r a (replicate n a) :=
  match n with
  | 0 => Chain.nil
  | n + 1 => Chain.cons h (chain_replicate_of_rel n h)

theorem chain_eq_iff_eq_replicate {a : α} {l : List α} :
    Chain (· = ·) a l ↔ l = replicate l.length a :=
  match l with
  | [] => by simp
  | b :: l => by
    rw [chain_cons]
    simp +contextual [eq_comm, replicate_succ, chain_eq_iff_eq_replicate]

theorem IsChain.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b) {l : List α} (p : IsChain R l) :
    IsChain S l := by cases l <;> [trivial; exact Chain.imp H p]

theorem IsChain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp fun a b => (H a b).1, IsChain.imp fun a b => (H a b).2⟩

theorem IsChain.iff_mem : ∀ {l : List α}, IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
  | [] => Iff.rfl
  | _ :: _ =>
    ⟨fun h => (Chain.iff_mem.1 h).imp fun _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, mem_cons.2 (Or.inr h₂), h₃⟩,
      IsChain.imp fun _ _ h => h.2.2⟩

@[simp]
theorem isChain_nil : IsChain R [] :=
  trivial

@[simp]
theorem isChain_singleton (a : α) : IsChain R [a] :=
  Chain.nil

@[simp]
theorem isChain_cons_cons {x y l} : IsChain R (x :: y :: l) ↔ R x y ∧ IsChain R (y :: l) :=
  chain_cons

@[deprecated (since := "2025-08-12")] alias isChain_cons := isChain_cons_cons

theorem isChain_isInfix : ∀ l : List α, IsChain (fun x y => [x, y] <:+: l) l
  | [] => isChain_nil
  | [_] => isChain_singleton _
  | a :: b :: l =>
    isChain_cons_cons.2
      ⟨⟨[], l, by simp⟩, (isChain_isInfix (b :: l)).imp fun _ _ h => h.trans ⟨[a], [], by simp⟩⟩

theorem isChain_split {a : α} :
    ∀ {l₁ l₂ : List α}, IsChain R (l₁ ++ a :: l₂) ↔ IsChain R (l₁ ++ [a]) ∧ IsChain R (a :: l₂)
  | [], _ => (and_iff_right (isChain_singleton a)).symm
  | _ :: _, _ => chain_split

@[simp]
theorem isChain_append_cons_cons {b c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ b :: c :: l₂) ↔ IsChain R (l₁ ++ [b]) ∧ R b c ∧ IsChain R (c :: l₂) := by
  rw [isChain_split, isChain_cons_cons]

theorem isChain_iff_forall_rel_of_append_cons_cons {l : List α} :
    IsChain R l ↔ ∀ ⦃a b l₁ l₂⦄, l = l₁ ++ a :: b :: l₂ → R a b := by
  refine ⟨fun h _ _ _ _ eq => (isChain_append_cons_cons.mp (eq ▸ h)).2.1, ?_⟩
  induction l with
  | nil => exact fun _ ↦ isChain_nil
  | cons head tail ih =>
    match tail with
    | nil => exact fun _ ↦ isChain_singleton head
    | cons head' tail =>
      refine fun h ↦ isChain_cons_cons.mpr ⟨h (nil_append _).symm, ih fun ⦃a b l₁ l₂⦄ eq => ?_⟩
      apply h
      rw [eq, cons_append]

theorem isChain_map (f : β → α) {l : List β} :
    IsChain R (map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l := by
  cases l <;> [rfl; exact chain_map _]

theorem isChain_of_isChain_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    {l : List α} (p : IsChain S (map f l)) : IsChain R l :=
  ((isChain_map f).1 p).imp H

theorem isChain_map_of_chain' {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (p : IsChain R l) : IsChain S (map f l) :=
  (isChain_map f).2 <| p.imp H

theorem Pairwise.chain' : ∀ {l : List α}, Pairwise R l → IsChain R l
  | [], _ => trivial
  | _ :: _, h => Pairwise.chain h

theorem isChain_iff_pairwise [IsTrans α R] : ∀ {l : List α}, IsChain R l ↔ Pairwise R l
  | [] => (iff_true_intro Pairwise.nil).symm
  | _ :: _ => chain_iff_pairwise

protected theorem IsChain.sublist [IsTrans α R] (hl : l₂.IsChain R) (h : l₁ <+ l₂) : l₁.IsChain R := by
  rw [isChain_iff_pairwise] at hl ⊢
  exact hl.sublist h

theorem IsChain.cons_cons {x y l} (h₁ : R x y) (h₂ : IsChain R (y :: l)) : IsChain R (x :: y :: l) :=
  isChain_cons_cons.2 ⟨h₁, h₂⟩

@[deprecated (since := "2025-08-12")] alias IsChain.cons := IsChain.cons_cons

theorem IsChain.tail : ∀ {l}, IsChain R l → IsChain R l.tail
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => (isChain_cons_cons.mp h).right

theorem IsChain.rel_head {x y l} (h : IsChain R (x :: y :: l)) : R x y :=
  rel_of_chain_cons h

theorem IsChain.rel_head? {x l} (h : IsChain R (x :: l)) ⦃y⦄ (hy : y ∈ head? l) : R x y := by
  rw [← cons_head?_tail hy] at h
  exact h.rel_head

theorem IsChain.cons' {x} : ∀ {l : List α}, IsChain R l → (∀ y ∈ l.head?, R x y) → IsChain R (x :: l)
  | [], _, _ => isChain_singleton x
  | _ :: _, hl, H => hl.cons_cons <| H _ rfl

lemma IsChain.cons_of_ne_nil {x : α} {l : List α} (l_ne_nil : l ≠ [])
    (hl : IsChain R l) (h : R x (l.head l_ne_nil)) : IsChain R (x :: l) := by
  refine hl.cons' fun y hy ↦ ?_
  convert h
  simpa [l.head?_eq_head l_ne_nil] using hy.symm

theorem isChain_cons' {x l} : IsChain R (x :: l) ↔ (∀ y ∈ head? l, R x y) ∧ IsChain R l :=
  ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons' h₁⟩

theorem isChain_append :
    ∀ {l₁ l₂ : List α},
      IsChain R (l₁ ++ l₂) ↔ IsChain R l₁ ∧ IsChain R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y
  | [], l => by simp
  | [a], l => by simp [isChain_cons', and_comm]
  | a :: b :: l₁, l₂ => by
    rw [cons_append, cons_append, isChain_cons_cons, isChain_cons_cons, ← cons_append, isChain_append,
      and_assoc]
    simp

theorem IsChain.append (h₁ : IsChain R l₁) (h₂ : IsChain R l₂)
    (h : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) : IsChain R (l₁ ++ l₂) :=
  isChain_append.2 ⟨h₁, h₂, h⟩

theorem IsChain.left_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₁ :=
  (isChain_append.1 h).1

theorem IsChain.right_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₂ :=
  (isChain_append.1 h).2.1

theorem IsChain.infix (h : IsChain R l) (h' : l₁ <:+: l) : IsChain R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append

theorem IsChain.suffix (h : IsChain R l) (h' : l₁ <:+ l) : IsChain R l₁ :=
  h.infix h'.isInfix

theorem IsChain.prefix (h : IsChain R l) (h' : l₁ <+: l) : IsChain R l₁ :=
  h.infix h'.isInfix

theorem IsChain.drop (h : IsChain R l) (n : ℕ) : IsChain R (drop n l) :=
  h.suffix (drop_suffix _ _)

theorem IsChain.init (h : IsChain R l) : IsChain R l.dropLast :=
  h.prefix l.dropLast_prefix

theorem IsChain.take (h : IsChain R l) (n : ℕ) : IsChain R (take n l) :=
  h.prefix (take_prefix _ _)

theorem isChain_pair {x y} : IsChain R [x, y] ↔ R x y := by
  simp only [isChain_singleton, isChain_cons_cons, and_true]

theorem IsChain.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : IsChain R (x :: l)) :
    IsChain R (y :: l) :=
  hl.tail.cons' fun _ hz => h <| hl.rel_head? hz

protected theorem IsChain.getElem (h : List.IsChain R l) (n : ℕ) (h' : n + 1 < l.length) :
    R l[n] l[n + 1] :=
  isChain_pair.mp <| h.infix ⟨l.take n, l.drop (n + 2), by simp⟩

theorem isChain_of_not (h : ¬List.IsChain R l) :
    ∃ n : ℕ, ∃ h : n + 1 < l.length, ¬R l[n] l[n + 1] := by
  contrapose! h
  induction l with
  | nil => simp
  | cons head tail ih =>
      refine List.isChain_cons'.mpr ⟨fun y yh ↦ ?_, ?_⟩
      · by_cases h' : tail.length = 0
        · simp [List.eq_nil_iff_length_eq_zero.mpr h'] at yh
        · simp only [head?_eq_getElem?, Option.mem_def] at yh
          obtain ⟨_, rfl⟩ := getElem?_eq_some_iff.mp yh
          have := h 0 (by rw [length_cons]; omega)
          rwa [getElem_cons_zero] at this
      · refine ih (fun n h' ↦ ?_)
        have := h (n + 1) (by rw [length_cons]; omega)
        simpa using this

theorem isChain_iff_forall_getElem :
    IsChain R l ↔ ∀ (n : ℕ) (h : n + 1 < l.length), R l[n] l[n + 1] := by
  refine ⟨IsChain.getElem, fun h ↦ ?_⟩
  contrapose! h
  exact isChain_of_not h

theorem isChain_reverse : ∀ {l}, IsChain R (reverse l) ↔ IsChain (flip R) l
  | [] => Iff.rfl
  | [a] => by simp only [isChain_singleton, reverse_singleton]
  | a :: b :: l => by
    rw [isChain_cons_cons, reverse_cons, reverse_cons, append_assoc, cons_append, nil_append,
      isChain_split, ← reverse_cons, @isChain_reverse (b :: l), and_comm, isChain_pair, flip]

theorem isChain_iff_get {R} : ∀ {l : List α}, IsChain R l ↔
    ∀ (i : ℕ) (h : i < length l - 1),
      R (get l ⟨i, by omega⟩) (get l ⟨i + 1, by omega⟩)
  | [] => iff_of_true (by simp) (fun _ h => by simp at h)
  | [a] => iff_of_true (by simp) (fun _ h => by simp at h)
  | a :: b :: t => by
    rw [← and_forall_add_one, isChain_cons_cons, isChain_iff_get]
    simp

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `IsChain R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
theorem IsChain.append_overlap {l₁ l₂ l₃ : List α} (h₁ : IsChain R (l₁ ++ l₂))
    (h₂ : IsChain R (l₂ ++ l₃)) (hn : l₂ ≠ []) : IsChain R (l₁ ++ l₂ ++ l₃) :=
  h₁.append h₂.right_of_append <| by
    simpa only [getLast?_append_of_ne_nil _ hn] using (isChain_append.1 h₂).2.2

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

theorem isChain_attachWith {l : List α} {p : α → Prop} (h : ∀ x ∈ l, p x)
    {r : {a // p a} → {a // p a} → Prop} :
    (l.attachWith p h).IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [attachWith_cons, isChain_cons', isChain_cons', IH, and_congr_left]
    simp_rw [head?_attachWith]
    intros
    constructor <;>
    intro hc b (hb : _ = _)
    · simp_rw [hb, Option.pbind_some] at hc
      have hb' := h b (mem_cons_of_mem a (mem_of_mem_head? hb))
      exact ⟨h a mem_cons_self, hb', hc ⟨b, hb'⟩ rfl⟩
    · cases l <;> aesop

theorem isChain_attach {l : List α} {r : {a // a ∈ l} → {a // a ∈ l} → Prop} :
    l.attach.IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ :=
  isChain_attachWith fun _ ↦ id

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

/-- Given a chain from `a` to `b`, and a predicate true at `a`, if `r x y → p x → p y` then
the predicate is true everywhere in the chain.
That is, we can propagate the predicate down the chain.
-/
theorem Chain.induction (p : α → Prop) (l : List α) (h : Chain r a l)
    (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (initial : p a) : ∀ i ∈ l, p i := by
  induction h with
  | nil => simp
  | @cons a b t hab _ h_ind =>
    simp only [mem_cons, forall_eq_or_imp]
    exact ⟨carries hab initial, h_ind (carries hab initial)⟩

/-- A version of `List.Chain.induction` for `List.IsChain`
-/
theorem IsChain.induction (p : α → Prop) (l : List α) (h : IsChain r l)
    (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (initial : (lne : l ≠ []) → p (l.head lne)) :
    ∀ i ∈ l, p i := by
  unfold IsChain at h
  split at h
  · simp
  · simp_all only [ne_eq, not_false_eq_true, head_cons, true_implies, mem_cons, forall_eq_or_imp,
      true_and, reduceCtorEq]
    exact h.induction p _ carries initial

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem Chain.backwards_induction (p : α → Prop) (l : List α) (h : Chain r a l)
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : ∀ i ∈ a :: l, p i := by
  have : IsChain (flip (flip r)) (a :: l) := by simpa [IsChain]
  replace this := isChain_reverse.mpr this
  simp_rw +singlePass [← List.mem_reverse]
  apply this.induction _ _ (fun _ _ h ↦ carries h)
  simpa only [ne_eq, reverse_eq_nil_iff, not_false_eq_true, head_reverse, forall_true_left, hb,
    reduceCtorEq]

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
@[elab_as_elim]
theorem Chain.backwards_induction_head (p : α → Prop) (l : List α) (h : Chain r a l)
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : p a :=
  (Chain.backwards_induction p l h hb carries final) _ mem_cons_self

/--
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` are related by the
reflexive transitive closure of `r`. The converse of `exists_chain_of_relationReflTransGen`.
-/
theorem relationReflTransGen_of_exists_chain (l : List α) (hl₁ : Chain r a l)
    (hl₂ : getLast (a :: l) (cons_ne_nil _ _) = b) : Relation.ReflTransGen r a b :=
  Chain.backwards_induction_head _ l hl₁ hl₂ (fun _ _ => Relation.ReflTransGen.head)
    Relation.ReflTransGen.refl

theorem IsChain.cons_of_le [LinearOrder α] {a : α} {as m : List α}
    (ha : List.IsChain (· > ·) (a :: as)) (hm : List.IsChain (· > ·) m) (hmas : m ≤ as) :
    List.IsChain (· > ·) (a :: m) := by
  cases m with
  | nil => simp only [List.isChain_singleton]
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

lemma IsChain.chain {α : Type*} {R : α → α → Prop} {l : List α} {v : α}
    (hl : l.IsChain R) (hv : (lne : l ≠ []) → R v (l.head lne)) : l.Chain R v := by
  rw [List.chain_iff_get]
  constructor
  · intro h
    rw [List.get_mk_zero]
    apply hv
  · exact List.isChain_iff_get.mp hl

lemma IsChain.iterate_eq_of_apply_eq {α : Type*} {f : α → α} {l : List α}
    (hl : l.IsChain (fun x y ↦ f x = y)) (i : ℕ) (hi : i < l.length) :
    f^[i] l[0] = l[i] := by
  induction i with
  | zero => rfl
  | succ i h =>
    rw [Function.iterate_succ', Function.comp_apply, h (by omega)]
    rw [List.isChain_iff_get] at hl
    apply hl
    omega

theorem isChain_replicate_of_rel (n : ℕ) {a : α} (h : r a a) : IsChain r (replicate n a) :=
  match n with
  | 0 => isChain_nil
  | n + 1 => chain_replicate_of_rel n h

theorem isChain_eq_iff_eq_replicate {l : List α} :
    IsChain (· = ·) l ↔ ∀ a ∈ l.head?, l = replicate l.length a :=
  match l with
  | [] => by simp
  | a :: l => by simp [IsChain, chain_eq_iff_eq_replicate, replicate_succ]

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
    have hl' := (List.isChain_cons'.1 hl).2
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
      · apply ihl ⟨m, (List.isChain_cons'.1 hm).2⟩ hr

/-- If `r` is well-founded, the lexicographic order on `r`-decreasing chains is also. -/
theorem WellFounded.list_chain' (hwf : WellFounded r) :
    WellFounded (List.lex_chains r) :=
  ⟨fun _ ↦ Acc.list_chain' (fun _ _ => hwf.apply _)⟩

instance [hwf : IsWellFounded α r] :
    IsWellFounded (List.chains r) (List.lex_chains r) :=
  ⟨hwf.wf.list_chain'⟩
