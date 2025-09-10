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
  induction' l₁ with x l₁ IH generalizing a <;>
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
  induction' l with lh lt l_ih generalizing a
  · simp
  · simp [H _ _ _ _ (rel_of_chain_cons hl₁), l_ih (chain_of_chain_cons hl₁)]

theorem chain_of_chain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl₁ : ∀ a ∈ l, p a) {a : α} (ha : p a) (hl₂ : Chain S (f a ha) (List.pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : Chain R a l := by
  induction' l with lh lt l_ih generalizing a
  · simp
  · simp [H _ _ _ _ (rel_of_chain_cons hl₂), l_ih _ _ (chain_of_chain_cons hl₂)]

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

theorem Chain'.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b) {l : List α} (p : Chain' R l) :
    Chain' S l := by cases l <;> [trivial; exact Chain.imp H p]

theorem Chain'.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    Chain' R l ↔ Chain' S l :=
  ⟨Chain'.imp fun a b => (H a b).1, Chain'.imp fun a b => (H a b).2⟩

theorem Chain'.iff_mem : ∀ {l : List α}, Chain' R l ↔ Chain' (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
  | [] => Iff.rfl
  | _ :: _ =>
    ⟨fun h => (Chain.iff_mem.1 h).imp fun _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, mem_cons.2 (Or.inr h₂), h₃⟩,
      Chain'.imp fun _ _ h => h.2.2⟩

@[simp]
theorem chain'_nil : Chain' R [] :=
  trivial

@[simp]
theorem chain'_singleton (a : α) : Chain' R [a] :=
  Chain.nil

@[simp]
theorem chain'_cons_cons {x y l} : Chain' R (x :: y :: l) ↔ R x y ∧ Chain' R (y :: l) :=
  chain_cons

@[deprecated (since := "2025-08-12")] alias chain'_cons := chain'_cons_cons

theorem chain'_isInfix : ∀ l : List α, Chain' (fun x y => [x, y] <:+: l) l
  | [] => chain'_nil
  | [_] => chain'_singleton _
  | a :: b :: l =>
    chain'_cons_cons.2
      ⟨⟨[], l, by simp⟩, (chain'_isInfix (b :: l)).imp fun _ _ h => h.trans ⟨[a], [], by simp⟩⟩

theorem chain'_split {a : α} :
    ∀ {l₁ l₂ : List α}, Chain' R (l₁ ++ a :: l₂) ↔ Chain' R (l₁ ++ [a]) ∧ Chain' R (a :: l₂)
  | [], _ => (and_iff_right (chain'_singleton a)).symm
  | _ :: _, _ => chain_split

@[simp]
theorem chain'_append_cons_cons {b c : α} {l₁ l₂ : List α} :
    Chain' R (l₁ ++ b :: c :: l₂) ↔ Chain' R (l₁ ++ [b]) ∧ R b c ∧ Chain' R (c :: l₂) := by
  rw [chain'_split, chain'_cons_cons]

theorem chain'_iff_forall_rel_of_append_cons_cons {l : List α} :
    Chain' R l ↔ ∀ ⦃a b l₁ l₂⦄, l = l₁ ++ a :: b :: l₂ → R a b := by
  refine ⟨fun h _ _ _ _ eq => (chain'_append_cons_cons.mp (eq ▸ h)).2.1, ?_⟩
  induction l with
  | nil => exact fun _ ↦ chain'_nil
  | cons head tail ih =>
    match tail with
    | nil => exact fun _ ↦ chain'_singleton head
    | cons head' tail =>
      refine fun h ↦ chain'_cons_cons.mpr ⟨h (nil_append _).symm, ih fun ⦃a b l₁ l₂⦄ eq => ?_⟩
      apply h
      rw [eq, cons_append]

theorem chain'_map (f : β → α) {l : List β} :
    Chain' R (map f l) ↔ Chain' (fun a b : β => R (f a) (f b)) l := by
  cases l <;> [rfl; exact chain_map _]

theorem chain'_of_chain'_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    {l : List α} (p : Chain' S (map f l)) : Chain' R l :=
  ((chain'_map f).1 p).imp H

theorem chain'_map_of_chain' {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (p : Chain' R l) : Chain' S (map f l) :=
  (chain'_map f).2 <| p.imp H

theorem Pairwise.chain' : ∀ {l : List α}, Pairwise R l → Chain' R l
  | [], _ => trivial
  | _ :: _, h => Pairwise.chain h

theorem chain'_iff_pairwise [IsTrans α R] : ∀ {l : List α}, Chain' R l ↔ Pairwise R l
  | [] => (iff_true_intro Pairwise.nil).symm
  | _ :: _ => chain_iff_pairwise

protected theorem Chain'.sublist [IsTrans α R] (hl : l₂.Chain' R) (h : l₁ <+ l₂) : l₁.Chain' R := by
  rw [chain'_iff_pairwise] at hl ⊢
  exact hl.sublist h

theorem Chain'.cons_cons {x y l} (h₁ : R x y) (h₂ : Chain' R (y :: l)) : Chain' R (x :: y :: l) :=
  chain'_cons_cons.2 ⟨h₁, h₂⟩

@[deprecated (since := "2025-08-12")] alias Chain'.cons := Chain'.cons_cons

theorem Chain'.tail : ∀ {l}, Chain' R l → Chain' R l.tail
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => (chain'_cons_cons.mp h).right

theorem Chain'.rel_head {x y l} (h : Chain' R (x :: y :: l)) : R x y :=
  rel_of_chain_cons h

theorem Chain'.rel_head? {x l} (h : Chain' R (x :: l)) ⦃y⦄ (hy : y ∈ head? l) : R x y := by
  rw [← cons_head?_tail hy] at h
  exact h.rel_head

theorem Chain'.cons' {x} : ∀ {l : List α}, Chain' R l → (∀ y ∈ l.head?, R x y) → Chain' R (x :: l)
  | [], _, _ => chain'_singleton x
  | _ :: _, hl, H => hl.cons_cons <| H _ rfl

lemma Chain'.cons_of_ne_nil {x : α} {l : List α} (l_ne_nil : l ≠ [])
    (hl : Chain' R l) (h : R x (l.head l_ne_nil)) : Chain' R (x :: l) := by
  refine hl.cons' fun y hy ↦ ?_
  convert h
  simpa [l.head?_eq_head l_ne_nil] using hy.symm

theorem chain'_cons' {x l} : Chain' R (x :: l) ↔ (∀ y ∈ head? l, R x y) ∧ Chain' R l :=
  ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons' h₁⟩

theorem chain'_append :
    ∀ {l₁ l₂ : List α},
      Chain' R (l₁ ++ l₂) ↔ Chain' R l₁ ∧ Chain' R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y
  | [], l => by simp
  | [a], l => by simp [chain'_cons', and_comm]
  | a :: b :: l₁, l₂ => by
    rw [cons_append, cons_append, chain'_cons_cons, chain'_cons_cons, ← cons_append, chain'_append,
      and_assoc]
    simp

theorem Chain'.append (h₁ : Chain' R l₁) (h₂ : Chain' R l₂)
    (h : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) : Chain' R (l₁ ++ l₂) :=
  chain'_append.2 ⟨h₁, h₂, h⟩

theorem Chain'.left_of_append (h : Chain' R (l₁ ++ l₂)) : Chain' R l₁ :=
  (chain'_append.1 h).1

theorem Chain'.right_of_append (h : Chain' R (l₁ ++ l₂)) : Chain' R l₂ :=
  (chain'_append.1 h).2.1

theorem Chain'.infix (h : Chain' R l) (h' : l₁ <:+: l) : Chain' R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append

theorem Chain'.suffix (h : Chain' R l) (h' : l₁ <:+ l) : Chain' R l₁ :=
  h.infix h'.isInfix

theorem Chain'.prefix (h : Chain' R l) (h' : l₁ <+: l) : Chain' R l₁ :=
  h.infix h'.isInfix

theorem Chain'.drop (h : Chain' R l) (n : ℕ) : Chain' R (drop n l) :=
  h.suffix (drop_suffix _ _)

theorem Chain'.init (h : Chain' R l) : Chain' R l.dropLast :=
  h.prefix l.dropLast_prefix

theorem Chain'.take (h : Chain' R l) (n : ℕ) : Chain' R (take n l) :=
  h.prefix (take_prefix _ _)

theorem chain'_pair {x y} : Chain' R [x, y] ↔ R x y := by
  simp only [chain'_singleton, chain'_cons_cons, and_true]

theorem Chain'.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : Chain' R (x :: l)) :
    Chain' R (y :: l) :=
  hl.tail.cons' fun _ hz => h <| hl.rel_head? hz

theorem chain'_reverse : ∀ {l}, Chain' R (reverse l) ↔ Chain' (flip R) l
  | [] => Iff.rfl
  | [a] => by simp only [chain'_singleton, reverse_singleton]
  | a :: b :: l => by
    rw [chain'_cons_cons, reverse_cons, reverse_cons, append_assoc, cons_append, nil_append,
      chain'_split, ← reverse_cons, @chain'_reverse (b :: l), and_comm, chain'_pair, flip]

theorem chain'_iff_get {R} : ∀ {l : List α}, Chain' R l ↔
    ∀ (i : ℕ) (h : i < length l - 1),
      R (get l ⟨i, by omega⟩) (get l ⟨i + 1, by omega⟩)
  | [] => iff_of_true (by simp) (fun _ h => by simp at h)
  | [a] => iff_of_true (by simp) (fun _ h => by simp at h)
  | a :: b :: t => by
    rw [← and_forall_add_one, chain'_cons_cons, chain'_iff_get]
    simp

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `Chain' R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
theorem Chain'.append_overlap {l₁ l₂ l₃ : List α} (h₁ : Chain' R (l₁ ++ l₂))
    (h₂ : Chain' R (l₂ ++ l₃)) (hn : l₂ ≠ []) : Chain' R (l₁ ++ l₂ ++ l₃) :=
  h₁.append h₂.right_of_append <| by
    simpa only [getLast?_append_of_ne_nil _ hn] using (chain'_append.1 h₂).2.2

lemma chain'_flatten : ∀ {L : List (List α)}, [] ∉ L →
    (Chain' R L.flatten ↔ (∀ l ∈ L, Chain' R l) ∧
    L.Chain' (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), R x y))
| [], _ => by simp
| [l], _ => by simp [flatten]
| (l₁ :: l₂ :: L), hL => by
    rw [mem_cons, not_or, ← Ne] at hL
    rw [flatten, chain'_append, chain'_flatten hL.2, forall_mem_cons, chain'_cons_cons]
    rw [mem_cons, not_or, ← Ne] at hL
    simp only [forall_mem_cons, and_assoc, flatten, head?_append_of_ne_nil _ hL.2.1.symm]
    exact Iff.rfl.and (Iff.rfl.and <| Iff.rfl.and and_comm)

theorem chain'_attachWith {l : List α} {p : α → Prop} (h : ∀ x ∈ l, p x)
    {r : {a // p a} → {a // p a} → Prop} :
    (l.attachWith p h).Chain' r ↔ l.Chain' fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [attachWith_cons, chain'_cons', chain'_cons', IH, and_congr_left]
    simp_rw [head?_attachWith]
    intros
    constructor <;>
    intro hc b (hb : _ = _)
    · simp_rw [hb, Option.pbind_some] at hc
      have hb' := h b (mem_cons_of_mem a (mem_of_mem_head? hb))
      exact ⟨h a mem_cons_self, hb', hc ⟨b, hb'⟩ rfl⟩
    · cases l <;> aesop

theorem chain'_attach {l : List α} {r : {a // a ∈ l} → {a // a ∈ l} → Prop} :
    l.attach.Chain' r ↔ l.Chain' fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ :=
  chain'_attachWith fun _ ↦ id

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

/-- A version of `List.Chain.induction` for `List.Chain'`
-/
theorem Chain'.induction (p : α → Prop) (l : List α) (h : Chain' r l)
    (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (initial : (lne : l ≠ []) → p (l.head lne)) :
    ∀ i ∈ l, p i := by
  unfold Chain' at h
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
  have : Chain' (flip (flip r)) (a :: l) := by simpa [Chain']
  replace this := chain'_reverse.mpr this
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

theorem Chain'.cons_of_le [LinearOrder α] {a : α} {as m : List α}
    (ha : List.Chain' (· > ·) (a :: as)) (hm : List.Chain' (· > ·) m) (hmas : m ≤ as) :
    List.Chain' (· > ·) (a :: m) := by
  cases m with
  | nil => simp only [List.chain'_singleton]
  | cons b bs =>
    apply hm.cons_cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, reduceCtorEq, or_false] at hmas
      exact (List.not_lt_nil _ hmas).elim
    | cons a' as =>
      rw [List.chain'_cons_cons] at ha
      refine lt_of_le_of_lt ?_ ha.1
      rw [le_iff_lt_or_eq] at hmas
      rcases hmas with hmas | hmas
      · by_contra! hh
        rw [← not_le] at hmas
        apply hmas
        apply le_of_lt
        exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel hh)
      · simp_all only [List.cons.injEq, le_refl]

lemma Chain'.chain {α : Type*} {R : α → α → Prop} {l : List α} {v : α}
    (hl : l.Chain' R) (hv : (lne : l ≠ []) → R v (l.head lne)) : l.Chain R v := by
  rw [List.chain_iff_get]
  constructor
  · intro h
    rw [List.get_mk_zero]
    apply hv
  · exact List.chain'_iff_get.mp hl

lemma Chain'.iterate_eq_of_apply_eq {α : Type*} {f : α → α} {l : List α}
    (hl : l.Chain' (fun x y ↦ f x = y)) (i : ℕ) (hi : i < l.length) :
    f^[i] l[0] = l[i] := by
  induction' i with i h
  · rfl
  · rw [Function.iterate_succ', Function.comp_apply, h (by omega)]
    rw [List.chain'_iff_get] at hl
    apply hl
    omega

theorem chain'_replicate_of_rel (n : ℕ) {a : α} (h : r a a) : Chain' r (replicate n a) :=
  match n with
  | 0 => chain'_nil
  | n + 1 => chain_replicate_of_rel n h

theorem chain'_eq_iff_eq_replicate {l : List α} :
    Chain' (· = ·) l ↔ ∀ a ∈ l.head?, l = replicate l.length a :=
  match l with
  | [] => by simp
  | a :: l => by simp [Chain', chain_eq_iff_eq_replicate, replicate_succ]

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
      rcases l with - | ⟨b, l⟩
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      /- l' is accessible by induction hypothesis -/
      · apply ih b (List.chain'_cons_cons.1 hl).1
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
      · apply ihl ⟨m, (List.chain'_cons'.1 hm).2⟩ hr

/-- If `r` is well-founded, the lexicographic order on `r`-decreasing chains is also. -/
theorem WellFounded.list_chain' (hwf : WellFounded r) :
    WellFounded (List.lex_chains r) :=
  ⟨fun _ ↦ Acc.list_chain' (fun _ _ => hwf.apply _)⟩

instance [hwf : IsWellFounded α r] :
    IsWellFounded (List.chains r) (List.lex_chains r) :=
  ⟨hwf.wf.list_chain'⟩
