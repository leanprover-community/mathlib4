/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Factorial.Basic

#align_import data.list.perm from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# List Permutations

This file introduces the `List.Perm` relation, which is true if two lists are permutations of one
another.

## Notation

The notation `~` is used for permutation equivalence.
-/


open Nat

universe uu vv

namespace List

variable {α : Type uu} {β : Type vv} {l₁ l₂ : List α}

/-- `Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive Perm : List α → List α → Prop
  | nil : Perm [] []
  | cons (x : α) {l₁ l₂ : List α} : Perm l₁ l₂ → Perm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : Perm (y :: x :: l) (x :: y :: l)
  | trans {l₁ l₂ l₃ : List α} : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃
#align list.perm List.Perm

instance {α : Type*} : Trans (@List.Perm α) (@List.Perm α) List.Perm where
  trans := @List.Perm.trans α

open Perm (swap)

/-- `Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
infixl:50 " ~ " => Perm

@[simp, refl]
protected theorem Perm.refl : ∀ l : List α, l ~ l
  | [] => Perm.nil
  | x :: xs => (Perm.refl xs).cons x
#align list.perm.refl List.Perm.refl

-- Porting note: used rec_on in mathlib3; lean4 eqn compiler still doesn't like it
@[symm]
protected theorem Perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
  p.rec
    .nil
    (fun x _ _ _ r₁ => .cons x r₁)
    (fun x y l => .swap y x l)
    (fun _ _ r₁ r₂ => .trans r₂ r₁)
#align list.perm.symm List.Perm.symm

theorem perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ :=
  ⟨Perm.symm, Perm.symm⟩
#align list.perm_comm List.perm_comm

theorem Perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y :: x :: l₁ ~ x :: y :: l₂ :=
  (swap _ _ _).trans ((p.cons _).cons _)
#align list.perm.swap' List.Perm.swap'

attribute [trans] Perm.trans

theorem Perm.eqv (α) : Equivalence (@Perm α) :=
  ⟨Perm.refl, Perm.symm, Perm.trans⟩
#align list.perm.eqv List.Perm.eqv

--Porting note: new theorem
theorem Perm.of_eq (h : l₁ = l₂) : l₁ ~ l₂ :=
  h ▸ Perm.refl l₁

instance isSetoid (α) : Setoid (List α) :=
  Setoid.mk (@Perm α) (Perm.eqv α)
#align list.is_setoid List.isSetoid

-- Porting note: used rec_on in mathlib3; lean4 eqn compiler still doesn't like it
theorem Perm.mem_iff {a : α} {l₁ l₂ : List α} (p : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
  p.rec
    Iff.rfl
    (fun _ _ _ _ hs => by simp only [mem_cons, hs])
    (fun _ _ _ => by simp only [mem_cons, or_left_comm])
    (fun _ _ => Iff.trans)
#align list.perm.mem_iff List.Perm.mem_iff

theorem Perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ :=
  fun _ => p.mem_iff.mp
#align list.perm.subset List.Perm.subset

theorem Perm.subset_congr_left {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₁ ⊆ l₃ ↔ l₂ ⊆ l₃ :=
  ⟨h.symm.subset.trans, h.subset.trans⟩
#align list.perm.subset_congr_left List.Perm.subset_congr_left

theorem Perm.subset_congr_right {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₃ ⊆ l₁ ↔ l₃ ⊆ l₂ :=
  ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩
#align list.perm.subset_congr_right List.Perm.subset_congr_right

theorem Perm.append_right {l₁ l₂ : List α} (t₁ : List α) (p : l₁ ~ l₂) : l₁ ++ t₁ ~ l₂ ++ t₁ :=
  p.rec
    (Perm.refl ([] ++ t₁))
    (fun x _ _ _ r₁ => r₁.cons x)
    (fun x y _ => swap x y _)
    (fun _ _ r₁ r₂ => r₁.trans r₂)
#align list.perm.append_right List.Perm.append_right

theorem Perm.append_left {t₁ t₂ : List α} : ∀ l : List α, t₁ ~ t₂ → l ++ t₁ ~ l ++ t₂
  | [], p => p
  | x :: xs, p => (p.append_left xs).cons x
#align list.perm.append_left List.Perm.append_left

theorem Perm.append {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ++ t₁ ~ l₂ ++ t₂ :=
  (p₁.append_right t₁).trans (p₂.append_left l₂)
#align list.perm.append List.Perm.append

theorem Perm.append_cons (a : α) {h₁ h₂ t₁ t₂ : List α} (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) :
    h₁ ++ a :: t₁ ~ h₂ ++ a :: t₂ :=
  p₁.append (p₂.cons a)
#align list.perm.append_cons List.Perm.append_cons

@[simp]
theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁ ++ a :: l₂ ~ a :: (l₁ ++ l₂)
  | [], _ => Perm.refl _
  | b :: l₁, l₂ => ((@perm_middle a l₁ l₂).cons _).trans (swap a b _)
#align list.perm_middle List.perm_middle

@[simp]
theorem perm_append_singleton (a : α) (l : List α) : l ++ [a] ~ a :: l :=
  perm_middle.trans <| by rw [append_nil]
#align list.perm_append_singleton List.perm_append_singleton

theorem perm_append_comm : ∀ {l₁ l₂ : List α}, l₁ ++ l₂ ~ l₂ ++ l₁
  | [], l₂ => by simp
  | a :: t, l₂ => (perm_append_comm.cons _).trans perm_middle.symm
#align list.perm_append_comm List.perm_append_comm

theorem concat_perm (l : List α) (a : α) : concat l a ~ a :: l := by simp
#align list.concat_perm List.concat_perm

theorem Perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ :=
  p.rec
    rfl
    (fun _x l₁ l₂ _p r => by simp [r])
    (fun _x _y l => by simp)
    (fun _p₁ _p₂ r₁ r₂ => Eq.trans r₁ r₂)
#align list.perm.length_eq List.Perm.length_eq

theorem Perm.eq_nil {l : List α} (p : l ~ []) : l = [] :=
  eq_nil_of_length_eq_zero p.length_eq
#align list.perm.eq_nil List.Perm.eq_nil

theorem Perm.nil_eq {l : List α} (p : [] ~ l) : [] = l :=
  p.symm.eq_nil.symm
#align list.perm.nil_eq List.Perm.nil_eq

@[simp]
theorem perm_nil {l₁ : List α} : l₁ ~ [] ↔ l₁ = [] :=
  ⟨fun p => p.eq_nil, fun e => e ▸ Perm.refl _⟩
#align list.perm_nil List.perm_nil

@[simp]
theorem nil_perm {l₁ : List α} : [] ~ l₁ ↔ l₁ = [] :=
  perm_comm.trans perm_nil
#align list.nil_perm List.nil_perm

theorem not_perm_nil_cons (x : α) (l : List α) : ¬[] ~ x :: l
  | p => by injection p.symm.eq_nil
#align list.not_perm_nil_cons List.not_perm_nil_cons

@[simp]
theorem reverse_perm : ∀ l : List α, reverse l ~ l
  | [] => Perm.nil
  | a :: l => by
    rw [reverse_cons]
    exact (perm_append_singleton _ _).trans ((reverse_perm l).cons a)
#align list.reverse_perm List.reverse_perm

theorem perm_cons_append_cons {l l₁ l₂ : List α} (a : α) (p : l ~ l₁ ++ l₂) :
    a :: l ~ l₁ ++ a :: l₂ :=
  (p.cons a).trans perm_middle.symm
#align list.perm_cons_append_cons List.perm_cons_append_cons

@[simp]
theorem perm_replicate {n : ℕ} {a : α} {l : List α} :
    l ~ replicate n a ↔ l = replicate n a :=
  ⟨fun p => eq_replicate.2
    ⟨p.length_eq.trans <| length_replicate _ _, fun _b m => eq_of_mem_replicate <| p.subset m⟩,
    fun h => h ▸ Perm.refl _⟩
#align list.perm_replicate List.perm_replicate

@[simp]
theorem replicate_perm {n : ℕ} {a : α} {l : List α} :
    replicate n a ~ l ↔ replicate n a = l :=
  (perm_comm.trans perm_replicate).trans eq_comm
#align list.replicate_perm List.replicate_perm

@[simp]
theorem perm_singleton {a : α} {l : List α} : l ~ [a] ↔ l = [a] :=
  @perm_replicate α 1 a l
#align list.perm_singleton List.perm_singleton

@[simp]
theorem singleton_perm {a : α} {l : List α} : [a] ~ l ↔ [a] = l :=
  @replicate_perm α 1 a l
#align list.singleton_perm List.singleton_perm

alias ⟨Perm.eq_singleton, _⟩ := perm_singleton
alias ⟨Perm.singleton_eq, _⟩ := singleton_perm

theorem singleton_perm_singleton {a b : α} : [a] ~ [b] ↔ a = b := by simp
#align list.singleton_perm_singleton List.singleton_perm_singleton

theorem perm_cons_erase [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : l ~ a :: l.erase a :=
  let ⟨_l₁, _l₂, _, e₁, e₂⟩ := exists_erase_eq h
  e₂.symm ▸ e₁.symm ▸ perm_middle
#align list.perm_cons_erase List.perm_cons_erase

@[elab_as_elim]
theorem perm_induction_on {P : List α → List α → Prop} {l₁ l₂ : List α} (p : l₁ ~ l₂) (h₁ : P [] [])
    (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x :: l₁) (x :: l₂))
    (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y :: x :: l₁) (x :: y :: l₂))
    (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) : P l₁ l₂ :=
  have P_refl : ∀ l, P l l := fun l => List.recOn l h₁ fun x xs ih => h₂ x xs xs (Perm.refl xs) ih
  p.rec h₁ h₂ (fun x y l => h₃ x y l l (Perm.refl l) (P_refl l)) @h₄
#align list.perm_induction_on List.perm_induction_onₓ

-- Porting note: TODO figure out why invalid congr
-- @[congr]
theorem Perm.filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    filterMap f l₁ ~ filterMap f l₂ := by
  induction p with
  | nil => simp
  | cons x _p IH =>
    cases h : f x
      <;> simp [h, filterMap, IH, Perm.cons]
  | swap x y l₂ =>
    cases hx : f x
      <;> cases hy : f y
        <;> simp [hx, hy, filterMap, swap]
  | trans _p₁ _p₂ IH₁ IH₂ =>
    exact IH₁.trans IH₂
#align list.perm.filter_map List.Perm.filterMap

-- Porting note: TODO figure out why invalid congr
-- @[congr]
theorem Perm.map (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ :=
  filterMap_eq_map f ▸ p.filterMap _
#align list.perm.map List.Perm.map

theorem Perm.pmap {p : α → Prop} (f : ∀ a, p a → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) {H₁ H₂} :
    pmap f l₁ H₁ ~ pmap f l₂ H₂ := by
  induction p with
  | nil => simp
  | cons x _p IH => simp [IH, Perm.cons]
  | swap x y => simp [swap]
  | trans _p₁ p₂ IH₁ IH₂ =>
    refine' IH₁.trans IH₂
    exact fun a m => H₂ a (p₂.subset m)
#align list.perm.pmap List.Perm.pmap

theorem Perm.filter (p : α → Bool) {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    filter p l₁ ~ filter p l₂ := by rw [← filterMap_eq_filter]; apply s.filterMap _
#align list.perm.filter List.Perm.filter

theorem filter_append_perm (p : α → Bool) (l : List α) :
    filter p l ++ filter (fun x => ¬p x) l ~ l := by
  induction' l with x l ih
  · rfl
  · by_cases h : p x
    · simp only [h, filter_cons_of_pos, filter_cons_of_neg, not_true, not_false_iff, cons_append,
        decide_False]
      exact ih.cons x
    · simp only [h, filter_cons_of_neg, not_false_iff, filter_cons_of_pos, cons_append,
        not_false_eq_true, decide_True]
      refine' Perm.trans _ (ih.cons x)
      exact perm_append_comm.trans (perm_append_comm.cons _)
#align list.filter_append_perm List.filter_append_perm

theorem exists_perm_sublist {l₁ l₂ l₂' : List α} (s : l₁ <+ l₂) (p : l₂ ~ l₂') :
    ∃ (l₁' : _) (_ : l₁' ~ l₁), l₁' <+ l₂' := by
  induction p generalizing l₁ with
  | nil =>
    exact ⟨[], eq_nil_of_sublist_nil s ▸ Perm.refl _, nil_sublist _⟩
  | cons x _ IH =>
    cases' s with _ _ _ s l₁ _ _ s
    · exact
        let ⟨l₁', p', s'⟩ := IH s
        ⟨l₁', p', s'.cons _⟩
    · exact
        let ⟨l₁', p', s'⟩ := IH s
        ⟨x :: l₁', p'.cons x, s'.cons₂ _⟩
  | swap x y _ =>
    cases' s with _ _ _ s l₁ _ _ s <;> cases' s with _ _ _ s l₁ _ _ s
    · exact ⟨l₁, Perm.refl _, (s.cons _).cons _⟩
    · exact ⟨x :: l₁, Perm.refl _, (s.cons _).cons₂ _⟩
    · exact ⟨y :: l₁, Perm.refl _, (s.cons₂ _).cons _⟩
    · exact ⟨x :: y :: l₁, Perm.swap _ _ _, (s.cons₂ _).cons₂ _⟩
  | trans _ _ IH₁ IH₂ =>
    exact
      let ⟨m₁, pm, sm⟩ := IH₁ s
      let ⟨r₁, pr, sr⟩ := IH₂ sm
      ⟨r₁, pr.trans pm, sr⟩
#align list.exists_perm_sublist List.exists_perm_sublist

theorem Perm.sizeOf_eq_sizeOf [SizeOf α] {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    sizeOf l₁ = sizeOf l₂ := by
  induction h with -- hd l₁ l₂ h₁₂ h_sz₁₂ a b l l₁ l₂ l₃ h₁₂ h₂₃ h_sz₁₂ h_sz₂₃
  | nil => rfl
  | cons _ _ h_sz₁₂ => simp [h_sz₁₂]
  | swap => simp [add_left_comm]
  | trans _ _ h_sz₁₂ h_sz₂₃ => simp [h_sz₁₂, h_sz₂₃]
#align list.perm.sizeof_eq_sizeof List.Perm.sizeOf_eq_sizeOf

section Rel

open Relator

variable {γ : Type*} {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

-- mathport name: «expr ∘r »
local infixr:80 " ∘r " => Relation.Comp

theorem perm_comp_perm : (Perm ∘r Perm : List α → List α → Prop) = Perm := by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => Perm.trans hab hba
  · exact fun h => ⟨a, Perm.refl a, h⟩
#align list.perm_comp_perm List.perm_comp_perm

theorem perm_comp_forall₂ {l u v} (hlu : Perm l u) (huv : Forall₂ r u v) :
    (Forall₂ r ∘r Perm) l v := by
  induction hlu generalizing v
  case nil => cases huv; exact ⟨[], Forall₂.nil, Perm.nil⟩
  case cons a l u _hlu ih =>
    cases' huv with _ b _ v hab huv'
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨b :: l₂, Forall₂.cons hab h₁₂, h₂₃.cons _⟩
  case swap a₁ a₂ h₂₃ =>
    cases' huv with _ b₁ _ l₂ h₁ hr₂₃
    cases' hr₂₃ with _ b₂ _ l₂ h₂ h₁₂
    exact ⟨b₂ :: b₁ :: l₂, Forall₂.cons h₂ (Forall₂.cons h₁ h₁₂), Perm.swap _ _ _⟩
  case
    trans la₁ la₂ la₃ _ _ ih₁ ih₂ =>
    rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩
    exact ⟨lb₁, hab₁, Perm.trans h₁₂ h₂₃⟩
#align list.perm_comp_forall₂ List.perm_comp_forall₂

theorem forall₂_comp_perm_eq_perm_comp_forall₂ : Forall₂ r ∘r Perm = Perm ∘r Forall₂ r := by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : Forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃
#align list.forall₂_comp_perm_eq_perm_comp_forall₂ List.forall₂_comp_perm_eq_perm_comp_forall₂

theorem rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· → ·)) Perm Perm :=
  fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r Perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r Perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨c', hbc, hcb⟩, hbd⟩ := this
  have : b' = b := right_unique_forall₂' hr hcb hbc
  this ▸ hbd
#align list.rel_perm_imp List.rel_perm_imp

theorem rel_perm (hr : BiUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm :=
  fun _a _b hab _c _d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)
#align list.rel_perm List.rel_perm

end Rel

section Subperm


/-- `Subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
  a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
  multiplicities of elements, and is used for the `≤` relation on multisets. -/
def Subperm (l₁ l₂ : List α) : Prop :=
  ∃ (l : _) (_ : l ~ l₁), l <+ l₂
#align list.subperm List.Subperm

/-- `Subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
  a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
  multiplicities of elements, and is used for the `≤` relation on multisets. -/
infixl:50 " <+~ " => Subperm

theorem nil_subperm {l : List α} : [] <+~ l :=
  ⟨[], Perm.nil, by simp⟩
#align list.nil_subperm List.nil_subperm

theorem Perm.subperm_left {l l₁ l₂ : List α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ :=
  suffices ∀ {l₁ l₂ : List α}, l₁ ~ l₂ → l <+~ l₁ → l <+~ l₂ from ⟨this p, this p.symm⟩
  fun p ⟨_u, pu, su⟩ =>
  let ⟨v, pv, sv⟩ := exists_perm_sublist su p
  ⟨v, pv.trans pu, sv⟩
#align list.perm.subperm_left List.Perm.subperm_left

theorem Perm.subperm_right {l₁ l₂ l : List α} (p : l₁ ~ l₂) : l₁ <+~ l ↔ l₂ <+~ l :=
  ⟨fun ⟨u, pu, su⟩ => ⟨u, pu.trans p, su⟩, fun ⟨u, pu, su⟩ => ⟨u, pu.trans p.symm, su⟩⟩
#align list.perm.subperm_right List.Perm.subperm_right

theorem Sublist.subperm {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁ <+~ l₂ :=
  ⟨l₁, Perm.refl _, s⟩
#align list.sublist.subperm List.Sublist.subperm

theorem Perm.subperm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ <+~ l₂ :=
  ⟨l₂, p.symm, Sublist.refl _⟩
#align list.perm.subperm List.Perm.subperm

@[refl]
theorem Subperm.refl (l : List α) : l <+~ l :=
  (Perm.refl _).subperm
#align list.subperm.refl List.Subperm.refl

@[trans]
theorem Subperm.trans {l₁ l₂ l₃ : List α} : l₁ <+~ l₂ → l₂ <+~ l₃ → l₁ <+~ l₃
  | s, ⟨_l₂', p₂, s₂⟩ =>
    let ⟨l₁', p₁, s₁⟩ := p₂.subperm_left.2 s
    ⟨l₁', p₁, s₁.trans s₂⟩
#align list.subperm.trans List.Subperm.trans

theorem Subperm.length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₁ ≤ length l₂
  | ⟨_l, p, s⟩ => p.length_eq ▸ s.length_le
#align list.subperm.length_le List.Subperm.length_le

theorem Subperm.perm_of_length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂
  | ⟨_l, p, s⟩, h => (s.eq_of_length_le <| p.symm.length_eq ▸ h) ▸ p.symm
#align list.subperm.perm_of_length_le List.Subperm.perm_of_length_le

theorem Subperm.antisymm {l₁ l₂ : List α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
  h₁.perm_of_length_le h₂.length_le
#align list.subperm.antisymm List.Subperm.antisymm

theorem Subperm.subset {l₁ l₂ : List α} : l₁ <+~ l₂ → l₁ ⊆ l₂
  | ⟨_l, p, s⟩ => Subset.trans p.symm.subset s.subset
#align list.subperm.subset List.Subperm.subset

theorem Subperm.filter (p : α → Bool) ⦃l l' : List α⦄ (h : l <+~ l') :
    filter p l <+~ filter p l' := by
  obtain ⟨xs, hp, h⟩ := h
  exact ⟨_, hp.filter p, h.filter p⟩
#align list.subperm.filter List.Subperm.filter

end Subperm

theorem Sublist.exists_perm_append : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → ∃ l, l₂ ~ l₁ ++ l
  | _, _, Sublist.slnil => ⟨nil, Perm.refl _⟩
  | _, _, Sublist.cons a s =>
    let ⟨l, p⟩ := Sublist.exists_perm_append s
    ⟨a :: l, (p.cons a).trans perm_middle.symm⟩
  | _, _, Sublist.cons₂ a s =>
    let ⟨l, p⟩ := Sublist.exists_perm_append s
    ⟨l, p.cons a⟩
#align list.sublist.exists_perm_append List.Sublist.exists_perm_append

theorem Perm.countP_eq (p : α → Bool) {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    countP p l₁ = countP p l₂ := by
  rw [countP_eq_length_filter, countP_eq_length_filter]; exact (s.filter _).length_eq
#align list.perm.countp_eq List.Perm.countP_eq

theorem Subperm.countP_le (p : α → Bool) {l₁ l₂ : List α} :
    l₁ <+~ l₂ → countP p l₁ ≤ countP p l₂
  | ⟨_l, p', s⟩ => p'.countP_eq p ▸ s.countP_le p
#align list.subperm.countp_le List.Subperm.countP_le

theorem Perm.countP_congr (s : l₁ ~ l₂) {p p' : α → Bool}
    (hp : ∀ x ∈ l₁, p x ↔ p' x) : l₁.countP p = l₂.countP p' := by
  rw [← s.countP_eq p']
  clear s
  induction' l₁ with y s hs
  · rfl
  · simp only [mem_cons, forall_eq_or_imp] at hp
    simp only [countP_cons, hs hp.2, hp.1]
#align list.perm.countp_congr List.Perm.countP_congr

theorem countP_eq_countP_filter_add (l : List α) (p q : α → Bool) :
    l.countP p = (l.filter q).countP p + (l.filter fun a => ¬q a).countP p := by
  rw [← countP_append]
  exact Perm.countP_eq _ (filter_append_perm _ _).symm
#align list.countp_eq_countp_filter_add List.countP_eq_countP_filter_add

lemma count_eq_count_filter_add [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (l : List α) (a : α) :
    count a l = count a (l.filter P) + count a (l.filter (¬ P ·)) := by
  convert countP_eq_countP_filter_add l _ P
  simp only [decide_eq_true_eq]

theorem Perm.count_eq [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) (a) :
    count a l₁ = count a l₂ :=
  p.countP_eq _
#align list.perm.count_eq List.Perm.count_eq

theorem Subperm.count_le [DecidableEq α] {l₁ l₂ : List α} (s : l₁ <+~ l₂) (a) :
    count a l₁ ≤ count a l₂ :=
  s.countP_le _
#align list.subperm.count_le List.Subperm.count_le

theorem Perm.foldl_eq' {f : β → α → β} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    (∀ x ∈ l₁, ∀ y ∈ l₁, ∀ (z), f (f z x) y = f (f z y) x) → ∀ b, foldl f b l₁ = foldl f b l₂ :=
  perm_induction_on p (fun _H b => rfl)
    (fun x t₁ t₂ _p r H b => r (fun x hx y hy => H _ (.tail _ hx) _ (.tail _ hy)) _)
    (fun x y t₁ t₂ _p r H b => by
      simp only [foldl]
      rw [H x (.tail _ <| .head _) y (.head _)]
      exact r (fun x hx y hy => H _ (.tail _ <| .tail _ hx) _ (.tail _ <| .tail _ hy)) _)
    fun t₁ t₂ t₃ p₁ _p₂ r₁ r₂ H b =>
    Eq.trans (r₁ H b) (r₂ (fun x hx y hy => H _ (p₁.symm.subset hx) _ (p₁.symm.subset hy)) b)
#align list.perm.foldl_eq' List.Perm.foldl_eq'

theorem Perm.foldl_eq {f : β → α → β} {l₁ l₂ : List α} (rcomm : RightCommutative f) (p : l₁ ~ l₂) :
    ∀ b, foldl f b l₁ = foldl f b l₂ :=
  p.foldl_eq' fun x _hx y _hy z => rcomm z x y
#align list.perm.foldl_eq List.Perm.foldl_eq

theorem Perm.foldr_eq {f : α → β → β} {l₁ l₂ : List α} (lcomm : LeftCommutative f) (p : l₁ ~ l₂) :
    ∀ b, foldr f b l₁ = foldr f b l₂ :=
  perm_induction_on p (fun b => rfl) (fun x t₁ t₂ _p r b => by simp; rw [r b])
    (fun x y t₁ t₂ _p r b => by simp; rw [lcomm, r b]) fun t₁ t₂ t₃ _p₁ _p₂ r₁ r₂ a =>
    Eq.trans (r₁ a) (r₂ a)
#align list.perm.foldr_eq List.Perm.foldr_eq

theorem Perm.rec_heq {β : List α → Sort*} {f : ∀ a l, β l → β (a :: l)} {b : β []} {l l' : List α}
    (hl : Perm l l') (f_congr : ∀ {a l l' b b'}, Perm l l' → HEq b b' → HEq (f a l b) (f a l' b'))
    (f_swap : ∀ {a a' l b}, HEq (f a (a' :: l) (f a' l b)) (f a' (a :: l) (f a l b))) :
    HEq (@List.rec α β b f l) (@List.rec α β b f l') := by
  induction hl
  case nil => rfl
  case cons a l l' h ih => exact f_congr h ih
  case swap a a' l => exact f_swap
  case trans l₁ l₂ l₃ _h₁ _h₂ ih₁ ih₂ => exact HEq.trans ih₁ ih₂
#align list.perm.rec_heq List.Perm.rec_heq

section

variable {op : α → α → α} [IA : IsAssociative α op] [IC : IsCommutative α op]

-- mathport name: op
local notation a " * " b => op a b

-- mathport name: foldl
local notation l " <*> " a => foldl op a l

theorem Perm.fold_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : (l₁ <*> a) = l₂ <*> a :=
  h.foldl_eq (right_comm _ IC.comm IA.assoc) _
#align list.perm.fold_op_eq List.Perm.fold_op_eq

end

section CommMonoid

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements. -/
@[to_additive
      "If elements of a list additively commute with each other, then their sum does not
      depend on the order of elements."]
theorem Perm.prod_eq' [M : Monoid α] {l₁ l₂ : List α} (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute) :
    l₁.prod = l₂.prod := by
  refine h.foldl_eq' ?_ _
  apply Pairwise.forall_of_forall
  · intro x y h z
    exact (h z).symm
  · intros; rfl
  · apply hc.imp
    intro a b h z
    rw [mul_assoc z, mul_assoc z, h]
#align list.perm.prod_eq' List.Perm.prod_eq'
#align list.perm.sum_eq' List.Perm.sum_eq'

variable [CommMonoid α]

@[to_additive]
theorem Perm.prod_eq {l₁ l₂ : List α} (h : Perm l₁ l₂) : prod l₁ = prod l₂ :=
  h.fold_op_eq
#align list.perm.prod_eq List.Perm.prod_eq
#align list.perm.sum_eq List.Perm.sum_eq

@[to_additive]
theorem prod_reverse (l : List α) : prod l.reverse = prod l :=
  (reverse_perm l).prod_eq
#align list.prod_reverse List.prod_reverse
#align list.sum_reverse List.sum_reverse

end CommMonoid

theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : List α} :
    l₁ ++ a :: r₁ ~ l₂ ++ a :: r₂ → l₁ ++ r₁ ~ l₂ ++ r₂ := by
  generalize e₁ : l₁ ++ a :: r₁ = s₁; generalize e₂ : l₂ ++ a :: r₂ = s₂
  intro p; revert l₁ l₂ r₁ r₂ e₁ e₂; clear l₁ l₂ β
  show ∀ _ _ _ _, _
  refine
      perm_induction_on p ?_ (fun x t₁ t₂ p IH => ?_) (fun x y t₁ t₂ p IH => ?_)
        fun t₁ t₂ t₃ p₁ p₂ IH₁ IH₂ => ?_
    <;> intro l₁ l₂ r₁ r₂ e₁ e₂
  · apply (not_mem_nil a).elim
    rw [← e₁]
    simp
  · cases' l₁ with y l₁ <;> cases' l₂ with z l₂ <;> dsimp at e₁ e₂ <;> injections <;> subst x
    · substs t₁ t₂
      exact p
    · substs z t₁ t₂
      exact p.trans perm_middle
    · substs y t₁ t₂
      exact perm_middle.symm.trans p
    · substs z t₁ t₂
      exact (IH _ _ _ _ rfl rfl).cons y
  · rcases l₁ with (_ | ⟨y, _ | ⟨z, l₁⟩⟩) <;> rcases l₂ with (_ | ⟨u, _ | ⟨v, l₂⟩⟩) <;>
          dsimp at e₁ e₂ <;> injections <;> substs x y
    · substs r₁ r₂
      exact p.cons a
    · substs r₁ r₂
      exact p.cons u
    · substs r₁ v t₂
      exact (p.trans perm_middle).cons u
    · substs r₁ r₂
      exact p.cons y
    · substs r₁ r₂ y u
      exact p.cons a
    · substs r₁ u v t₂
      exact ((p.trans perm_middle).cons y).trans (swap _ _ _)
    · substs r₂ z t₁
      exact (perm_middle.symm.trans p).cons y
    · substs r₂ y z t₁
      exact (swap _ _ _).trans ((perm_middle.symm.trans p).cons u)
    · substs u v t₁ t₂
      exact (IH _ _ _ _ rfl rfl).swap' _ _
  · substs t₁ t₃
    have : a ∈ t₂ := p₁.subset (by simp)
    rcases mem_split this with ⟨l₂, r₂, e₂⟩
    subst t₂
    exact (IH₁ _ _ _ _ rfl rfl).trans (IH₂ _ _ _ _ rfl rfl)
#align list.perm_inv_core List.perm_inv_core

theorem Perm.cons_inv {a : α} {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ → l₁ ~ l₂ :=
  @perm_inv_core _ _ [] [] _ _
#align list.perm.cons_inv List.Perm.cons_inv

@[simp]
theorem perm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ ↔ l₁ ~ l₂ :=
  ⟨Perm.cons_inv, Perm.cons a⟩
#align list.perm_cons List.perm_cons

theorem perm_append_left_iff {l₁ l₂ : List α} : ∀ l, l ++ l₁ ~ l ++ l₂ ↔ l₁ ~ l₂
  | [] => Iff.rfl
  | a :: l => (perm_cons a).trans (perm_append_left_iff l)
#align list.perm_append_left_iff List.perm_append_left_iff

theorem perm_append_right_iff {l₁ l₂ : List α} (l) : l₁ ++ l ~ l₂ ++ l ↔ l₁ ~ l₂ :=
  ⟨fun p => (perm_append_left_iff _).1 <| perm_append_comm.trans <| p.trans perm_append_comm,
    Perm.append_right _⟩
#align list.perm_append_right_iff List.perm_append_right_iff

theorem perm_option_to_list {o₁ o₂ : Option α} : o₁.toList ~ o₂.toList ↔ o₁ = o₂ := by
  refine' ⟨fun p => _, fun e => e ▸ Perm.refl _⟩
  cases' o₁ with a <;> cases' o₂ with b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)
#align list.perm_option_to_list List.perm_option_to_list

theorem subperm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ <+~ a :: l₂ ↔ l₁ <+~ l₂ :=
  ⟨fun ⟨l, p, s⟩ => by
    cases' s with _ _ _ s' u _ _ s'
    · exact (p.subperm_left.2 <| (sublist_cons _ _).subperm).trans s'.subperm
    · exact ⟨u, p.cons_inv, s'⟩, fun ⟨l, p, s⟩ => ⟨a :: l, p.cons a, s.cons₂ _⟩⟩
#align list.subperm_cons List.subperm_cons

alias ⟨subperm.of_cons, subperm.cons⟩ := subperm_cons
#align list.subperm.of_cons List.subperm.of_cons
#align list.subperm.cons List.subperm.cons

--Porting note: commented out
--attribute [protected] subperm.cons

theorem cons_subperm_of_mem {a : α} {l₁ l₂ : List α} (d₁ : Nodup l₁) (h₁ : a ∉ l₁) (h₂ : a ∈ l₂)
    (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ := by
  rcases s with ⟨l, p, s⟩
  induction s generalizing l₁
  case slnil => cases h₂
  case cons r₁ r₂ b s' ih =>
    simp at h₂
    cases' h₂ with e m
    · subst b
      exact ⟨a :: r₁, p.cons a, s'.cons₂ _⟩
    · rcases ih d₁ h₁ m p with ⟨t, p', s'⟩
      exact ⟨t, p', s'.cons _⟩
  case cons₂ r₁ r₂ b _ ih =>
    have bm : b ∈ l₁ := p.subset <| mem_cons_self _ _
    have am : a ∈ r₂ := by
      simp only [find?, mem_cons] at h₂
      exact h₂.resolve_left fun e => h₁ <| e.symm ▸ bm
    rcases mem_split bm with ⟨t₁, t₂, rfl⟩
    have st : t₁ ++ t₂ <+ t₁ ++ b :: t₂ := by simp
    rcases ih (d₁.sublist st) (mt (fun x => st.subset x) h₁) am
        (Perm.cons_inv <| p.trans perm_middle) with
      ⟨t, p', s'⟩
    exact
      ⟨b :: t, (p'.cons b).trans <| (swap _ _ _).trans (perm_middle.symm.cons a), s'.cons₂ _⟩
#align list.cons_subperm_of_mem List.cons_subperm_of_mem

theorem subperm_append_left {l₁ l₂ : List α} : ∀ l, l ++ l₁ <+~ l ++ l₂ ↔ l₁ <+~ l₂
  | [] => Iff.rfl
  | a :: l => (subperm_cons a).trans (subperm_append_left l)
#align list.subperm_append_left List.subperm_append_left

theorem subperm_append_right {l₁ l₂ : List α} (l) : l₁ ++ l <+~ l₂ ++ l ↔ l₁ <+~ l₂ :=
  (perm_append_comm.subperm_left.trans perm_append_comm.subperm_right).trans (subperm_append_left l)
#align list.subperm_append_right List.subperm_append_right

theorem Subperm.exists_of_length_lt {l₁ l₂ : List α} :
    l₁ <+~ l₂ → length l₁ < length l₂ → ∃ a, a :: l₁ <+~ l₂
  | ⟨l, p, s⟩, h => by
    suffices length l < length l₂ → ∃ a : α, a :: l <+~ l₂ from
      (this <| p.symm.length_eq ▸ h).imp fun a => (p.cons a).subperm_right.1
    clear h p l₁
    induction' s with l₁ l₂ a s IH _ _ b _ IH <;> intro h
    · cases h
    · cases' lt_or_eq_of_le (Nat.le_of_lt_succ h : length l₁ ≤ length l₂) with h h
      · exact (IH h).imp fun a s => s.trans (sublist_cons _ _).subperm
      · exact ⟨a, s.eq_of_length h ▸ Subperm.refl _⟩
    · exact (IH <| Nat.lt_of_succ_lt_succ h).imp fun a s =>
          (swap _ _ _).subperm_right.1 <| (subperm_cons _).2 s
#align list.subperm.exists_of_length_lt List.Subperm.exists_of_length_lt

protected theorem Nodup.subperm (d : Nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ := by
  induction' d with a l₁' h d IH
  · exact ⟨nil, Perm.nil, nil_sublist _⟩
  · cases' forall_mem_cons.1 H with H₁ H₂
    simp at h
    exact cons_subperm_of_mem d h H₁ (IH H₂)
#align list.nodup.subperm List.Nodup.subperm

theorem perm_ext {l₁ l₂ : List α} (d₁ : Nodup l₁) (d₂ : Nodup l₂) :
    l₁ ~ l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂ :=
  ⟨fun p _ => p.mem_iff, fun H =>
    (d₁.subperm fun a => (H a).1).antisymm <| d₂.subperm fun a => (H a).2⟩
#align list.perm_ext List.perm_ext

theorem Nodup.sublist_ext {l₁ l₂ l : List α} (d : Nodup l) (s₁ : l₁ <+ l) (s₂ : l₂ <+ l) :
    l₁ ~ l₂ ↔ l₁ = l₂ :=
  ⟨fun h => by
    induction' s₂ with l₂ l a s₂ IH l₂ l a _ IH generalizing l₁
    · exact h.eq_nil
    · simp at d
      cases' s₁ with _ _ _ s₁ l₁ _ _ s₁
      · exact IH d.2 s₁ h
      · apply d.1.elim
        exact Subperm.subset ⟨_, h.symm, s₂⟩ (mem_cons_self _ _)
    · simp at d
      cases' s₁ with _ _ _ s₁ l₁ _ _ s₁
      · apply d.1.elim
        exact Subperm.subset ⟨_, h, s₁⟩ (mem_cons_self _ _)
      · rw [IH d.2 s₁ h.cons_inv], fun h => by rw [h]⟩
#align list.nodup.sublist_ext List.Nodup.sublist_ext

section

variable [DecidableEq α]

-- attribute [congr]
theorem Perm.erase (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.erase a ~ l₂.erase a :=
  if h₁ : a ∈ l₁ then
    have h₂ : a ∈ l₂ := p.subset h₁
    Perm.cons_inv <| (perm_cons_erase h₁).symm.trans <| p.trans (perm_cons_erase h₂)
  else by
    have h₂ : a ∉ l₂ := mt p.mem_iff.2 h₁
    rw [erase_of_not_mem h₁, erase_of_not_mem h₂]; exact p
#align list.perm.erase List.Perm.erase

theorem subperm_cons_erase (a : α) (l : List α) : l <+~ a :: l.erase a := by
  by_cases h : a ∈ l
  · exact (perm_cons_erase h).subperm
  · rw [erase_of_not_mem h]
    exact (sublist_cons _ _).subperm
#align list.subperm_cons_erase List.subperm_cons_erase

theorem erase_subperm (a : α) (l : List α) : l.erase a <+~ l :=
  (erase_sublist _ _).subperm
#align list.erase_subperm List.erase_subperm

theorem Subperm.erase {l₁ l₂ : List α} (a : α) (h : l₁ <+~ l₂) : l₁.erase a <+~ l₂.erase a :=
  let ⟨l, hp, hs⟩ := h
  ⟨l.erase a, hp.erase _, hs.erase _⟩
#align list.subperm.erase List.Subperm.erase

theorem Perm.diff_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) : l₁.diff t ~ l₂.diff t := by
  induction t generalizing l₁ l₂ h <;> simp [*, Perm.erase]
#align list.perm.diff_right List.Perm.diff_right

theorem Perm.diff_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l.diff t₁ = l.diff t₂ := by
  induction h generalizing l <;>
    first |simp [*, Perm.erase, erase_comm]
#align list.perm.diff_left List.Perm.diff_left

theorem Perm.diff {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) : l₁.diff t₁ ~ l₂.diff t₂ :=
  ht.diff_left l₂ ▸ hl.diff_right _
#align list.perm.diff List.Perm.diff

theorem Subperm.diff_right {l₁ l₂ : List α} (h : l₁ <+~ l₂) (t : List α) :
    l₁.diff t <+~ l₂.diff t := by induction t generalizing l₁ l₂ h <;> simp [*, Subperm.erase]
#align list.subperm.diff_right List.Subperm.diff_right

theorem erase_cons_subperm_cons_erase (a b : α) (l : List α) :
    (a :: l).erase b <+~ a :: l.erase b := by
  by_cases h : a = b
  · subst b
    rw [erase_cons_head]
    apply subperm_cons_erase
  · rw [erase_cons_tail _ h]
#align list.erase_cons_subperm_cons_erase List.erase_cons_subperm_cons_erase

theorem subperm_cons_diff {a : α} : ∀ {l₁ l₂ : List α}, (a :: l₁).diff l₂ <+~ a :: l₁.diff l₂
  | l₁, [] => ⟨a :: l₁, by simp⟩
  | l₁, b :: l₂ => by
    simp only [diff_cons]
    refine' ((erase_cons_subperm_cons_erase a b l₁).diff_right l₂).trans _
    apply subperm_cons_diff
#align list.subperm_cons_diff List.subperm_cons_diff

theorem subset_cons_diff {a : α} {l₁ l₂ : List α} : (a :: l₁).diff l₂ ⊆ a :: l₁.diff l₂ :=
  subperm_cons_diff.subset
#align list.subset_cons_diff List.subset_cons_diff

theorem Perm.bagInter_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) :
    l₁.bagInter t ~ l₂.bagInter t := by
  induction' h with x _ _ _ _ x y _ _ _ _ _ _ ih_1 ih_2 generalizing t; · simp
  · by_cases x ∈ t <;> simp [*, Perm.cons]
  · by_cases h : x = y
    · simp [h]
    by_cases xt : x ∈ t <;> by_cases yt : y ∈ t
    · simp [xt, yt, mem_erase_of_ne h, mem_erase_of_ne (Ne.symm h), erase_comm, swap]
    · simp [xt, yt, mt mem_of_mem_erase, Perm.cons]
    · simp [xt, yt, mt mem_of_mem_erase, Perm.cons]
    · simp [xt, yt]
  · exact (ih_1 _).trans (ih_2 _)
#align list.perm.bag_inter_right List.Perm.bagInter_right

theorem Perm.bagInter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) :
    l.bagInter t₁ = l.bagInter t₂ := by
  induction' l with a l IH generalizing t₁ t₂ p; · simp
  by_cases h : a ∈ t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]
#align list.perm.bag_inter_left List.Perm.bagInter_left

theorem Perm.bagInter {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
    l₁.bagInter t₁ ~ l₂.bagInter t₂ :=
  ht.bagInter_left l₂ ▸ hl.bagInter_right _
#align list.perm.bag_inter List.Perm.bagInter

theorem cons_perm_iff_perm_erase {a : α} {l₁ l₂ : List α} :
    a :: l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a :=
  ⟨fun h =>
    have : a ∈ l₂ := h.subset (mem_cons_self a l₁)
    ⟨this, (h.trans <| perm_cons_erase this).cons_inv⟩,
    fun ⟨m, h⟩ => (h.cons a).trans (perm_cons_erase m).symm⟩
#align list.cons_perm_iff_perm_erase List.cons_perm_iff_perm_erase

theorem perm_iff_count {l₁ l₂ : List α} : l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂ :=
  ⟨Perm.count_eq, fun H => by
    induction' l₁ with a l₁ IH generalizing l₂
    · cases' l₂ with b l₂
      · rfl
      specialize H b
      simp at H
      contradiction
    · have : a ∈ l₂ := count_pos_iff_mem.1 (by rw [← H, count_pos_iff_mem]; simp)
      refine' ((IH fun b => _).cons a).trans (perm_cons_erase this).symm
      specialize H b
      rw [(perm_cons_erase this).count_eq] at H
      by_cases h : b = a <;> simpa [h] using H⟩
#align list.perm_iff_count List.perm_iff_count

theorem perm_replicate_append_replicate {l : List α} {a b : α} {m n : ℕ} (h : a ≠ b) :
    l ~ replicate m a ++ replicate n b ↔ count a l = m ∧ count b l = n ∧ l ⊆ [a, b] := by
  rw [perm_iff_count, ← Decidable.and_forall_ne a, ← Decidable.and_forall_ne b]
  suffices l ⊆ [a, b] ↔ ∀ c, c ≠ b → c ≠ a → c ∉ l by
    simp (config := { contextual := true }) [count_replicate, h, h.symm, this, count_eq_zero]
  simp_rw [Ne.def, ← and_imp, ← not_or, Decidable.not_imp_not, subset_def, mem_cons,
    not_mem_nil, or_false, or_comm]
#align list.perm_replicate_append_replicate List.perm_replicate_append_replicate

theorem Subperm.cons_right {α : Type*} {l l' : List α} (x : α) (h : l <+~ l') : l <+~ x :: l' :=
  h.trans (sublist_cons x l').subperm
#align list.subperm.cons_right List.Subperm.cons_right

/-- The list version of `add_tsub_cancel_of_le` for multisets. -/
theorem subperm_append_diff_self_of_count_le {l₁ l₂ : List α}
    (h : ∀ x ∈ l₁, count x l₁ ≤ count x l₂) : l₁ ++ l₂.diff l₁ ~ l₂ := by
  induction' l₁ with hd tl IH generalizing l₂
  · simp
  · have : hd ∈ l₂ := by
      rw [← count_pos_iff_mem]
      exact lt_of_lt_of_le (count_pos_iff_mem.mpr (mem_cons_self _ _)) (h hd (mem_cons_self _ _))
    replace := perm_cons_erase this
    refine' Perm.trans _ this.symm
    rw [cons_append, diff_cons, perm_cons]
    refine' IH fun x hx => _
    specialize h x (mem_cons_of_mem _ hx)
    rw [perm_iff_count.mp this] at h
    by_cases hx : x = hd
    · subst hd
      simpa [Nat.succ_le_succ_iff] using h
    · simpa [hx] using h
#align list.subperm_append_diff_self_of_count_le List.subperm_append_diff_self_of_count_le

/-- The list version of `Multiset.le_iff_count`. -/
theorem subperm_ext_iff {l₁ l₂ : List α} : l₁ <+~ l₂ ↔ ∀ x ∈ l₁, count x l₁ ≤ count x l₂ := by
  refine' ⟨fun h x _ => Subperm.count_le h x, fun h => _⟩
  suffices l₁ <+~ l₂.diff l₁ ++ l₁ by
    refine' this.trans (Perm.subperm _)
    exact perm_append_comm.trans (subperm_append_diff_self_of_count_le h)
  exact (subperm_append_right l₁).mpr nil_subperm
#align list.subperm_ext_iff List.subperm_ext_iff

instance decidableSubperm : DecidableRel ((· <+~ ·) : List α → List α → Prop) := fun _ _ =>
  decidable_of_iff _ List.subperm_ext_iff.symm
#align list.decidable_subperm List.decidableSubperm

@[simp]
theorem subperm_singleton_iff {α} {l : List α} {a : α} : [a] <+~ l ↔ a ∈ l :=
  ⟨fun ⟨s, hla, h⟩ => by rwa [perm_singleton.mp hla, singleton_sublist] at h, fun h =>
    ⟨[a], Perm.refl _, singleton_sublist.mpr h⟩⟩
#align list.subperm_singleton_iff List.subperm_singleton_iff

theorem Subperm.cons_left {l₁ l₂ : List α} (h : l₁ <+~ l₂) (x : α) (hx : count x l₁ < count x l₂) :
    x :: l₁ <+~ l₂ := by
  rw [subperm_ext_iff] at h ⊢
  intro y hy
  by_cases hy' : y = x
  · subst x
    simpa using Nat.succ_le_of_lt hx
  · rw [count_cons_of_ne hy']
    refine' h y _
    simpa [hy'] using hy
#align list.subperm.cons_left List.Subperm.cons_left

instance decidablePerm : ∀ l₁ l₂ : List α, Decidable (l₁ ~ l₂)
  | [], [] => isTrue <| Perm.refl _
  | [], b :: l₂ => isFalse fun h => by have := h.nil_eq; contradiction
  | a :: l₁, l₂ =>
    haveI := decidablePerm l₁ (l₂.erase a)
    decidable_of_iff' _ cons_perm_iff_perm_erase
#align list.decidable_perm List.decidablePerm

-- @[congr]
theorem Perm.dedup {l₁ l₂ : List α} (p : l₁ ~ l₂) : dedup l₁ ~ dedup l₂ :=
  perm_iff_count.2 fun a =>
    if h : a ∈ l₁ then by simp [nodup_dedup, h, p.subset h] else by simp [h, mt p.mem_iff.2 h]
#align list.perm.dedup List.Perm.dedup

-- attribute [congr]
protected theorem Perm.insert (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.insert a ~ l₂.insert a :=
  if h : a ∈ l₁ then by simpa [h, p.subset h] using p
  else by simpa [h, mt p.mem_iff.2 h] using p.cons a
#align list.perm.insert List.Perm.insert

theorem perm_insert_swap (x y : α) (l : List α) :
    List.insert x (List.insert y l) ~ List.insert y (List.insert x l) := by
  by_cases xl : x ∈ l <;> by_cases yl : y ∈ l <;> simp [xl, yl]
  by_cases xy : x = y; · simp [xy]
  simp only [List.insert, Bool.not_eq_true, mem_cons, xy, xl, or_self, ite_false, Ne.symm xy, yl]
  constructor
#align list.perm_insert_swap List.perm_insert_swap

theorem perm_insertNth {α} (x : α) (l : List α) {n} (h : n ≤ l.length) :
    insertNth n x l ~ x :: l := by
  induction' l with _ _ l_ih generalizing n
  · cases n
    rfl
    cases h
  cases n
  · simp [insertNth]
  · simp only [insertNth, modifyNthTail]
    refine' Perm.trans (Perm.cons _ (l_ih _)) _
    · apply Nat.le_of_succ_le_succ h
    · apply Perm.swap
#align list.perm_insert_nth List.perm_insertNth

theorem Perm.union_right {l₁ l₂ : List α} (t₁ : List α) (h : l₁ ~ l₂) :
    l₁ ∪ t₁ ~ l₂ ∪ t₁ := by
  induction' h with a _ _ _ ih _ _ _ _ _ _ _ _ ih_1 ih_2 <;> try simp
  · exact ih.insert a
  · apply perm_insert_swap
  · exact ih_1.trans ih_2
#align list.perm.union_right List.Perm.union_right

theorem Perm.union_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ := by
  induction l <;> simp [*, Perm.insert]
#align list.perm.union_left List.Perm.union_left

-- @[congr]
theorem Perm.union {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
  (p₁.union_right t₁).trans (p₂.union_left l₂)
#align list.perm.union List.Perm.union

theorem Perm.inter_right {l₁ l₂ : List α} (t₁ : List α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ :=
  Perm.filter _
#align list.perm.inter_right List.Perm.inter_right

theorem Perm.inter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ :=
  filter_congr' fun a _ => by simpa using p.mem_iff
#align list.perm.inter_left List.Perm.inter_left

-- @[congr]
theorem Perm.inter {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∩ t₁ ~ l₂ ∩ t₂ :=
  p₂.inter_left l₂ ▸ p₁.inter_right t₁
#align list.perm.inter List.Perm.inter

theorem Perm.inter_append {l t₁ t₂ : List α} (h : Disjoint t₁ t₂) :
    l ∩ (t₁ ++ t₂) ~ l ∩ t₁ ++ l ∩ t₂ := by
  induction l
  case nil => simp
  case cons x xs l_ih =>
    by_cases h₁ : x ∈ t₁
    · have h₂ : x ∉ t₂ := h h₁
      simp [*]
    by_cases h₂ : x ∈ t₂
    · simp only [*, inter_cons_of_not_mem, false_or_iff, mem_append, inter_cons_of_mem,
        not_false_iff]
      refine' Perm.trans (Perm.cons _ l_ih) _
      change [x] ++ xs ∩ t₁ ++ xs ∩ t₂ ~ xs ∩ t₁ ++ ([x] ++ xs ∩ t₂)
      rw [← List.append_assoc]
      solve_by_elim [Perm.append_right, perm_append_comm]
    · simp [*]
#align list.perm.inter_append List.Perm.inter_append

end

theorem Perm.pairwise_iff {R : α → α → Prop} (S : Symmetric R) :
    ∀ {l₁ l₂ : List α} (_p : l₁ ~ l₂), Pairwise R l₁ ↔ Pairwise R l₂ :=
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise R l₁ → Pairwise R l₂
    from fun p => ⟨this p, this p.symm⟩
  @fun l₁ l₂ p d => by
  induction' d with a l₁ h _ IH generalizing l₂
  · rw [← p.nil_eq]
    constructor
  · have : a ∈ l₂ := p.subset (mem_cons_self _ _)
    rcases mem_split this with ⟨s₂, t₂, rfl⟩
    have p' := (p.trans perm_middle).cons_inv
    refine' (pairwise_middle @S).2 (pairwise_cons.2 ⟨fun b m => _, IH _ p'⟩)
    exact h _ (p'.symm.subset m)
#align list.perm.pairwise_iff List.Perm.pairwise_iff


theorem Pairwise.perm {R : α → α → Prop} {l l' : List α} (hR : l.Pairwise R) (hl : l ~ l')
    (hsymm : Symmetric R) : l'.Pairwise R :=
  (hl.pairwise_iff hsymm).mp hR
#align list.pairwise.perm List.Pairwise.perm

theorem Perm.pairwise {R : α → α → Prop} {l l' : List α} (hl : l ~ l') (hR : l.Pairwise R)
    (hsymm : Symmetric R) : l'.Pairwise R :=
  hR.perm hl hsymm
#align list.perm.pairwise List.Perm.pairwise

theorem Perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (Nodup l₁ ↔ Nodup l₂) :=
  Perm.pairwise_iff <| @Ne.symm α
#align list.perm.nodup_iff List.Perm.nodup_iff

theorem Perm.join {l₁ l₂ : List (List α)} (h : l₁ ~ l₂) : l₁.join ~ l₂.join :=
  Perm.recOn h (Perm.refl _) (fun x xs₁ xs₂ _ ih => ih.append_left x)
    (fun x₁ x₂ xs => by simpa only [join, append_assoc] using perm_append_comm.append_right _)
    @fun xs₁ xs₂ xs₃ _ _ => Perm.trans
#align list.perm.join List.Perm.join

theorem Perm.bind_right {l₁ l₂ : List α} (f : α → List β) (p : l₁ ~ l₂) : l₁.bind f ~ l₂.bind f :=
  (p.map _).join
#align list.perm.bind_right List.Perm.bind_right

theorem Perm.join_congr :
    ∀ {l₁ l₂ : List (List α)} (_ : List.Forall₂ (· ~ ·) l₁ l₂), l₁.join ~ l₂.join
  | _, _, Forall₂.nil => Perm.refl _
  | _ :: _, _ :: _, Forall₂.cons h₁ h₂ => h₁.append (Perm.join_congr h₂)
#align list.perm.join_congr List.Perm.join_congr

theorem Perm.bind_left (l : List α) {f g : α → List β} (h : ∀ a ∈ l, f a ~ g a) :
    l.bind f ~ l.bind g :=
  Perm.join_congr <| by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]
#align list.perm.bind_left List.Perm.bind_left

theorem bind_append_perm (l : List α) (f g : α → List β) :
    l.bind f ++ l.bind g ~ l.bind fun x => f x ++ g x := by
  induction' l with a l IH <;> simp
  refine' (Perm.trans _ (IH.append_left _)).append_left _
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append_right _
#align list.bind_append_perm List.bind_append_perm

theorem map_append_bind_perm (l : List α) (f : α → β) (g : α → List β) :
    l.map f ++ l.bind g ~ l.bind fun x => f x :: g x := by
  simpa [← map_eq_bind] using bind_append_perm l (fun x => [f x]) g
#align list.map_append_bind_perm List.map_append_bind_perm

theorem Perm.product_right {l₁ l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂) :
    product l₁ t₁ ~ product l₂ t₁ :=
  p.bind_right _
#align list.perm.product_right List.Perm.product_right

theorem Perm.product_left (l : List α) {t₁ t₂ : List β} (p : t₁ ~ t₂) :
    product l t₁ ~ product l t₂ :=
  (Perm.bind_left _) fun _ _ => p.map _
#align list.perm.product_left List.Perm.product_left

-- @[congr]
theorem Perm.product {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    product l₁ t₁ ~ product l₂ t₂ :=
  (p₁.product_right t₁).trans (p₂.product_left l₂)
#align list.perm.product List.Perm.product

theorem perm_lookmap (f : α → Option α) {l₁ l₂ : List α}
    (H : Pairwise (fun a b => ∀ c ∈ f a, ∀ d ∈ f b, a = b ∧ c = d) l₁) (p : l₁ ~ l₂) :
    lookmap f l₁ ~ lookmap f l₂ := by
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ _ IH₁ IH₂; · simp
  · cases h : f a
    · simp [h]
      exact IH (pairwise_cons.1 H).2
    · simp [lookmap_cons_some _ _ h, p]
  · cases' h₁ : f a with c <;> cases' h₂ : f b with d
    · simp [h₁, h₂]
      apply swap
    · simp [h₁, lookmap_cons_some _ _ h₂]
      apply swap
    · simp [lookmap_cons_some _ _ h₁, h₂]
      apply swap
    · simp [lookmap_cons_some _ _ h₁, lookmap_cons_some _ _ h₂]
      rcases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) _ h₂ _ h₁ with ⟨rfl, rfl⟩
      exact Perm.refl _
  · refine' (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H))
    exact fun a b h c h₁ d h₂ => (h d h₂ c h₁).imp Eq.symm Eq.symm
#align list.perm_lookmap List.perm_lookmap

theorem Perm.erasep (f : α → Prop) [DecidablePred f] {l₁ l₂ : List α}
    (H : Pairwise (fun a b => f a → f b → False) l₁) (p : l₁ ~ l₂) : eraseP f l₁ ~ eraseP f l₂ := by
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ _ IH₁ IH₂; · simp
  · by_cases h : f a
    · simp [h, p]
    · simp [h]
      exact IH (pairwise_cons.1 H).2
  · by_cases h₁ : f a <;> by_cases h₂ : f b <;> simp [h₁, h₂]
    · cases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) h₂ h₁
    · apply swap
  · refine' (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H))
    exact fun a b h h₁ h₂ => h h₂ h₁
#align list.perm.erasep List.Perm.erasep

theorem Perm.take_inter {α : Type*} [DecidableEq α] {xs ys : List α} (n : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : xs.take n ~ ys.inter (xs.take n) := by
  simp only [List.inter]
  exact Perm.trans (show xs.take n ~ xs.filter (· ∈ xs.take n) by
      conv_lhs => rw [Nodup.take_eq_filter_mem ((Perm.nodup_iff h).2 h')])
    (Perm.filter _ h)
#align list.perm.take_inter List.Perm.take_inter

theorem Perm.drop_inter {α} [DecidableEq α] {xs ys : List α} (n : ℕ) (h : xs ~ ys) (h' : ys.Nodup) :
    xs.drop n ~ ys.inter (xs.drop n) := by
  by_cases h'' : n ≤ xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by
      rwa [tsub_tsub_cancel_of_le]
    have h₁ : n' ≤ xs.length := by apply tsub_le_self
    have h₂ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [reverse_take _ h₁, h₀, reverse_reverse]
    rw [h₂]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply Perm.take_inter _ _ h'
    apply (reverse_perm _).trans; assumption
  · have : drop n xs = [] := by
      apply eq_nil_of_length_eq_zero
      rw [length_drop, tsub_eq_zero_iff_le]
      apply le_of_not_ge h''
    simp [this, List.inter]
#align list.perm.drop_inter List.Perm.drop_inter

theorem Perm.dropSlice_inter {α} [DecidableEq α] {xs ys : List α} (n m : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : List.dropSlice n m xs ~ ys ∩ List.dropSlice n m xs := by
  simp only [dropSlice_eq]
  have : n ≤ n + m := Nat.le_add_right _ _
  have h₂ := h.nodup_iff.2 h'
  apply Perm.trans _ (Perm.inter_append _).symm
  · exact Perm.append (Perm.take_inter _ h h') (Perm.drop_inter _ h h')
  · exact disjoint_take_drop h₂ this
#align list.perm.slice_inter List.Perm.dropSlice_inter

-- enumerating permutations
section Permutations

theorem perm_of_mem_permutationsAux :
    ∀ {ts is l : List α}, l ∈ permutationsAux ts is → l ~ ts ++ is := by
  show ∀ (ts is l : List α), l ∈ permutationsAux ts is → l ~ ts ++ is
  refine' permutationsAux.rec (by simp) _
  introv IH1 IH2 m
  rw [permutationsAux_cons, permutations, mem_foldr_permutationsAux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, rfl⟩)
  · exact (IH1 _ m).trans perm_middle
  · have p : l₁ ++ l₂ ~ is := by
      simp [permutations] at m
      cases' m with e m
      · simp [e]
      exact is.append_nil ▸ IH2 _ m
    exact ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _)
#align list.perm_of_mem_permutations_aux List.perm_of_mem_permutationsAux

theorem perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
  (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutationsAux m
#align list.perm_of_mem_permutations List.perm_of_mem_permutations

theorem length_permutationsAux :
    ∀ ts is : List α, length (permutationsAux ts is) + is.length ! = (length ts + length is)! := by
  refine' permutationsAux.rec (by simp) _
  intro t ts is IH1 IH2
  have IH2 : length (permutationsAux is nil) + 1 = is.length ! := by simpa using IH2
  simp [Nat.factorial, Nat.add_succ, mul_comm] at IH1
  rw [permutationsAux_cons,
    length_foldr_permutationsAux2' _ _ _ _ _ fun l m => (perm_of_mem_permutations m).length_eq,
    permutations, length, length, IH2, Nat.succ_add, Nat.factorial_succ, mul_comm (_ + 1),
    ← Nat.succ_eq_add_one, ← IH1, add_comm (_ * _), add_assoc, Nat.mul_succ, mul_comm]
#align list.length_permutations_aux List.length_permutationsAux

theorem length_permutations (l : List α) : length (permutations l) = (length l)! :=
  length_permutationsAux l []
#align list.length_permutations List.length_permutations

theorem mem_permutations_of_perm_lemma {is l : List α}
    (H : l ~ [] ++ is → (∃ (ts' : _) (_ : ts' ~ []), l = ts' ++ is) ∨ l ∈ permutationsAux is []) :
    l ~ is → l ∈ permutations is := by simpa [permutations, perm_nil] using H
#align list.mem_permutations_of_perm_lemma List.mem_permutations_of_perm_lemma

theorem mem_permutationsAux_of_perm :
    ∀ {ts is l : List α},
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is := by
  show ∀ (ts is l : List α),
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is
  refine' permutationsAux.rec (by simp) _
  intro t ts is IH1 IH2 l p
  rw [permutationsAux_cons, mem_foldr_permutationsAux2]
  rcases IH1 _ (p.trans perm_middle) with (⟨is', p', e⟩ | m)
  · clear p
    subst e
    rcases mem_split (p'.symm.subset (mem_cons_self _ _)) with ⟨l₁, l₂, e⟩
    subst is'
    have p := (perm_middle.symm.trans p').cons_inv
    cases' l₂ with a l₂'
    · exact Or.inl ⟨l₁, by simpa using p⟩
    · exact Or.inr (Or.inr ⟨l₁, a :: l₂', mem_permutations_of_perm_lemma (IH2 _) p, by simp⟩)
  · exact Or.inr (Or.inl m)
#align list.mem_permutations_aux_of_perm List.mem_permutationsAux_of_perm

@[simp]
theorem mem_permutations {s t : List α} : s ∈ permutations t ↔ s ~ t :=
  ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutationsAux_of_perm⟩
#align list.mem_permutations List.mem_permutations

--Porting note: temporary theorem to solve diamond issue
private theorem DecEq_eq {α : Type*} [DecidableEq α] :
     instBEqList = @instBEq (List α) instDecidableEqList :=
  congr_arg BEq.mk <| by
    funext l₁ l₂
    show (l₁ == l₂) = _
    rw [Bool.eq_iff_eq_true_iff, @beq_iff_eq _ (_), decide_eq_true_iff]

theorem perm_permutations'Aux_comm (a b : α) (l : List α) :
    (permutations'Aux a l).bind (permutations'Aux b) ~
      (permutations'Aux b l).bind (permutations'Aux a) := by
  induction' l with c l ih
  · simp [swap]
  simp only [permutations'Aux, cons_bind, map_cons, map_map, cons_append]
  apply Perm.swap'
  have :
    ∀ a b,
      (map (cons c) (permutations'Aux a l)).bind (permutations'Aux b) ~
        map (cons b ∘ cons c) (permutations'Aux a l) ++
          map (cons c) ((permutations'Aux a l).bind (permutations'Aux b)) := by
    intros a' b'
    simp only [map_bind, permutations'Aux]
    show List.bind (permutations'Aux _ l) (fun a => ([b' :: c :: a] ++
      map (cons c) (permutations'Aux _ a))) ~ _
    refine' (bind_append_perm _ (fun x => [b' :: c :: x]) _).symm.trans _
    rw [← map_eq_bind, ← bind_map]
    exact Perm.refl _
  refine' (((this _ _).append_left _).trans _).trans ((this _ _).append_left _).symm
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append (ih.map _)
#align list.perm_permutations'_aux_comm List.perm_permutations'Aux_comm

theorem Perm.permutations' {s t : List α} (p : s ~ t) : permutations' s ~ permutations' t := by
  induction' p with a s t _ IH a b l s t u _ _ IH₁ IH₂; · simp
  · exact IH.bind_right _
  · dsimp [permutations']
    rw [bind_assoc, bind_assoc]
    apply Perm.bind_left
    intro l' _
    apply perm_permutations'Aux_comm
  · exact IH₁.trans IH₂
#align list.perm.permutations' List.Perm.permutations'

theorem permutations_perm_permutations' (ts : List α) : ts.permutations ~ ts.permutations' := by
  obtain ⟨n, h⟩ : ∃ n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction' n with n IH generalizing ts; · cases h
  refine' List.reverseRecOn ts (fun _ => _) (fun ts t _ h => _) h; · simp [permutations]
  rw [← concat_eq_append, length_concat, Nat.succ_lt_succ_iff] at h
  have IH₂ := (IH ts.reverse (by rwa [length_reverse])).trans (reverse_perm _).permutations'
  simp only [permutations_append, foldr_permutationsAux2, permutationsAux_nil,
    permutationsAux_cons, append_nil]
  refine'
    (perm_append_comm.trans ((IH₂.bind_right _).append ((IH _ h).map _))).trans
      (Perm.trans _ perm_append_comm.permutations')
  rw [map_eq_bind, singleton_append, permutations']
  refine' (bind_append_perm _ _ _).trans _
  refine' Perm.of_eq _
  congr
  funext _
  rw [permutations'Aux_eq_permutationsAux2, permutationsAux2_append]
#align list.permutations_perm_permutations' List.permutations_perm_permutations'

@[simp]
theorem mem_permutations' {s t : List α} : s ∈ permutations' t ↔ s ~ t :=
  (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations
#align list.mem_permutations' List.mem_permutations'

theorem Perm.permutations {s t : List α} (h : s ~ t) : permutations s ~ permutations t :=
  (permutations_perm_permutations' _).trans <|
    h.permutations'.trans (permutations_perm_permutations' _).symm
#align list.perm.permutations List.Perm.permutations

@[simp]
theorem perm_permutations_iff {s t : List α} : permutations s ~ permutations t ↔ s ~ t :=
  ⟨fun h => mem_permutations.1 <| h.mem_iff.1 <| mem_permutations.2 (Perm.refl _),
    Perm.permutations⟩
#align list.perm_permutations_iff List.perm_permutations_iff

@[simp]
theorem perm_permutations'_iff {s t : List α} : permutations' s ~ permutations' t ↔ s ~ t :=
  ⟨fun h => mem_permutations'.1 <| h.mem_iff.1 <| mem_permutations'.2 (Perm.refl _),
    Perm.permutations'⟩
#align list.perm_permutations'_iff List.perm_permutations'_iff

set_option linter.deprecated false in
theorem nthLe_permutations'Aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s).nthLe n hn = s.insertNth n x := by
  induction' s with y s IH generalizing n
  · simp only [length, zero_add, lt_one_iff] at hn
    simp [hn]
  · cases n
    · simp [nthLe]
    · simpa [nthLe] using IH _ _
#align list.nth_le_permutations'_aux List.nthLe_permutations'Aux

theorem count_permutations'Aux_self [DecidableEq α] (l : List α) (x : α) :
    count (x :: l) (permutations'Aux x l) = length (takeWhile ((· = ·) x) l) + 1 := by
  induction' l with y l IH generalizing x
  · simp [takeWhile, count]
  · rw [permutations'Aux, DecEq_eq, count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [takeWhile, Nat.succ_inj', DecEq_eq] using IH _
    · rw [takeWhile]
      simp only [mem_map, cons.injEq, Ne.symm hx, false_and, and_false, exists_false,
        not_false_iff, count_eq_zero_of_not_mem, zero_add, hx, decide_False, length_nil]
#align list.count_permutations'_aux_self List.count_permutations'Aux_self

@[simp]
theorem length_permutations'Aux (s : List α) (x : α) :
    length (permutations'Aux x s) = length s + 1 := by
  induction' s with y s IH
  · simp
  · simpa using IH
#align list.length_permutations'_aux List.length_permutations'Aux

@[simp]
theorem permutations'Aux_nthLe_zero (s : List α) (x : α)
    (hn : 0 < length (permutations'Aux x s) := (by simp)) :
    (permutations'Aux x s).nthLe 0 hn = x :: s :=
  nthLe_permutations'Aux _ _ _ _
#align list.permutations'_aux_nth_le_zero List.permutations'Aux_nthLe_zero

theorem injective_permutations'Aux (x : α) : Function.Injective (permutations'Aux x) := by
  intro s t h
  apply insertNth_injective s.length x
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← nthLe_permutations'Aux s x s.length (by simp), ←
    nthLe_permutations'Aux t x s.length (by simp [hl])]
  simp [h, hl]
#align list.injective_permutations'_aux List.injective_permutations'Aux

theorem nodup_permutations'Aux_of_not_mem (s : List α) (x : α) (hx : x ∉ s) :
    Nodup (permutations'Aux x s) := by
  induction' s with y s IH
  · simp
  · simp only [not_or, mem_cons] at hx
    simp only [permutations'Aux, nodup_cons, mem_map, cons.injEq, exists_eq_right_right, not_and]
    refine' ⟨fun _ => Ne.symm hx.left, _⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp
#align list.nodup_permutations'_aux_of_not_mem List.nodup_permutations'Aux_of_not_mem

set_option linter.deprecated false in
theorem nodup_permutations'Aux_iff {s : List α} {x : α} : Nodup (permutations'Aux x s) ↔ x ∉ s := by
  refine' ⟨fun h => _, nodup_permutations'Aux_of_not_mem _ _⟩
  intro H
  obtain ⟨k, hk, hk'⟩ := nthLe_of_mem H
  rw [nodup_iff_nthLe_inj] at h
  suffices k = k + 1 by simp at this
  refine' h k (k + 1) _ _ _
  · simpa [Nat.lt_succ_iff] using hk.le
  · simpa using hk
  rw [nthLe_permutations'Aux, nthLe_permutations'Aux]
  have hl : length (insertNth k x s) = length (insertNth (k + 1) x s) := by
    rw [length_insertNth _ _ hk.le, length_insertNth _ _ (Nat.succ_le_of_lt hk)]
  refine' ext_nthLe hl fun n hn hn' => _
  rcases lt_trichotomy n k with (H | rfl | H)
  · rw [nthLe_insertNth_of_lt _ _ _ _ H (H.trans hk),
      nthLe_insertNth_of_lt _ _ _ _ (H.trans (Nat.lt_succ_self _))]
  · rw [nthLe_insertNth_self _ _ _ hk.le, nthLe_insertNth_of_lt _ _ _ _ (Nat.lt_succ_self _) hk,
      hk']
  · rcases (Nat.succ_le_of_lt H).eq_or_lt with (rfl | H')
    · rw [nthLe_insertNth_self _ _ _ (Nat.succ_le_of_lt hk)]
      convert hk' using 1
      exact nthLe_insertNth_add_succ _ _ _ 0 _
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt H'
      erw [length_insertNth _ _ hk.le, Nat.succ_lt_succ_iff, Nat.succ_add] at hn
      rw [nthLe_insertNth_add_succ]
      convert nthLe_insertNth_add_succ s x k m.succ (by simpa using hn) using 2
      · simp [Nat.add_succ, Nat.succ_add]
      · simp [add_left_comm, add_comm]
      · simpa [Nat.succ_add] using hn
#align list.nodup_permutations'_aux_iff List.nodup_permutations'Aux_iff

set_option linter.deprecated false in
theorem nodup_permutations (s : List α) (hs : Nodup s) : Nodup s.permutations := by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction' hs with x l h h' IH
  · simp
  · rw [permutations']
    rw [nodup_bind]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'Aux_iff, hy.mem_iff]
      exact fun H => h x H rfl
    · refine' IH.pairwise_of_forall_ne fun as ha bs hb H => _
      rw [disjoint_iff_ne]
      rintro a ha' b hb' rfl
      obtain ⟨⟨n, hn⟩, hn'⟩ := get_of_mem ha'
      obtain ⟨⟨m, hm⟩, hm'⟩ := get_of_mem hb'
      rw [mem_permutations'] at ha hb
      have hl : as.length = bs.length := (ha.trans hb.symm).length_eq
      simp only [Nat.lt_succ_iff, length_permutations'Aux] at hn hm
      rw [← nthLe, nthLe_permutations'Aux] at hn' hm'
      have hx :
        nthLe (insertNth n x as) m (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff, hl]) = x :=
        by simp [hn', ← hm', hm]
      have hx' :
        nthLe (insertNth m x bs) n (by rwa [length_insertNth _ _ hm, Nat.lt_succ_iff, ← hl]) =
          x :=
        by simp [hm', ← hn', hn]
      rcases lt_trichotomy n m with (ht | ht | ht)
      · suffices x ∈ bs by exact h x (hb.subset this) rfl
        rw [← hx', nthLe_insertNth_of_lt _ _ _ _ ht (ht.trans_le hm)]
        exact nthLe_mem _ _ _
      · simp only [ht] at hm' hn'
        rw [← hm'] at hn'
        exact H (insertNth_injective _ _ hn')
      · suffices x ∈ as by exact h x (ha.subset this) rfl
        rw [← hx, nthLe_insertNth_of_lt _ _ _ _ ht (ht.trans_le hn)]
        exact nthLe_mem _ _ _
#align list.nodup_permutations List.nodup_permutations

-- TODO: `nodup s.permutations ↔ nodup s`
-- TODO: `count s s.permutations = (zip_with count s s.tails).prod`
end Permutations

end List
