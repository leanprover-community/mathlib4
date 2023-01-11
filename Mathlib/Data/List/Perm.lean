/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module data.list.perm
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Dedup
import Mathbin.Data.List.Permutation
import Mathbin.Data.List.Range
import Mathbin.Data.Nat.Factorial.Basic

/-!
# List Permutations

This file introduces the `list.perm` relation, which is true if two lists are permutations of one
another.

## Notation

The notation `~` is used for permutation equivalence.
-/


open Nat

universe uu vv

namespace List

variable {α : Type uu} {β : Type vv} {l₁ l₂ : List α}

#print List.Perm /-
/-- `perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive Perm : List α → List α → Prop
  | nil : perm [] []
  | cons : ∀ (x : α) {l₁ l₂ : List α}, perm l₁ l₂ → perm (x :: l₁) (x :: l₂)
  | swap : ∀ (x y : α) (l : List α), perm (y :: x :: l) (x :: y :: l)
  | trans : ∀ {l₁ l₂ l₃ : List α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃
#align list.perm List.Perm
-/

open Perm (swap)

-- mathport name: list.perm
infixl:50 " ~ " => Perm

#print List.Perm.refl /-
@[refl]
protected theorem Perm.refl : ∀ l : List α, l ~ l
  | [] => Perm.nil
  | x :: xs => (perm.refl xs).cons x
#align list.perm.refl List.Perm.refl
-/

#print List.Perm.symm /-
@[symm]
protected theorem Perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
  Perm.rec_on p Perm.nil (fun x l₁ l₂ p₁ r₁ => r₁.cons x) (fun x y l => swap y x l)
    fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ => r₂.trans r₁
#align list.perm.symm List.Perm.symm
-/

theorem perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ :=
  ⟨Perm.symm, Perm.symm⟩
#align list.perm_comm List.perm_comm

#print List.Perm.swap' /-
theorem Perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y :: x :: l₁ ~ x :: y :: l₂ :=
  (swap _ _ _).trans ((p.cons _).cons _)
#align list.perm.swap' List.Perm.swap'
-/

attribute [trans] perm.trans

theorem Perm.eqv (α) : Equivalence (@Perm α) :=
  Equivalence.mk (@Perm α) (@Perm.refl α) (@Perm.symm α) (@Perm.trans α)
#align list.perm.eqv List.Perm.eqv

instance isSetoid (α) : Setoid (List α) :=
  Setoid.mk (@Perm α) (Perm.eqv α)
#align list.is_setoid List.isSetoid

#print List.Perm.subset /-
theorem Perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := fun a =>
  Perm.rec_on p (fun h => h)
    (fun x l₁ l₂ p₁ r₁ i => Or.elim i (fun ax => by simp [ax]) fun al₁ => Or.inr (r₁ al₁))
    (fun x y l ayxl =>
      Or.elim ayxl (fun ay => by simp [ay]) fun axl =>
        Or.elim axl (fun ax => by simp [ax]) fun al => Or.inr (Or.inr al))
    fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ ainl₁ => r₂ (r₁ ainl₁)
#align list.perm.subset List.Perm.subset
-/

#print List.Perm.mem_iff /-
theorem Perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
  Iff.intro (fun m => h.Subset m) fun m => h.symm.Subset m
#align list.perm.mem_iff List.Perm.mem_iff
-/

theorem Perm.append_right {l₁ l₂ : List α} (t₁ : List α) (p : l₁ ~ l₂) : l₁ ++ t₁ ~ l₂ ++ t₁ :=
  Perm.rec_on p (Perm.refl ([] ++ t₁)) (fun x l₁ l₂ p₁ r₁ => r₁.cons x) (fun x y l => swap x y _)
    fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ => r₁.trans r₂
#align list.perm.append_right List.Perm.append_right

theorem Perm.append_left {t₁ t₂ : List α} : ∀ l : List α, t₁ ~ t₂ → l ++ t₁ ~ l ++ t₂
  | [], p => p
  | x :: xs, p => (perm.append_left xs p).cons x
#align list.perm.append_left List.Perm.append_left

theorem Perm.append {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ++ t₁ ~ l₂ ++ t₂ :=
  (p₁.append_right t₁).trans (p₂.append_left l₂)
#align list.perm.append List.Perm.append

theorem Perm.append_cons (a : α) {h₁ h₂ t₁ t₂ : List α} (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) :
    h₁ ++ a :: t₁ ~ h₂ ++ a :: t₂ :=
  p₁.append (p₂.cons a)
#align list.perm.append_cons List.Perm.append_cons

#print List.perm_middle /-
@[simp]
theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁ ++ a :: l₂ ~ a :: (l₁ ++ l₂)
  | [], l₂ => Perm.refl _
  | b :: l₁, l₂ => ((@perm_middle l₁ l₂).cons _).trans (swap a b _)
#align list.perm_middle List.perm_middle
-/

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

#print List.Perm.length_eq /-
theorem Perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ :=
  Perm.rec_on p rfl (fun x l₁ l₂ p r => by simp [r]) (fun x y l => by simp)
    fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ => Eq.trans r₁ r₂
#align list.perm.length_eq List.Perm.length_eq
-/

#print List.Perm.eq_nil /-
theorem Perm.eq_nil {l : List α} (p : l ~ []) : l = [] :=
  eq_nil_of_length_eq_zero p.length_eq
#align list.perm.eq_nil List.Perm.eq_nil
-/

#print List.Perm.nil_eq /-
theorem Perm.nil_eq {l : List α} (p : [] ~ l) : [] = l :=
  p.symm.eq_nil.symm
#align list.perm.nil_eq List.Perm.nil_eq
-/

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
theorem perm_repeat {a : α} {n : ℕ} {l : List α} : l ~ repeat a n ↔ l = repeat a n :=
  ⟨fun p =>
    eq_repeat.2 ⟨p.length_eq.trans <| length_repeat _ _, fun b m => eq_of_mem_repeat <| p.Subset m⟩,
    fun h => h ▸ Perm.refl _⟩
#align list.perm_repeat List.perm_repeat

@[simp]
theorem repeat_perm {a : α} {n : ℕ} {l : List α} : repeat a n ~ l ↔ repeat a n = l :=
  (perm_comm.trans perm_repeat).trans eq_comm
#align list.repeat_perm List.repeat_perm

@[simp]
theorem perm_singleton {a : α} {l : List α} : l ~ [a] ↔ l = [a] :=
  @perm_repeat α a 1 l
#align list.perm_singleton List.perm_singleton

@[simp]
theorem singleton_perm {a : α} {l : List α} : [a] ~ l ↔ [a] = l :=
  @repeat_perm α a 1 l
#align list.singleton_perm List.singleton_perm

theorem Perm.eq_singleton {a : α} {l : List α} (p : l ~ [a]) : l = [a] :=
  perm_singleton.1 p
#align list.perm.eq_singleton List.Perm.eq_singleton

theorem Perm.singleton_eq {a : α} {l : List α} (p : [a] ~ l) : [a] = l :=
  p.symm.eq_singleton.symm
#align list.perm.singleton_eq List.Perm.singleton_eq

theorem singleton_perm_singleton {a b : α} : [a] ~ [b] ↔ a = b := by simp
#align list.singleton_perm_singleton List.singleton_perm_singleton

theorem perm_cons_erase [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : l ~ a :: l.erase a :=
  let ⟨l₁, l₂, _, e₁, e₂⟩ := exists_erase_eq h
  e₂.symm ▸ e₁.symm ▸ perm_middle
#align list.perm_cons_erase List.perm_cons_erase

/- warning: list.perm_induction_on -> List.perm_induction_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (List.{u1} α) -> (List.{u1} α) -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Perm.{u1} α l₁ l₂) -> (P (List.nil.{u1} α) (List.nil.{u1} α)) -> (forall (x : α) (l₁ : List.{u1} α) (l₂ : List.{u1} α), (List.Perm.{u1} α l₁ l₂) -> (P l₁ l₂) -> (P (List.cons.{u1} α x l₁) (List.cons.{u1} α x l₂))) -> (forall (x : α) (y : α) (l₁ : List.{u1} α) (l₂ : List.{u1} α), (List.Perm.{u1} α l₁ l₂) -> (P l₁ l₂) -> (P (List.cons.{u1} α y (List.cons.{u1} α x l₁)) (List.cons.{u1} α x (List.cons.{u1} α y l₂)))) -> (forall (l₁ : List.{u1} α) (l₂ : List.{u1} α) (l₃ : List.{u1} α), (List.Perm.{u1} α l₁ l₂) -> (List.Perm.{u1} α l₂ l₃) -> (P l₁ l₂) -> (P l₂ l₃) -> (P l₁ l₃)) -> (P l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} {P : forall (ᾰ : List.{u1} α) (ᾰ_1 : List.{u1} α), (List.Perm.{u1} α ᾰ ᾰ_1) -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u1} α} (p : List.Perm.{u1} α l₁ l₂), (P (List.nil.{u1} α) (List.nil.{u1} α) (List.Perm.nil.{u1} α)) -> (forall (x : α) (l₁ : List.{u1} α) (l₂ : List.{u1} α) (ᾰ : List.Perm.{u1} α l₁ l₂), (P l₁ l₂ ᾰ) -> (P (List.cons.{u1} α x l₁) (List.cons.{u1} α x l₂) (List.Perm.cons.{u1} α x l₁ l₂ ᾰ))) -> (forall (x : α) (y : α) (l₁ : List.{u1} α) (l₂ : List.{u1} α) (ᾰ : List.Perm.{u1} α l₁ l₂), (P l₁ l₂ ᾰ) -> (P (List.cons.{u1} α y (List.cons.{u1} α x l₁)) (List.cons.{u1} α x (List.cons.{u1} α y l₂)) (List.Perm.trans.{u1} α (List.cons.{u1} α y (List.cons.{u1} α x l₁)) (List.cons.{u1} α x (List.cons.{u1} α y l₁)) (List.cons.{u1} α x (List.cons.{u1} α y l₂)) (List.Perm.swap.{u1} α x y l₁) (List.Perm.cons.{u1} α x (List.cons.{u1} α y l₁) (List.cons.{u1} α y l₂) (List.Perm.cons.{u1} α y l₁ l₂ ᾰ))))) -> (forall (l₁ : List.{u1} α) (l₂ : List.{u1} α) (l₃ : List.{u1} α) (ᾰ : List.Perm.{u1} α l₁ l₂) (ᾰ_1 : List.Perm.{u1} α l₂ l₃), (P l₁ l₂ ᾰ) -> (P l₂ l₃ ᾰ_1) -> (P l₁ l₃ (List.Perm.trans.{u1} α l₁ l₂ l₃ ᾰ ᾰ_1))) -> (P l₁ l₂ p)
Case conversion may be inaccurate. Consider using '#align list.perm_induction_on List.perm_induction_onₓ'. -/
@[elab_as_elim]
theorem perm_induction_on {P : List α → List α → Prop} {l₁ l₂ : List α} (p : l₁ ~ l₂) (h₁ : P [] [])
    (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x :: l₁) (x :: l₂))
    (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y :: x :: l₁) (x :: y :: l₂))
    (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) : P l₁ l₂ :=
  have P_refl : ∀ l, P l l := fun l => List.recOn l h₁ fun x xs ih => h₂ x xs xs (Perm.refl xs) ih
  Perm.rec_on p h₁ h₂ (fun x y l => h₃ x y l l (Perm.refl l) (P_refl l)) h₄
#align list.perm_induction_on List.perm_induction_on

@[congr]
theorem Perm.filter_map (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    filterMap f l₁ ~ filterMap f l₂ :=
  by
  induction' p with x l₂ l₂' p IH x y l₂ l₂ m₂ r₂ p₁ p₂ IH₁ IH₂
  · simp
  · simp only [filter_map]
    cases' f x with a <;> simp [filter_map, IH, perm.cons]
  · simp only [filter_map]
    cases' f x with a <;> cases' f y with b <;> simp [filter_map, swap]
  · exact IH₁.trans IH₂
#align list.perm.filter_map List.Perm.filter_map

@[congr]
theorem Perm.map (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ :=
  filterMap_eq_map f ▸ p.filterMap _
#align list.perm.map List.Perm.map

theorem Perm.pmap {p : α → Prop} (f : ∀ a, p a → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) {H₁ H₂} :
    pmap f l₁ H₁ ~ pmap f l₂ H₂ :=
  by
  induction' p with x l₂ l₂' p IH x y l₂ l₂ m₂ r₂ p₁ p₂ IH₁ IH₂
  · simp
  · simp [IH, perm.cons]
  · simp [swap]
  · refine' IH₁.trans IH₂
    exact fun a m => H₂ a (p₂.subset m)
#align list.perm.pmap List.Perm.pmap

theorem Perm.filter (p : α → Prop) [DecidablePred p] {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    filter p l₁ ~ filter p l₂ := by rw [← filter_map_eq_filter] <;> apply s.filter_map _
#align list.perm.filter List.Perm.filter

theorem filter_append_perm (p : α → Prop) [DecidablePred p] (l : List α) :
    filter p l ++ filter (fun x => ¬p x) l ~ l :=
  by
  induction' l with x l ih
  · rfl
  · by_cases h : p x
    · simp only [h, filter_cons_of_pos, filter_cons_of_neg, not_true, not_false_iff, cons_append]
      exact ih.cons x
    · simp only [h, filter_cons_of_neg, not_false_iff, filter_cons_of_pos]
      refine' perm.trans _ (ih.cons x)
      exact perm_append_comm.trans (perm_append_comm.cons _)
#align list.filter_append_perm List.filter_append_perm

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (l₁' list.perm l₁) -/
theorem exists_perm_sublist {l₁ l₂ l₂' : List α} (s : l₁ <+ l₂) (p : l₂ ~ l₂') :
    ∃ (l₁' : _)(_ : l₁' ~ l₁), l₁' <+ l₂' :=
  by
  induction' p with x l₂ l₂' p IH x y l₂ l₂ m₂ r₂ p₁ p₂ IH₁ IH₂ generalizing l₁ s
  · exact ⟨[], eq_nil_of_sublist_nil s ▸ perm.refl _, nil_sublist _⟩
  · cases' s with _ _ _ s l₁ _ _ s
    ·
      exact
        let ⟨l₁', p', s'⟩ := IH s
        ⟨l₁', p', s'.cons _ _ _⟩
    ·
      exact
        let ⟨l₁', p', s'⟩ := IH s
        ⟨x :: l₁', p'.cons x, s'.cons2 _ _ _⟩
  · cases' s with _ _ _ s l₁ _ _ s <;> cases' s with _ _ _ s l₁ _ _ s
    · exact ⟨l₁, perm.refl _, (s.cons _ _ _).cons _ _ _⟩
    · exact ⟨x :: l₁, perm.refl _, (s.cons _ _ _).cons2 _ _ _⟩
    · exact ⟨y :: l₁, perm.refl _, (s.cons2 _ _ _).cons _ _ _⟩
    · exact ⟨x :: y :: l₁, perm.swap _ _ _, (s.cons2 _ _ _).cons2 _ _ _⟩
  ·
    exact
      let ⟨m₁, pm, sm⟩ := IH₁ s
      let ⟨r₁, pr, sr⟩ := IH₂ sm
      ⟨r₁, pr.trans pm, sr⟩
#align list.exists_perm_sublist List.exists_perm_sublist

theorem Perm.sizeof_eq_sizeof [SizeOf α] {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁.sizeof = l₂.sizeof :=
  by
  induction' h with hd l₁ l₂ h₁₂ h_sz₁₂ a b l l₁ l₂ l₃ h₁₂ h₂₃ h_sz₁₂ h_sz₂₃
  · rfl
  · simp only [List.sizeof, h_sz₁₂]
  · simp only [List.sizeof, add_left_comm]
  · simp only [h_sz₁₂, h_sz₂₃]
#align list.perm.sizeof_eq_sizeof List.Perm.sizeof_eq_sizeof

section Rel

open Relator

variable {γ : Type _} {δ : Type _} {r : α → β → Prop} {p : γ → δ → Prop}

-- mathport name: «expr ∘r »
local infixr:80 " ∘r " => Relation.Comp

theorem perm_comp_perm : (perm ∘r perm : List α → List α → Prop) = perm :=
  by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => perm.trans hab hba
  · exact fun h => ⟨a, perm.refl a, h⟩
#align list.perm_comp_perm List.perm_comp_perm

theorem perm_comp_forall₂ {l u v} (hlu : Perm l u) (huv : Forall₂ r u v) :
    (Forall₂ r ∘r perm) l v := by
  induction hlu generalizing v
  case nil => cases huv; exact ⟨[], forall₂.nil, perm.nil⟩
  case cons a l u hlu ih =>
    cases' huv with _ b _ v hab huv'
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨b :: l₂, forall₂.cons hab h₁₂, h₂₃.cons _⟩
  case swap a₁ a₂ l₁ l₂ h₂₃ =>
    cases' h₂₃ with _ b₁ _ l₂ h₁ hr_₂₃
    cases' hr_₂₃ with _ b₂ _ l₂ h₂ h₁₂
    exact ⟨b₂ :: b₁ :: l₂, forall₂.cons h₂ (forall₂.cons h₁ h₁₂), perm.swap _ _ _⟩
  case
    trans la₁ la₂ la₃ _ _ ih₁ ih₂ =>
    rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩
    exact ⟨lb₁, hab₁, perm.trans h₁₂ h₂₃⟩
#align list.perm_comp_forall₂ List.perm_comp_forall₂

theorem forall₂_comp_perm_eq_perm_comp_forall₂ : Forall₂ r ∘r perm = perm ∘r Forall₂ r :=
  by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃
#align list.forall₂_comp_perm_eq_perm_comp_forall₂ List.forall₂_comp_perm_eq_perm_comp_forall₂

theorem rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ Implies) Perm Perm :=
  fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨c', hbc, hcb⟩, hbd⟩ := this
  have : b' = b := right_unique_forall₂' hr hcb hbc
  this ▸ hbd
#align list.rel_perm_imp List.rel_perm_imp

theorem rel_perm (hr : BiUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm :=
  fun a b hab c d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)
#align list.rel_perm List.rel_perm

end Rel

section Subperm

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (l list.perm l₁) -/
/-- `subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
  a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
  multiplicities of elements, and is used for the `≤` relation on multisets. -/
def Subperm (l₁ l₂ : List α) : Prop :=
  ∃ (l : _)(_ : l ~ l₁), l <+ l₂
#align list.subperm List.Subperm

-- mathport name: «expr <+~ »
infixl:50 " <+~ " => Subperm

theorem nil_subperm {l : List α} : [] <+~ l :=
  ⟨[], Perm.nil, by simp⟩
#align list.nil_subperm List.nil_subperm

theorem Perm.subperm_left {l l₁ l₂ : List α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ :=
  suffices ∀ {l₁ l₂ : List α}, l₁ ~ l₂ → l <+~ l₁ → l <+~ l₂ from ⟨this p, this p.symm⟩
  fun l₁ l₂ p ⟨u, pu, su⟩ =>
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
  (Perm.refl _).Subperm
#align list.subperm.refl List.Subperm.refl

@[trans]
theorem Subperm.trans {l₁ l₂ l₃ : List α} : l₁ <+~ l₂ → l₂ <+~ l₃ → l₁ <+~ l₃
  | s, ⟨l₂', p₂, s₂⟩ =>
    let ⟨l₁', p₁, s₁⟩ := p₂.subperm_left.2 s
    ⟨l₁', p₁, s₁.trans s₂⟩
#align list.subperm.trans List.Subperm.trans

theorem Subperm.length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₁ ≤ length l₂
  | ⟨l, p, s⟩ => p.length_eq ▸ s.length_le
#align list.subperm.length_le List.Subperm.length_le

theorem Subperm.perm_of_length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂
  | ⟨l, p, s⟩, h => (s.eq_of_length_le <| p.symm.length_eq ▸ h) ▸ p.symm
#align list.subperm.perm_of_length_le List.Subperm.perm_of_length_le

theorem Subperm.antisymm {l₁ l₂ : List α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
  h₁.perm_of_length_le h₂.length_le
#align list.subperm.antisymm List.Subperm.antisymm

theorem Subperm.subset {l₁ l₂ : List α} : l₁ <+~ l₂ → l₁ ⊆ l₂
  | ⟨l, p, s⟩ => Subset.trans p.symm.Subset s.Subset
#align list.subperm.subset List.Subperm.subset

theorem Subperm.filter (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l <+~ l') :
    filter p l <+~ filter p l' := by
  obtain ⟨xs, hp, h⟩ := h
  exact ⟨_, hp.filter p, h.filter p⟩
#align list.subperm.filter List.Subperm.filter

end Subperm

theorem Sublist.exists_perm_append : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → ∃ l, l₂ ~ l₁ ++ l
  | _, _, sublist.slnil => ⟨nil, Perm.refl _⟩
  | _, _, sublist.cons l₁ l₂ a s =>
    let ⟨l, p⟩ := sublist.exists_perm_append s
    ⟨a :: l, (p.cons a).trans perm_middle.symm⟩
  | _, _, sublist.cons2 l₁ l₂ a s =>
    let ⟨l, p⟩ := sublist.exists_perm_append s
    ⟨l, p.cons a⟩
#align list.sublist.exists_perm_append List.Sublist.exists_perm_append

theorem Perm.countp_eq (p : α → Prop) [DecidablePred p] {l₁ l₂ : List α} (s : l₁ ~ l₂) :
    countp p l₁ = countp p l₂ := by
  rw [countp_eq_length_filter, countp_eq_length_filter] <;> exact (s.filter _).length_eq
#align list.perm.countp_eq List.Perm.countp_eq

theorem Subperm.countp_le (p : α → Prop) [DecidablePred p] {l₁ l₂ : List α} :
    l₁ <+~ l₂ → countp p l₁ ≤ countp p l₂
  | ⟨l, p', s⟩ => p'.countp_eq p ▸ s.countp_le p
#align list.subperm.countp_le List.Subperm.countp_le

theorem Perm.countp_congr (s : l₁ ~ l₂) {p p' : α → Prop} [DecidablePred p] [DecidablePred p']
    (hp : ∀ x ∈ l₁, p x = p' x) : l₁.countp p = l₂.countp p' :=
  by
  rw [← s.countp_eq p']
  clear s
  induction' l₁ with y s hs
  · rfl
  · simp only [mem_cons_iff, forall_eq_or_imp] at hp
    simp only [countp_cons, hs hp.2, hp.1]
#align list.perm.countp_congr List.Perm.countp_congr

theorem countp_eq_countp_filter_add (l : List α) (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] : l.countp p = (l.filter q).countp p + (l.filter fun a => ¬q a).countp p :=
  by
  rw [← countp_append]
  exact perm.countp_eq _ (filter_append_perm _ _).symm
#align list.countp_eq_countp_filter_add List.countp_eq_countp_filter_add

theorem Perm.count_eq [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) (a) :
    count a l₁ = count a l₂ :=
  p.countp_eq _
#align list.perm.count_eq List.Perm.count_eq

theorem Subperm.count_le [DecidableEq α] {l₁ l₂ : List α} (s : l₁ <+~ l₂) (a) :
    count a l₁ ≤ count a l₂ :=
  s.countp_le _
#align list.subperm.count_le List.Subperm.count_le

theorem Perm.foldl_eq' {f : β → α → β} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    (∀ x ∈ l₁, ∀ y ∈ l₁, ∀ (z), f (f z x) y = f (f z y) x) → ∀ b, foldl f b l₁ = foldl f b l₂ :=
  perm_induction_on p (fun H b => rfl)
    (fun x t₁ t₂ p r H b => r (fun x hx y hy => H _ (Or.inr hx) _ (Or.inr hy)) _)
    (fun x y t₁ t₂ p r H b => by
      simp only [foldl]
      rw [H x (Or.inr <| Or.inl rfl) y (Or.inl rfl)]
      exact r (fun x hx y hy => H _ (Or.inr <| Or.inr hx) _ (Or.inr <| Or.inr hy)) _)
    fun t₁ t₂ t₃ p₁ p₂ r₁ r₂ H b =>
    Eq.trans (r₁ H b) (r₂ (fun x hx y hy => H _ (p₁.symm.Subset hx) _ (p₁.symm.Subset hy)) b)
#align list.perm.foldl_eq' List.Perm.foldl_eq'

theorem Perm.foldl_eq {f : β → α → β} {l₁ l₂ : List α} (rcomm : RightCommutative f) (p : l₁ ~ l₂) :
    ∀ b, foldl f b l₁ = foldl f b l₂ :=
  p.foldl_eq' fun x hx y hy z => rcomm z x y
#align list.perm.foldl_eq List.Perm.foldl_eq

theorem Perm.foldr_eq {f : α → β → β} {l₁ l₂ : List α} (lcomm : LeftCommutative f) (p : l₁ ~ l₂) :
    ∀ b, foldr f b l₁ = foldr f b l₂ :=
  perm_induction_on p (fun b => rfl) (fun x t₁ t₂ p r b => by simp <;> rw [r b])
    (fun x y t₁ t₂ p r b => by simp <;> rw [lcomm, r b]) fun t₁ t₂ t₃ p₁ p₂ r₁ r₂ a =>
    Eq.trans (r₁ a) (r₂ a)
#align list.perm.foldr_eq List.Perm.foldr_eq

theorem Perm.rec_heq {β : List α → Sort _} {f : ∀ a l, β l → β (a :: l)} {b : β []} {l l' : List α}
    (hl : Perm l l') (f_congr : ∀ {a l l' b b'}, Perm l l' → HEq b b' → HEq (f a l b) (f a l' b'))
    (f_swap : ∀ {a a' l b}, HEq (f a (a' :: l) (f a' l b)) (f a' (a :: l) (f a l b))) :
    HEq (@List.rec α β b f l) (@List.rec α β b f l') :=
  by
  induction hl
  case nil => rfl
  case cons a l l' h ih => exact f_congr h ih
  case swap a a' l => exact f_swap
  case trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ => exact HEq.trans ih₁ ih₂
#align list.perm.rec_heq List.Perm.rec_heq

section

variable {op : α → α → α} [IsAssociative α op] [IsCommutative α op]

-- mathport name: op
local notation a " * " b => op a b

-- mathport name: foldl
local notation l " <*> " a => foldl op a l

theorem Perm.fold_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : (l₁ <*> a) = l₂ <*> a :=
  h.foldl_eq (right_comm _ IsCommutative.comm IsAssociative.assoc) _
#align list.perm.fold_op_eq List.Perm.fold_op_eq

end

section CommMonoid

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements. -/
@[to_additive
      "If elements of a list additively commute with each other, then their sum does not\ndepend on the order of elements."]
theorem Perm.prod_eq' [Monoid α] {l₁ l₂ : List α} (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute) :
    l₁.Prod = l₂.Prod :=
  h.foldl_eq'
    ((Pairwise.forall_of_forall (fun x y h z => (h z).symm) fun x hx z => rfl) <|
      hc.imp fun x y h z => by simp only [mul_assoc, h.eq])
    _
#align list.perm.prod_eq' List.Perm.prod_eq'

variable [CommMonoid α]

@[to_additive]
theorem Perm.prod_eq {l₁ l₂ : List α} (h : Perm l₁ l₂) : prod l₁ = prod l₂ :=
  h.fold_op_eq
#align list.perm.prod_eq List.Perm.prod_eq

@[to_additive]
theorem prod_reverse (l : List α) : prod l.reverse = prod l :=
  (reverse_perm l).prod_eq
#align list.prod_reverse List.prod_reverse

end CommMonoid

#print List.perm_inv_core /-
theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : List α} :
    l₁ ++ a :: r₁ ~ l₂ ++ a :: r₂ → l₁ ++ r₁ ~ l₂ ++ r₂ :=
  by
  generalize e₁ : l₁ ++ a :: r₁ = s₁; generalize e₂ : l₂ ++ a :: r₂ = s₂
  intro p; revert l₁ l₂ r₁ r₂ e₁ e₂
  refine'
      perm_induction_on p _ (fun x t₁ t₂ p IH => _) (fun x y t₁ t₂ p IH => _)
        fun t₁ t₂ t₃ p₁ p₂ IH₁ IH₂ => _ <;>
    intro l₁ l₂ r₁ r₂ e₁ e₂
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
      exact (IH rfl rfl).cons y
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
      exact (IH rfl rfl).swap' _ _
  · substs t₁ t₃
    have : a ∈ t₂ := p₁.subset (by simp)
    rcases mem_split this with ⟨l₂, r₂, e₂⟩
    subst t₂
    exact (IH₁ rfl rfl).trans (IH₂ rfl rfl)
#align list.perm_inv_core List.perm_inv_core
-/

#print List.Perm.cons_inv /-
theorem Perm.cons_inv {a : α} {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ → l₁ ~ l₂ :=
  @perm_inv_core _ _ [] [] _ _
#align list.perm.cons_inv List.Perm.cons_inv
-/

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

theorem perm_option_to_list {o₁ o₂ : Option α} : o₁.toList ~ o₂.toList ↔ o₁ = o₂ :=
  by
  refine' ⟨fun p => _, fun e => e ▸ perm.refl _⟩
  cases' o₁ with a <;> cases' o₂ with b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)
#align list.perm_option_to_list List.perm_option_to_list

theorem subperm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ <+~ a :: l₂ ↔ l₁ <+~ l₂ :=
  ⟨fun ⟨l, p, s⟩ => by
    cases' s with _ _ _ s' u _ _ s'
    · exact (p.subperm_left.2 <| (sublist_cons _ _).Subperm).trans s'.subperm
    · exact ⟨u, p.cons_inv, s'⟩, fun ⟨l, p, s⟩ => ⟨a :: l, p.cons a, s.cons2 _ _ _⟩⟩
#align list.subperm_cons List.subperm_cons

alias subperm_cons ↔ subperm.of_cons subperm.cons

attribute [protected] subperm.cons

theorem cons_subperm_of_mem {a : α} {l₁ l₂ : List α} (d₁ : Nodup l₁) (h₁ : a ∉ l₁) (h₂ : a ∈ l₂)
    (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ :=
  by
  rcases s with ⟨l, p, s⟩
  induction s generalizing l₁
  case slnil => cases h₂
  case cons r₁ r₂ b s' ih =>
    simp at h₂
    cases' h₂ with e m
    · subst b
      exact ⟨a :: r₁, p.cons a, s'.cons2 _ _ _⟩
    · rcases ih m d₁ h₁ p with ⟨t, p', s'⟩
      exact ⟨t, p', s'.cons _ _ _⟩
  case
    cons2 r₁ r₂ b s' ih =>
    have bm : b ∈ l₁ := p.subset <| mem_cons_self _ _
    have am : a ∈ r₂ := h₂.resolve_left fun e => h₁ <| e.symm ▸ bm
    rcases mem_split bm with ⟨t₁, t₂, rfl⟩
    have st : t₁ ++ t₂ <+ t₁ ++ b :: t₂ := by simp
    rcases ih am (d₁.sublist st) (mt (fun x => st.subset x) h₁)
        (perm.cons_inv <| p.trans perm_middle) with
      ⟨t, p', s'⟩
    exact
      ⟨b :: t, (p'.cons b).trans <| (swap _ _ _).trans (perm_middle.symm.cons a), s'.cons2 _ _ _⟩
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
  | ⟨l, p, s⟩, h =>
    by
    suffices length l < length l₂ → ∃ a : α, a :: l <+~ l₂ from
      (this <| p.symm.length_eq ▸ h).imp fun a => (p.cons a).subperm_right.1
    clear subperm.exists_of_length_lt p h l₁; rename' l₂ => u
    induction' s with l₁ l₂ a s IH _ _ b s IH <;> intro h
    · cases h
    · cases' lt_or_eq_of_le (Nat.le_of_lt_succ h : length l₁ ≤ length l₂) with h h
      · exact (IH h).imp fun a s => s.trans (sublist_cons _ _).Subperm
      · exact ⟨a, s.eq_of_length h ▸ subperm.refl _⟩
    ·
      exact
        (IH <| Nat.lt_of_succ_lt_succ h).imp fun a s =>
          (swap _ _ _).subperm_right.1 <| (subperm_cons _).2 s
#align list.subperm.exists_of_length_lt List.Subperm.exists_of_length_lt

protected theorem Nodup.subperm (d : Nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ :=
  by
  induction' d with a l₁' h d IH
  · exact ⟨nil, perm.nil, nil_sublist _⟩
  · cases' forall_mem_cons.1 H with H₁ H₂
    simp at h
    exact cons_subperm_of_mem d h H₁ (IH H₂)
#align list.nodup.subperm List.Nodup.subperm

theorem perm_ext {l₁ l₂ : List α} (d₁ : Nodup l₁) (d₂ : Nodup l₂) :
    l₁ ~ l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂ :=
  ⟨fun p a => p.mem_iff, fun H =>
    (d₁.Subperm fun a => (H a).1).antisymm <| d₂.Subperm fun a => (H a).2⟩
#align list.perm_ext List.perm_ext

theorem Nodup.sublist_ext {l₁ l₂ l : List α} (d : Nodup l) (s₁ : l₁ <+ l) (s₂ : l₂ <+ l) :
    l₁ ~ l₂ ↔ l₁ = l₂ :=
  ⟨fun h => by
    induction' s₂ with l₂ l a s₂ IH l₂ l a s₂ IH generalizing l₁
    · exact h.eq_nil
    · simp at d
      cases' s₁ with _ _ _ s₁ l₁ _ _ s₁
      · exact IH d.2 s₁ h
      · apply d.1.elim
        exact subperm.subset ⟨_, h.symm, s₂⟩ (mem_cons_self _ _)
    · simp at d
      cases' s₁ with _ _ _ s₁ l₁ _ _ s₁
      · apply d.1.elim
        exact subperm.subset ⟨_, h, s₁⟩ (mem_cons_self _ _)
      · rw [IH d.2 s₁ h.cons_inv], fun h => by rw [h]⟩
#align list.nodup.sublist_ext List.Nodup.sublist_ext

section

variable [DecidableEq α]

-- attribute [congr]
theorem Perm.erase (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.erase a ~ l₂.erase a :=
  if h₁ : a ∈ l₁ then
    have h₂ : a ∈ l₂ := p.Subset h₁
    perm.cons_inv <| (perm_cons_erase h₁).symm.trans <| p.trans (perm_cons_erase h₂)
  else by
    have h₂ : a ∉ l₂ := mt p.mem_iff.2 h₁
    rw [erase_of_not_mem h₁, erase_of_not_mem h₂] <;> exact p
#align list.perm.erase List.Perm.erase

theorem subperm_cons_erase (a : α) (l : List α) : l <+~ a :: l.erase a :=
  by
  by_cases h : a ∈ l
  · exact (perm_cons_erase h).Subperm
  · rw [erase_of_not_mem h]
    exact (sublist_cons _ _).Subperm
#align list.subperm_cons_erase List.subperm_cons_erase

theorem erase_subperm (a : α) (l : List α) : l.erase a <+~ l :=
  (erase_sublist _ _).Subperm
#align list.erase_subperm List.erase_subperm

theorem Subperm.erase {l₁ l₂ : List α} (a : α) (h : l₁ <+~ l₂) : l₁.erase a <+~ l₂.erase a :=
  let ⟨l, hp, hs⟩ := h
  ⟨l.erase a, hp.erase _, hs.erase _⟩
#align list.subperm.erase List.Subperm.erase

theorem Perm.diff_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) : l₁.diff t ~ l₂.diff t := by
  induction t generalizing l₁ l₂ h <;> simp [*, perm.erase]
#align list.perm.diff_right List.Perm.diff_right

theorem Perm.diff_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l.diff t₁ = l.diff t₂ := by
  induction h generalizing l <;>
    first |simp [*, perm.erase, erase_comm]|exact (ih_1 _).trans (ih_2 _)
#align list.perm.diff_left List.Perm.diff_left

theorem Perm.diff {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) : l₁.diff t₁ ~ l₂.diff t₂ :=
  ht.diff_left l₂ ▸ hl.diff_right _
#align list.perm.diff List.Perm.diff

theorem Subperm.diff_right {l₁ l₂ : List α} (h : l₁ <+~ l₂) (t : List α) :
    l₁.diff t <+~ l₂.diff t := by induction t generalizing l₁ l₂ h <;> simp [*, subperm.erase]
#align list.subperm.diff_right List.Subperm.diff_right

theorem erase_cons_subperm_cons_erase (a b : α) (l : List α) :
    (a :: l).erase b <+~ a :: l.erase b :=
  by
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
  subperm_cons_diff.Subset
#align list.subset_cons_diff List.subset_cons_diff

theorem Perm.bag_inter_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) :
    l₁.bagInter t ~ l₂.bagInter t :=
  by
  induction' h with x _ _ _ _ x y _ _ _ _ _ _ ih_1 ih_2 generalizing t; · simp
  · by_cases x ∈ t <;> simp [*, perm.cons]
  · by_cases x = y
    · simp [h]
    by_cases xt : x ∈ t <;> by_cases yt : y ∈ t
    · simp [xt, yt, mem_erase_of_ne h, mem_erase_of_ne (Ne.symm h), erase_comm, swap]
    · simp [xt, yt, mt mem_of_mem_erase, perm.cons]
    · simp [xt, yt, mt mem_of_mem_erase, perm.cons]
    · simp [xt, yt]
  · exact (ih_1 _).trans (ih_2 _)
#align list.perm.bag_inter_right List.Perm.bag_inter_right

theorem Perm.bag_inter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) :
    l.bagInter t₁ = l.bagInter t₂ :=
  by
  induction' l with a l IH generalizing t₁ t₂ p; · simp
  by_cases a ∈ t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]
#align list.perm.bag_inter_left List.Perm.bag_inter_left

theorem Perm.bag_inter {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
    l₁.bagInter t₁ ~ l₂.bagInter t₂ :=
  ht.bag_inter_left l₂ ▸ hl.bag_inter_right _
#align list.perm.bag_inter List.Perm.bag_inter

theorem cons_perm_iff_perm_erase {a : α} {l₁ l₂ : List α} :
    a :: l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a :=
  ⟨fun h =>
    have : a ∈ l₂ := h.Subset (mem_cons_self a l₁)
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
    · have : a ∈ l₂ := count_pos.1 (by rw [← H] <;> simp <;> apply Nat.succ_pos)
      refine' ((IH fun b => _).cons a).trans (perm_cons_erase this).symm
      specialize H b
      rw [(perm_cons_erase this).count_eq] at H
      by_cases b = a <;> simp [h] at H⊢ <;> assumption⟩
#align list.perm_iff_count List.perm_iff_count

theorem Subperm.cons_right {α : Type _} {l l' : List α} (x : α) (h : l <+~ l') : l <+~ x :: l' :=
  h.trans (sublist_cons x l').Subperm
#align list.subperm.cons_right List.Subperm.cons_right

/-- The list version of `add_tsub_cancel_of_le` for multisets. -/
theorem subperm_append_diff_self_of_count_le {l₁ l₂ : List α}
    (h : ∀ x ∈ l₁, count x l₁ ≤ count x l₂) : l₁ ++ l₂.diff l₁ ~ l₂ :=
  by
  induction' l₁ with hd tl IH generalizing l₂
  · simp
  · have : hd ∈ l₂ := by
      rw [← count_pos]
      exact lt_of_lt_of_le (count_pos.mpr (mem_cons_self _ _)) (h hd (mem_cons_self _ _))
    replace this : l₂ ~ hd :: l₂.erase hd := perm_cons_erase this
    refine' perm.trans _ this.symm
    rw [cons_append, diff_cons, perm_cons]
    refine' IH fun x hx => _
    specialize h x (mem_cons_of_mem _ hx)
    rw [perm_iff_count.mp this] at h
    by_cases hx : x = hd
    · subst hd
      simpa [Nat.succ_le_succ_iff] using h
    · simpa [hx] using h
#align list.subperm_append_diff_self_of_count_le List.subperm_append_diff_self_of_count_le

/-- The list version of `multiset.le_iff_count`. -/
theorem subperm_ext_iff {l₁ l₂ : List α} : l₁ <+~ l₂ ↔ ∀ x ∈ l₁, count x l₁ ≤ count x l₂ :=
  by
  refine' ⟨fun h x hx => subperm.count_le h x, fun h => _⟩
  suffices l₁ <+~ l₂.diff l₁ ++ l₁
    by
    refine' this.trans (perm.subperm _)
    exact perm_append_comm.trans (subperm_append_diff_self_of_count_le h)
  convert (subperm_append_right _).mpr nil_subperm using 1
#align list.subperm_ext_iff List.subperm_ext_iff

instance decidableSubperm : DecidableRel ((· <+~ ·) : List α → List α → Prop) := fun l₁ l₂ =>
  decidable_of_iff _ List.subperm_ext_iff.symm
#align list.decidable_subperm List.decidableSubperm

@[simp]
theorem subperm_singleton_iff {α} {l : List α} {a : α} : [a] <+~ l ↔ a ∈ l :=
  ⟨fun ⟨s, hla, h⟩ => by rwa [perm_singleton.mp hla, singleton_sublist] at h, fun h =>
    ⟨[a], Perm.refl _, singleton_sublist.mpr h⟩⟩
#align list.subperm_singleton_iff List.subperm_singleton_iff

theorem Subperm.cons_left {l₁ l₂ : List α} (h : l₁ <+~ l₂) (x : α) (hx : count x l₁ < count x l₂) :
    x :: l₁ <+~ l₂ := by
  rw [subperm_ext_iff] at h⊢
  intro y hy
  by_cases hy' : y = x
  · subst x
    simpa using Nat.succ_le_of_lt hx
  · rw [count_cons_of_ne hy']
    refine' h y _
    simpa [hy'] using hy
#align list.subperm.cons_left List.Subperm.cons_left

instance decidablePerm : ∀ l₁ l₂ : List α, Decidable (l₁ ~ l₂)
  | [], [] => is_true <| Perm.refl _
  | [], b :: l₂ => is_false fun h => by have := h.nil_eq <;> contradiction
  | a :: l₁, l₂ =>
    haveI := decidable_perm l₁ (l₂.erase a)
    decidable_of_iff' _ cons_perm_iff_perm_erase
#align list.decidable_perm List.decidablePerm

-- @[congr]
theorem Perm.dedup {l₁ l₂ : List α} (p : l₁ ~ l₂) : dedup l₁ ~ dedup l₂ :=
  perm_iff_count.2 fun a =>
    if h : a ∈ l₁ then by simp [nodup_dedup, h, p.subset h] else by simp [h, mt p.mem_iff.2 h]
#align list.perm.dedup List.Perm.dedup

-- attribute [congr]
theorem Perm.insert (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : insert a l₁ ~ insert a l₂ :=
  if h : a ∈ l₁ then by simpa [h, p.subset h] using p
  else by simpa [h, mt p.mem_iff.2 h] using p.cons a
#align list.perm.insert List.Perm.insert

theorem perm_insert_swap (x y : α) (l : List α) : insert x (insert y l) ~ insert y (insert x l) :=
  by
  by_cases xl : x ∈ l <;> by_cases yl : y ∈ l <;> simp [xl, yl]
  by_cases xy : x = y; · simp [xy]
  simp [not_mem_cons_of_ne_of_not_mem xy xl, not_mem_cons_of_ne_of_not_mem (Ne.symm xy) yl]
  constructor
#align list.perm_insert_swap List.perm_insert_swap

theorem perm_insert_nth {α} (x : α) (l : List α) {n} (h : n ≤ l.length) :
    insertNth n x l ~ x :: l := by
  induction l generalizing n
  · cases n
    rfl
    cases h
  cases n
  · simp [insert_nth]
  · simp only [insert_nth, modify_nth_tail]
    trans
    · apply perm.cons
      apply l_ih
      apply Nat.le_of_succ_le_succ h
    · apply perm.swap
#align list.perm_insert_nth List.perm_insert_nth

theorem Perm.union_right {l₁ l₂ : List α} (t₁ : List α) (h : l₁ ~ l₂) : l₁ ∪ t₁ ~ l₂ ∪ t₁ :=
  by
  induction' h with a _ _ _ ih _ _ _ _ _ _ _ _ ih_1 ih_2 <;> try simp
  · exact ih.insert a
  · apply perm_insert_swap
  · exact ih_1.trans ih_2
#align list.perm.union_right List.Perm.union_right

theorem Perm.union_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ := by
  induction l <;> simp [*, perm.insert]
#align list.perm.union_left List.Perm.union_left

-- @[congr]
theorem Perm.union {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
  (p₁.union_right t₁).trans (p₂.union_left l₂)
#align list.perm.union List.Perm.union

theorem Perm.inter_right {l₁ l₂ : List α} (t₁ : List α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ :=
  Perm.filter _
#align list.perm.inter_right List.Perm.inter_right

theorem Perm.inter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ :=
  filter_congr' fun a _ => p.mem_iff
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
      trans
      · apply perm.cons _ l_ih
      change [x] ++ xs ∩ t₁ ++ xs ∩ t₂ ~ xs ∩ t₁ ++ ([x] ++ xs ∩ t₂)
      rw [← List.append_assoc]
      solve_by_elim [perm.append_right, perm_append_comm]
    · simp [*]
#align list.perm.inter_append List.Perm.inter_append

end

#print List.Perm.pairwise_iff /-
theorem Perm.pairwise_iff {R : α → α → Prop} (S : Symmetric R) :
    ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), Pairwise R l₁ ↔ Pairwise R l₂ :=
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise R l₁ → Pairwise R l₂ from fun l₁ l₂ p =>
    ⟨this p, this p.symm⟩
  fun l₁ l₂ p d => by
  induction' d with a l₁ h d IH generalizing l₂
  · rw [← p.nil_eq]
    constructor
  · have : a ∈ l₂ := p.subset (mem_cons_self _ _)
    rcases mem_split this with ⟨s₂, t₂, rfl⟩
    have p' := (p.trans perm_middle).cons_inv
    refine' (pairwise_middle S).2 (pairwise_cons.2 ⟨fun b m => _, IH _ p'⟩)
    exact h _ (p'.symm.subset m)
#align list.perm.pairwise_iff List.Perm.pairwise_iff
-/

theorem Pairwise.perm {R : α → α → Prop} {l l' : List α} (hR : l.Pairwise R) (hl : l ~ l')
    (hsymm : Symmetric R) : l'.Pairwise R :=
  (hl.pairwise_iff hsymm).mp hR
#align list.pairwise.perm List.Pairwise.perm

theorem Perm.pairwise {R : α → α → Prop} {l l' : List α} (hl : l ~ l') (hR : l.Pairwise R)
    (hsymm : Symmetric R) : l'.Pairwise R :=
  hR.Perm hl hsymm
#align list.perm.pairwise List.Perm.pairwise

#print List.Perm.nodup_iff /-
theorem Perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (Nodup l₁ ↔ Nodup l₂) :=
  perm.pairwise_iff <| @Ne.symm α
#align list.perm.nodup_iff List.Perm.nodup_iff
-/

theorem Perm.join {l₁ l₂ : List (List α)} (h : l₁ ~ l₂) : l₁.join ~ l₂.join :=
  Perm.rec_on h (Perm.refl _) (fun x xs₁ xs₂ hxs ih => ih.append_left x)
    (fun x₁ x₂ xs => by simpa only [join, append_assoc] using perm_append_comm.append_right _)
    fun xs₁ xs₂ xs₃ h₁₂ h₂₃ => Perm.trans
#align list.perm.join List.Perm.join

theorem Perm.bind_right {l₁ l₂ : List α} (f : α → List β) (p : l₁ ~ l₂) : l₁.bind f ~ l₂.bind f :=
  (p.map _).join
#align list.perm.bind_right List.Perm.bind_right

theorem Perm.join_congr :
    ∀ {l₁ l₂ : List (List α)} (h : List.Forall₂ (· ~ ·) l₁ l₂), l₁.join ~ l₂.join
  | _, _, forall₂.nil => Perm.refl _
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => h₁.append (perm.join_congr h₂)
#align list.perm.join_congr List.Perm.join_congr

theorem Perm.bind_left (l : List α) {f g : α → List β} (h : ∀ a ∈ l, f a ~ g a) :
    l.bind f ~ l.bind g :=
  perm.join_congr <| by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]
#align list.perm.bind_left List.Perm.bind_left

theorem bind_append_perm (l : List α) (f g : α → List β) :
    l.bind f ++ l.bind g ~ l.bind fun x => f x ++ g x :=
  by
  induction' l with a l IH <;> simp
  refine' (perm.trans _ (IH.append_left _)).append_left _
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
  (Perm.bind_left _) fun a ha => p.map _
#align list.perm.product_left List.Perm.product_left

@[congr]
theorem Perm.product {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    product l₁ t₁ ~ product l₂ t₂ :=
  (p₁.product_right t₁).trans (p₂.product_left l₂)
#align list.perm.product List.Perm.product

theorem perm_lookmap (f : α → Option α) {l₁ l₂ : List α}
    (H : Pairwise (fun a b => ∀ c ∈ f a, ∀ d ∈ f b, a = b ∧ c = d) l₁) (p : l₁ ~ l₂) :
    lookmap f l₁ ~ lookmap f l₂ :=
  by
  let F a b := ∀ c ∈ f a, ∀ d ∈ f b, a = b ∧ c = d
  change Pairwise F l₁ at H
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂; · simp
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
      rcases(pairwise_cons.1 H).1 _ (Or.inl rfl) _ h₂ _ h₁ with ⟨rfl, rfl⟩
      rfl
  · refine' (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H))
    exact fun a b h c h₁ d h₂ => (h d h₂ c h₁).imp Eq.symm Eq.symm
#align list.perm_lookmap List.perm_lookmap

theorem Perm.erasep (f : α → Prop) [DecidablePred f] {l₁ l₂ : List α}
    (H : Pairwise (fun a b => f a → f b → False) l₁) (p : l₁ ~ l₂) : eraseP f l₁ ~ eraseP f l₂ :=
  by
  let F a b := f a → f b → False
  change Pairwise F l₁ at H
  induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂; · simp
  · by_cases h : f a
    · simp [h, p]
    · simp [h]
      exact IH (pairwise_cons.1 H).2
  · by_cases h₁ : f a <;> by_cases h₂ : f b <;> simp [h₁, h₂]
    · cases (pairwise_cons.1 H).1 _ (Or.inl rfl) h₂ h₁
    · apply swap
  · refine' (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H))
    exact fun a b h h₁ h₂ => h h₂ h₁
#align list.perm.erasep List.Perm.erasep

theorem Perm.take_inter {α} [DecidableEq α] {xs ys : List α} (n : ℕ) (h : xs ~ ys) (h' : ys.Nodup) :
    xs.take n ~ ys.inter (xs.take n) :=
  by
  simp only [List.inter] at *
  induction h generalizing n
  case nil n => simp only [not_mem_nil, filter_false, take_nil]
  case
    cons h_x h_l₁ h_l₂ h_a h_ih n =>
    cases n <;>
      simp only [mem_cons_iff, true_or_iff, eq_self_iff_true, filter_cons_of_pos, perm_cons, take,
        not_mem_nil, filter_false]
    cases' h' with _ _ h₁ h₂
    convert h_ih h₂ n using 1
    apply filter_congr'
    introv h; simp only [(h₁ x h).symm, false_or_iff]
  case swap h_x h_y h_l n =>
    cases' h' with _ _ h₁ h₂
    cases' h₂ with _ _ h₂ h₃
    have := h₁ _ (Or.inl rfl)
    cases n <;> simp only [mem_cons_iff, not_mem_nil, filter_false, take]
    cases n <;>
      simp only [mem_cons_iff, false_or_iff, true_or_iff, filter, *, Nat.zero_eq, if_true,
        not_mem_nil, eq_self_iff_true, or_false_iff, if_false, perm_cons, take]
    · rw [filter_eq_nil.2]
      intros
      solve_by_elim [Ne.symm]
    · convert perm.swap _ _ _
      rw [@filter_congr' _ _ (· ∈ take n h_l)]
      · clear h₁
        induction n generalizing h_l
        · simp
        cases h_l <;>
          simp only [mem_cons_iff, true_or_iff, eq_self_iff_true, filter_cons_of_pos, true_and_iff,
            take, not_mem_nil, filter_false, take_nil]
        cases' h₃ with _ _ h₃ h₄
        rwa [@filter_congr' _ _ (· ∈ take n_n h_l_tl), n_ih]
        · introv h
          apply h₂ _ (Or.inr h)
        · introv h
          simp only [(h₃ x h).symm, false_or_iff]
      · introv h
        simp only [(h₂ x h).symm, (h₁ x (Or.inr h)).symm, false_or_iff]
  case trans h_l₁ h_l₂ h_l₃ h₀ h₁ h_ih₀ h_ih₁ n =>
    trans
    · apply h_ih₀
      rwa [h₁.nodup_iff]
    · apply perm.filter _ h₁
#align list.perm.take_inter List.Perm.take_inter

theorem Perm.drop_inter {α} [DecidableEq α] {xs ys : List α} (n : ℕ) (h : xs ~ ys) (h' : ys.Nodup) :
    xs.drop n ~ ys.inter (xs.drop n) :=
  by
  by_cases h'' : n ≤ xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by
      dsimp [n']
      rwa [tsub_tsub_cancel_of_le]
    have h₁ : n' ≤ xs.length := by apply tsub_le_self
    have h₂ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [reverse_take _ h₁, h₀, reverse_reverse]
    rw [h₂]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply perm.take_inter _ _ h'
    apply (reverse_perm _).trans <;> assumption
  · have : drop n xs = [] := by
      apply eq_nil_of_length_eq_zero
      rw [length_drop, tsub_eq_zero_iff_le]
      apply le_of_not_ge h''
    simp [this, List.inter]
#align list.perm.drop_inter List.Perm.drop_inter

theorem Perm.slice_inter {α} [DecidableEq α] {xs ys : List α} (n m : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : List.dropSlice n m xs ~ ys ∩ List.dropSlice n m xs :=
  by
  simp only [slice_eq]
  have : n ≤ n + m := Nat.le_add_right _ _
  have := h.nodup_iff.2 h'
  apply perm.trans _ (perm.inter_append _).symm <;>
    solve_by_elim (config := { max_depth := 7 }) [perm.append, perm.drop_inter, perm.take_inter,
      disjoint_take_drop, h, h']
#align list.perm.slice_inter List.Perm.slice_inter

-- enumerating permutations
section Permutations

theorem perm_of_mem_permutations_aux :
    ∀ {ts is l : List α}, l ∈ permutationsAux ts is → l ~ ts ++ is :=
  by
  refine' permutations_aux.rec (by simp) _
  introv IH1 IH2 m
  rw [permutations_aux_cons, permutations, mem_foldr_permutations_aux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, e⟩)
  · exact (IH1 m).trans perm_middle
  · subst e
    have p : l₁ ++ l₂ ~ is := by
      simp [permutations] at m
      cases' m with e m
      · simp [e]
      exact is.append_nil ▸ IH2 m
    exact ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _)
#align list.perm_of_mem_permutations_aux List.perm_of_mem_permutations_aux

theorem perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
  (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutations_aux m
#align list.perm_of_mem_permutations List.perm_of_mem_permutations

theorem length_permutations_aux :
    ∀ ts is : List α, length (permutationsAux ts is) + is.length ! = (length ts + length is)! :=
  by
  refine' permutations_aux.rec (by simp) _
  intro t ts is IH1 IH2
  have IH2 : length (permutations_aux is nil) + 1 = is.length ! := by simpa using IH2
  simp [-add_comm, Nat.factorial, Nat.add_succ, mul_comm] at IH1
  rw [permutations_aux_cons,
    length_foldr_permutations_aux2' _ _ _ _ _ fun l m => (perm_of_mem_permutations m).length_eq,
    permutations, length, length, IH2, Nat.succ_add, Nat.factorial_succ, mul_comm (Nat.succ _), ←
    IH1, add_comm (_ * _), add_assoc, Nat.mul_succ, mul_comm]
#align list.length_permutations_aux List.length_permutations_aux

theorem length_permutations (l : List α) : length (permutations l) = (length l)! :=
  length_permutations_aux l []
#align list.length_permutations List.length_permutations

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (ts' list.perm «expr[ ,]»([])) -/
theorem mem_permutations_of_perm_lemma {is l : List α}
    (H : l ~ [] ++ is → (∃ (ts' : _)(_ : ts' ~ []), l = ts' ++ is) ∨ l ∈ permutationsAux is []) :
    l ~ is → l ∈ permutations is := by simpa [permutations, perm_nil] using H
#align list.mem_permutations_of_perm_lemma List.mem_permutations_of_perm_lemma

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (is' list.perm is) -/
theorem mem_permutations_aux_of_perm :
    ∀ {ts is l : List α},
      l ~ is ++ ts → (∃ (is' : _)(_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is :=
  by
  refine' permutations_aux.rec (by simp) _
  intro t ts is IH1 IH2 l p
  rw [permutations_aux_cons, mem_foldr_permutations_aux2]
  rcases IH1 (p.trans perm_middle) with (⟨is', p', e⟩ | m)
  · clear p
    subst e
    rcases mem_split (p'.symm.subset (mem_cons_self _ _)) with ⟨l₁, l₂, e⟩
    subst is'
    have p := (perm_middle.symm.trans p').cons_inv
    cases' l₂ with a l₂'
    · exact Or.inl ⟨l₁, by simpa using p⟩
    · exact Or.inr (Or.inr ⟨l₁, a :: l₂', mem_permutations_of_perm_lemma IH2 p, by simp⟩)
  · exact Or.inr (Or.inl m)
#align list.mem_permutations_aux_of_perm List.mem_permutations_aux_of_perm

@[simp]
theorem mem_permutations {s t : List α} : s ∈ permutations t ↔ s ~ t :=
  ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutations_aux_of_perm⟩
#align list.mem_permutations List.mem_permutations

theorem perm_permutations'_aux_comm (a b : α) (l : List α) :
    (permutations'Aux a l).bind (permutations'Aux b) ~
      (permutations'Aux b l).bind (permutations'Aux a) :=
  by
  induction' l with c l ih
  · simp [swap]
  simp [permutations'_aux]
  apply perm.swap'
  have :
    ∀ a b,
      (map (cons c) (permutations'_aux a l)).bind (permutations'_aux b) ~
        map (cons b ∘ cons c) (permutations'_aux a l) ++
          map (cons c) ((permutations'_aux a l).bind (permutations'_aux b)) :=
    by
    intros
    simp only [map_bind, permutations'_aux]
    refine' (bind_append_perm _ (fun x => [_]) _).symm.trans _
    rw [← map_eq_bind, ← bind_map]
  refine' (((this _ _).append_left _).trans _).trans ((this _ _).append_left _).symm
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append (ih.map _)
#align list.perm_permutations'_aux_comm List.perm_permutations'_aux_comm

theorem Perm.permutations' {s t : List α} (p : s ~ t) : permutations' s ~ permutations' t :=
  by
  induction' p with a s t p IH a b l s t u p₁ p₂ IH₁ IH₂; · simp
  · simp only [permutations']
    exact IH.bind_right _
  · simp only [permutations']
    rw [bind_assoc, bind_assoc]
    apply perm.bind_left
    intro l' hl'
    apply perm_permutations'_aux_comm
  · exact IH₁.trans IH₂
#align list.perm.permutations' List.Perm.permutations'

theorem permutations_perm_permutations' (ts : List α) : ts.permutations ~ ts.permutations' :=
  by
  obtain ⟨n, h⟩ : ∃ n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction' n with n IH generalizing ts; · cases h
  refine' List.reverseRecOn ts (fun h => _) (fun ts t _ h => _) h; · simp [permutations]
  rw [← concat_eq_append, length_concat, Nat.succ_lt_succ_iff] at h
  have IH₂ := (IH ts.reverse (by rwa [length_reverse])).trans (reverse_perm _).permutations'
  simp only [permutations_append, foldr_permutations_aux2, permutations_aux_nil,
    permutations_aux_cons, append_nil]
  refine'
    (perm_append_comm.trans ((IH₂.bind_right _).append ((IH _ h).map _))).trans
      (perm.trans _ perm_append_comm.permutations')
  rw [map_eq_bind, singleton_append, permutations']
  convert bind_append_perm _ _ _; funext ys
  rw [permutations'_aux_eq_permutations_aux2, permutations_aux2_append]
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

theorem nth_le_permutations'_aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s).nthLe n hn = s.insertNth n x :=
  by
  induction' s with y s IH generalizing n
  · simp only [length, permutations'_aux, Nat.lt_one_iff] at hn
    simp [hn]
  · cases n
    · simp
    · simpa using IH _ _
#align list.nth_le_permutations'_aux List.nth_le_permutations'_aux

theorem count_permutations'_aux_self [DecidableEq α] (l : List α) (x : α) :
    count (x :: l) (permutations'Aux x l) = length (takeWhile ((· = ·) x) l) + 1 :=
  by
  induction' l with y l IH generalizing x
  · simp [take_while]
  · rw [permutations'_aux, count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [take_while, Nat.succ_inj'] using IH _
    · rw [take_while]
      rw [if_neg hx]
      cases' permutations'_aux x l with a as
      · simp
      · rw [count_eq_zero_of_not_mem, length, zero_add]
        simp [hx, Ne.symm hx]
#align list.count_permutations'_aux_self List.count_permutations'_aux_self

@[simp]
theorem length_permutations'_aux (s : List α) (x : α) :
    length (permutations'Aux x s) = length s + 1 :=
  by
  induction' s with y s IH
  · simp
  · simpa using IH
#align list.length_permutations'_aux List.length_permutations'_aux

@[simp]
theorem permutations'_aux_nth_le_zero (s : List α) (x : α)
    (hn : 0 < length (permutations'Aux x s) := (by simp)) :
    (permutations'Aux x s).nthLe 0 hn = x :: s :=
  nth_le_permutations'_aux _ _ _ _
#align list.permutations'_aux_nth_le_zero List.permutations'_aux_nth_le_zero

theorem injective_permutations'_aux (x : α) : Function.Injective (permutations'Aux x) :=
  by
  intro s t h
  apply insert_nth_injective s.length x
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← nth_le_permutations'_aux s x s.length (by simp), ←
    nth_le_permutations'_aux t x s.length (by simp [hl])]
  simp [h, hl]
#align list.injective_permutations'_aux List.injective_permutations'_aux

theorem nodup_permutations'_aux_of_not_mem (s : List α) (x : α) (hx : x ∉ s) :
    Nodup (permutations'Aux x s) := by
  induction' s with y s IH
  · simp
  · simp only [not_or, mem_cons_iff] at hx
    simp only [not_and, exists_eq_right_right, mem_map, permutations'_aux, nodup_cons]
    refine' ⟨fun _ => Ne.symm hx.left, _⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp
#align list.nodup_permutations'_aux_of_not_mem List.nodup_permutations'_aux_of_not_mem

theorem nodup_permutations'_aux_iff {s : List α} {x : α} : Nodup (permutations'Aux x s) ↔ x ∉ s :=
  by
  refine' ⟨fun h => _, nodup_permutations'_aux_of_not_mem _ _⟩
  intro H
  obtain ⟨k, hk, hk'⟩ := nth_le_of_mem H
  rw [nodup_iff_nth_le_inj] at h
  suffices k = k + 1 by simpa using this
  refine' h k (k + 1) _ _ _
  · simpa [Nat.lt_succ_iff] using hk.le
  · simpa using hk
  rw [nth_le_permutations'_aux, nth_le_permutations'_aux]
  have hl : length (insert_nth k x s) = length (insert_nth (k + 1) x s) := by
    rw [length_insert_nth _ _ hk.le, length_insert_nth _ _ (Nat.succ_le_of_lt hk)]
  refine' ext_le hl fun n hn hn' => _
  rcases lt_trichotomy n k with (H | rfl | H)
  ·
    rw [nth_le_insert_nth_of_lt _ _ _ _ H (H.trans hk),
      nth_le_insert_nth_of_lt _ _ _ _ (H.trans (Nat.lt_succ_self _))]
  ·
    rw [nth_le_insert_nth_self _ _ _ hk.le, nth_le_insert_nth_of_lt _ _ _ _ (Nat.lt_succ_self _) hk,
      hk']
  · rcases(Nat.succ_le_of_lt H).eq_or_lt with (rfl | H')
    · rw [nth_le_insert_nth_self _ _ _ (Nat.succ_le_of_lt hk)]
      convert hk' using 1
      convert nth_le_insert_nth_add_succ _ _ _ 0 _
      simpa using hk
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt H'
      rw [length_insert_nth _ _ hk.le, Nat.succ_lt_succ_iff, Nat.succ_add] at hn
      rw [nth_le_insert_nth_add_succ]
      convert nth_le_insert_nth_add_succ s x k m.succ _ using 2
      · simp [Nat.add_succ, Nat.succ_add]
      · simp [add_left_comm, add_comm]
      · simpa [Nat.add_succ] using hn
      · simpa [Nat.succ_add] using hn
#align list.nodup_permutations'_aux_iff List.nodup_permutations'_aux_iff

theorem nodup_permutations (s : List α) (hs : Nodup s) : Nodup s.permutations :=
  by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction' hs with x l h h' IH
  · simp
  · rw [permutations']
    rw [nodup_bind]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'_aux_iff, hy.mem_iff]
      exact fun H => h x H rfl
    · refine' IH.pairwise_of_forall_ne fun as ha bs hb H => _
      rw [disjoint_iff_ne]
      rintro a ha' b hb' rfl
      obtain ⟨n, hn, hn'⟩ := nth_le_of_mem ha'
      obtain ⟨m, hm, hm'⟩ := nth_le_of_mem hb'
      rw [mem_permutations'] at ha hb
      have hl : as.length = bs.length := (ha.trans hb.symm).length_eq
      simp only [Nat.lt_succ_iff, length_permutations'_aux] at hn hm
      rw [nth_le_permutations'_aux] at hn' hm'
      have hx :
        nth_le (insert_nth n x as) m (by rwa [length_insert_nth _ _ hn, Nat.lt_succ_iff, hl]) = x :=
        by simp [hn', ← hm', hm]
      have hx' :
        nth_le (insert_nth m x bs) n (by rwa [length_insert_nth _ _ hm, Nat.lt_succ_iff, ← hl]) =
          x :=
        by simp [hm', ← hn', hn]
      rcases lt_trichotomy n m with (ht | ht | ht)
      · suffices x ∈ bs by exact h x (hb.subset this) rfl
        rw [← hx', nth_le_insert_nth_of_lt _ _ _ _ ht (ht.trans_le hm)]
        exact nth_le_mem _ _ _
      · simp only [ht] at hm' hn'
        rw [← hm'] at hn'
        exact H (insert_nth_injective _ _ hn')
      · suffices x ∈ as by exact h x (ha.subset this) rfl
        rw [← hx, nth_le_insert_nth_of_lt _ _ _ _ ht (ht.trans_le hn)]
        exact nth_le_mem _ _ _
#align list.nodup_permutations List.nodup_permutations

-- TODO: `nodup s.permutations ↔ nodup s`
-- TODO: `count s s.permutations = (zip_with count s s.tails).prod`
end Permutations

end List

