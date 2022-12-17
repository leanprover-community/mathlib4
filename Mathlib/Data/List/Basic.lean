/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

! This file was ported from Lean 3 source module data.list.basic
! leanprover-community/mathlib commit cf9386b56953fb40904843af98b7a80757bbe7f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.List.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Init.Core

/-!
# Basic properties of lists
-/


open Function

open Nat hiding one_pos

/- ./././Mathport/Syntax/Translate/Command.lean:719:14: unsupported user command assert_not_exists -/
namespace List

universe u v w x

variable {ι : Type _} {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {l₁ l₂ : List α}

-- Porting note: Delete this attribute
--attribute [inline] List.head

/-- There is only one list of an empty type -/
instance uniqueOfIsEmpty [IsEmpty α] : Unique (List α) :=
  { instInhabitedList with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: _ => isEmptyElim a }
#align list.unique_of_is_empty List.uniqueOfIsEmpty

instance : IsLeftId (List α) Append.append [] :=
  ⟨nil_append⟩

instance : IsRightId (List α) Append.append [] :=
  ⟨append_nil⟩

instance : IsAssociative (List α) Append.append :=
  ⟨append_assoc⟩

--Porting note : Order of implicit arguments is different in Lean 3 and Lean 4
#align list.head_eq_of_cons_eq List.head_eq_of_cons_eq

--Porting note : Order of implicit arguments is different in Lean 3 and Lean 4
#align list.tail_eq_of_cons_eq List.tail_eq_of_cons_eq

@[simp] theorem cons_injective {a : α} : Injective (cons a) :=
λ _ _ Pe => tail_eq_of_cons_eq Pe
#align list.cons_injective List.cons_injective

theorem cons_eq_cons {a b : α} {l l' : List α} : a :: l = b :: l' ↔ a = b ∧ l = l' :=
  ⟨List.cons.inj, fun h => h.1 ▸ h.2 ▸ rfl⟩
#align list.cons_eq_cons List.cons_eq_cons

theorem singleton_injective : Injective fun a : α => [a] := fun _ _ h => (cons_eq_cons.1 h).1
#align list.singleton_injective List.singleton_injective

theorem singleton_inj {a b : α} : [a] = [b] ↔ a = b :=
  singleton_injective.eq_iff
#align list.singleton_inj List.singleton_inj

theorem set_of_mem_cons (l : List α) (a : α) : { x | x ∈ a :: l } = insert a { x | x ∈ l } :=
-- Porting note: abuse of def-eq due no import of `Set.mem_insert`
  Set.ext <| fun x => show x ∈ a :: l ↔ x = a ∨ x ∈ l by simp only [mem_cons, iff_self]
#align list.set_of_mem_cons List.set_of_mem_cons

/-! ### mem -/

theorem Decidable.List.eq_or_ne_mem_of_mem [DecidableEq α] {a b : α} {l : List α} (h : a ∈ b :: l) :
    a = b ∨ a ≠ b ∧ a ∈ l := by
  by_cases hab : a = b
  · exact Or.inl hab
  . exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))
#align list.decidable.list.eq_or_ne_mem_of_mem List.Decidable.List.eq_or_ne_mem_of_mem

alias mem_cons ↔ eq_or_mem_of_mem_cons _

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩
#align list.not_mem_append List.not_mem_append

#align list.ne_nil_of_mem List.ne_nil_of_mem

theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    cases h with
    | head => exact ⟨[], l, rfl⟩
    | tail _ h =>
      rcases ih h with ⟨s, t, rfl⟩
      exact ⟨b :: s, t, rfl⟩
#align list.mem_split List.mem_split

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
Or.elim (eq_or_mem_of_mem_cons h₂) (fun e ↦ absurd e h₁) (fun r ↦ r)
#align list.mem_of_ne_of_mem List.mem_of_ne_of_mem

theorem ne_of_not_mem_cons {a b : α} {l : List α} : (a ∉ b::l) → a ≠ b :=
fun nin aeqb ↦ absurd (aeqb ▸ Mem.head ..) nin
#align list.ne_of_not_mem_cons List.ne_of_not_mem_cons

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : (a ∉ b::l) → a ∉ l :=
fun nin nainl ↦ absurd (Mem.tail _ nainl) nin
#align list.not_mem_of_not_mem_cons List.not_mem_of_not_mem_cons

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → (a ∉ l) → (a ∉ y::l) :=
fun p1 p2 ↦ fun Pain ↦ absurd (eq_or_mem_of_mem_cons Pain) (not_or.mpr ⟨p1, p2⟩)
#align list.not_mem_cons_of_ne_of_not_mem List.not_mem_cons_of_ne_of_not_mem

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : (a ∉ y::l) → a ≠ y ∧ a ∉ l :=
fun p ↦ And.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)
#align list.ne_and_not_mem_of_not_mem_cons List.ne_and_not_mem_of_not_mem_cons

-- Porting TODO: fix `List.mem_map` in Std to this statement.
@[simp]
theorem mem_map' {f : α → β} {b : β} {l : List α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
  by simp only [List.mem_map, eq_comm, iff_self]
#align list.mem_map List.mem_map'

-- Porting TODO: This line breaks everything
--alias mem_map' ↔ exists_of_mem_map

-- Porting note: implicit arguments in different order in Lean3 and Lean4
#align list.mem_map_of_mem List.mem_map_of_mem

theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
    f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m =>
    let ⟨_, m', e⟩ := exists_of_mem_map m
    H e ▸ m',
    mem_map_of_mem _⟩
#align list.mem_map_of_injective List.mem_map_of_injective

@[simp]
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff {f : α → α}
   (hf : Function.Involutive f) (x : α) (l : List α) : (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by
    rintro ⟨y, h, rfl⟩
    rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩
#align
  function.involutive.exists_mem_and_apply_eq_iff
  Function.Involutive.exists_mem_and_apply_eq_iff

theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
    a ∈ map f l ↔ f a ∈ l := by rw [mem_map', hf.exists_mem_and_apply_eq_iff]
#align list.mem_map_of_involutive List.mem_map_of_involutive

#align list.forall_mem_map_iff List.forall_mem_map_iff

attribute [simp] List.map_eq_nil
#align list.map_eq_nil List.map_eq_nil

attribute [simp] List.mem_join
#align list.mem_join List.mem_join

#align list.exists_of_mem_join List.exists_of_mem_join

--Porting note: Implicit arguments in a different order in Lean3 and Lean4
#align list.mem_join_of_mem List.mem_join_of_mem

--Porting note: Implicit arguments in a different order in Lean3 and Lean4
attribute [simp] List.mem_bind
#align list.mem_bind List.mem_bind

--Porting note: bExists in Lean3, And in Lean4
#align list.exists_of_mem_bind List.exists_of_mem_bind

--Porting note: Implicit arguments in a different order in Lean3 and Lean4
#align list.mem_bind_of_mem List.mem_bind_of_mem

--Porting note : Implicit arguments in a different order in Lean3 and Lean4
#align list.bind_map List.bind_map

theorem map_bind (g : β → List γ) (f : α → β) :
    ∀ l : List α, (List.map f l).bind g = l.bind fun a => g (f a)
  | [] => rfl
  | a :: l => by simp only [cons_bind, map_cons, map_bind _ _ l]
#align list.map_bind List.map_bind

/-! ### length -/

#align list.length_eq_zero List.length_eq_zero

attribute [simp] List.length_singleton
#align list.length_singleton List.length_singleton

#align list.length_pos_of_mem List.length_pos_of_mem

#align list.exists_mem_of_length_pos List.exists_mem_of_length_pos

#align list.length_pos_iff_exists_mem List.length_pos_iff_exists_mem

alias length_pos ↔ ne_nil_of_length_pos length_pos_of_ne_nil
#align list.ne_nil_of_length_pos List.ne_nil_of_length_pos

#align list.length_pos_of_ne_nil List.length_pos_of_ne_nil

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩
#align list.length_pos_iff_ne_nil List.length_pos_iff_ne_nil

#align list.exists_mem_of_ne_nil List.exists_mem_of_ne_nil

#align list.length_eq_one List.length_eq_one

theorem exists_of_length_succ {n} :
  ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
| [], H => absurd H.symm $ Nat.succ_ne_zero n
| h :: t, _ => ⟨h, t, rfl⟩
#align list.exists_of_length_succ List.exists_of_length_succ

@[simp]
lemma length_injective_iff : Injective (List.length : List α → ℕ) ↔ Subsingleton α := by
  constructor
  · intro h; refine ⟨λ x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intros hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    case nil.nil => rfl
    case nil.cons => cases hl
    case cons.nil => cases hl
    case cons.cons ih _ _ => congr
                             · exact Subsingleton.elim _ _
                             · apply ih; simpa using hl
#align list.length_injective_iff List.length_injective_iff

@[simp default+1]
lemma length_injective [Subsingleton α] : Injective (length : List α → ℕ) :=
length_injective_iff.mpr inferInstance
#align list.length_injective List.length_injective

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  Iff.intro
    (fun _ => match l with
      | [a, b] => ⟨a, b, rfl⟩)
    (fun ⟨_, _, e⟩ => e.symm ▸ rfl)
#align list.length_eq_two List.length_eq_two

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  Iff.intro
    (fun _ => match l with
      | [a, b, c] => ⟨a, b, c, rfl⟩)
    (fun ⟨_, _, _, e⟩ => e.symm ▸ rfl)
#align list.length_eq_three List.length_eq_three

--Portin note: from Lean3 core
theorem length_le_of_sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ ≤ length l₂
| _, _, Sublist.slnil           => le_refl 0
| _, _, Sublist.cons _ s => le_succ_of_le (length_le_of_sublist s)
| _, _, Sublist.cons₂ _ s => succ_le_succ (length_le_of_sublist s)
#align list.length_le_of_sublist List.length_le_of_sublist

alias length_le_of_sublist ← sublist.length_le

/-! ### set-theoretic notation of lists -/

#align list.empty_eq List.empty_eq

--Porting Note: instance from Lean3 core
instance : Singleton α (List α) := ⟨fun x => [x]⟩
#align list.has_singleton List.instSingletonList

--Porting Note: instance from Lean3 core
instance [DecidableEq α] : Insert α (List α) := ⟨List.insert⟩

--Porting Note: instance from Lean3 core
instance [DecidableEq α]: IsLawfulSingleton α (List α) :=
  { insert_emptyc_eq := fun x =>
      show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg (not_mem_nil _) }

theorem singleton_eq (x : α) : ({x} : List α) = [x] :=
  rfl
#align list.singleton_eq List.singleton_eq

theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) : Insert.insert x l = x :: l :=
  if_neg h
#align list.insert_neg List.insert_neg

theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) : Insert.insert x l = l :=
  if_pos h
#align list.insert_pos List.insert_pos

theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y] := by
  rw [insert_neg, singleton_eq]
  rwa [singleton_eq, mem_singleton]
#align list.doubleton_eq List.doubleton_eq

/-! ### bounded quantifiers over lists -/

#align list.forall_mem_nil List.forall_mem_nil

#align list.forall_mem_cons List.forall_mem_cons

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α}
    (h : ∀ x, x ∈ a :: l → p x) :
  ∀ x, x ∈ l → p x :=
(forall_mem_cons.1 h).2
#align list.forall_mem_of_forall_mem_cons List.forall_mem_of_forall_mem_cons

#align list.forall_mem_singleton List.forall_mem_singleton

#align list.forall_mem_append List.forall_mem_append

theorem not_exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x :=
  fun.
#align list.not_exists_mem_nil List.not_exists_mem_nil

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ x ∈ a :: l, p x :=
  ⟨a, (mem_cons_self _ _), h⟩
#align list.exists_mem_cons_of List.exists_mem_cons_of

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ l, p x) →
    ∃ x ∈ a :: l, p x :=
  fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩
#align list.exists_mem_cons_of_exists List.exists_mem_cons_of_exists

-- Porting note: bExists in Lean3 and And in Lean4
theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ a :: l, p x) →
    p a ∨ ∃ x ∈ l, p x :=
  fun ⟨x, xal, px⟩ =>
    Or.elim (eq_or_mem_of_mem_cons xal) (fun h : x = a => by rw [← h]; left; exact px)
      fun h : x ∈ l => Or.inr ⟨x, h, px⟩
#align list.or_exists_of_exists_mem_cons List.or_exists_of_exists_mem_cons

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  Iff.intro or_exists_of_exists_mem_cons fun h =>
    Or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists
#align list.exists_mem_cons_iff List.exists_mem_cons_iff

/-! ### list subset -/

#align list.subset_def List.subset_def

#align list.subset_append_of_subset_left List.subset_append_of_subset_left

-- Porting TODO: Get rid of ' in name and match Lean3 and Lean4 statements
theorem subset_append_of_subset_right' (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ := fun s =>
  Subset.trans s <| subset_append_right _ _
#align list.subset_append_of_subset_right List.subset_append_of_subset_right'

#align list.cons_subset List.cons_subset

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
  (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
cons_subset.2 ⟨ainm, lsubm⟩
#align list.cons_subset_of_subset_of_mem List.cons_subset_of_subset_of_mem

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
fun _ h ↦ (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)
#align list.append_subset_of_subset_of_subset List.append_subset_of_subset_of_subset

@[simp]
theorem append_subset_iff {l₁ l₂ l : List α} : l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by
  constructor
  · intro h
    simp only [subset_def] at *
    constructor <;> intros <;> simp [*]
  · rintro ⟨h1, h2⟩
    apply append_subset_of_subset_of_subset h1 h2
#align list.append_subset_iff List.append_subset_iff

alias subset_nil ↔ eq_nil_of_subset_nil _
#align list.eq_nil_of_subset_nil List.eq_nil_of_subset_nil

#align list.eq_nil_iff_forall_not_mem List.eq_nil_iff_forall_not_mem

#align list.map_subset List.map_subset

theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := by
  refine' ⟨_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'
#align list.map_subset_iff List.map_subset_iff

/-! ### append -/


theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl
#align list.append_eq_has_append List.append_eq_has_append

#align list.singleton_append List.singleton_append

#align list.append_ne_nil_of_ne_nil_left List.append_ne_nil_of_ne_nil_left

#align list.append_ne_nil_of_ne_nil_right List.append_ne_nil_of_ne_nil_right

#align list.append_eq_nil List.append_eq_nil

@[simp]
theorem nil_eq_append_iff {a b : List α} : [] = a ++ b ↔ a = [] ∧ b = [] := by
  rw [eq_comm, append_eq_nil]
#align list.nil_eq_append_iff List.nil_eq_append_iff

theorem append_eq_cons_iff {a b c : List α} {x : α} :
    a ++ b = x :: c ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  cases a <;>
    simp only [nil_append, true_and, @eq_comm _ c, false_and, exists_false, or_false, iff_self,
      cons_append, cons.injEq, false_and, and_assoc, exists_and_left, exists_eq_left', false_or]
#align list.append_eq_cons_iff List.append_eq_cons_iff

theorem cons_eq_append_iff {a b c : List α} {x : α} :
    (x :: c : List α) = a ++ b ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  rw [eq_comm, append_eq_cons_iff]
#align list.cons_eq_append_iff List.cons_eq_append_iff

#align list.append_eq_append_iff List.append_eq_append_iff

#align list.take_append_drop List.take_append_drop

#align list.append_inj List.append_inj

--Porting note: Implicit arguments in a different order
#align list.append_inj_right List.append_inj_right

--Porting note: Implicit arguments in a different order
#align list.append_inj_left List.append_inj_left

--Porting note: Implicit arguments in a different order
#align list.append_inj' List.append_inj'

--Porting note: Implicit arguments in a different order
#align list.append_inj_right' List.append_inj_right'

--Porting note: Implicit arguments in a different order
#align list.append_inj_left' List.append_inj_left'

theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  (append_right_inj _).1 h
#align list.append_left_cancel List.append_left_cancel

theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  (append_left_inj _).1 h
#align list.append_right_cancel List.append_right_cancel

theorem append_right_injective (s : List α) : Injective fun t ↦ s ++ t :=
fun _ _ ↦ append_left_cancel
#align list.append_right_injective List.append_right_injective

#align list.append_right_inj List.append_right_inj

theorem append_left_injective (t : List α) : Injective fun s ↦ s ++ t :=
fun _ _ ↦ append_right_cancel
#align list.append_left_injective List.append_left_injective

#align list.append_left_inj List.append_left_inj

#align list.map_eq_append_split List.map_eq_append_split

/-! ### repeat -/

--Porting note: From Lean3 Core
@[simp] lemma length_repeat (a : α) (n : ℕ) : length (List.repeat a n) = n :=
by induction n <;> simp [*]
#align list.length_repeat List.length_repeat

@[simp]
theorem repeat_succ (a : α) (n) : List.repeat a (n + 1) = a :: List.repeat a n :=
  rfl
#align list.repeat_succ List.repeat_succ

theorem mem_repeat {a b : α} : ∀ {n}, b ∈ List.repeat a n ↔ n ≠ 0 ∧ b = a
  | 0 => by simp
  | n + 1 => by simp [mem_repeat]
#align list.mem_repeat List.mem_repeat

theorem eq_of_mem_repeat {a b : α} {n} (h : b ∈ List.repeat a n) : b = a :=
  (mem_repeat.1 h).2
#align list.eq_of_mem_repeat List.eq_of_mem_repeat

theorem eq_repeat_of_mem {a : α} : ∀ {l : List α}, (∀ b ∈ l, b = a) → l = List.repeat a l.length
  | [], _ => rfl
  | b :: l, H => by
    rw [length_cons, List.repeat]
    cases' forall_mem_cons.1 H with H₁ H₂
    conv_lhs => rw [H₁, eq_repeat_of_mem H₂]
#align list.eq_repeat_of_mem List.eq_repeat_of_mem

theorem eq_repeat' {a : α} {l : List α} : l = List.repeat a l.length ↔ ∀ b ∈ l, b = a :=
  ⟨fun h => h.symm ▸ fun _ => eq_of_mem_repeat, eq_repeat_of_mem⟩
#align list.eq_repeat' List.eq_repeat'

theorem eq_repeat {a : α} {n} {l : List α} : l = List.repeat a n ↔ length l = n ∧ ∀ b ∈ l, b = a :=
  ⟨fun h => h.symm ▸ ⟨length_repeat _ _, fun _ => eq_of_mem_repeat⟩, fun ⟨e, al⟩ =>
    e ▸ eq_repeat_of_mem al⟩
#align list.eq_repeat List.eq_repeat

theorem repeat_add (a : α) (m n) : List.repeat a (m + n) = List.repeat a m ++ List.repeat a n := by
  induction m <;> simp [*, zero_add, succ_add, List.repeat]
#align list.repeat_add List.repeat_add

theorem repeat_subset_singleton (a : α) (n) : List.repeat a n ⊆ [a] := fun _ h =>
  mem_singleton.2 (eq_of_mem_repeat h)
#align list.repeat_subset_singleton List.repeat_subset_singleton

theorem subset_singleton_iff {a : α} : ∀ L : List α, L ⊆ [a] ↔ ∃ n, L = List.repeat a n
  | [] => ⟨fun _ => ⟨0, by simp⟩, by simp⟩
  | h :: L => by
    refine' ⟨fun h => _, fun ⟨k, hk⟩ => by simp [hk, repeat_subset_singleton]⟩
    rw [cons_subset] at h
    obtain ⟨n, rfl⟩ := (subset_singleton_iff L).mp h.2
    exact ⟨n.succ, by simp [mem_singleton.mp h.1]⟩
#align list.subset_singleton_iff List.subset_singleton_iff

@[simp]
theorem map_repeat (f : α → β) (a : α) (n) : map f (List.repeat a n) = List.repeat (f a) n := by
  induction n <;> [rfl, simp only [*, List.repeat, map]]
#align list.map_repeat List.map_repeat

@[simp]
theorem tail_repeat (a : α) (n) : tail (List.repeat a n) = List.repeat a n.pred := by cases n <;> rfl
#align list.tail_repeat List.tail_repeat

@[simp]
theorem join_repeat_nil (n : ℕ) : join (List.repeat [] n) = @nil α := by
  induction n <;> [rfl, simp only [*, List.repeat, join, append_nil]]
#align list.join_repeat_nil List.join_repeat_nil

theorem repeat_left_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective fun a : α => List.repeat a n :=
  fun _ _ h => (eq_repeat.1 h).2 _ <| mem_repeat.2 ⟨hn, rfl⟩
#align list.repeat_left_injective List.repeat_left_injective

theorem repeat_left_inj {a b : α} {n : ℕ} (hn : n ≠ 0) : List.repeat a n = List.repeat b n ↔ a = b :=
  (repeat_left_injective hn).eq_iff
#align list.repeat_left_inj List.repeat_left_inj

@[simp]
theorem repeat_left_inj' {a b : α} : ∀ {n}, List.repeat a n = List.repeat b n ↔ n = 0 ∨ a = b
  | 0 => by simp
  | n + 1 => (repeat_left_inj n.succ_ne_zero).trans <| by simp [n.succ_ne_zero, false_or_iff]
#align list.repeat_left_inj' List.repeat_left_inj'

theorem repeat_right_injective (a : α) : Function.Injective (List.repeat a) :=
  Function.LeftInverse.injective (length_repeat a)
#align list.repeat_right_injective List.repeat_right_injective

@[simp]
theorem repeat_right_inj {a : α} {n m : ℕ} : List.repeat a n = List.repeat a m ↔ n = m :=
  (repeat_right_injective a).eq_iff
#align list.repeat_right_inj List.repeat_right_inj

/-! ### pure -/

--Porting Note: TODO this is from Lean3 core, so doesn't belong here
instance : Monad List := { pure := @List.ret, bind := @List.bind, map := @List.map }

@[simp]
theorem mem_pure {α} (x y : α) : x ∈ (pure y : List α) ↔ x = y :=
  show x ∈ [y] ↔ x = y by simp
#align list.mem_pure List.mem_pure

/-! ### bind -/

@[simp]
theorem bind_eq_bind {α β} (f : α → List β) (l : List α) : l >>= f = l.bind f :=
  rfl
#align list.bind_eq_bind List.bind_eq_bind

-- TODO: duplicate of a lemma in core
theorem bind_append (f : α → List β) (l₁ l₂ : List α) :
    (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f :=
  append_bind _ _ _
#align list.bind_append List.bind_append

@[simp]
theorem bind_singleton (f : α → List β) (x : α) : [x].bind f = f x :=
  append_nil (f x)
#align list.bind_singleton List.bind_singleton

--Porting TODO: follows from IsLawfulMonad which is not ported yet
@[simp]
theorem bind_singleton' (l : List α) : (l.bind fun x => [x]) = l :=
  by induction l <;> simp [*]
#align list.bind_singleton' List.bind_singleton'

theorem map_eq_bind {α β} (f : α → β) (l : List α) : map f l = l.bind fun x => [f x] := by
  trans
  rw [← bind_singleton' l, bind_map]
  rfl
#align list.map_eq_bind List.map_eq_bind

theorem bind_assoc {α β} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.bind f).bind g = l.bind fun x => (f x).bind g := by induction l <;> simp [*]
#align list.bind_assoc List.bind_assoc

/-! ### concat -/


theorem concat_nil (a : α) : concat [] a = [a] :=
  rfl
#align list.concat_nil List.concat_nil

theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl
#align list.concat_cons List.concat_cons

--Porting TODO: Fix statement of `concat_eq_append` to match Lean3
@[simp]
theorem concat_eq_append' (a : α) (l : List α) : concat l a = l ++ [a] := by
  induction l <;> simp only [*, concat] <;> constructor
#align list.concat_eq_append List.concat_eq_append'

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ := by
  intro h
  rw [concat_eq_append, concat_eq_append] at h
  exact append_right_cancel h
#align list.init_eq_of_concat_eq List.init_eq_of_concat_eq

theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b := by
  intro h
  rw [concat_eq_append, concat_eq_append] at h
  exact head_eq_of_cons_eq (append_left_cancel h)
#align list.last_eq_of_concat_eq List.last_eq_of_concat_eq

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by simp
#align list.concat_ne_nil List.concat_ne_nil

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by simp
#align list.concat_append List.concat_append

--Porting TODO: Fix statement of `length_concat` to match Lean3
theorem length_concat' (a : α) (l : List α) : length (concat l a) = succ (length l) := by
  simp only [concat_eq_append, length_append, length]
#align list.length_concat List.length_concat'

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by simp
#align list.append_concat List.append_concat

/-! ### reverse -/

#align list.reverse_nil List.reverse_nil

#align list.reverse_core List.reverseAux

attribute [local simp] reverseAux

#align list.reverse_cons List.reverse_cons


theorem reverse_core_eq (l₁ l₂ : List α) : reverseAux l₁ l₂ = reverse l₁ ++ l₂ := by
  induction l₁ generalizing l₂ <;> [rfl,
      simp only [*, reverseAux, reverse_cons, append_assoc]];
    rfl
#align list.reverse_core_eq List.reverse_core_eq

theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]
#align list.reverse_cons' List.reverse_cons'

@[simp]
theorem reverse_singleton (a : α) : reverse [a] = [a] :=
  rfl
#align list.reverse_singleton List.reverse_singleton

attribute [simp] List.reverse_append
#align list.reverse_append List.reverse_append

#align list.reverse_concat List.reverse_concat

attribute [simp] List.reverse_reverse
#align list.reverse_reverse List.reverse_reverse

@[simp]
theorem reverse_involutive : Involutive (@reverse α) :=
  reverse_reverse
#align list.reverse_involutive List.reverse_involutive

@[simp]
theorem reverse_injective : Injective (@reverse α) :=
  reverse_involutive.injective
#align list.reverse_injective List.reverse_injective

theorem reverse_surjective : Surjective (@reverse α) :=
  reverse_involutive.surjective
#align list.reverse_surjective List.reverse_surjective

theorem reverse_bijective : Bijective (@reverse α) :=
  reverse_involutive.bijective
#align list.reverse_bijective List.reverse_bijective

@[simp]
theorem reverse_inj {l₁ l₂ : List α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
  reverse_injective.eq_iff
#align list.reverse_inj List.reverse_inj

theorem reverse_eq_iff {l l' : List α} : l.reverse = l' ↔ l = l'.reverse :=
  reverse_involutive.eq_iff
#align list.reverse_eq_iff List.reverse_eq_iff

@[simp]
theorem reverse_eq_nil {l : List α} : reverse l = [] ↔ l = [] :=
  @reverse_inj _ l []
#align list.reverse_eq_nil List.reverse_eq_nil

theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  simp only [concat_eq_append, reverse_cons, reverse_reverse]
#align list.concat_eq_reverse_cons List.concat_eq_reverse_cons

attribute [simp] List.length_reverse
#align list.length_reverse List.length_reverse


@[simp]
theorem map_reverse (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) := by
  induction l <;> [rfl, simp only [*, map, reverse_cons, map_append]]
#align list.map_reverse List.map_reverse

theorem map_reverseAux (f : α → β) (l₁ l₂ : List α) :
    map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverse_core_eq, map_append, map_reverse]
#align list.map_reverse_core List.map_reverseAux

--Porting TODO: Fix statement of `mem_reverse` to match Lean3
@[simp] theorem mem_reverse' {a : α} {l : List α} : a ∈ reverse l ↔ a ∈ l :=
  List.mem_reverse _ _
#align list.mem_reverse List.mem_reverse'

@[simp]
theorem reverse_repeat (a : α) (n) : reverse (List.repeat a n) = List.repeat a n :=
  eq_repeat.2
    ⟨by simp only [length_reverse, length_repeat], fun b h => eq_of_mem_repeat (mem_reverse'.1 h)⟩
#align list.reverse_repeat List.reverse_repeat

/-! ### empty -/

--Porting note: Definition from Lean3 core, so should be moved
/-- Boolean checking if a list is empty or not -/
def empty : List α → Bool
| [] => true
| (_::_) => false

attribute [simp] List.empty

theorem empty_iff_eq_nil {l : List α} : l.empty ↔ l = [] :=
  List.casesOn l (by simp) (by simp)
#align list.empty_iff_eq_nil List.empty_iff_eq_nil

/-! ### init -/

@[simp]
theorem length_init : ∀ l : List α, length (l.init) = length l - 1
  | [] => rfl
  | [_] => rfl
  | a::b::l => by
    rw [init, length_cons, length_cons, length_init (b::l), succ_sub_one, length_cons,
      succ_sub_one]
    simp
#align list.length_init List.length_init

--Porting note: `rw [init]` in Lean4 generates a goal `(b::l) ≠ []` so we use this lemma instead
def init_cons_cons (a b : α) (l : List α) : init (a::b::l) = a::init (b::l) := rfl

/-! ### last -/

@[simp]
theorem last_cons {a : α} {l : List α} :
    ∀ h : l ≠ nil, last (a :: l) (cons_ne_nil a l) = last l h := by
  induction l <;> intros
  contradiction
  rfl
#align list.last_cons List.last_cons

@[simp]
theorem last_append_singleton {a : α} (l : List α) :
    last (l ++ [a]) (append_ne_nil_of_ne_nil_right l _ (cons_ne_nil a _)) = a := by
  induction l <;> [rfl,
    simp only [cons_append, last_cons fun H => cons_ne_nil _ _ (append_eq_nil.1 H).2, *]]
#align list.last_append_singleton List.last_append_singleton

theorem last_append (l₁ l₂ : List α) (h : l₂ ≠ []) :
    last (l₁ ++ l₂) (append_ne_nil_of_ne_nil_right l₁ l₂ h) = last l₂ h := by
  induction' l₁ with _ _ ih
  · simp
  · simp only [cons_append]
    rw [List.last_cons]
    exact ih
#align list.last_append List.last_append

theorem last_concat {a : α} (l : List α) : last (concat l a) (concat_ne_nil a l) = a := by
  simp only [concat_eq_append, last_append_singleton]
#align list.last_concat List.last_concat

@[simp]
theorem last_singleton (a : α) : last [a] (cons_ne_nil a []) = a :=
  rfl
#align list.last_singleton List.last_singleton

@[simp]
theorem last_cons_cons (a₁ a₂ : α) (l : List α) :
    last (a₁ :: a₂ :: l) (cons_ne_nil _ _) = last (a₂ :: l) (cons_ne_nil a₂ l) :=
  rfl
#align list.last_cons_cons List.last_cons_cons

theorem init_append_last : ∀ {l : List α} (h : l ≠ []), init l ++ [last l h] = l
  | [], h => absurd rfl h
  | [a], h => rfl
  | a :: b :: l, h => by
    rw [init_cons_cons, cons_append, last_cons (cons_ne_nil _ _)]
    congr
    exact init_append_last (cons_ne_nil b l)
#align list.init_append_last List.init_append_last

theorem last_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
    last l₁ h₁ = last l₂ h₂ := by subst l₁; rfl
#align list.last_congr List.last_congr

theorem last_mem : ∀ {l : List α} (h : l ≠ []), last l h ∈ l
  | [], h => absurd rfl h
  | [a], _ => by simp only [last, mem_singleton]
  | a :: b :: l, h =>
    List.mem_cons.2 <| Or.inr <| by
        rw [last_cons_cons]
        exact last_mem (cons_ne_nil b l)
#align list.last_mem List.last_mem

theorem last_repeat_succ (a m : ℕ) :
    (List.repeat a m.succ).last
        (ne_nil_of_length_eq_succ (show (List.repeat a m.succ).length = m.succ by rw [length_repeat])) =
      a :=
  by
  induction' m with k IH
  · simp
  · simpa only [repeat_succ, last]
#align list.last_repeat_succ List.last_repeat_succ

/-! ### last' -/

--Porting note: This theorem has moved because I changed to use this theorem
@[simp] theorem last'_cons_cons (a b : α) (l : List α) :
    last' (a :: b :: l) = last' (b :: l) := rfl
#align list.last'_cons_cons List.last'_cons_cons

@[simp]
theorem last'_is_none : ∀ {l : List α}, (last' l).isNone ↔ l = []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@last'_is_none (b :: l)]
#align list.last'_is_none List.last'_is_none

@[simp]
theorem last'_is_some : ∀ {l : List α}, l.last'.isSome ↔ l ≠ []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@last'_is_some (b :: l)]
#align list.last'_is_some List.last'_is_some

theorem mem_last'_eq_last : ∀ {l : List α} {x : α}, x ∈ l.last' → ∃ h, x = last l h
  | [], x, hx => False.elim <| by simp at hx
  | [a], x, hx =>
    have : a = x := by simpa using hx
    this ▸ ⟨cons_ne_nil a [], rfl⟩
  | a :: b :: l, x, hx => by
    rw [last'_cons_cons] at hx
    rcases mem_last'_eq_last hx with ⟨_, h₂⟩
    use cons_ne_nil _ _
#align list.mem_last'_eq_last List.mem_last'_eq_last

theorem last'_eq_last_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.last' = some (l.last h)
  | [], h => (h rfl).elim
  | [a], _ => by
    unfold last
    unfold last'; rfl
  | _ :: b :: l, _ => @last'_eq_last_of_ne_nil (b :: l) (cons_ne_nil _ _)
#align list.last'_eq_last_of_ne_nil List.last'_eq_last_of_ne_nil

theorem mem_last'_cons {x y : α} : ∀ {l : List α} (_ : x ∈ l.last'), x ∈ (y :: l).last'
  | [], _ => by contradiction
  | _ :: _, h => h
#align list.mem_last'_cons List.mem_last'_cons

theorem mem_of_mem_last' {l : List α} {a : α} (ha : a ∈ l.last') : a ∈ l :=
  let ⟨_, h₂⟩ := mem_last'_eq_last ha
  h₂.symm ▸ last_mem _
#align list.mem_of_mem_last' List.mem_of_mem_last'

theorem init_append_last' : ∀ {l : List α}, ∀ a ∈ l.last', init l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [last'_cons_cons] at hc
    rw [init_cons_cons, cons_append, init_append_last' _ hc]
#align list.init_append_last' List.init_append_last'

theorem ilast_eq_last' [Inhabited α] : ∀ l : List α, l.ilast = l.last'.iget
  | [] => by simp [ilast, Inhabited.default]
  | [a] => rfl
  | [a, b] => rfl
  | [a, b, c] => rfl
  | _ :: _ :: c :: l => by simp [ilast, ilast_eq_last' (c :: l)]
#align list.ilast_eq_last' List.ilast_eq_last'

@[simp]
theorem last'_append_cons :
    ∀ (l₁ : List α) (a : α) (l₂ : List α), last' (l₁ ++ a :: l₂) = last' (a :: l₂)
  | [], a, l₂ => rfl
  | [b], a, l₂ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, last'_cons_cons,
    ← cons_append, last'_append_cons (c :: l₁)]
#align list.last'_append_cons List.last'_append_cons

theorem last'_append_of_ne_nil (l₁ : List α) :
    ∀ {l₂ : List α} (_ : l₂ ≠ []), last' (l₁ ++ l₂) = last' l₂
  | [], hl₂ => by contradiction
  | b :: l₂, _ => last'_append_cons l₁ b l₂
#align list.last'_append_of_ne_nil List.last'_append_of_ne_nil

theorem last'_append {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.last') : x ∈ (l₁ ++ l₂).last' := by
  cases l₂
  · contradiction
  · rw [List.last'_append_cons]
    exact h
#align list.last'_append List.last'_append

/-! ### head(') and tail -/

#align list.head List.head!

theorem head!_eq_head? [Inhabited α] (l : List α) : head! l = (head? l).iget := by cases l <;> rfl
#align list.head_eq_head' List.head!_eq_head?

theorem surjective_head [Inhabited α] : Surjective (@head! α _) := fun x => ⟨[x], rfl⟩
#align list.surjective_head List.surjective_head

theorem surjective_head' : Surjective (@head? α) :=
  Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩
#align list.surjective_head' List.surjective_head'

theorem surjective_tail : Surjective (@tail α)
  | [] => ⟨[], rfl⟩
  | a :: l => ⟨a :: a :: l, rfl⟩
#align list.surjective_tail List.surjective_tail

theorem eq_cons_of_mem_head' {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: tail l
  | [], h => (Option.not_mem_none _ h).elim
  | a :: l, h => by
    simp only [head?, Option.mem_def, Option.some_inj] at h
    exact h ▸ rfl
#align list.eq_cons_of_mem_head' List.eq_cons_of_mem_head'

theorem mem_of_mem_head' {x : α} {l : List α} (h : x ∈ l.head?) : x ∈ l :=
  (eq_cons_of_mem_head' h).symm ▸ mem_cons_self _ _
#align list.mem_of_mem_head' List.mem_of_mem_head'

@[simp]
theorem head!_cons [Inhabited α] (a : α) (l : List α) : head! (a :: l) = a :=
  rfl
#align list.head_cons List.head!_cons

#align list.tail_nil List.tail_nil

#align list.tail_cons List.tail_cons


@[simp]
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
    head! (s ++ t) = head! s :=
  by
  induction s
  contradiction
  rfl
#align list.head_append List.head!_append

theorem head?_append {s t : List α} {x : α} (h : x ∈ s.head?) : x ∈ (s ++ t).head? := by
  cases s
  contradiction
  exact h
#align list.head'_append List.head?_append

theorem head?_append_of_ne_nil :
    ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []), head? (l₁ ++ l₂) = head? l₁
  | [], _, hl₁ => by contradiction
  | x :: l₁, _, _ => rfl
#align list.head'_append_of_ne_nil List.head?_append_of_ne_nil

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
    tail (l ++ [a]) = tail l ++ [a] := by
  induction l
  contradiction
  rw [tail, cons_append, tail]
#align list.tail_append_singleton_of_ne_nil List.tail_append_singleton_of_ne_nil

theorem cons_head?_tail : ∀ {l : List α} {a : α} (_ : a ∈ head? l), a :: tail l = l
  | [], a, h => by contradiction
  | b :: l, a, h => by
    simp at h
    simp [h]
#align list.cons_head'_tail List.cons_head?_tail

theorem head!_mem_head? [Inhabited α] : ∀ {l : List α} (_ : l ≠ []), head! l ∈ head? l
  | [], h => by contradiction
  | a :: l, _ => rfl
#align list.head_mem_head' List.head!_mem_head?

theorem cons_head!_tail [Inhabited α] {l : List α} (h : l ≠ []) : head! l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)
#align list.cons_head_tail List.cons_head!_tail

theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  have h' := mem_cons_self l.head! l.tail
  rwa [cons_head!_tail h] at h'
#align list.head_mem_self List.head!_mem_self

@[simp]
theorem head?_map (f : α → β) (l) : head? (map f l) = (head? l).map f := by cases l <;> rfl
#align list.head'_map List.head?_map

theorem tail_append_of_ne_nil (l l' : List α) (h : l ≠ []) : (l ++ l').tail = l.tail ++ l' := by
  cases l
  · contradiction
  · simp
#align list.tail_append_of_ne_nil List.tail_append_of_ne_nil

-- Porting note: there was a default argument for `h'` `by simpa [← lt_tsub_iff_right] using h`.
@[simp]
theorem nthLe_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length) :
    l.tail.nthLe i h = l.nthLe (i + 1) h' := by
  cases l
  · cases h
  · rfl
#align list.nth_le_tail List.nthLe_tail

theorem nthLe_cons_aux {l : List α} {a : α} {n} (hn : n ≠ 0) (h : n < (a :: l).length) :
    n - 1 < l.length := by
  contrapose! h
  rw [length_cons]
  convert succ_le_succ h
  exact (Nat.succ_pred_eq_of_pos hn.bot_lt).symm
#align list.nth_le_cons_aux List.nthLe_cons_aux

theorem nthLe_cons {l : List α} {a : α} {n} (hl) :
    (a :: l).nthLe n hl = if hn : n = 0 then a else l.nthLe (n - 1) (nthLe_cons_aux hn hl) := by
  split_ifs with h
  · simp [nthLe, h]
  cases l
  · rw [length_singleton, lt_succ_iff, nonpos_iff_eq_zero] at hl
    contradiction
  cases n
  · contradiction
  rfl
#align list.nth_le_cons List.nthLe_cons

@[simp]
theorem modify_head_modify_head (l : List α) (f g : α → α) :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp
#align list.modify_head_modify_head List.modify_head_modify_head

/-! ### Induction from the right -/


/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
def reverseRecOn {C : List α → Sort _} (l : List α) (H0 : C [])
    (H1 : ∀ (l : List α) (a : α), C l → C (l ++ [a])) : C l := by
  rw [← reverse_reverse l]
  match h:(reverse l) with
  | [] => exact H0
  | head :: tail =>
    have : tail.length < l.length := by
        rw [← length_reverse l, h, length_cons]
        simp [Nat.lt_succ]
    let ih := reverseRecOn (reverse tail) H0 H1
    rw [reverse_cons]
    exact H1 _ _ ih
termination_by _ _ l _ _ => l.length
#align list.reverse_rec_on List.reverseRecOn

/- warning: list.bidirectional_rec -> List.bidirectionalRec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {C : (List.{u} α) -> Sort.{u_1}}, (C (List.nil.{u} α)) -> (forall (a : α), C (List.cons.{u} α a (List.nil.{u} α))) -> (forall (a : α) (l : List.{u} α) (b : α), (C l) -> (C (List.cons.{u} α a (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l (List.cons.{u} α b (List.nil.{u} α)))))) -> (forall (l : List.{u} α), C l)
but is expected to have type
  forall {α : Type.{u}} {C : (List.{u} α) -> Sort.{_aux_param_0}}, (C (List.nil.{u} α)) -> (forall (a : α), C (List.cons.{u} α a (List.nil.{u} α))) -> (forall (a : α) (l : List.{u} α) (b : α), (C l) -> (C (List.cons.{u} α a (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l (List.cons.{u} α b (List.nil.{u} α)))))) -> (forall (l : List.{u} α), C l)
Case conversion may be inaccurate. Consider using '#align list.bidirectional_rec List.bidirectionalRecₓ'. -/
/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectionalRec {C : List α → Sort _} (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : ∀ l, C l
  | [] => H0
  | [a] => H1 a
  | a :: b :: l => by
    let l' := init (b :: l)
    let b' := last (b :: l) (cons_ne_nil _ _)
    have : length l' < length (a :: b :: l) := by
      change _ < length l + 2
      simp
    rw [← init_append_last (cons_ne_nil b l)]
    have : C l' := bidirectionalRec H0 H1 Hn l'
    exact Hn a l' b' ‹C l'›
termination_by' measure List.length
#align list.bidirectional_rec List.bidirectionalRec

/-- Like `bidirectionalRec`, but with the list parameter placed first. -/
@[elab_as_elim]
def bidirectionalRecOn {C : List α → Sort _} (l : List α) (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
  bidirectionalRec H0 H1 Hn l
#align list.bidirectional_rec_on List.bidirectionalRecOn

/-! ### sublists -/

attribute [refl] List.Sublist.refl

#align list.nil_sublist List.nil_sublist

#align list.sublist.refl List.Sublist.refl

#align list.sublist.trans List.Sublist.trans

#align list.sublist_cons List.sublist_cons

#align list.sublist_of_cons_sublist List.sublist_of_cons_sublist

theorem Sublist.cons_cons {l₁ l₂ : List α} (a : α) (s : l₁ <+ l₂) : a :: l₁ <+ a :: l₂ :=
  Sublist.cons₂ _ s
#align list.sublist.cons_cons List.Sublist.cons_cons

#align list.sublist_append_left List.sublist_append_left

#align list.sublist_append_right List.sublist_append_right

theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ <+ a :: l₂ :=
  Sublist.cons _
#align list.sublist_cons_of_sublist List.sublist_cons_of_sublist

#align list.sublist_append_of_sublist_left List.sublist_append_of_sublist_left

#align list.sublist_append_of_sublist_right List.sublist_append_of_sublist_right

theorem sublist_of_cons_sublist_cons {l₁ l₂ : List α} : ∀ {a : α}, a :: l₁ <+ a :: l₂ → l₁ <+ l₂
  | _, Sublist.cons _ s => sublist_of_cons_sublist s
  | _, Sublist.cons₂ _ s => s
#align list.sublist_of_cons_sublist_cons List.sublist_of_cons_sublist_cons

theorem cons_sublist_cons_iff {l₁ l₂ : List α} {a : α} : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  ⟨sublist_of_cons_sublist_cons, Sublist.cons_cons _⟩
#align list.cons_sublist_cons_iff List.cons_sublist_cons_iff

#align list.append_sublist_append_left List.append_sublist_append_left

#align list.sublist.append_right List.Sublist.append_right

#align list.sublist_or_mem_of_sublist List.sublist_or_mem_of_sublist

#align list.sublist.reverse List.Sublist.reverse

@[simp]
theorem reverse_sublist_iff {l₁ l₂ : List α} : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
  ⟨fun h => l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, Sublist.reverse⟩
#align list.reverse_sublist_iff List.reverse_sublist_iff

#align list.append_sublist_append_right List.append_sublist_append_right

#align list.sublist.append List.Sublist.append

#align list.sublist.subset List.Sublist.subset

@[simp]
theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l :=
  ⟨fun h => h.subset (mem_singleton_self _), fun h =>
    let ⟨_, _, e⟩ := mem_split h
    e.symm ▸ ((nil_sublist _).cons_cons _).trans (sublist_append_right _ _)⟩
#align list.singleton_sublist List.singleton_sublist

theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil <| s.subset
#align list.eq_nil_of_sublist_nil List.eq_nil_of_sublist_nil

@[simp]
theorem sublist_nil_iff_eq_nil {l : List α} : l <+ [] ↔ l = [] :=
  ⟨eq_nil_of_sublist_nil, fun H => H ▸ Sublist.refl _⟩
#align list.sublist_nil_iff_eq_nil List.sublist_nil_iff_eq_nil

@[simp]
theorem repeat_sublist_repeat (a : α) {m n} : List.repeat a m <+ List.repeat a n ↔ m ≤ n :=
  ⟨fun h => by simpa only [length_repeat] using h.length_le, fun h => by
    induction h <;> [rfl, simp only [*, repeat_succ, Sublist.cons]]⟩
#align list.repeat_sublist_repeat List.repeat_sublist_repeat

theorem sublist_repeat_iff {l : List α} {a : α} {n : ℕ} :
    l <+ List.repeat a n ↔ ∃ k ≤ n, l = List.repeat a k :=
  ⟨fun h =>
    ⟨l.length, h.length_le.trans (length_repeat _ _).le,
      eq_repeat.mpr ⟨rfl, fun b hb => List.eq_of_mem_repeat (h.subset hb)⟩⟩,
    by
    rintro ⟨k, h, rfl⟩
    exact (repeat_sublist_repeat _).mpr h⟩
#align list.sublist_repeat_iff List.sublist_repeat_iff

theorem Sublist.eq_of_length : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
  | _, _, Sublist.slnil, _ => rfl
  | _, _, Sublist.cons a s, h => by
    cases s.length_le.not_lt (by rw [h]; apply lt_succ_self)
  | _, _, Sublist.cons₂ a s, h => by
    rw [length, length] at h; injection h with h; rw [s.eq_of_length h]
#align list.sublist.eq_of_length List.Sublist.eq_of_length

theorem Sublist.eq_of_length_le (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) : l₁ = l₂ :=
  s.eq_of_length <| s.length_le.antisymm h
#align list.sublist.eq_of_length_le List.Sublist.eq_of_length_le

theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le
#align list.sublist.antisymm List.Sublist.antisymm

instance decidableSublist [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+ l₂)
  | [], l₂ => isTrue <| nil_sublist _
  | a :: l₁, [] => isFalse fun h => List.noConfusion <| eq_nil_of_sublist_nil h
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      @decidable_of_decidable_of_iff _ _ (decidableSublist l₁ l₂) <| by
        rw [← h]; exact ⟨Sublist.cons_cons _, sublist_of_cons_sublist_cons⟩
    else
      @decidable_of_decidable_of_iff _ _ (decidableSublist (a :: l₁) l₂)
        ⟨sublist_cons_of_sublist _, fun s =>
          match a, l₁, s, h with
          | _, _, Sublist.cons _ s', h => s'
          | _, _, Sublist.cons₂ t _, h => absurd rfl h⟩
#align list.decidable_sublist List.decidableSublist

/-! ### indexOf -/


section IndexOf

variable [DecidableEq α]

@[simp]
theorem indexOf_nil (a : α) : indexOf a [] = 0 :=
  rfl
#align list.index_of_nil List.indexOf_nil

theorem indexOf_cons (a b : α) (l : List α) :
    indexOf a (b :: l) = if a = b then 0 else succ (indexOf a l) :=
  rfl
#align list.index_of_cons List.indexOf_cons

theorem indexOf_cons_eq {a b : α} (l : List α) : a = b → indexOf a (b :: l) = 0 := fun e =>
  if_pos e
#align list.index_of_cons_eq List.indexOf_cons_eq

@[simp]
theorem indexOf_cons_self (a : α) (l : List α) : indexOf a (a :: l) = 0 :=
  indexOf_cons_eq _ rfl
#align list.index_of_cons_self List.indexOf_cons_self

@[simp]
theorem indexOf_cons_ne {a b : α} (l : List α) : a ≠ b → indexOf a (b :: l) = succ (indexOf a l) :=
  fun n => if_neg n
#align list.index_of_cons_ne List.indexOf_cons_ne

theorem indexOf_eq_length {a : α} {l : List α} : indexOf a l = length l ↔ a ∉ l := by
  induction' l with b l ih
  · exact iff_of_true rfl (not_mem_nil _)
  simp only [length, mem_cons_iff, index_of_cons]; split_ifs
  · exact iff_of_false (by rintro ⟨⟩) fun H => H <| Or.inl h
  · simp only [h, false_or_iff]
    rw [← ih]
    exact succ_inj'
#align list.index_of_eq_length List.indexOf_eq_length

@[simp]
theorem indexOf_of_not_mem {l : List α} {a : α} : a ∉ l → indexOf a l = length l :=
  indexOf_eq_length.2
#align list.index_of_of_not_mem List.indexOf_of_not_mem

theorem indexOf_le_length {a : α} {l : List α} : indexOf a l ≤ length l := by
  induction' l with b l ih; · rfl
  simp only [length, indexOf_cons]
  by_cases h : a = b;
  · rw [if_pos h]
    exact Nat.zero_le _
  rw [if_neg h]; exact succ_le_succ ih
#align list.index_of_le_length List.indexOf_le_length

theorem indexOf_lt_length {a} {l : List α} : indexOf a l < length l ↔ a ∈ l :=
  ⟨fun h => Decidable.by_contradiction fun al => Nat.ne_of_lt h <| indexOf_eq_length.2 al, fun al =>
    (lt_of_le_of_ne indexOf_le_length) fun h => indexOf_eq_length.1 h al⟩
#align list.index_of_lt_length List.indexOf_lt_length

theorem indexOf_append_of_mem {a : α} (h : a ∈ l₁) : indexOf a (l₁ ++ l₂) = indexOf a l₁ := by
  induction' l₁ with d₁ t₁ ih
  · exfalso
    exact not_mem_nil a h
  rw [List.cons_append]
  by_cases hh : a = d₁
  · iterate 2 rw [indexOf_cons_eq _ hh]
  rw [indexOf_cons_ne _ hh, indexOf_cons_ne _ hh, ih (mem_of_ne_of_mem hh h)]
#align list.index_of_append_of_mem List.indexOf_append_of_mem

theorem indexOf_append_of_not_mem {a : α} (h : a ∉ l₁) :
    indexOf a (l₁ ++ l₂) = l₁.length + indexOf a l₂ := by
  induction' l₁ with d₁ t₁ ih
  · rw [List.nil_append, List.length, zero_add]
  rw [List.cons_append, indexOf_cons_ne _ (ne_of_not_mem_cons h), List.length,
    ih (not_mem_of_not_mem_cons h), Nat.succ_add]
#align list.index_of_append_of_not_mem List.indexOf_append_of_not_mem

end IndexOf

/-! ### nth element -/


theorem nth_le_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ n h, nthLe l n h = a
  | a, _ :: l, Or.inl rfl => ⟨0, succ_pos _, rfl⟩
  | a, b :: l, Or.inr m =>
    let ⟨n, h, e⟩ := nth_le_of_mem m
    ⟨n + 1, succ_lt_succ h, e⟩
#align list.nth_le_of_mem List.nth_le_of_mem

theorem nth_le_nth : ∀ {l : List α} {n} (h), nth l n = some (nthLe l n h)
  | a :: l, 0, h => rfl
  | a :: l, n + 1, h => @nth_le_nth l n _
#align list.nth_le_nth List.nth_le_nth

theorem nth_len_le : ∀ {l : List α} {n}, length l ≤ n → nth l n = none
  | [], n, h => rfl
  | a :: l, n + 1, h => nth_len_le (le_of_succ_le_succ h)
#align list.nth_len_le List.nth_len_le

@[simp]
theorem nth_length (l : List α) : l.nth l.length = none :=
  nth_len_le le_rfl
#align list.nth_length List.nth_length

theorem nth_eq_some {l : List α} {n a} : nth l n = some a ↔ ∃ h, nthLe l n h = a :=
  ⟨fun e =>
    have h : n < length l := lt_of_not_ge fun hn => by rw [nth_len_le hn] at e; contradiction
    ⟨h, by rw [nth_le_nth h] at e; injection e with e <;> apply nth_le_mem⟩,
    fun ⟨h, e⟩ => e ▸ nth_le_nth _⟩
#align list.nth_eq_some List.nth_eq_some

@[simp]
theorem nth_eq_none_iff : ∀ {l : List α} {n}, nth l n = none ↔ length l ≤ n := by
  intros ; constructor
  · intro h
    by_contra h'
    have h₂ : ∃ h, l.nth_le n h = l.nth_le n (lt_of_not_ge h') := ⟨lt_of_not_ge h', rfl⟩
    rw [← nth_eq_some, h] at h₂
    cases h₂
  · solve_by_elim [nth_len_le]
#align list.nth_eq_none_iff List.nth_eq_none_iff

theorem nth_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, nth l n = some a :=
  let ⟨n, h, e⟩ := nth_le_of_mem h
  ⟨n, by rw [nth_le_nth, e]⟩
#align list.nth_of_mem List.nth_of_mem

theorem nth_le_mem : ∀ (l : List α) (n h), nthLe l n h ∈ l
  | a :: l, 0, h => mem_cons_self _ _
  | a :: l, n + 1, h => mem_cons_of_mem _ (nth_le_mem l _ _)
#align list.nth_le_mem List.nth_le_mem

theorem nth_mem {l : List α} {n a} (e : nth l n = some a) : a ∈ l :=
  let ⟨h, e⟩ := nth_eq_some.1 e
  e ▸ nth_le_mem _ _ _
#align list.nth_mem List.nth_mem

theorem mem_iff_nth_le {a} {l : List α} : a ∈ l ↔ ∃ n h, nthLe l n h = a :=
  ⟨nth_le_of_mem, fun ⟨n, h, e⟩ => e ▸ nth_le_mem _ _ _⟩
#align list.mem_iff_nth_le List.mem_iff_nth_le

theorem mem_iff_nth {a} {l : List α} : a ∈ l ↔ ∃ n, nth l n = some a :=
  mem_iff_nth_le.trans <| exists_congr fun n => nth_eq_some.symm
#align list.mem_iff_nth List.mem_iff_nth

theorem nth_zero (l : List α) : l.nth 0 = l.head' := by cases l <;> rfl
#align list.nth_zero List.nth_zero

theorem nth_injective {α : Type u} {xs : List α} {i j : ℕ} (h₀ : i < xs.length) (h₁ : Nodup xs)
    (h₂ : xs.nth i = xs.nth j) : i = j := by
  induction' xs with x xs generalizing i j
  · cases h₀
  · cases i <;> cases j
    case zero.zero => rfl
    case succ.succ =>
      congr ; cases h₁
      apply xs_ih <;> solve_by_elim [lt_of_succ_lt_succ]
    iterate 2
      dsimp at h₂
      cases' h₁ with _ _ h h'
      cases h x _ rfl
      rw [mem_iff_nth]
      first |exact ⟨_, h₂.symm⟩|exact ⟨_, h₂⟩
#align list.nth_injective List.nth_injective

@[simp]
theorem nth_map (f : α → β) : ∀ l n, nth (map f l) n = (nth l n).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nth_map f l n
#align list.nth_map List.nth_map

theorem nth_le_map (f : α → β) {l n} (H1 H2) : nthLe (map f l) n H1 = f (nthLe l n H2) :=
  Option.some.inj <| by rw [← nth_le_nth, nth_map, nth_le_nth] <;> rfl
#align list.nth_le_map List.nth_le_map

/-- A version of `nth_le_map` that can be used for rewriting. -/
theorem nth_le_map_rev (f : α → β) {l n} (H) :
    f (nthLe l n H) = nthLe (map f l) n ((length_map f l).symm ▸ H) :=
  (nth_le_map f _ _).symm
#align list.nth_le_map_rev List.nth_le_map_rev

@[simp]
theorem nth_le_map' (f : α → β) {l n} (H) :
    nthLe (map f l) n H = f (nthLe l n (length_map f l ▸ H)) :=
  nth_le_map f _ _
#align list.nth_le_map' List.nth_le_map'

/-- If one has `nth_le L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
theorem nth_le_of_eq {L L' : List α} (h : L = L') {i : ℕ} (hi : i < L.length) :
    nthLe L i hi = nthLe L' i (h ▸ hi) := by
  congr
#align list.nth_le_of_eq List.nth_le_of_eq

@[simp]
theorem nth_le_singleton (a : α) {n : ℕ} (hn : n < 1) : nthLe [a] n hn = a := by
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero (le_of_lt_succ hn)
  subst hn0 <;> rfl
#align list.nth_le_singleton List.nth_le_singleton

theorem nth_le_zero [Inhabited α] {L : List α} (h : 0 < L.length) : L.nthLe 0 h = L.head := by
  cases L
  cases h
  simp
#align list.nth_le_zero List.nth_le_zero

theorem nth_le_append :
    ∀ {l₁ l₂ : List α} {n : ℕ} (hn₁) (hn₂), (l₁ ++ l₂).nthLe n hn₁ = l₁.nthLe n hn₂
  | [], _, n, hn₁, hn₂ => (Nat.not_lt_zero _ hn₂).elim
  | a :: l, _, 0, hn₁, hn₂ => rfl
  | a :: l, _, n + 1, hn₁, hn₂ => by simp only [nth_le, cons_append] <;> exact nth_le_append _ _
#align list.nth_le_append List.nth_le_append

theorem nth_le_append_right_aux {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n)
    (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length := by
  rw [List.length_append] at h₂
  apply lt_of_add_lt_add_right
  rwa [Nat.sub_add_cancel h₁, Nat.add_comm]
#align list.nth_le_append_right_aux List.nth_le_append_right_aux

theorem nth_le_append_right :
    ∀ {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂),
      (l₁ ++ l₂).nthLe n h₂ = l₂.nthLe (n - l₁.length) (nth_le_append_right_aux h₁ h₂)
  | [], _, n, h₁, h₂ => rfl
  | a :: l, _, n + 1, h₁, h₂ => by
    dsimp
    conv =>
      rhs
      congr
      skip
      rw [Nat.add_sub_add_right]
    rw [nth_le_append_right (nat.lt_succ_iff.mp h₁)]
#align list.nth_le_append_right List.nth_le_append_right

@[simp]
theorem nth_le_repeat (a : α) {n m : ℕ} (h : m < (List.repeat a n).length) :
    (List.repeat a n).nthLe m h = a :=
  eq_of_mem_repeat (nth_le_mem _ _ _)
#align list.nth_le_repeat List.nth_le_repeat

theorem nth_append {l₁ l₂ : List α} {n : ℕ} (hn : n < l₁.length) : (l₁ ++ l₂).nth n = l₁.nth n := by
  have hn' : n < (l₁ ++ l₂).length :=
    lt_of_lt_of_le hn (by rw [length_append] <;> exact Nat.le_add_right _ _)
  rw [nth_le_nth hn, nth_le_nth hn', nth_le_append]
#align list.nth_append List.nth_append

theorem nth_append_right {l₁ l₂ : List α} {n : ℕ} (hn : l₁.length ≤ n) :
    (l₁ ++ l₂).nth n = l₂.nth (n - l₁.length) := by
  by_cases hl : n < (l₁ ++ l₂).length
  · rw [nth_le_nth hl, nth_le_nth, nth_le_append_right hn]
  · rw [nth_len_le (le_of_not_lt hl), nth_len_le]
    rw [not_lt, length_append] at hl
    exact le_tsub_of_add_le_left hl
#align list.nth_append_right List.nth_append_right

theorem last_eq_nth_le :
    ∀ (l : List α) (h : l ≠ []),
      last l h = l.nthLe (l.length - 1) (Nat.sub_lt (length_pos_of_ne_nil h) one_pos)
  | [], h => rfl
  | [a], h => by rw [last_singleton, nth_le_singleton]
  | a :: b :: l, h => by
    rw [last_cons, last_eq_nth_le (b :: l)]
    rfl
    exact cons_ne_nil b l
#align list.last_eq_nth_le List.last_eq_nth_le

theorem nth_le_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.nthLe (l.length - 1) h =
      l.last
        (by
          rintro rfl
          exact Nat.lt_irrefl 0 h) :=
  (last_eq_nth_le l _).symm
#align list.nth_le_length_sub_one List.nth_le_length_sub_one

@[simp]
theorem nth_concat_length : ∀ (l : List α) (a : α), (l ++ [a]).nth l.length = some a
  | [], a => rfl
  | b :: l, a => by rw [cons_append, length_cons, nth, nth_concat_length]
#align list.nth_concat_length List.nth_concat_length

theorem nth_le_cons_length (x : α) (xs : List α) (n : ℕ) (h : n = xs.length) :
    (x :: xs).nthLe n (by simp [h]) = (x :: xs).last (cons_ne_nil x xs) := by
  rw [last_eq_nth_le]
  congr
  simp [h]
#align list.nth_le_cons_length List.nth_le_cons_length

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.nthLe n h] := by
  induction' l with x l ih generalizing n
  · cases h
  · by_cases h₁ : l = []
    · subst h₁
      rw [nth_le_singleton]
      simp [lt_succ_iff] at h
      subst h
      simp
    have h₂ := h
    rw [length_cons, Nat.lt_succ_iff, le_iff_eq_or_lt] at h₂
    cases n
    · simp
    rw [drop, nth_le]
    apply ih
#align list.take_one_drop_eq_of_lt_length List.take_one_drop_eq_of_lt_length

/- warning: list.ext -> List.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {l₁ : List.{u} α} {l₂ : List.{u} α}, (forall (n : Nat), Eq.{succ u} (Option.{u} α) (List.nth.{u} α l₁ n) (List.nth.{u} α l₂ n)) -> (Eq.{succ u} (List.{u} α) l₁ l₂)
but is expected to have type
  forall {α : Type.{u_1}} {l₁ : List.{u_1} α} {l₂ : List.{u_1} α}, (forall (n : Nat), Eq.{succ u_1} (Option.{u_1} α) (List.get?.{u_1} α l₁ n) (List.get?.{u_1} α l₂ n)) -> (Eq.{succ u_1} (List.{u_1} α) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align list.ext List.extₓ'. -/
@[ext]
theorem ext : ∀ {l₁ l₂ : List α}, (∀ n, nth l₁ n = nth l₂ n) → l₁ = l₂
  | [], [], h => rfl
  | a :: l₁, [], h => by have h0 := h 0 <;> contradiction
  | [], a' :: l₂, h => by have h0 := h 0 <;> contradiction
  | a :: l₁, a' :: l₂, h => by
    have h0 : some a = some a' := h 0 <;> injection h0 with aa <;>
          simp only [aa, ext fun n => h (n + 1)] <;>
        constructor <;>
      rfl
#align list.ext List.ext

theorem ext_le {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ n h₁ h₂, nthLe l₁ n h₁ = nthLe l₂ n h₂) : l₁ = l₂ :=
  ext fun n =>
    if h₁ : n < length l₁ then by rw [nth_le_nth, nth_le_nth, h n h₁ (by rwa [← hl])]
    else by
      let h₁ := le_of_not_gt h₁
      rw [nth_len_le h₁, nth_len_le]
      rwa [← hl]
#align list.ext_le List.ext_le

@[simp]
theorem indexOf_nth_le [DecidableEq α] {a : α} : ∀ {l : List α} (h), nthLe l (indexOf a l) h = a
  | b :: l, h => by
    by_cases h' : a = b <;>
      simp only [h', if_pos, if_false, index_of_cons, nth_le, @index_of_nth_le l]
#align list.index_of_nth_le List.indexOf_nth_le

@[simp]
theorem indexOf_nth [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    nth l (indexOf a l) = some a := by rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]
#align list.index_of_nth List.indexOf_nth

theorem nth_le_reverse_aux1 :
    ∀ (l r : List α) (i h1 h2), nthLe (reverseCore l r) (i + length l) h1 = nthLe r i h2
  | [], r, i => fun h1 h2 => rfl
  | a :: l, r, i => by
    rw [show i + length (a :: l) = i + 1 + length l from add_right_comm i (length l) 1] <;>
      exact fun h1 h2 => nth_le_reverse_aux1 l (a :: r) (i + 1) h1 (succ_lt_succ h2)
#align list.nth_le_reverse_aux1 List.nth_le_reverse_aux1

theorem indexOf_inj [DecidableEq α] {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    indexOf x l = indexOf y l ↔ x = y :=
  ⟨fun h => by
    have :
      nthLe l (indexOf x l) (index_of_lt_length.2 hx) =
        nthLe l (indexOf y l) (index_of_lt_length.2 hy) :=
      by simp only [h]
    simpa only [index_of_nth_le] , fun h => by subst h⟩
#align list.index_of_inj List.indexOf_inj

theorem nth_le_reverse_aux2 :
    ∀ (l r : List α) (i : Nat) (h1) (h2),
      nthLe (reverseCore l r) (length l - 1 - i) h1 = nthLe l i h2
  | [], r, i, h1, h2 => absurd h2 (Nat.not_lt_zero _)
  | a :: l, r, 0, h1, h2 => by
    have aux := nth_le_reverse_aux1 l (a :: r) 0
    rw [zero_add] at aux
    exact aux _ (zero_lt_succ _)
  | a :: l, r, i + 1, h1, h2 => by
    have aux := nth_le_reverse_aux2 l (a :: r) i
    have heq :=
      calc
        length (a :: l) - 1 - (i + 1) = length l - (1 + i) := by rw [add_comm] <;> rfl
        _ = length l - 1 - i := by rw [← tsub_add_eq_tsub_tsub]

    rw [← HEq] at aux
    apply aux
#align list.nth_le_reverse_aux2 List.nth_le_reverse_aux2

@[simp]
theorem nth_le_reverse (l : List α) (i : Nat) (h1 h2) :
    nthLe (reverse l) (length l - 1 - i) h1 = nthLe l i h2 :=
  nth_le_reverse_aux2 _ _ _ _ _
#align list.nth_le_reverse List.nth_le_reverse

theorem nth_le_reverse' (l : List α) (n : ℕ) (hn : n < l.reverse.length) (hn') :
    l.reverse.nthLe n hn = l.nthLe (l.length - 1 - n) hn' := by
  rw [eq_comm]
  convert nth_le_reverse l.reverse _ _ _ using 1
  · simp
  · simpa
#align list.nth_le_reverse' List.nth_le_reverse'

theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) :
    l = [l.nthLe 0 (h.symm ▸ zero_lt_one)] := by
  refine' ext_le (by convert h) fun n h₁ h₂ => _
  simp only [nth_le_singleton]
  congr
  exact eq_bot_iff.mpr (nat.lt_succ_iff.mp h₂)
#align list.eq_cons_of_length_one List.eq_cons_of_length_one

theorem nth_le_eq_iff {l : List α} {n : ℕ} {x : α} {h} : l.nthLe n h = x ↔ l.nth n = some x := by
  rw [nth_eq_some]
  tauto
#align list.nth_le_eq_iff List.nth_le_eq_iff

theorem some_nth_le_eq {l : List α} {n : ℕ} {h} : some (l.nthLe n h) = l.nth n := by
  symm
  rw [nth_eq_some]
  tauto
#align list.some_nth_le_eq List.some_nth_le_eq

theorem modify_nth_tail_modify_nth_tail {f g : List α → List α} (m : ℕ) :
    ∀ (n) (l : List α),
      (l.modifyNthTail f n).modifyNthTail g (m + n) =
        l.modifyNthTail (fun l => (f l).modifyNthTail g m) n
  | 0, l => rfl
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (List.cons a) (modify_nth_tail_modify_nth_tail n l)
#align list.modify_nth_tail_modify_nth_tail List.modify_nth_tail_modify_nth_tail

theorem modify_nth_tail_modify_nth_tail_le {f g : List α → List α} (m n : ℕ) (l : List α)
    (h : n ≤ m) :
    (l.modifyNthTail f n).modifyNthTail g m =
      l.modifyNthTail (fun l => (f l).modifyNthTail g (m - n)) n :=
  by
  rcases exists_add_of_le h with ⟨m, rfl⟩
  rw [add_tsub_cancel_left, add_comm, modify_nth_tail_modify_nth_tail]
#align list.modify_nth_tail_modify_nth_tail_le List.modify_nth_tail_modify_nth_tail_le

theorem modify_nth_tail_modify_nth_tail_same {f g : List α → List α} (n : ℕ) (l : List α) :
    (l.modifyNthTail f n).modifyNthTail g n = l.modifyNthTail (g ∘ f) n := by
  rw [modify_nth_tail_modify_nth_tail_le n n l (le_refl n), tsub_self] <;> rfl
#align list.modify_nth_tail_modify_nth_tail_same List.modify_nth_tail_modify_nth_tail_same

theorem modify_nth_tail_id : ∀ (n) (l : List α), l.modifyNthTail id n = l
  | 0, l => rfl
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (List.cons a) (modify_nth_tail_id n l)
#align list.modify_nth_tail_id List.modify_nth_tail_id

theorem remove_nth_eq_nth_tail : ∀ (n) (l : List α), removeNth l n = modifyNthTail tail n l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (cons _) (remove_nth_eq_nth_tail _ _)
#align list.remove_nth_eq_nth_tail List.remove_nth_eq_nth_tail

theorem update_nth_eq_modify_nth (a : α) :
    ∀ (n) (l : List α), updateNth l n a = modifyNth (fun _ => a) n l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, b :: l => congr_arg (cons _) (update_nth_eq_modify_nth _ _)
#align list.update_nth_eq_modify_nth List.update_nth_eq_modify_nth

theorem modify_nth_eq_update_nth (f : α → α) :
    ∀ (n) (l : List α), modifyNth f n l = ((fun a => updateNth l n (f a)) <$> nth l n).getOrElse l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, b :: l =>
    (congr_arg (cons b) (modify_nth_eq_update_nth n l)).trans <| by cases nth l n <;> rfl
#align list.modify_nth_eq_update_nth List.modify_nth_eq_update_nth

theorem nth_modify_nth (f : α → α) :
    ∀ (n) (l : List α) (m),
      nth (modifyNth f n l) m = (fun a => if n = m then f a else a) <$> nth l m
  | n, l, 0 => by cases l <;> cases n <;> rfl
  | n, [], m + 1 => by cases n <;> rfl
  | 0, a :: l, m + 1 => by cases nth l m <;> rfl
  | n + 1, a :: l, m + 1 =>
    (nth_modify_nth n l m).trans <| by
      cases' nth l m with b <;> by_cases n = m <;>
        simp only [h, if_pos, if_true, if_false, Option.map_none, Option.map_some, mt succ.inj,
          not_false_iff]
#align list.nth_modify_nth List.nth_modify_nth

theorem modify_nth_tail_length (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyNthTail f n l) = length l
  | 0, l => H _
  | n + 1, [] => rfl
  | n + 1, a :: l => @congr_arg _ _ _ _ (· + 1) (modify_nth_tail_length _ _)
#align list.modify_nth_tail_length List.modify_nth_tail_length

@[simp]
theorem modify_nth_length (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  modify_nth_tail_length _ fun l => by cases l <;> rfl
#align list.modify_nth_length List.modify_nth_length

@[simp]
theorem update_nth_length (l : List α) (n) (a : α) : length (updateNth l n a) = length l := by
  simp only [update_nth_eq_modify_nth, modify_nth_length]
#align list.update_nth_length List.update_nth_length

@[simp]
theorem nth_modify_nth_eq (f : α → α) (n) (l : List α) : nth (modifyNth f n l) n = f <$> nth l n :=
  by simp only [nth_modify_nth, if_pos]
#align list.nth_modify_nth_eq List.nth_modify_nth_eq

@[simp]
theorem nth_modify_nth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
    nth (modifyNth f m l) n = nth l n := by simp only [nth_modify_nth, if_neg h, id_map']
#align list.nth_modify_nth_ne List.nth_modify_nth_ne

theorem nth_update_nth_eq (a : α) (n) (l : List α) :
    nth (updateNth l n a) n = (fun _ => a) <$> nth l n := by
  simp only [update_nth_eq_modify_nth, nth_modify_nth_eq]
#align list.nth_update_nth_eq List.nth_update_nth_eq

theorem nth_update_nth_of_lt (a : α) {n} {l : List α} (h : n < length l) :
    nth (updateNth l n a) n = some a := by rw [nth_update_nth_eq, nth_le_nth h] <;> rfl
#align list.nth_update_nth_of_lt List.nth_update_nth_of_lt

theorem nth_update_nth_ne (a : α) {m n} (l : List α) (h : m ≠ n) :
    nth (updateNth l m a) n = nth l n := by
  simp only [update_nth_eq_modify_nth, nth_modify_nth_ne _ _ h]
#align list.nth_update_nth_ne List.nth_update_nth_ne

@[simp]
theorem update_nth_nil (n : ℕ) (a : α) : [].updateNth n a = [] :=
  rfl
#align list.update_nth_nil List.update_nth_nil

@[simp]
theorem update_nth_succ (x : α) (xs : List α) (n : ℕ) (a : α) :
    (x :: xs).updateNth n.succ a = x :: xs.updateNth n a :=
  rfl
#align list.update_nth_succ List.update_nth_succ

theorem update_nth_comm (a b : α) :
    ∀ {n m : ℕ} (l : List α) (h : n ≠ m),
      (l.updateNth n a).updateNth m b = (l.updateNth m b).updateNth n a
  | _, _, [], _ => by simp
  | 0, 0, x :: t, h => absurd rfl h
  | n + 1, 0, x :: t, h => by simp [List.updateNth]
  | 0, m + 1, x :: t, h => by simp [List.updateNth]
  | n + 1, m + 1, x :: t, h => by
    simp only [update_nth, true_and_iff, eq_self_iff_true]
    exact update_nth_comm t fun h' => h <| nat.succ_inj'.mpr h'
#align list.update_nth_comm List.update_nth_comm

@[simp]
theorem nth_le_update_nth_eq (l : List α) (i : ℕ) (a : α) (h : i < (l.updateNth i a).length) :
    (l.updateNth i a).nthLe i h = a := by
  rw [← Option.some_inj, ← nth_le_nth, nth_update_nth_eq, nth_le_nth] <;> simp_all
#align list.nth_le_update_nth_eq List.nth_le_update_nth_eq

@[simp]
theorem nth_le_update_nth_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.updateNth i a).length) :
    (l.updateNth i a).nthLe j hj = l.nthLe j (by simpa using hj) := by
  rw [← Option.some_inj, ← List.nth_le_nth, List.nth_update_nth_ne _ _ h, List.nth_le_nth]
#align list.nth_le_update_nth_of_ne List.nth_le_update_nth_of_ne

theorem mem_or_eq_of_mem_update_nth :
    ∀ {l : List α} {n : ℕ} {a b : α} (h : a ∈ l.updateNth n b), a ∈ l ∨ a = b
  | [], n, a, b, h => False.elim h
  | c :: l, 0, a, b, h => ((mem_cons_iff _ _ _).1 h).elim Or.inr (Or.inl ∘ mem_cons_of_mem _)
  | c :: l, n + 1, a, b, h =>
    ((mem_cons_iff _ _ _).1 h).elim (fun h => h ▸ Or.inl (mem_cons_self _ _)) fun h =>
      (mem_or_eq_of_mem_update_nth h).elim (Or.inl ∘ mem_cons_of_mem _) Or.inr
#align list.mem_or_eq_of_mem_update_nth List.mem_or_eq_of_mem_update_nth

section InsertNth

variable {a : α}

@[simp]
theorem insert_nth_zero (s : List α) (x : α) : insertNth 0 x s = x :: s :=
  rfl
#align list.insert_nth_zero List.insert_nth_zero

@[simp]
theorem insert_nth_succ_nil (n : ℕ) (a : α) : insertNth (n + 1) a [] = [] :=
  rfl
#align list.insert_nth_succ_nil List.insert_nth_succ_nil

@[simp]
theorem insert_nth_succ_cons (s : List α) (hd x : α) (n : ℕ) :
    insertNth (n + 1) x (hd :: s) = hd :: insertNth n x s :=
  rfl
#align list.insert_nth_succ_cons List.insert_nth_succ_cons

theorem length_insert_nth : ∀ n as, n ≤ length as → length (insertNth n a as) = length as + 1
  | 0, as, h => rfl
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => congr_arg Nat.succ <| length_insert_nth n as (Nat.le_of_succ_le_succ h)
#align list.length_insert_nth List.length_insert_nth

theorem remove_nth_insert_nth (n : ℕ) (l : List α) : (l.insertNth n a).removeNth n = l := by
  rw [remove_nth_eq_nth_tail, insert_nth, modify_nth_tail_modify_nth_tail_same] <;>
    exact modify_nth_tail_id _ _
#align list.remove_nth_insert_nth List.remove_nth_insert_nth

theorem insert_nth_remove_nth_of_ge :
    ∀ n m as,
      n < length as → n ≤ m → insertNth m a (as.removeNth n) = (as.insertNth (m + 1) a).removeNth n
  | 0, 0, [], has, _ => (lt_irrefl _ has).elim
  | 0, 0, a :: as, has, hmn => by simp [remove_nth, insert_nth]
  | 0, m + 1, a :: as, has, hmn => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insert_nth_remove_nth_of_ge n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_ge List.insert_nth_remove_nth_of_ge

theorem insert_nth_remove_nth_of_le :
    ∀ n m as,
      n < length as → m ≤ n → insertNth m a (as.removeNth n) = (as.insertNth m a).removeNth (n + 1)
  | n, 0, a :: as, has, hmn => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insert_nth_remove_nth_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_le List.insert_nth_remove_nth_of_le

theorem insert_nth_comm (a b : α) :
    ∀ (i j : ℕ) (l : List α) (h : i ≤ j) (hj : j ≤ length l),
      (l.insertNth i a).insertNth (j + 1) b = (l.insertNth j b).insertNth i a
  | 0, j, l => by simp [insert_nth]
  | i + 1, 0, l => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp [insert_nth] <;>
      exact insert_nth_comm i j l (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)
#align list.insert_nth_comm List.insert_nth_comm

theorem mem_insert_nth {a b : α} :
    ∀ {n : ℕ} {l : List α} (hi : n ≤ l.length), a ∈ l.insertNth n b ↔ a = b ∨ a ∈ l
  | 0, as, h => Iff.rfl
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    dsimp [List.insertNth]
    erw [mem_insert_nth (Nat.le_of_succ_le_succ h), ← or_assoc, or_comm' (a = a'), or_assoc]
#align list.mem_insert_nth List.mem_insert_nth

theorem insert_nth_of_length_lt (l : List α) (x : α) (n : ℕ) (h : l.length < n) :
    insertNth n x l = l := by
  induction' l with hd tl IH generalizing n
  · cases n
    · simpa using h
    · simp
  · cases n
    · simpa using h
    · simp only [Nat.succ_lt_succ_iff, length] at h
      simpa using IH _ h
#align list.insert_nth_of_length_lt List.insert_nth_of_length_lt

@[simp]
theorem insert_nth_length_self (l : List α) (x : α) : insertNth l.length x l = l ++ [x] := by
  induction' l with hd tl IH
  · simp
  · simpa using IH
#align list.insert_nth_length_self List.insert_nth_length_self

theorem length_le_length_insert_nth (l : List α) (x : α) (n : ℕ) :
    l.length ≤ (insertNth n x l).length := by
  cases' le_or_lt n l.length with hn hn
  · rw [length_insert_nth _ _ hn]
    exact (Nat.lt_succ_self _).le
  · rw [insert_nth_of_length_lt _ _ _ hn]
#align list.length_le_length_insert_nth List.length_le_length_insert_nth

theorem length_insert_nth_le_succ (l : List α) (x : α) (n : ℕ) :
    (insertNth n x l).length ≤ l.length + 1 := by
  cases' le_or_lt n l.length with hn hn
  · rw [length_insert_nth _ _ hn]
  · rw [insert_nth_of_length_lt _ _ _ hn]
    exact (Nat.lt_succ_self _).le
#align list.length_insert_nth_le_succ List.length_insert_nth_le_succ

theorem nth_le_insert_nth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insert_nth _ _ _)) :
    (insertNth n x l).nthLe k hk' = l.nthLe k hk := by
  induction' n with n IH generalizing k l
  · simpa using hn
  · cases' l with hd tl
    · simp
    · cases k
      · simp
      · rw [Nat.succ_lt_succ_iff] at hn
        simpa using IH _ _ hn _
#align list.nth_le_insert_nth_of_lt List.nth_le_insert_nth_of_lt

@[simp]
theorem nth_le_insert_nth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := by rwa [length_insert_nth _ _ hn, Nat.lt_succ_iff]) :
    (insertNth n x l).nthLe n hn' = x := by
  induction' l with hd tl IH generalizing n
  · simp only [length, nonpos_iff_eq_zero] at hn
    simp [hn]
  · cases n
    · simp
    · simp only [Nat.succ_le_succ_iff, length] at hn
      simpa using IH _ hn
#align list.nth_le_insert_nth_self List.nth_le_insert_nth_self

theorem nth_le_insert_nth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := by
      rwa [length_insert_nth _ _ (le_self_add.trans hk'.le), Nat.succ_lt_succ_iff]) :
    (insertNth n x l).nthLe (n + k + 1) hk = nthLe l (n + k) hk' := by
  induction' l with hd tl IH generalizing n k
  · simpa using hk'
  · cases n
    · simpa
    · simpa [succ_add] using IH _ _ _
#align list.nth_le_insert_nth_add_succ List.nth_le_insert_nth_add_succ

theorem insert_nth_injective (n : ℕ) (x : α) : Function.Injective (insertNth n x) := by
  induction' n with n IH
  · have : insert_nth 0 x = cons x := funext fun _ => rfl
    simp [this]
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> first |simpa [IH.eq_iff] using h|rfl
#align list.insert_nth_injective List.insert_nth_injective

end InsertNth

/-! ### map -/

#align list.map_nil List.map_nil

theorem map_eq_foldr (f : α → β) (l : List α) : map f l = foldr (fun a bs => f a :: bs) [] l := by
  induction l <;> simp [*]
#align list.map_eq_foldr List.map_eq_foldr

theorem map_congr {f g : α → β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]
#align list.map_congr List.map_congr

theorem map_eq_map_iff {f g : α → β} {l : List α} : map f l = map g l ↔ ∀ x ∈ l, f x = g x := by
  refine' ⟨_, map_congr⟩; intro h x hx
  rw [mem_iff_nth_le] at hx; rcases hx with ⟨n, hn, rfl⟩
  rw [nth_le_map_rev f, nth_le_map_rev g]; congr
#align list.map_eq_map_iff List.map_eq_map_iff

theorem map_concat (f : α → β) (a : α) (l : List α) : map f (concat l a) = concat (map f l) (f a) :=
  by
  induction l <;> [rfl, simp only [*, concat_eq_append, cons_append, map, map_append]]
#align list.map_concat List.map_concat

@[simp]
theorem map_id'' (l : List α) : map (fun x => x) l = l :=
  map_id _
#align list.map_id'' List.map_id''

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : List α) : map f l = l := by
  simp [show f = id from funext h]
#align list.map_id' List.map_id'

theorem eq_nil_of_map_eq_nil {f : α → β} {l : List α} (h : map f l = nil) : l = nil :=
  eq_nil_of_length_eq_zero <| by rw [← length_map f l, h] <;> rfl
#align list.eq_nil_of_map_eq_nil List.eq_nil_of_map_eq_nil

@[simp]
theorem map_join (f : α → β) (L : List (List α)) : map f (join L) = join (map (map f) L) := by
  induction L <;> [rfl, simp only [*, join, map, map_append]]
#align list.map_join List.map_join

theorem bind_ret_eq_map (f : α → β) (l : List α) : l.bind (List.ret ∘ f) = map f l := by
  unfold List.bind <;> induction l <;>
        simp only [map, join, List.ret, cons_append, nil_append, *] <;>
      constructor <;>
    rfl
#align list.bind_ret_eq_map List.bind_ret_eq_map

theorem bind_congr {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    List.bind l f = List.bind l g :=
  (congr_arg List.join <| map_congr h : _)
#align list.bind_congr List.bind_congr

@[simp]
theorem map_eq_map {α β} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl
#align list.map_eq_map List.map_eq_map

@[simp]
theorem map_tail (f : α → β) (l) : map f (tail l) = tail (map f l) := by cases l <;> rfl
#align list.map_tail List.map_tail

@[simp]
theorem map_injective_iff {f : α → β} : Injective (map f) ↔ Injective f := by
  constructor <;> intro h x y hxy
  · suffices [x] = [y] by simpa using this
    apply h
    simp [hxy]
  · induction' y with yh yt y_ih generalizing x
    simpa using hxy
    cases x
    simp at hxy
    simp at hxy
    simp [y_ih hxy.2, h hxy.1]
#align list.map_injective_iff List.map_injective_iff

/-- A single `list.map` of a composition of functions is equal to
composing a `list.map` with another `list.map`, fully applied.
This is the reverse direction of `list.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  (map_map _ _ _).symm
#align list.comp_map List.comp_map

/-- Composing a `list.map` with another `list.map` is equal to
a single `list.map` of composed functions.
-/
@[simp]
theorem map_comp_map (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) := by
  ext l
  rw [comp_map]
#align list.map_comp_map List.map_comp_map

theorem map_filter_eq_foldr (f : α → β) (p : α → Prop) [DecidablePred p] (as : List α) :
    map f (filter p as) = foldr (fun a bs => if p a then f a :: bs else bs) [] as := by
  induction as
  · rfl
  · simp! [*, apply_ite (map f)]
#align list.map_filter_eq_foldr List.map_filter_eq_foldr

theorem last_map (f : α → β) {l : List α} (hl : l ≠ []) :
    (l.map f).last (mt eq_nil_of_map_eq_nil hl) = f (l.last hl) := by
  induction' l with l_hd l_tl l_ih
  · apply (hl rfl).elim
  · cases l_tl
    · simp
    · simpa using l_ih
#align list.last_map List.last_map

theorem map_eq_repeat_iff {l : List α} {f : α → β} {b : β} :
    l.map f = List.repeat b l.length ↔ ∀ x ∈ l, f x = b := by
  induction' l with x l' ih
  ·
    simp only [List.repeat, length, not_mem_nil, IsEmpty.forall_iff, imp_true_iff, map_nil,
      eq_self_iff_true]
  · simp only [map, length, mem_cons_iff, forall_eq_or_imp, repeat_succ, and_congr_right_iff]
    exact fun _ => ih
#align list.map_eq_repeat_iff List.map_eq_repeat_iff

@[simp]
theorem map_const (l : List α) (b : β) : map (Function.const α b) l = List.repeat b l.length :=
  map_eq_repeat_iff.mpr fun _ _ => rfl
#align list.map_const List.map_const

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (Function.const α b₂) l) :
    b₁ = b₂ := by rw [map_const] at h; exact eq_of_mem_repeat h
#align list.eq_of_mem_map_const List.eq_of_mem_map_const

/-! ### map₂ -/


theorem nil_map₂ (f : α → β → γ) (l : List β) : map₂ f [] l = [] := by cases l <;> rfl
#align list.nil_map₂ List.nil_map₂

theorem map₂_nil (f : α → β → γ) (l : List α) : map₂ f l [] = [] := by cases l <;> rfl
#align list.map₂_nil List.map₂_nil

@[simp]
theorem map₂_flip (f : α → β → γ) : ∀ as bs, map₂ (flip f) bs as = map₂ f as bs
  | [], [] => rfl
  | [], b :: bs => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => by
    simp! [map₂_flip]
    rfl
#align list.map₂_flip List.map₂_flip

/-! ### take, drop -/


@[simp]
theorem take_zero (l : List α) : take 0 l = [] :=
  rfl
#align list.take_zero List.take_zero

@[simp]
theorem take_nil : ∀ n, take n [] = ([] : List α)
  | 0 => rfl
  | n + 1 => rfl
#align list.take_nil List.take_nil

theorem take_cons (n) (a : α) (l : List α) : take (succ n) (a :: l) = a :: take n l :=
  rfl
#align list.take_cons List.take_cons

#print List.take_length /-
@[simp]
theorem take_length : ∀ l : List α, take (length l) l = l
  | [] => rfl
  | a :: l => by change a :: take (length l) l = a :: l; rw [take_length]
#align list.take_length List.take_length
-/

theorem take_all_of_le : ∀ {n} {l : List α}, length l ≤ n → take n l = l
  | 0, [], _ => rfl
  | 0, a :: l, h => absurd h (not_le_of_gt (zero_lt_succ _))
  | n + 1, [], _ => rfl
  | n + 1, a :: l, h => by
    change a :: take n l = a :: l
    rw [take_all_of_le (le_of_succ_le_succ h)]
#align list.take_all_of_le List.take_all_of_le

@[simp]
theorem take_left : ∀ l₁ l₂ : List α, take (length l₁) (l₁ ++ l₂) = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congr_arg (cons a) (take_left l₁ l₂)
#align list.take_left List.take_left

theorem take_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left
#align list.take_left' List.take_left'

theorem take_take : ∀ (n m) (l : List α), take n (take m l) = take (min n m) l
  | n, 0, l => by rw [min_zero, take_zero, take_nil]
  | 0, m, l => by rw [zero_min, take_zero, take_zero]
  | succ n, succ m, nil => by simp only [take_nil]
  | succ n, succ m, a :: l => by
    simp only [take, min_succ_succ, take_take n m l]
#align list.take_take List.take_take

theorem take_repeat (a : α) : ∀ n m : ℕ, take n (List.repeat a m) = List.repeat a (min n m)
  | n, 0 => by simp
  | 0, m => by simp
  | succ n, succ m => by simp [min_succ_succ, take_repeat]
#align list.take_repeat List.take_repeat

theorem map_take {α β : Type _} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.take i).map f = (L.map f).take i
  | [], i => by simp
  | _, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    have : length t < length (h :: t) := by simp [length_cons]
    have ih := map_take f t n
    rw [ih]
termination_by _ _ _  l _ => l.length
decreasing_by assumption
#align list.map_take List.map_take

/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
theorem take_append_eq_append_take {l₁ l₂ : List α} {n : ℕ} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := by
  induction l₁ generalizing n; · simp
  cases n; · simp; simp [*]
#align list.take_append_eq_append_take List.take_append_eq_append_take

theorem take_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by simp [take_append_eq_append_take, tsub_eq_zero_iff_le.mpr h]
#align list.take_append_of_le_length List.take_append_of_le_length

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
theorem take_append {l₁ l₂ : List α} (i : ℕ) : take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ take i l₂ :=
  by simp [take_append_eq_append_take, take_all_of_le le_self_add]
#align list.take_append List.take_append

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem nth_le_take (L : List α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
    nthLe L i hi =
      nthLe (L.take j) i
        (by
          rw [length_take]
          exact lt_min hj hi) :=
  by
  rw [nth_le_of_eq (take_append_drop j L).symm hi]
  exact nth_le_append _ _
#align list.nth_le_take List.nth_le_take

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
theorem nth_le_take' (L : List α) {i j : ℕ} (hi : i < (L.take j).length) :
    nthLe (L.take j) i hi = nthLe L i (lt_of_lt_of_le hi (by simp [le_refl])) := by
  simp at hi
  rw [nth_le_take L _ hi.1]
#align list.nth_le_take' List.nth_le_take'

theorem nth_take {l : List α} {n m : ℕ} (h : m < n) : (l.take n).nth m = l.nth m := by
  induction' n with n hn generalizing l m
  · simp only [Nat.zero_eq] at h
    exact absurd h (not_lt_of_le m.zero_le)
  · cases' l with hd tl
    · simp only [take_nil]
    · cases m
      · simp only [nth, take]
      · simpa only using hn (Nat.lt_of_succ_lt_succ h)
#align list.nth_take List.nth_take

@[simp]
theorem nth_take_of_succ {l : List α} {n : ℕ} : (l.take (n + 1)).nth n = l.nth n :=
  nth_take (Nat.lt_succ_self n)
#align list.nth_take_of_succ List.nth_take_of_succ

theorem take_succ {l : List α} {n : ℕ} : l.take (n + 1) = l.take n ++ (l.nth n).toList := by
  induction' l with hd tl hl generalizing n
  · simp only [Option.toList, nth, take_nil, append_nil]
  · cases n
    · simp only [Option.toList, nth, eq_self_iff_true, and_self_iff, take, nil_append]
    · simp only [hl, cons_append, nth, eq_self_iff_true, and_self_iff, take]
#align list.take_succ List.take_succ

@[simp]
theorem take_eq_nil_iff {l : List α} {k : ℕ} : l.take k = [] ↔ l = [] ∨ k = 0 := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]
#align list.take_eq_nil_iff List.take_eq_nil_iff

theorem take_eq_take :
    ∀ {l : List α} {m n : ℕ}, l.take m = l.take n ↔ min m l.length = min n l.length
  | [], m, n => by simp
  | x :: xs, 0, 0 => by simp
  | x :: xs, m + 1, 0 => by simp
  | x :: xs, 0, n + 1 => by simp [@eq_comm ℕ 0]
  | x :: xs, m + 1, n + 1 => by simp [Nat.min_succ_succ, take_eq_take]
#align list.take_eq_take List.take_eq_take

theorem take_add (l : List α) (m n : ℕ) : l.take (m + n) = l.take m ++ (l.drop m).take n := by
  convert_to take (m + n) (take m l ++ drop m l) = take m l ++ take n (drop m l)
  · rw [take_append_drop]
  rw [take_append_eq_append_take, take_all_of_le, append_right_inj]; swap
  · trans m
    · apply length_take_le
    · simp
  simp only [take_eq_take, length_take, length_drop]
  generalize l.length = k; by_cases h : m ≤ k
  · simp [min_eq_left_iff.mpr h]
  · push_neg  at h
    simp [Nat.sub_eq_zero_of_le (le_of_lt h)]
#align list.take_add List.take_add

theorem init_eq_take (l : List α) : l.init = l.take l.length.pred := by
  cases' l with x l
  · simp [init]
  · induction' l with hd tl hl generalizing x
    · simp [init]
    · simp [init, hl]
#align list.init_eq_take List.init_eq_take

theorem init_take {n : ℕ} {l : List α} (h : n < l.length) : (l.take n).init = l.take n.pred := by
  simp [init_eq_take, min_eq_left_of_lt h, take_take, pred_le]
#align list.init_take List.init_take

@[simp]
theorem init_cons_of_ne_nil {α : Type _} {x : α} :
    ∀ {l : List α} (_ : l ≠ []), (x :: l).init = x :: l.init
  | [], h => False.elim (h rfl)
  | a :: l, _ => by simp [init]
#align list.init_cons_of_ne_nil List.init_cons_of_ne_nil

@[simp]
theorem init_append_of_ne_nil {α : Type _} {l : List α} :
    ∀ (l' : List α) (h : l ≠ []), (l' ++ l).init = l' ++ l.init
  | [], _ => by simp only [nil_append]
  | a :: l', h => by simp [append_ne_nil_of_ne_nil_right l' l h, init_append_of_ne_nil l' h]
#align list.init_append_of_ne_nil List.init_append_of_ne_nil

#align list.drop_eq_nil_of_le List.drop_eq_nil_of_le

theorem drop_eq_nil_iff_le {l : List α} {k : ℕ} : l.drop k = [] ↔ l.length ≤ k := by
  refine' ⟨fun h => _, drop_eq_nil_of_le⟩
  induction' k with k hk generalizing l
  · simp only [drop] at h
    simp [h]
  · cases l
    · simp
    · simp only [drop] at h
      simpa [Nat.succ_le_succ_iff] using hk h
#align list.drop_eq_nil_iff_le List.drop_eq_nil_iff_le

theorem tail_drop (l : List α) (n : ℕ) : (l.drop n).tail = l.drop (n + 1) := by
  induction' l with hd tl hl generalizing n
  · simp
  · cases n
    · simp
    · simp [hl]
#align list.tail_drop List.tail_drop

theorem cons_nth_le_drop_succ {l : List α} {n : ℕ} (hn : n < l.length) :
    l.nthLe n hn :: l.drop (n + 1) = l.drop n := by
  induction' l with hd tl hl generalizing n
  · exact absurd n.zero_le (not_le_of_lt (by simp at hn))
  · cases n
    · simp
    · simp only [Nat.succ_lt_succ_iff, List.length] at hn
      simpa [List.nthLe, List.drop] using hl hn
#align list.cons_nth_le_drop_succ List.cons_nth_le_drop_succ

#align list.drop_nil List.drop_nil

@[simp]
theorem drop_one : ∀ l : List α, drop 1 l = tail l
  | [] => rfl
  | _ :: _ => rfl
#align list.drop_one List.drop_one

theorem drop_add : ∀ (m n) (l : List α), drop (m + n) l = drop m (drop n l)
  | m, 0, l => rfl
  | m, n + 1, [] => (drop_nil _).symm
  | m, n + 1, a :: l => drop_add m n _
#align list.drop_add List.drop_add

@[simp]
theorem drop_left : ∀ l₁ l₂ : List α, drop (length l₁) (l₁ ++ l₂) = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_left l₁ l₂
#align list.drop_left List.drop_left

theorem drop_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : drop n (l₁ ++ l₂) = l₂ := by
  rw [← h]; apply drop_left
#align list.drop_left' List.drop_left'

theorem drop_eq_nth_le_cons : ∀ {n} {l : List α} (h), drop n l = nthLe l n h :: drop (n + 1) l
  | 0, _ :: _, _ => rfl
  | n + 1, _ :: _, _ => @drop_eq_nth_le_cons n _ _
#align list.drop_eq_nth_le_cons List.drop_eq_nth_le_cons

#align list.drop_length List.drop_length

theorem drop_length_cons {l : List α} (h : l ≠ []) (a : α) : (a :: l).drop l.length = [l.last h] :=
  by
  induction' l with y l ih generalizing a
  · cases h rfl
  · simp only [drop, length]
    by_cases h₁ : l = []
    · simp [h₁]
    rw [last_cons h₁]
    exact ih h₁ y
#align list.drop_length_cons List.drop_length_cons

/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
theorem drop_append_eq_append_drop {l₁ l₂ : List α} {n : ℕ} :
    drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ := by
  induction l₁ generalizing n; · simp
  cases n; · simp; simp [*]
#align list.drop_append_eq_append_drop List.drop_append_eq_append_drop

theorem drop_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, tsub_eq_zero_iff_le.mpr h]
#align list.drop_append_of_le_length List.drop_append_of_le_length

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
theorem drop_append {l₁ l₂ : List α} (i : ℕ) : drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ := by
  simp [drop_append_eq_append_drop, take_all_of_le le_self_add]
#align list.drop_append List.drop_append

theorem drop_sizeof_le [SizeOf α] (l : List α) : ∀ n : ℕ, (l.drop n).sizeof ≤ l.sizeof := by
  induction' l with _ _ lih <;> intro n
  · rw [drop_nil]
  · induction' n with n nih
    · rfl
    · exact trans (lih _) le_add_self
#align list.drop_sizeof_le List.drop_sizeof_le

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem nth_le_drop (L : List α) {i j : ℕ} (h : i + j < L.length) :
    nthLe L (i + j) h =
      nthLe (L.drop i) j
        (by
          have A : i < L.length := lt_of_le_of_lt (Nat.le.intro rfl) h
          rw [(take_append_drop i L).symm] at h
          simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take,
            length_append] using h) :=
  by
  have A : length (take i L) = i := by simp [le_of_lt (lt_of_le_of_lt (Nat.le.intro rfl) h)]
  rw [nth_le_of_eq (take_append_drop i L).symm h, nth_le_append_right] <;> simp [A]
#align list.nth_le_drop List.nth_le_drop

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
theorem nth_le_drop' (L : List α) {i j : ℕ} (h : j < (L.drop i).length) :
    nthLe (L.drop i) j h = nthLe L (i + j) (lt_tsub_iff_left.mp (length_drop i L ▸ h)) := by
  rw [nth_le_drop]
#align list.nth_le_drop' List.nth_le_drop'

theorem nth_drop (L : List α) (i j : ℕ) : nth (L.drop i) j = nth L (i + j) := by
  ext
  simp only [nth_eq_some, nth_le_drop', Option.mem_def]
  constructor <;> exact fun ⟨h, ha⟩ => ⟨by simpa [lt_tsub_iff_left] using h, ha⟩
#align list.nth_drop List.nth_drop

@[simp]
theorem drop_drop (n : ℕ) : ∀ (m) (l : List α), drop n (drop m l) = drop (n + m) l
  | m, [] => by simp
  | 0, l => by simp
  | m + 1, a :: l =>
    calc
      drop n (drop (m + 1) (a :: l)) = drop n (drop m l) := rfl
      _ = drop (n + m) l := drop_drop n m l
      _ = drop (n + (m + 1)) (a :: l) := rfl

#align list.drop_drop List.drop_drop

theorem drop_take : ∀ (m : ℕ) (n : ℕ) (l : List α), drop m (take (m + n) l) = take n (drop m l)
  | 0, n, _ => by simp
  | m + 1, n, nil => by simp
  | m + 1, n, _ :: l => by
    have h : m + 1 + n = m + n + 1 := by ac_rfl
    simpa [take_cons, h] using drop_take m n l
#align list.drop_take List.drop_take

theorem map_drop {α β : Type _} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.drop i).map f = (L.map f).drop i
  | [], i => by simp
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [map_drop]
#align list.map_drop List.map_drop

theorem modify_nth_tail_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ n l, modifyNthTail f n l = take n l ++ f (drop n l)
  | 0, l => rfl
  | n + 1, [] => H.symm
  | n + 1, b :: l => congr_arg (cons b) (modify_nth_tail_eq_take_drop n l)
#align list.modify_nth_tail_eq_take_drop List.modify_nth_tail_eq_take_drop

theorem modify_nth_eq_take_drop (f : α → α) :
    ∀ n l, modifyNth f n l = take n l ++ modifyHead f (drop n l) :=
  modify_nth_tail_eq_take_drop _ rfl
#align list.modify_nth_eq_take_drop List.modify_nth_eq_take_drop

theorem modify_nth_eq_take_cons_drop (f : α → α) {n l} (h) :
    modifyNth f n l = take n l ++ f (nthLe l n h) :: drop (n + 1) l := by
  rw [modify_nth_eq_take_drop, drop_eq_nth_le_cons h] <;> rfl
#align list.modify_nth_eq_take_cons_drop List.modify_nth_eq_take_cons_drop

theorem update_nth_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
    updateNth l n a = take n l ++ a :: drop (n + 1) l := by
  rw [update_nth_eq_modify_nth, modify_nth_eq_take_cons_drop _ h]
#align list.update_nth_eq_take_cons_drop List.update_nth_eq_take_cons_drop

theorem reverse_take {α} {xs : List α} (n : ℕ) (h : n ≤ xs.length) :
    xs.reverse.take n = (xs.drop (xs.length - n)).reverse := by
  induction xs generalizing n <;>
    simp only [reverse_cons, drop, reverse_nil, zero_tsub, length, take_nil]
  cases' h.lt_or_eq_dec with h' h'
  · replace h' := le_of_succ_le_succ h'
    rwa [take_append_of_le_length, xs_ih _ h']
    rw [show xs_tl.length + 1 - n = succ (xs_tl.length - n) from _, drop]
    · rwa [succ_eq_add_one, ← tsub_add_eq_add_tsub]
    · rwa [length_reverse]
  · subst h'
    rw [length, tsub_self, drop]
    suffices xs_tl.length + 1 = (xs_tl.reverse ++ [xs_hd]).length by
      rw [this, take_length, reverse_cons]
    rw [length_append, length_reverse]
    rfl
#align list.reverse_take List.reverse_take

@[simp]
theorem updateNth_eq_nil (l : List α) (n : ℕ) (a : α) : l.updateNth n a = [] ↔ l = [] := by
  cases l <;> cases n <;> simp only [updateNth]
#align list.update_nth_eq_nil List.updateNth_eq_nil

section Take'

variable [Inhabited α]

@[simp]
theorem take'_length : ∀ n l, length (@take' α _ n l) = n
  | 0, l => rfl
  | n + 1, l => congr_arg succ (take'_length _ _)
#align list.take'_length List.take'_length

@[simp]
theorem take'_nil : ∀ n, take' n (@nil α) = repeat default n
  | 0 => rfl
  | n + 1 => congr_arg (cons _) (take'_nil _)
#align list.take'_nil List.take'_nil

theorem take'_eq_take : ∀ {n} {l : List α}, n ≤ length l → take' n l = take n l
  | 0, l, h => rfl
  | n + 1, a :: l, h => congr_arg (cons _) <| take'_eq_take <| le_of_succ_le_succ h
#align list.take'_eq_take List.take'_eq_take

@[simp]
theorem take'_left (l₁ l₂ : List α) : take' (length l₁) (l₁ ++ l₂) = l₁ :=
  (take'_eq_take (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)
#align list.take'_left List.take'_left

theorem take'_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take' n (l₁ ++ l₂) = l₁ := by
  rw [← h] <;> apply take'_left
#align list.take'_left' List.take'_left'

end Take'

/-! ### foldl, foldr -/


theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
    foldl f a l = foldl g a l := by
  induction' l with hd tl ih generalizing a; · rfl
  unfold foldl
  rw [ih fun a b bin => H a b <| mem_cons_of_mem _ bin, H a hd (mem_cons_self _ _)]
#align list.foldl_ext List.foldl_ext

theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction' l with hd tl ih; · rfl
  simp only [mem_cons_iff, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]
#align list.foldr_ext List.foldr_ext

@[simp]
theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a :=
  rfl
#align list.foldl_nil List.foldl_nil

@[simp]
theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : List β) :
    foldl f a (b :: l) = foldl f (f a b) l :=
  rfl
#align list.foldl_cons List.foldl_cons

@[simp]
theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b :=
  rfl
#align list.foldr_nil List.foldr_nil

@[simp]
theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    foldr f b (a :: l) = f a (foldr f b l) :=
  rfl
#align list.foldr_cons List.foldr_cons

#align list.foldl_append List.foldl_append

#align list.foldr_append List.foldr_append

theorem foldl_fixed' {f : α → β → α} {a : α} (hf : ∀ b, f a b = a) : ∀ l : List β, foldl f a l = a
  | [] => rfl
  | b :: l => by rw [foldl_cons, hf b, foldl_fixed' hf l]
#align list.foldl_fixed' List.foldl_fixed'

theorem foldr_fixed' {f : α → β → β} {b : β} (hf : ∀ a, f a b = b) : ∀ l : List α, foldr f b l = b
  | [] => rfl
  | a :: l => by rw [foldr_cons, foldr_fixed' hf l, hf a]
#align list.foldr_fixed' List.foldr_fixed'

@[simp]
theorem foldl_fixed {a : α} : ∀ l : List β, foldl (fun a _ => a) a l = a :=
  foldl_fixed' fun _ => rfl
#align list.foldl_fixed List.foldl_fixed

@[simp]
theorem foldr_fixed {b : β} : ∀ l : List α, foldr (fun _ b => b) b l = b :=
  foldr_fixed' fun _ => rfl
#align list.foldr_fixed List.foldr_fixed

@[simp]
theorem foldl_join (f : α → β → α) :
    ∀ (a : α) (L : List (List β)), foldl f a (join L) = foldl (foldl f) a L
  | a, [] => rfl
  | a, l :: L => by simp only [join, foldl_append, foldl_cons, foldl_join (foldl f a l) L]
#align list.foldl_join List.foldl_join

@[simp]
theorem foldr_join (f : α → β → β) :
    ∀ (b : β) (L : List (List α)), foldr f b (join L) = foldr (fun l b => foldr f b l) b L
  | a, [] => rfl
  | a, l :: L => by simp only [join, foldr_append, foldr_join a L, foldr_cons]
#align list.foldr_join List.foldr_join

#align list.foldl_reverse List.foldl_reverse

#align list.foldr_reverse List.foldr_reverse

@[simp]
theorem foldr_eta : ∀ l : List α, foldr cons [] l = l
  | [] => rfl
  | x :: l => by simp only [foldr_cons, foldr_eta l]
#align list.foldr_eta List.foldr_eta

@[simp]
theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  rw [← foldr_reverse] <;> simp
#align list.reverse_foldl List.reverse_foldl

#align list.foldl_map List.foldl_map

#align list.foldr_map List.foldr_map

theorem foldl_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldl f' (g a) (l.map g) = g (List.foldl f a l) := by
  induction l generalizing a
  · simp; · simp [l_ih, h]
#align list.foldl_map' List.foldl_map'

theorem foldr_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldr f' (g a) (l.map g) = g (List.foldr f a l) := by
  induction l generalizing a
  · simp; · simp [l_ih, h]
#align list.foldr_map' List.foldr_map'

#align list.foldl_hom List.foldl_hom

#align list.foldr_hom List.foldr_hom

theorem foldl_hom₂ (l : List ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β)
    (op₃ : γ → ι → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
    foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
  Eq.symm <| by
    revert a b
    induction l <;> intros <;> [rfl, simp only [*, foldl]]
#align list.foldl_hom₂ List.foldl_hom₂

theorem foldr_hom₂ (l : List ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β)
    (op₃ : ι → γ → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
    foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) := by
  revert a
  induction l <;> intros <;> [rfl, simp only [*, foldr]]
#align list.foldr_hom₂ List.foldr_hom₂

theorem injective_foldl_comp {α : Type _} {l : List (α → α)} {f : α → α}
    (hl : ∀ f ∈ l, Function.Injective f) (hf : Function.Injective f) :
    Function.Injective (@List.foldl (α → α) (α → α) Function.comp f l) := by
  induction' l with lh lt l_ih generalizing f
  · exact hf
  · apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ (List.mem_cons_self _ _)
#align list.injective_foldl_comp List.injective_foldl_comp

/-- Induction principle for values produced by a `foldr`: if a property holds
for the seed element `b : β` and for all incremental `op : α → β → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldrRecOn {C : β → Sort _} (l : List α) (op : α → β → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op a b)) : C (foldr op b l) := by
  induction' l with hd tl IH
  · exact hb
  · refine' hl _ _ hd (mem_cons_self hd tl)
    refine' IH _
    intro y hy x hx
    exact hl y hy x (mem_cons_of_mem hd hx)
#align list.foldr_rec_on List.foldrRecOn

/-- Induction principle for values produced by a `foldl`: if a property holds
for the seed element `b : β` and for all incremental `op : β → α → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldlRecOn {C : β → Sort _} (l : List α) (op : β → α → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op b a)) : C (foldl op b l) := by
  induction' l with hd tl IH generalizing b
  · exact hb
  · refine' IH _ _ _
    · intro y hy x hx
      exact hl y hy x (mem_cons_of_mem hd hx)
    · exact hl b hb hd (mem_cons_self hd tl)
#align list.foldl_rec_on List.foldlRecOn

@[simp]
theorem foldr_rec_on_nil {C : β → Sort _} (op : α → β → β) (b) (hb : C b) (hl) :
    foldrRecOn [] op b hb hl = hb :=
  rfl
#align list.foldr_rec_on_nil List.foldr_rec_on_nil

@[simp]
theorem foldr_rec_on_cons {C : β → Sort _} (x : α) (l : List α) (op : α → β → β) (b) (hb : C b)
    (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ x :: l), C (op a b)) :
    foldrRecOn (x :: l) op b hb hl =
      hl _ (foldrRecOn l op b hb fun b hb a ha => hl b hb a (mem_cons_of_mem _ ha)) x
        (mem_cons_self _ _) :=
  rfl
#align list.foldr_rec_on_cons List.foldr_rec_on_cons

@[simp]
theorem foldl_rec_on_nil {C : β → Sort _} (op : β → α → β) (b) (hb : C b) (hl) :
    foldlRecOn [] op b hb hl = hb :=
  rfl
#align list.foldl_rec_on_nil List.foldl_rec_on_nil

-- scanl
section Scanl

variable {f : β → α → β} {b : β} {a : α} {l : List α}

theorem length_scanl : ∀ a l, length (scanl f a l) = l.length + 1
  | a, [] => rfl
  | a, x :: l => by erw [length_cons, length_cons, length_scanl]
#align list.length_scanl List.length_scanl

@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl
#align list.scanl_nil List.scanl_nil

@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := by
  simp only [scanl, eq_self_iff_true, singleton_append, and_self_iff]
#align list.scanl_cons List.scanl_cons

@[simp]
theorem nth_zero_scanl : (scanl f b l).nth 0 = some b := by
  cases l
  · simp only [nth, scanl_nil]
  · simp only [nth, scanl_cons, singleton_append]
#align list.nth_zero_scanl List.nth_zero_scanl

@[simp]
theorem nth_le_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).nthLe 0 h = b := by
  cases l
  · simp only [nth_le, scanl_nil]
  · simp only [nth_le, scanl_cons, singleton_append]
#align list.nth_le_zero_scanl List.nth_le_zero_scanl

theorem nth_succ_scanl {i : ℕ} :
    (scanl f b l).nth (i + 1) = ((scanl f b l).nth i).bind fun x => (l.nth i).map fun y => f x y :=
  by
  induction' l with hd tl hl generalizing b i
  · symm
    simp only [Option.bind_eq_none', nth, forall₂_true_iff, not_false_iff, Option.map_none',
      scanl_nil, Option.not_mem_none, forall_true_iff]
  · simp only [nth, scanl_cons, singleton_append]
    cases i
    · simp only [Option.map_some', nth_zero_scanl, nth, Option.some_bind']
    · simp only [hl, nth]
#align list.nth_succ_scanl List.nth_succ_scanl

theorem nth_le_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
    (scanl f b l).nthLe (i + 1) h =
      f ((scanl f b l).nthLe i (Nat.lt_of_succ_lt h))
        (l.nthLe i (Nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l))))) :=
  by
  induction' i with i hi generalizing b l
  · cases l
    · simp only [length, zero_add, scanl_nil] at h
      exact absurd h (lt_irrefl 1)
    · simp only [scanl_cons, singleton_append, nth_le_zero_scanl, nth_le]
  · cases l
    · simp only [length, add_lt_iff_neg_right, scanl_nil] at h
      exact absurd h (not_lt_of_lt Nat.succ_pos')
    · simp_rw [scanl_cons]
      rw [nth_le_append_right _]
      · simpa only [hi, length, succ_add_sub_one]
      · simp only [length, Nat.zero_le, le_add_iff_nonneg_left]
#align list.nth_le_succ_scanl List.nth_le_succ_scanl

end Scanl

-- scanr
@[simp]
theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl
#align list.scanr_nil List.scanr_nil

@[simp]
theorem scanr_aux_cons (f : α → β → β) (b : β) :
    ∀ (a : α) (l : List α), scanrAux f b (a :: l) = (foldr f b (a :: l), scanr f b l)
  | a, [] => rfl
  | a, x :: l => by
    let t := scanr_aux_cons x l
    simp only [scanr, scanr_aux, t, foldr_cons]
#align list.scanr_aux_cons List.scanr_aux_cons

@[simp]
theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, scanr_aux_cons, foldr_cons] <;> constructor <;> rfl
#align list.scanr_cons List.scanr_cons

section FoldlEqFoldr

-- foldl and foldr coincide when f is commutative and associative
variable {f : α → α → α} (hcomm : Commutative f) (hassoc : Associative f)

theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l ++ [b]) = foldr f b (a :: l)
  | a, b, nil => rfl
  | a, b, c :: l => by
    simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l]; rw [hassoc]
#align list.foldl1_eq_foldr1 List.foldl1_eq_foldr1

theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b :: l) = f b (foldl f a l)
  | a, b, nil => hcomm a b
  | a, b, c :: l => by
    simp only [foldl_cons] <;> rw [← foldl_eq_of_comm_of_assoc, right_comm _ hcomm hassoc] <;> rfl
#align list.foldl_eq_of_comm_of_assoc List.foldl_eq_of_comm_of_assoc

theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a, nil => rfl
  | a, b :: l => by
    simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc]; rw [foldl_eq_foldr a l]
#align list.foldl_eq_foldr List.foldl_eq_foldr

end FoldlEqFoldr

section FoldlEqFoldlr'

variable {f : α → β → α}

variable (hf : ∀ a b c, f (f a b) c = f (f a c) b)

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b :: l) = f (foldl f a l) b
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldl, foldl, foldl, ← foldl_eq_of_comm', foldl, hf]
#align list.foldl_eq_of_comm' List.foldl_eq_of_comm'

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
  | a, [] => rfl
  | a, b :: l => by rw [foldl_eq_of_comm' hf, foldr, foldl_eq_foldr'] <;> rfl
#align list.foldl_eq_foldr' List.foldl_eq_foldr'

end FoldlEqFoldlr'

section FoldlEqFoldlr'

variable {f : α → β → β}

variable (hf : ∀ a b c, f a (f b c) = f b (f a c))

theorem foldr_eq_of_comm' : ∀ a b l, foldr f a (b :: l) = foldr f (f b a) l
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldr, foldr, foldr, hf, ← foldr_eq_of_comm'] <;> rfl
#align list.foldr_eq_of_comm' List.foldr_eq_of_comm'

end FoldlEqFoldlr'

section

variable {op : α → α → α} [ha : IsAssociative α op] [hc : IsCommutative α op]

-- mathport name: op
local notation a " * " b => op a b

-- mathport name: foldl
local notation l " <*> " a => foldl op a l

include ha

theorem foldl_assoc : ∀ {l : List α} {a₁ a₂}, (l <*> a₁ * a₂) = a₁ * l <*> a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ =>
    calc
      ((a :: l) <*> a₁ * a₂) = l <*> a₁ * a₂ * a := by simp only [foldl_cons, ha.assoc]
      _ = a₁ * (a :: l) <*> a₂ := by rw [foldl_assoc, foldl_cons]

#align list.foldl_assoc List.foldl_assoc

theorem foldl_op_eq_op_foldr_assoc :
    ∀ {l : List α} {a₁ a₂}, ((l <*> a₁) * a₂) = a₁ * l.foldr (· * ·) a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ => by
    simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc] <;> rw [foldl_op_eq_op_foldr_assoc]
#align list.foldl_op_eq_op_foldr_assoc List.foldl_op_eq_op_foldr_assoc

include hc

theorem foldl_assoc_comm_cons {l : List α} {a₁ a₂} : ((a₁ :: l) <*> a₂) = a₁ * l <*> a₂ := by
  rw [foldl_cons, hc.comm, foldl_assoc]
#align list.foldl_assoc_comm_cons List.foldl_assoc_comm_cons

end

/-! ### mfoldl, mfoldr, mmap -/


section MfoldlMfoldr

variable {m : Type v → Type w} [Monad m]

@[simp]
theorem mfoldl_nil (f : β → α → m β) {b} : foldlM f b [] = pure b :=
  rfl
#align list.mfoldl_nil List.mfoldl_nil

@[simp]
theorem mfoldr_nil (f : α → β → m β) {b} : foldrM f b [] = pure b :=
  rfl
#align list.mfoldr_nil List.mfoldr_nil

@[simp]
theorem mfoldl_cons {f : β → α → m β} {b a l} :
    foldlM f b (a :: l) = f b a >>= fun b' => foldlM f b' l :=
  rfl
#align list.mfoldl_cons List.mfoldl_cons

@[simp]
theorem mfoldr_cons {f : α → β → m β} {b a l} : foldrM f b (a :: l) = foldrM f b l >>= f a :=
  rfl
#align list.mfoldr_cons List.mfoldr_cons

theorem mfoldr_eq_foldr (f : α → β → m β) (b l) :
    foldrM f b l = foldr (fun a mb => mb >>= f a) (pure b) l := by induction l <;> simp [*]
#align list.mfoldr_eq_foldr List.mfoldr_eq_foldr

attribute [simp] mmap mmap'

variable [LawfulMonad m]

theorem mfoldl_eq_foldl (f : β → α → m β) (b l) :
    foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l := by
  suffices h :
    ∀ mb : m β, (mb >>= fun b => mfoldl f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
  · simp [← h (pure b)]
  induction l <;> intro
  · simp
  · simp only [mfoldl, foldl, ← l_ih, functor_norm]
#align list.mfoldl_eq_foldl List.mfoldl_eq_foldl

@[simp]
theorem mfoldl_append {f : β → α → m β} :
    ∀ {b l₁ l₂}, foldlM f b (l₁ ++ l₂) = foldlM f b l₁ >>= fun x => foldlM f x l₂
  | _, [], _ => by simp only [nil_append, mfoldl_nil, pure_bind]
  | _, _ :: _, _ => by simp only [cons_append, mfoldl_cons, mfoldl_append, LawfulMonad.bind_assoc]
#align list.mfoldl_append List.mfoldl_append

@[simp]
theorem mfoldr_append {f : α → β → m β} :
    ∀ {b l₁ l₂}, foldrM f b (l₁ ++ l₂) = foldrM f b l₂ >>= fun x => foldrM f x l₁
  | _, [], _ => by simp only [nil_append, mfoldr_nil, bind_pure]
  | _, _ :: _, _ => by simp only [mfoldr_cons, cons_append, mfoldr_append, LawfulMonad.bind_assoc]
#align list.mfoldr_append List.mfoldr_append

end MfoldlMfoldr

/-! ### intersperse -/


@[simp]
theorem intersperse_nil {α : Type u} (a : α) : intersperse a [] = [] :=
  rfl
#align list.intersperse_nil List.intersperse_nil

@[simp]
theorem intersperse_singleton {α : Type u} (a b : α) : intersperse a [b] = [b] :=
  rfl
#align list.intersperse_singleton List.intersperse_singleton

@[simp]
theorem intersperse_cons_cons {α : Type u} (a b c : α) (tl : List α) :
    intersperse a (b :: c :: tl) = b :: a :: intersperse a (c :: tl) :=
  rfl
#align list.intersperse_cons_cons List.intersperse_cons_cons

/-! ### split_at and split_on -/


section SplitAtOn

variable (p : α → Prop) [DecidablePred p] (xs ys : List α) (ls : List (List α))
  (f : List α → List α)

@[simp]
theorem split_at_eq_take_drop : ∀ (n : ℕ) (l : List α), splitAt n l = (take n l, drop n l)
  | 0, a => rfl
  | succ n, [] => rfl
  | succ n, x :: xs => by simp only [split_at, split_at_eq_take_drop n xs, take, drop]
#align list.split_at_eq_take_drop List.split_at_eq_take_drop

@[simp]
theorem split_on_nil {α : Type u} [DecidableEq α] (a : α) : [].splitOn a = [[]] :=
  rfl
#align list.split_on_nil List.split_on_nil

@[simp]
theorem split_on_p_nil : [].splitOnP p = [[]] :=
  rfl
#align list.split_on_p_nil List.split_on_p_nil

/-- An auxiliary definition for proving a specification lemma for `split_on_p`.

`split_on_p_aux' P xs ys` splits the list `ys ++ xs` at every element satisfying `P`,
where `ys` is an accumulating parameter for the initial segment of elements not satisfying `P`.
-/
def splitOnPAux' {α : Type u} (P : α → Prop) [DecidablePred P] : List α → List α → List (List α)
  | [], xs => [xs]
  | h :: t, xs => if P h then xs :: split_on_p_aux' t [] else split_on_p_aux' t (xs ++ [h])
#align list.split_on_p_aux' List.splitOnPAux'

theorem split_on_p_aux_eq : splitOnPAux' p xs ys = splitOnPAux p xs ((· ++ ·) ys) := by
  induction' xs with a t ih generalizing ys <;>
    simp! only [append_nil, eq_self_iff_true, and_self_iff]
  split_ifs <;> rw [ih]
  · refine' ⟨rfl, rfl⟩
  · congr
    ext
    simp
#align list.split_on_p_aux_eq List.split_on_p_aux_eq

theorem split_on_p_aux_nil : splitOnPAux p xs id = splitOnPAux' p xs [] := by
  rw [split_on_p_aux_eq]
  rfl
#align list.split_on_p_aux_nil List.split_on_p_aux_nil

/-- The original list `L` can be recovered by joining the lists produced by `split_on_p p L`,
interspersed with the elements `L.filter p`. -/
theorem split_on_p_spec (as : List α) :
    join (zipWith (· ++ ·) (splitOnP p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as := by
  rw [split_on_p, split_on_p_aux_nil]
  suffices
    ∀ xs,
      join
          (zip_with (· ++ ·) (split_on_p_aux' p as xs) (((as.filter p).map fun x => [x]) ++ [[]])) =
        xs ++ as
    by
    rw [this]
    rfl
  induction as <;> intro <;> simp! only [split_on_p_aux', append_nil]
  split_ifs <;> simp [zip_with, join, *]
#align list.split_on_p_spec List.split_on_p_spec

theorem split_on_p_aux_ne_nil : splitOnPAux p xs f ≠ [] := by
  induction' xs with _ _ ih generalizing f; · trivial
  simp only [split_on_p_aux]; split_ifs; · trivial; exact ih _
#align list.split_on_p_aux_ne_nil List.split_on_p_aux_ne_nil

theorem split_on_p_aux_spec : splitOnPAux p xs f = (xs.splitOnP p).modifyHead f := by
  simp only [split_on_p]
  induction' xs with hd tl ih generalizing f; · simp [split_on_p_aux]
  simp only [split_on_p_aux]; split_ifs; · simp
  rw [ih fun l => f (hd :: l), ih fun l => id (hd :: l)]
  simp
#align list.split_on_p_aux_spec List.split_on_p_aux_spec

theorem split_on_p_ne_nil : xs.splitOnP p ≠ [] :=
  split_on_p_aux_ne_nil _ _ id
#align list.split_on_p_ne_nil List.split_on_p_ne_nil

@[simp]
theorem split_on_p_cons (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) :=
  by
  simp only [split_on_p, split_on_p_aux]
  split_ifs
  · simp
  rw [split_on_p_aux_spec]
  rfl
#align list.split_on_p_cons List.split_on_p_cons

/-- If no element satisfies `p` in the list `xs`, then `xs.split_on_p p = [xs]` -/
theorem split_on_p_eq_single (h : ∀ x ∈ xs, ¬p x) : xs.splitOnP p = [xs] := by
  induction' xs with hd tl ih
  · rfl
  simp [h hd _, ih fun t ht => h t (Or.inr ht)]
#align list.split_on_p_eq_single List.split_on_p_eq_single

/-- When a list of the form `[...xs, sep, ...as]` is split on `p`, the first element is `xs`,
  assuming no element in `xs` satisfies `p` but `sep` does satisfy `p` -/
theorem split_on_p_first (h : ∀ x ∈ xs, ¬p x) (sep : α) (hsep : p sep) (as : List α) :
    (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p := by
  induction' xs with hd tl ih
  · simp [hsep]
  simp [h hd _, ih fun t ht => h t (Or.inr ht)]
#align list.split_on_p_first List.split_on_p_first

/-- `intercalate [x]` is the left inverse of `split_on x`  -/
theorem intercalate_split_on (x : α) [DecidableEq α] : [x].intercalate (xs.splitOn x) = xs := by
  simp only [intercalate, split_on]
  induction' xs with hd tl ih; · simp [join]; simp only [split_on_p_cons]
  cases' h' : split_on_p (· = x) tl with hd' tl'; · exact (split_on_p_ne_nil _ tl h').elim
  rw [h'] at ih; split_ifs;
  · subst h
    simp [ih, join]
  cases tl' <;> simpa [join] using ih
#align list.intercalate_split_on List.intercalate_split_on

/-- `split_on x` is the left inverse of `intercalate [x]`, on the domain
  consisting of each nonempty list of lists `ls` whose elements do not contain `x`  -/
theorem split_on_intercalate [DecidableEq α] (x : α) (hx : ∀ l ∈ ls, x ∉ l) (hls : ls ≠ []) :
    ([x].intercalate ls).splitOn x = ls := by
  simp only [intercalate]
  induction' ls with hd tl ih; · contradiction
  cases tl
  · suffices hd.split_on x = [hd] by simpa [join]
    refine' split_on_p_eq_single _ _ _
    intro y hy H
    rw [H] at hy
    refine' hx hd _ hy
    simp
  · simp only [intersperse_cons_cons, singleton_append, join]
    specialize ih _ _
    · intro l hl
      apply hx l
      simp at hl⊢
      tauto
    · trivial
    have := split_on_p_first (· = x) hd _ x rfl _
    · simp only [split_on] at ih⊢
      rw [this]
      rw [ih]
    intro y hy H
    rw [H] at hy
    exact hx hd (Or.inl rfl) hy
#align list.split_on_intercalate List.split_on_intercalate

end SplitAtOn

/-! ### map for partial functions -/


#print List.pmap /-
/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
  | [], H => []
  | a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap l (forall_mem_cons.1 H).2
#align list.pmap List.pmap
-/

#print List.attach /-
/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach (l : List α) : List { x // x ∈ l } :=
  pmap Subtype.mk l fun a => id
#align list.attach List.attach
-/

theorem sizeof_lt_sizeof_of_mem [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) :
    SizeOf.sizeOf x < SizeOf.sizeOf l := by
  induction' l with h t ih <;> cases hx
  · rw [hx]
    exact lt_add_of_lt_of_nonneg (lt_one_add _) (Nat.zero_le _)
  · exact lt_add_of_pos_of_le (zero_lt_one_add _) (le_of_lt (ih hx))
#align list.sizeof_lt_sizeof_of_mem List.sizeof_lt_sizeof_of_mem

/- warning: list.pmap_eq_map -> List.pmap_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (p : α -> Prop) (f : α -> β) (l : List.{u} α) (H : forall (a : α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (p a)), Eq.{succ v} (List.{v} β) (List.pmap.{u, v} α β p (fun (a : α) (_x : p a) => f a) l H) (List.map.{u, v} α β f l)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (p : α -> Prop) (f : α -> β) (l : List.{u_1} α) (H : forall (a : α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (p a)), Eq.{succ u_2} (List.{u_2} β) (List.pmap.{u_1, u_2} α β p (fun (a : α) (x._@.Mathlib.Data.List.Basic._hyg.1879 : p a) => f a) l H) (List.map.{u_1, u_2} α β f l)
Case conversion may be inaccurate. Consider using '#align list.pmap_eq_map List.pmap_eq_mapₓ'. -/
@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l <;> [rfl, simp only [*, pmap, map]] <;> constructor <;> rfl
#align list.pmap_eq_map List.pmap_eq_map

/- warning: list.pmap_congr -> List.pmap_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {p : α -> Prop} {q : α -> Prop} {f : forall (a : α), (p a) -> β} {g : forall (a : α), (q a) -> β} (l : List.{u} α) {H₁ : forall (a : α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (p a)} {H₂ : forall (a : α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (q a)}, (forall (a : α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (forall (h₁ : p a) (h₂ : q a), Eq.{succ v} β (f a h₁) (g a h₂))) -> (Eq.{succ v} (List.{v} β) (List.pmap.{u, v} α β (fun (a : α) => p a) f l H₁) (List.pmap.{u, v} α β (fun (a : α) => q a) g l H₂))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : α -> Prop} {q : α -> Prop} {f : forall (a : α), (p a) -> β} {g : forall (a : α), (q a) -> β} (l : List.{u_1} α) {H₁ : forall (a : α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (p a)} {H₂ : forall (a : α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (q a)}, (forall (a : α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (forall (h₁ : p a) (h₂ : q a), Eq.{succ u_2} β (f a h₁) (g a h₂))) -> (Eq.{succ u_2} (List.{u_2} β) (List.pmap.{u_1, u_2} α β (fun (a : α) => p a) f l H₁) (List.pmap.{u_1, u_2} α β (fun (a : α) => q a) g l H₂))
Case conversion may be inaccurate. Consider using '#align list.pmap_congr List.pmap_congrₓ'. -/
theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  induction' l with _ _ ih
  · rfl
  · rw [pmap, pmap, h _ (mem_cons_self _ _), ih fun a ha => h a (mem_cons_of_mem _ ha)]
#align list.pmap_congr List.pmap_congr

/- warning: list.map_pmap -> List.map_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} {p : α -> Prop} (g : β -> γ) (f : forall (a : α), (p a) -> β) (l : List.{u} α) (H : forall (a : α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (p a)), Eq.{succ w} (List.{w} γ) (List.map.{v, w} β γ g (List.pmap.{u, v} α β (fun (a : α) => p a) f l H)) (List.pmap.{u, w} α γ (fun (a : α) => p a) (fun (a : α) (h : p a) => g (f a h)) l H)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {p : α -> Prop} (g : β -> γ) (f : forall (a : α), (p a) -> β) (l : List.{u_1} α) (H : forall (a : α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (p a)), Eq.{succ u_3} (List.{u_3} γ) (List.map.{u_2, u_3} β γ g (List.pmap.{u_1, u_2} α β (fun (a : α) => p a) f l H)) (List.pmap.{u_1, u_3} α γ (fun (a : α) => p a) (fun (a : α) (h : p a) => g (f a h)) l H)
Case conversion may be inaccurate. Consider using '#align list.map_pmap List.map_pmapₓ'. -/
theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l <;> [rfl, simp only [*, pmap, map]] <;> constructor <;> rfl
#align list.map_pmap List.map_pmap

/- warning: list.pmap_map -> List.pmap_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} {p : β -> Prop} (g : forall (b : β), (p b) -> γ) (f : α -> β) (l : List.{u} α) (H : forall (a : β), (Membership.Mem.{v, v} β (List.{v} β) (List.hasMem.{v} β) a (List.map.{u, v} α β f l)) -> (p a)), Eq.{succ w} (List.{w} γ) (List.pmap.{v, w} β γ (fun (b : β) => p b) g (List.map.{u, v} α β f l) H) (List.pmap.{u, w} α γ (fun (a : α) => p (f a)) (fun (a : α) (h : p (f a)) => g (f a) h) l (fun (a : α) (h : Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) => H (f a) (List.mem_map_of_mem.{u, v} α β f a l h)))
but is expected to have type
  forall {β : Type.{u_1}} {γ : Type.{u_2}} {α : Type.{u_3}} {p : β -> Prop} (g : forall (b : β), (p b) -> γ) (f : α -> β) (l : List.{u_3} α) (H : forall (a : β), (Membership.mem.{u_1, u_1} β (List.{u_1} β) (List.instMembershipList.{u_1} β) a (List.map.{u_3, u_1} α β f l)) -> (p a)), Eq.{succ u_2} (List.{u_2} γ) (List.pmap.{u_1, u_2} β γ (fun (a : β) => p a) g (List.map.{u_3, u_1} α β f l) H) (List.pmap.{u_3, u_2} α γ (fun (a : α) => p (f a)) (fun (a : α) (h : p (f a)) => g (f a) h) l (fun (a : α) (h : Membership.mem.{u_3, u_3} α (List.{u_3} α) (List.instMembershipList.{u_3} α) a l) => H (f a) (List.mem_map_of_mem.{u_1, u_3} α β a l f h)))
Case conversion may be inaccurate. Consider using '#align list.pmap_map List.pmap_mapₓ'. -/
theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun a h => H _ (mem_map_of_mem _ h) := by
  induction l <;> [rfl, simp only [*, pmap, map]] <;> constructor <;> rfl
#align list.pmap_map List.pmap_map

/- warning: list.pmap_eq_map_attach -> List.pmap_eq_map_attach is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (l : List.{u} α) (H : forall (a : α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (p a)), Eq.{succ v} (List.{v} β) (List.pmap.{u, v} α β (fun (a : α) => p a) f l H) (List.map.{u, v} (Subtype.{succ u} α (fun (x : α) => Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) x l)) β (fun (x : Subtype.{succ u} α (fun (x : α) => Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) x l)) => f (Subtype.val.{succ u} α (fun (x : α) => Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) x l) x) (H (Subtype.val.{succ u} α (fun (x : α) => Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) x l) x) (Subtype.property.{succ u} α (fun (x : α) => Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) x l) x))) (List.attach.{u} α l))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (l : List.{u_1} α) (H : forall (a : α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (p a)), Eq.{succ u_2} (List.{u_2} β) (List.pmap.{u_1, u_2} α β (fun (a : α) => p a) f l H) (List.map.{u_1, u_2} (Subtype.{succ u_1} α (fun (x : α) => Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) x l)) β (fun (x : Subtype.{succ u_1} α (fun (x : α) => Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) x l)) => f (Subtype.val.{succ u_1} α (fun (x : α) => Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) x l) x) (H (Subtype.val.{succ u_1} α (fun (x : α) => Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) x l) x) (Subtype.property.{succ u_1} α (fun (x : α) => Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) x l) x))) (List.attach.{u_1} α l))
Case conversion may be inaccurate. Consider using '#align list.pmap_eq_map_attach List.pmap_eq_map_attachₓ'. -/
theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, map_pmap] <;> exact pmap_congr l fun _ _ _ _ => rfl
#align list.pmap_eq_map_attach List.pmap_eq_map_attach

@[simp]
theorem attach_map_coe' (l : List α) (f : α → β) : (l.attach.map fun i => f i) = l.map f := by
  rw [attach, map_pmap] <;> exact pmap_eq_map _ _ _ _
#align list.attach_map_coe' List.attach_map_coe'

theorem attach_map_val' (l : List α) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe' _ _
#align list.attach_map_val' List.attach_map_val'

@[simp]
theorem attach_map_coe (l : List α) : l.attach.map (coe : _ → α) = l :=
  (attach_map_coe' _ _).trans l.map_id
#align list.attach_map_coe List.attach_map_coe

#print List.attach_map_val /-
theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l :=
  attach_map_coe _
#align list.attach_map_val List.attach_map_val
-/

#print List.mem_attach /-
@[simp]
theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_val] <;> exact h) <;>
      · rcases this with ⟨⟨_, _⟩, m, rfl⟩
        exact m
#align list.mem_attach List.mem_attach
-/

/- warning: list.mem_pmap -> List.mem_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {l : List.{u} α} {H : forall (a : α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (p a)} {b : β}, Iff (Membership.Mem.{v, v} β (List.{v} β) (List.hasMem.{v} β) b (List.pmap.{u, v} α β (fun (a : α) => p a) f l H)) (Exists.{succ u} α (fun (a : α) => Exists.{0} (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) (fun (h : Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) => Eq.{succ v} β (f a (H a h)) b)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : α -> Prop} {f : forall (a : α), (p a) -> β} {l : List.{u_1} α} {H : forall (a : α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (p a)} {b : β}, Iff (Membership.mem.{u_2, u_2} β (List.{u_2} β) (List.instMembershipList.{u_2} β) b (List.pmap.{u_1, u_2} α β (fun (a : α) => p a) f l H)) (Exists.{succ u_1} α (fun (a : α) => Exists.{0} (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) (fun (h : Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) => Eq.{succ u_2} β (f a (H a h)) b)))
Case conversion may be inaccurate. Consider using '#align list.mem_pmap List.mem_pmapₓ'. -/
@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _)(h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and_iff, Subtype.exists]
#align list.mem_pmap List.mem_pmap

@[simp]
theorem length_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l <;> [rfl, simp only [*, pmap, length]]
#align list.length_pmap List.length_pmap

@[simp]
theorem length_attach (L : List α) : L.attach.length = L.length :=
  length_pmap
#align list.length_attach List.length_attach

@[simp]
theorem pmap_eq_nil {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] := by
  rw [← length_eq_zero, length_pmap, length_eq_zero]
#align list.pmap_eq_nil List.pmap_eq_nil

@[simp]
theorem attach_eq_nil (l : List α) : l.attach = [] ↔ l = [] :=
  pmap_eq_nil
#align list.attach_eq_nil List.attach_eq_nil

theorem last_pmap {α β : Type _} (p : α → Prop) (f : ∀ a, p a → β) (l : List α) (hl₁ : ∀ a ∈ l, p a)
    (hl₂ : l ≠ []) :
    (l.pmap f hl₁).last (mt List.pmap_eq_nil.1 hl₂) = f (l.last hl₂) (hl₁ _ (List.last_mem hl₂)) :=
  by
  induction' l with l_hd l_tl l_ih
  · apply (hl₂ rfl).elim
  · cases l_tl
    · simp
    · apply l_ih
#align list.last_pmap List.last_pmap

theorem nth_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) (n : ℕ) :
    nth (pmap f l h) n = Option.pmap f (nth l n) fun x H => h x (nth_mem H) := by
  induction' l with hd tl hl generalizing n
  · simp
  · cases n <;> simp [hl]
#align list.nth_pmap List.nth_pmap

theorem nth_le_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : ℕ}
    (hn : n < (pmap f l h).length) :
    nthLe (pmap f l h) n hn =
      f (nthLe l n (@length_pmap _ _ p f l h ▸ hn))
        (h _ (nth_le_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
  by
  induction' l with hd tl hl generalizing n
  · simp only [length, pmap] at hn
    exact absurd hn (not_lt_of_le n.zero_le)
  · cases n
    · simp
    · simpa [hl]
#align list.nth_le_pmap List.nth_le_pmap

theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ l₂ : List ι)
    (h : ∀ a ∈ l₁ ++ l₂, p a) :
    (l₁ ++ l₂).pmap f h =
      (l₁.pmap f fun a ha => h a (mem_append_left l₂ ha)) ++
        l₂.pmap f fun a ha => h a (mem_append_right l₁ ha) :=
  by
  induction' l₁ with _ _ ih
  · rfl
  · dsimp only [pmap, cons_append]
    rw [ih]
#align list.pmap_append List.pmap_append

theorem pmap_append' {α β : Type _} {p : α → Prop} (f : ∀ a : α, p a → β) (l₁ l₂ : List α)
    (h₁ : ∀ a ∈ l₁, p a) (h₂ : ∀ a ∈ l₂, p a) :
    ((l₁ ++ l₂).pmap f fun a ha => (List.mem_append.1 ha).elim (h₁ a) (h₂ a)) =
      l₁.pmap f h₁ ++ l₂.pmap f h₂ :=
  pmap_append f l₁ l₂ _
#align list.pmap_append' List.pmap_append'

/-! ### find -/


section Find

variable {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

@[simp]
theorem find_nil (p : α → Prop) [DecidablePred p] : find p [] = none :=
  rfl
#align list.find_nil List.find_nil

@[simp]
theorem find_cons_of_pos (l) (h : p a) : find p (a :: l) = some a :=
  if_pos h
#align list.find_cons_of_pos List.find_cons_of_pos

@[simp]
theorem find_cons_of_neg (l) (h : ¬p a) : find p (a :: l) = find p l :=
  if_neg h
#align list.find_cons_of_neg List.find_cons_of_neg

@[simp]
theorem find_eq_none : find p l = none ↔ ∀ x ∈ l, ¬p x := by
  induction' l with a l IH
  · exact iff_of_true rfl (forall_mem_nil _)
  rw [forall_mem_cons]; by_cases h : p a
  · simp only [find_cons_of_pos _ h, h, not_true, false_and_iff]
  · rwa [find_cons_of_neg _ h, iff_true_intro h, true_and_iff]
#align list.find_eq_none List.find_eq_none

theorem find_some (H : find p l = some a) : p a := by
  induction' l with b l IH; · contradiction
  by_cases h : p b
  · rw [find_cons_of_pos _ h] at H
    cases H
    exact h
  · rw [find_cons_of_neg _ h] at H
    exact IH H
#align list.find_some List.find_some

@[simp]
theorem find_mem (H : find p l = some a) : a ∈ l := by
  induction' l with b l IH; · contradiction
  by_cases h : p b
  · rw [find_cons_of_pos _ h] at H
    cases H
    apply mem_cons_self
  · rw [find_cons_of_neg _ h] at H
    exact mem_cons_of_mem _ (IH H)
#align list.find_mem List.find_mem

end Find

/-! ### lookmap -/


section Lookmap

variable (f : α → Option α)

@[simp]
theorem lookmap_nil : [].lookmap f = [] :=
  rfl
#align list.lookmap_nil List.lookmap_nil

@[simp]
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) :
    (a :: l).lookmap f = a :: l.lookmap f := by simp [lookmap, h]
#align list.lookmap_cons_none List.lookmap_cons_none

@[simp]
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) : (a :: l).lookmap f = b :: l :=
  by simp [lookmap, h]
#align list.lookmap_cons_some List.lookmap_cons_some

theorem lookmap_some : ∀ l : List α, l.lookmap some = l
  | [] => rfl
  | a :: l => rfl
#align list.lookmap_some List.lookmap_some

theorem lookmap_none : ∀ l : List α, (l.lookmap fun _ => none) = l
  | [] => rfl
  | a :: l => congr_arg (cons a) (lookmap_none l)
#align list.lookmap_none List.lookmap_none

theorem lookmap_congr {f g : α → Option α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
  | [], H => rfl
  | a :: l, H => by
    cases' forall_mem_cons.1 H with H₁ H₂
    cases' h : g a with b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]
#align list.lookmap_congr List.lookmap_congr

theorem lookmap_of_forall_not {l : List α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)
#align list.lookmap_of_forall_not List.lookmap_of_forall_not

theorem lookmap_map_eq (g : α → β) (h : ∀ (a), ∀ b ∈ f a, g a = g b) :
    ∀ l : List α, map g (l.lookmap f) = map g l
  | [] => rfl
  | a :: l => by
    cases' h' : f a with b
    · simp [h', lookmap_map_eq]
    · simp [lookmap_cons_some _ _ h', h _ _ h']
#align list.lookmap_map_eq List.lookmap_map_eq

theorem lookmap_id' (h : ∀ (a), ∀ b ∈ f a, a = b) (l : List α) : l.lookmap f = l := by
  rw [← map_id (l.lookmap f), lookmap_map_eq, map_id] <;> exact h
#align list.lookmap_id' List.lookmap_id'

theorem length_lookmap (l : List α) : length (l.lookmap f) = length l := by
  rw [← length_map, lookmap_map_eq _ fun _ => (), length_map] <;> simp
#align list.length_lookmap List.length_lookmap

end Lookmap

/-! ### filter_map -/


@[simp]
theorem filter_map_nil (f : α → Option β) : filterMap f [] = [] :=
  rfl
#align list.filter_map_nil List.filter_map_nil

@[simp]
theorem filter_map_cons_none {f : α → Option β} (a : α) (l : List α) (h : f a = none) :
    filterMap f (a :: l) = filterMap f l := by simp only [filter_map, h]
#align list.filter_map_cons_none List.filter_map_cons_none

@[simp]
theorem filter_map_cons_some (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) :
    filterMap f (a :: l) = b :: filterMap f l := by
  simp only [filter_map, h] <;> constructor <;> rfl
#align list.filter_map_cons_some List.filter_map_cons_some

theorem filter_map_cons (f : α → Option β) (a : α) (l : List α) :
    filterMap f (a :: l) = Option.casesOn (f a) (filterMap f l) fun b => b :: filterMap f l := by
  generalize eq : f a = b
  cases b
  · rw [filter_map_cons_none _ _ Eq]
  · rw [filter_map_cons_some _ _ _ Eq]
#align list.filter_map_cons List.filter_map_cons

theorem filter_map_append {α β : Type _} (l l' : List α) (f : α → Option β) :
    filterMap f (l ++ l') = filterMap f l ++ filterMap f l' := by
  induction' l with hd tl hl generalizing l'
  · simp
  · rw [cons_append, filter_map, filter_map]
    cases f hd <;> simp only [filter_map, hl, cons_append, eq_self_iff_true, and_self_iff]
#align list.filter_map_append List.filter_map_append

theorem filter_map_eq_map (f : α → β) : filterMap (some ∘ f) = map f := by
  funext l
  induction' l with a l IH; · rfl
  simp only [filter_map_cons_some (some ∘ f) _ _ rfl, IH, map_cons]; constructor <;> rfl
#align list.filter_map_eq_map List.filter_map_eq_map

theorem filter_map_eq_filter (p : α → Prop) [DecidablePred p] :
    filterMap (Option.guard p) = filter p := by
  funext l
  induction' l with a l IH; · rfl
  by_cases pa : p a
  · simp only [filter_map, Option.guard, IH, if_pos pa, filter_cons_of_pos _ pa]
    constructor <;> rfl
  · simp only [filter_map, Option.guard, IH, if_neg pa, filter_cons_of_neg _ pa]
#align list.filter_map_eq_filter List.filter_map_eq_filter

theorem filter_map_filter_map (f : α → Option β) (g : β → Option γ) (l : List α) :
    filterMap g (filterMap f l) = filterMap (fun x => (f x).bind g) l := by
  induction' l with a l IH; · rfl
  cases' h : f a with b
  · rw [filter_map_cons_none _ _ h, filter_map_cons_none, IH]
    simp only [h, Option.none_bind']
  rw [filter_map_cons_some _ _ _ h]
  cases' h' : g b with c <;> [rw [filter_map_cons_none _ _ h', filter_map_cons_none, IH],
      rw [filter_map_cons_some _ _ _ h', filter_map_cons_some, IH]] <;>
    simp only [h, h', Option.some_bind']
#align list.filter_map_filter_map List.filter_map_filter_map

theorem map_filter_map (f : α → Option β) (g : β → γ) (l : List α) :
    map g (filterMap f l) = filterMap (fun x => (f x).map g) l := by
  rw [← filter_map_eq_map, filter_map_filter_map] <;> rfl
#align list.map_filter_map List.map_filter_map

theorem filter_map_map (f : α → β) (g : β → Option γ) (l : List α) :
    filterMap g (map f l) = filterMap (g ∘ f) l := by
  rw [← filter_map_eq_map, filter_map_filter_map] <;> rfl
#align list.filter_map_map List.filter_map_map

theorem filter_filter_map (f : α → Option β) (p : β → Prop) [DecidablePred p] (l : List α) :
    filter p (filterMap f l) = filterMap (fun x => (f x).filter p) l := by
  rw [← filter_map_eq_filter, filter_map_filter_map] <;> rfl
#align list.filter_filter_map List.filter_filter_map

theorem filter_map_filter (p : α → Prop) [DecidablePred p] (f : α → Option β) (l : List α) :
    filterMap f (filter p l) = filterMap (fun x => if p x then f x else none) l := by
  rw [← filter_map_eq_filter, filter_map_filter_map]; congr
  funext x
  show (Option.guard p x).bind f = ite (p x) (f x) none
  by_cases h : p x
  · simp only [Option.guard, if_pos h, Option.some_bind']
  · simp only [Option.guard, if_neg h, Option.none_bind']
#align list.filter_map_filter List.filter_map_filter

@[simp]
theorem filter_map_some (l : List α) : filterMap some l = l := by
  rw [filter_map_eq_map] <;> apply map_id
#align list.filter_map_some List.filter_map_some

theorem map_filter_map_some_eq_filter_map_is_some (f : α → Option β) (l : List α) :
    (l.filterMap f).map some = (l.map f).filter fun b => b.isSome := by
  induction' l with x xs ih
  · simp
  · cases h : f x <;> rw [List.filter_map_cons, h] <;> simp [h, ih]
#align list.map_filter_map_some_eq_filter_map_is_some List.map_filter_map_some_eq_filter_map_is_some

@[simp]
theorem mem_filter_map (f : α → Option β) (l : List α) {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  induction' l with a l IH
  · constructor
    · intro H
      cases H
    · rintro ⟨_, H, _⟩
      cases H
  cases' h : f a with b'
  · have : f a ≠ some b := by
      rw [h]
      intro
      contradiction
    simp only [filter_map_cons_none _ _ h, IH, mem_cons_iff, or_and_right, exists_or,
      exists_eq_left, this, false_or_iff]
  · have : f a = some b ↔ b = b' := by
      constructor <;> intro t
      · rw [t] at h <;> injection h
      · exact t.symm ▸ h
    simp only [filter_map_cons_some _ _ _ h, IH, mem_cons_iff, or_and_right, exists_or, this,
      exists_eq_left]
#align list.mem_filter_map List.mem_filter_map

@[simp]
theorem filter_map_join (f : α → Option β) (L : List (List α)) :
    filterMap f (join L) = join (map (filterMap f) L) := by
  induction' L with hd tl ih
  · rfl
  · rw [map, join, join, filter_map_append, ih]
#align list.filter_map_join List.filter_map_join

theorem map_filter_map_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (l : List α) : map g (filterMap f l) = l := by simp only [map_filter_map, H, filter_map_some]
#align list.map_filter_map_of_inv List.map_filter_map_of_inv

theorem length_filter_le (p : α → Prop) [DecidablePred p] (l : List α) :
    (l.filter p).length ≤ l.length :=
  (List.filter_sublist _).length_le
#align list.length_filter_le List.length_filter_le

theorem length_filter_map_le (f : α → Option β) (l : List α) :
    (List.filterMap f l).length ≤ l.length := by
  rw [← List.length_map some, List.map_filter_map_some_eq_filter_map_is_some, ← List.length_map f]
  apply List.length_filter_le
#align list.length_filter_map_le List.length_filter_map_le

theorem Sublist.filter_map (f : α → Option β) {l₁ l₂ : List α} (s : l₁ <+ l₂) :
    filterMap f l₁ <+ filterMap f l₂ := by
  induction' s with l₁ l₂ a s IH l₁ l₂ a s IH <;> simp only [filter_map] <;> cases' f a with b <;>
    simp only [filter_map, IH, sublist.cons, sublist.cons2]
#align list.sublist.filter_map List.Sublist.filter_map

theorem Sublist.map (f : α → β) {l₁ l₂ : List α} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
  filter_map_eq_map f ▸ s.filterMap _
#align list.sublist.map List.Sublist.map

/-! ### reduce_option -/


@[simp]
theorem reduce_option_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduce_option, filter_map, id.def, eq_self_iff_true, and_self_iff]
#align list.reduce_option_cons_of_some List.reduce_option_cons_of_some

@[simp]
theorem reduce_option_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduce_option, filter_map, id.def]
#align list.reduce_option_cons_of_none List.reduce_option_cons_of_none

@[simp]
theorem reduce_option_nil : @reduceOption α [] = [] :=
  rfl
#align list.reduce_option_nil List.reduce_option_nil

@[simp]
theorem reduce_option_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction' l with hd tl hl
  · simp only [reduce_option_nil, map_nil]
  ·
    cases hd <;>
      simpa only [true_and_iff, Option.map_some', map, eq_self_iff_true,
        reduce_option_cons_of_some] using hl
#align list.reduce_option_map List.reduce_option_map

theorem reduce_option_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filter_map_append l l' id
#align list.reduce_option_append List.reduce_option_append

theorem reduce_option_length_le (l : List (Option α)) : l.reduceOption.length ≤ l.length := by
  induction' l with hd tl hl
  · simp only [reduce_option_nil, length]
  · cases hd
    · exact Nat.le_succ_of_le hl
    · simpa only [length, add_le_add_iff_right, reduce_option_cons_of_some] using hl
#align list.reduce_option_length_le List.reduce_option_length_le

theorem reduce_option_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x := by
  induction' l with hd tl hl
  ·
    simp only [forall_const, reduce_option_nil, not_mem_nil, forall_prop_of_false, eq_self_iff_true,
      length, not_false_iff]
  · cases hd
    · simp only [mem_cons_iff, forall_eq_or_imp, Bool.coe_sort_ff, false_and_iff,
        reduce_option_cons_of_none, length, Option.isSome_none, iff_false_iff]
      intro H
      have := reduce_option_length_le tl
      rw [H] at this
      exact absurd (Nat.lt_succ_self _) (not_lt_of_le this)
    ·
      simp only [hl, true_and_iff, mem_cons_iff, forall_eq_or_imp, add_left_inj, Bool.coe_sort_tt,
        length, Option.isSome_some, reduce_option_cons_of_some]
#align list.reduce_option_length_eq_iff List.reduce_option_length_eq_iff

theorem reduce_option_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none ∈ l := by
  rw [(reduce_option_length_le l).lt_iff_ne, Ne, reduce_option_length_eq_iff]
  induction l <;> simp [*]
  rw [eq_comm, ← Option.not_isSome_iff_eq_none, Decidable.imp_iff_not_or]
#align list.reduce_option_length_lt_iff List.reduce_option_length_lt_iff

theorem reduce_option_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl
#align list.reduce_option_singleton List.reduce_option_singleton

theorem reduce_option_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList := by
  induction' l with hd tl hl generalizing x
  · cases x <;> simp [Option.toList]
  · simp only [concat_eq_append, reduce_option_append] at hl
    cases hd <;> simp [hl, reduce_option_append]
#align list.reduce_option_concat List.reduce_option_concat

theorem reduce_option_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduce_option_nil, concat_eq_append, reduce_option_append, reduce_option_cons_of_some]
#align list.reduce_option_concat_of_some List.reduce_option_concat_of_some

theorem reduce_option_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduceOption ↔ some x ∈ l := by
  simp only [reduce_option, id.def, mem_filter_map, exists_eq_right]
#align list.reduce_option_mem_iff List.reduce_option_mem_iff

theorem reduce_option_nth_iff {l : List (Option α)} {x : α} :
    (∃ i, l.nth i = some (some x)) ↔ ∃ i, l.reduceOption.nth i = some x := by
  rw [← mem_iff_nth, ← mem_iff_nth, reduce_option_mem_iff]
#align list.reduce_option_nth_iff List.reduce_option_nth_iff

/-! ### filter -/


section Filter

variable {p : α → Prop} [DecidablePred p]

theorem filter_singleton {a : α} : [a].filter p = if p a then [a] else [] :=
  rfl
#align list.filter_singleton List.filter_singleton

theorem filter_eq_foldr (p : α → Prop) [DecidablePred p] (l : List α) :
    filter p l = foldr (fun a out => if p a then a :: out else out) [] l := by
  induction l <;> simp [*, filter]
#align list.filter_eq_foldr List.filter_eq_foldr

theorem filter_congr' {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    ∀ {l : List α}, (∀ x ∈ l, p x ↔ q x) → filter p l = filter q l
  | [], _ => rfl
  | a :: l, h => by
    rw [forall_mem_cons] at h <;> by_cases pa : p a <;>
          [simp only [filter_cons_of_pos _ pa, filter_cons_of_pos _ (h.1.1 pa), filter_congr' h.2],
          simp only [filter_cons_of_neg _ pa, filter_cons_of_neg _ (mt h.1.2 pa),
            filter_congr' h.2]] <;>
        constructor <;>
      rfl
#align list.filter_congr' List.filter_congr'

@[simp]
theorem filter_subset (l : List α) : filter p l ⊆ l :=
  (filter_sublist l).Subset
#align list.filter_subset List.filter_subset

theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
  | b :: l, ain =>
    if pb : p b then
      have : a ∈ b :: filter p l := by simpa only [filter_cons_of_pos _ pb] using ain
      Or.elim (eq_or_mem_of_mem_cons this) (fun this : a = b => by rw [← this] at pb; exact pb)
        fun this : a ∈ filter p l => of_mem_filter this
    else by simp only [filter_cons_of_neg _ pb] at ain; exact of_mem_filter ain
#align list.of_mem_filter List.of_mem_filter

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset l h
#align list.mem_of_mem_filter List.mem_of_mem_filter

theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
  | _ :: l, Or.inl rfl, pa => by rw [filter_cons_of_pos _ pa] <;> apply mem_cons_self
  | b :: l, Or.inr ain, pa =>
    if pb : p b then by
      rw [filter_cons_of_pos _ pb] <;> apply mem_cons_of_mem <;> apply mem_filter_of_mem ain pa
    else by rw [filter_cons_of_neg _ pb] <;> apply mem_filter_of_mem ain pa
#align list.mem_filter_of_mem List.mem_filter_of_mem

/- warning: list.mem_filter -> List.mem_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u} α p] {a : α} {l : List.{u} α}, Iff (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a (List.filterₓ.{u} α p (fun (a : α) => _inst_1 a) l)) (And (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) (p a))
but is expected to have type
  forall {α._@.Std.Data.List.Lemmas._hyg.21892 : Type.{u_1}} {x : α._@.Std.Data.List.Lemmas._hyg.21892} {p : α._@.Std.Data.List.Lemmas._hyg.21892 -> Bool} {as : List.{u_1} α._@.Std.Data.List.Lemmas._hyg.21892}, Iff (Membership.mem.{u_1, u_1} α._@.Std.Data.List.Lemmas._hyg.21892 (List.{u_1} α._@.Std.Data.List.Lemmas._hyg.21892) (List.instMembershipList.{u_1} α._@.Std.Data.List.Lemmas._hyg.21892) x (List.filter.{u_1} α._@.Std.Data.List.Lemmas._hyg.21892 p as)) (And (Membership.mem.{u_1, u_1} α._@.Std.Data.List.Lemmas._hyg.21892 (List.{u_1} α._@.Std.Data.List.Lemmas._hyg.21892) (List.instMembershipList.{u_1} α._@.Std.Data.List.Lemmas._hyg.21892) x as) (Eq.{1} Bool (p x) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.mem_filter List.mem_filterₓ'. -/
@[simp]
theorem mem_filter {a : α} {l} : a ∈ filter p l ↔ a ∈ l ∧ p a :=
  ⟨fun h => ⟨mem_of_mem_filter h, of_mem_filter h⟩, fun ⟨h₁, h₂⟩ => mem_filter_of_mem h₁ h₂⟩
#align list.mem_filter List.mem_filter

theorem monotone_filter_left (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l ⊆ l') :
    filter p l ⊆ filter p l' := by
  intro x hx
  rw [mem_filter] at hx⊢
  exact ⟨h hx.left, hx.right⟩
#align list.monotone_filter_left List.monotone_filter_left

theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a := by
  induction' l with a l ih
  · exact iff_of_true rfl (forall_mem_nil _)
  rw [forall_mem_cons]; by_cases p a
  · rw [filter_cons_of_pos _ h, cons_inj, ih, and_iff_right h]
  · refine' iff_of_false (fun hl => h <| of_mem_filter (_ : a ∈ filter p (a :: l))) (mt And.left h)
    rw [hl]
    exact mem_cons_self _ _
#align list.filter_eq_self List.filter_eq_self

theorem filter_length_eq_length {l} : (filter p l).length = l.length ↔ ∀ a ∈ l, p a :=
  Iff.trans ⟨l.filter_sublist.eq_of_length, congr_arg List.length⟩ filter_eq_self
#align list.filter_length_eq_length List.filter_length_eq_length

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a ∈ l, ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]
#align list.filter_eq_nil List.filter_eq_nil

variable (p)

theorem Sublist.filter {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ :=
  filter_map_eq_filter p ▸ s.filterMap _
#align list.sublist.filter List.Sublist.filter

theorem monotone_filter_right (l : List α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : p ≤ q) : l.filter p <+ l.filter q := by
  induction' l with hd tl IH
  · rfl
  · by_cases hp : p hd
    · rw [filter_cons_of_pos _ hp, filter_cons_of_pos _ (h _ hp)]
      exact IH.cons_cons hd
    · rw [filter_cons_of_neg _ hp]
      by_cases hq : q hd
      · rw [filter_cons_of_pos _ hq]
        exact sublist_cons_of_sublist hd IH
      · rw [filter_cons_of_neg _ hq]
        exact IH
#align list.monotone_filter_right List.monotone_filter_right

theorem map_filter (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  rw [← filter_map_eq_map, filter_filter_map, filter_map_filter] <;> rfl
#align list.map_filter List.map_filter

@[simp]
theorem filter_filter (q) [DecidablePred q] :
    ∀ l, filter p (filter q l) = filter (fun a => p a ∧ q a) l
  | [] => rfl
  | a :: l => by
    by_cases hp : p a <;> by_cases hq : q a <;>
      simp only [hp, hq, filter, if_true, if_false, true_and_iff, false_and_iff, filter_filter l,
        eq_self_iff_true]
#align list.filter_filter List.filter_filter

@[simp]
theorem filter_true {h : DecidablePred fun a : α => True} (l : List α) :
    @filter α (fun _ => True) h l = l := by convert filter_eq_self.2 fun _ _ => trivial
#align list.filter_true List.filter_true

@[simp]
theorem filter_false {h : DecidablePred fun a : α => False} (l : List α) :
    @filter α (fun _ => False) h l = [] := by convert filter_eq_nil.2 fun _ _ => id
#align list.filter_false List.filter_false

@[simp]
theorem span_eq_take_drop : ∀ l : List α, span p l = (takeWhile p l, dropWhile p l)
  | [] => rfl
  | a :: l =>
    if pa : p a then by simp only [span, if_pos pa, span_eq_take_drop l, take_while, drop_while]
    else by simp only [span, take_while, drop_while, if_neg pa]
#align list.span_eq_take_drop List.span_eq_take_drop

@[simp]
theorem take_while_append_drop : ∀ l : List α, takeWhile p l ++ dropWhile p l = l
  | [] => rfl
  | a :: l =>
    if pa : p a then by
      rw [take_while, drop_while, if_pos pa, if_pos pa, cons_append, take_while_append_drop l]
    else by rw [take_while, drop_while, if_neg pa, if_neg pa, nil_append]
#align list.take_while_append_drop List.take_while_append_drop

theorem drop_while_nth_le_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).nthLe 0 hl) := by
  induction' l with hd tl IH
  · cases hl
  · simp only [drop_while]
    split_ifs with hp
    · exact IH _
    · simpa using hp
#align list.drop_while_nth_le_zero_not List.drop_while_nth_le_zero_not

variable {p} {l : List α}

@[simp]
theorem drop_while_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp [drop_while]
  · by_cases hp : p x <;> simp [hp, drop_while, IH]
#align list.drop_while_eq_nil_iff List.drop_while_eq_nil_iff

@[simp]
theorem take_while_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp [take_while]
  · by_cases hp : p x <;> simp [hp, take_while, IH]
#align list.take_while_eq_self_iff List.take_while_eq_self_iff

@[simp]
theorem take_while_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.nthLe 0 hl) := by
  induction' l with x xs IH
  · simp
  · by_cases hp : p x <;> simp [hp, take_while, IH]
#align list.take_while_eq_nil_iff List.take_while_eq_nil_iff

theorem mem_take_while_imp {x : α} (hx : x ∈ takeWhile p l) : p x := by
  induction' l with hd tl IH
  · simpa [take_while] using hx
  · simp only [take_while] at hx
    split_ifs  at hx
    · rw [mem_cons_iff] at hx
      rcases hx with (rfl | hx)
      · exact h
      · exact IH hx
    · simpa using hx
#align list.mem_take_while_imp List.mem_take_while_imp

theorem take_while_take_while (p q : α → Prop) [DecidablePred p] [DecidablePred q] (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction' l with hd tl IH
  · simp [take_while]
  · by_cases hp : p hd <;> by_cases hq : q hd <;> simp [take_while, hp, hq, IH]
#align list.take_while_take_while List.take_while_take_while

theorem take_while_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [take_while_take_while, and_self_iff]
#align list.take_while_idem List.take_while_idem

end Filter

/-! ### erasep -/


section Erasep

variable {p : α → Prop} [DecidablePred p]

@[simp]
theorem eraseP_nil : [].erasep p = [] :=
  rfl
#align list.erasep_nil List.erasep_nil

theorem eraseP_cons (a : α) (l : List α) : (a :: l).erasep p = if p a then l else a :: l.erasep p :=
  rfl
#align list.erasep_cons List.erasep_cons

@[simp]
theorem eraseP_cons_of_pos {a : α} {l : List α} (h : p a) : (a :: l).erasep p = l := by
  simp [erasep_cons, h]
#align list.erasep_cons_of_pos List.erasep_cons_of_pos

@[simp]
theorem eraseP_cons_of_neg {a : α} {l : List α} (h : ¬p a) : (a :: l).erasep p = a :: l.erasep p :=
  by simp [erasep_cons, h]
#align list.erasep_cons_of_neg List.erasep_cons_of_neg

theorem eraseP_of_forall_not {l : List α} (h : ∀ a ∈ l, ¬p a) : l.erasep p = l := by
  induction' l with _ _ ih <;> [rfl, simp [h _ (Or.inl rfl), ih (forall_mem_of_forall_mem_cons h)]]
#align list.erasep_of_forall_not List.erasep_of_forall_not

-- theorem exists_of_eraseP {l : List α} {a} (al : a ∈ l) (pa : p a) :
--     ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ := by
--   induction' l with b l IH; · cases al
--   by_cases pb : p b
--   · exact ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩
--   · rcases al with (rfl | al)
--     · exact pb.elim pa
--     rcases IH al with ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩
--     exact ⟨c, b :: l₁, l₂, forall_mem_cons.2 ⟨pb, h₁⟩, h₂, by rw [h₃] <;> rfl, by simp [pb, h₄]⟩
#align list.exists_of_erasep List.exists_of_eraseP

-- theorem exists_or_eq_self_of_eraseP (p : α → Prop) [DecidablePred p] (l : List α) :
--     l.erasep p = l ∨
--       ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.eraseP p = l₁ ++ l₂ :=
--   by
--   by_cases h : ∃ a ∈ l, p a
--   · rcases h with ⟨a, ha, pa⟩
--     exact Or.inr (exists_of_erasep ha pa)
--   · simp at h
--     exact Or.inl (erasep_of_forall_not h)
#align list.exists_or_eq_self_of_erasep List.exists_or_eq_self_of_eraseP

-- @[simp]
-- theorem length_eraseP_of_mem {l : List α} {a} (al : a ∈ l) (pa : p a) :
--     length (l.eraseP p) = pred (length l) := by
--   rcases exists_of_erasep al pa with ⟨_, l₁, l₂, _, _, e₁, e₂⟩ <;> rw [e₂] <;>
--       simp [-add_comm, e₁] <;>
--     rfl
#align list.length_erasep_of_mem List.length_eraseP_of_mem

@[simp]
theorem length_eraseP_add_one {l : List α} {a} (al : a ∈ l) (pa : p a) :
    (l.eraseP p).length + 1 = l.length := by
  let ⟨_, l₁, l₂, _, _, h₁, h₂⟩ := exists_of_eraseP al pa
  rw [h₂, h₁, length_append, length_append]
  rfl
#align list.length_erasep_add_one List.length_eraseP_add_one

-- theorem eraseP_append_left {a : α} (pa : p a) :
--     ∀ {l₁ : List α} (l₂), a ∈ l₁ → (l₁ ++ l₂).erasep p = l₁.erasep p ++ l₂
--   | x :: xs, l₂, h => by
--     by_cases h' : p x <;> simp [h']
--     rw [erasep_append_left l₂ (mem_of_ne_of_mem (mt _ h') h)]
--     rintro rfl; exact pa
#align list.erasep_append_left List.eraseP_append_left

-- theorem eraseP_append_right :
--     ∀ {l₁ : List α} (l₂), (∀ b ∈ l₁, ¬p b) → (l₁ ++ l₂).erasep p = l₁ ++ l₂.erasep p
--   | [], l₂, h => rfl
--   | x :: xs, l₂, h => by
--     simp [(forall_mem_cons.1 h).1, erasep_append_right _ (forall_mem_cons.1 h).2]
#align list.erasep_append_right List.eraseP_append_right

-- theorem eraseP_sublist (l : List α) : l.erasep p <+ l := by
--   rcases exists_or_eq_self_of_erasep p l with (h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩) <;> [rw [h],
--     · rw [h₄, h₃]
--       simp]
#align list.erasep_sublist List.eraseP_sublist

-- theorem eraseP_subset (l : List α) : l.erasep p ⊆ l :=
--   (erasep_sublist l).Subset
#align list.erasep_subset List.eraseP_subset

-- theorem Sublist.eraseP {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p := by
--   induction s
--   case slnil => rfl
--   case cons l₁ l₂ a s IH =>
--     by_cases h : p a <;> simp [h]
--     exacts[IH.trans (erasep_sublist _), IH.cons _ _ _]
--   case cons2 l₁ l₂ a s IH =>
--     by_cases h : p a <;> simp [h]
--     exacts[s, IH.cons2 _ _ _]
#align list.sublist.erasep List.Sublist.eraseP

-- theorem mem_of_mem_erasep {a : α} {l : List α} : a ∈ l.erasep p → a ∈ l :=
  -- @erasep_subset _ _ _ _ _
#align list.mem_of_mem_erasep List.mem_of_mem_eraseP

-- @[simp]
-- theorem mem_eraseP_of_neg {a : α} {l : List α} (pa : ¬p a) : a ∈ l.erasep p ↔ a ∈ l :=
--   ⟨mem_of_mem_erasep, fun al => by
--     rcases exists_or_eq_self_of_erasep p l with (h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩)
--     · rwa [h]
--     · rw [h₄]
--       rw [h₃] at al
--       have : a ≠ c := by
--         rintro rfl
--         exact pa.elim h₂
--       simpa [this] using al⟩
#align list.mem_erasep_of_neg List.mem_eraseP_of_neg

-- theorem eraseP_map (f : β → α) : ∀ l : List β, (map f l).erasep p = map f (l.erasep (p ∘ f))
--   | [] => rfl
--   | b :: l => by by_cases p (f b) <;> simp [h, erasep_map l]
#align list.erasep_map List.eraseP_map

@[simp]
theorem extractP_eq_find_eraseP : ∀ l : List α, extractP p l =
    (find p l, eraseP p l)
  | [] => rfl
  | a :: l => by by_cases pa : p a <;> simp [extractp, pa, extractp_eq_find_erasep l]
#align list.extractp_eq_find_erasep List.extractP_eq_find_eraseP

end Erasep

/-! ### erase -/


section Erase

variable [DecidableEq α]

#print List.erase_nil /-
@[simp]
theorem erase_nil (a : α) : [].erase a = [] :=
  rfl
#align list.erase_nil List.erase_nil
-/

/- warning: list.erase_cons -> List.erase_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] (a : α) (b : α) (l : List.{u} α), Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u} α b l) a) (ite.{succ u} (List.{u} α) (Eq.{succ u} α b a) (_inst_1 b a) l (List.cons.{u} α b (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.20459 : DecidableEq.{succ u_1} α] (a : α) (b : α) (l : List.{u_1} α), Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.20459 a b)) (List.cons.{u_1} α b l) a) (ite.{succ u_1} (List.{u_1} α) (Eq.{succ u_1} α b a) (inst._@.Std.Data.List.Lemmas._hyg.20459 b a) l (List.cons.{u_1} α b (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.20459 a b)) l a)))
Case conversion may be inaccurate. Consider using '#align list.erase_cons List.erase_consₓ'. -/
theorem erase_cons (a b : α) (l : List α) :
    (b :: l).erase a = if b = a then l else b :: l.erase a :=
  rfl
#align list.erase_cons List.erase_cons

/- warning: list.erase_cons_head -> List.erase_cons_head is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] (a : α) (l : List.{u} α), Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u} α a l) a) l
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.20555 : DecidableEq.{succ u_1} α] (a : α) (l : List.{u_1} α), Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.20555 a b)) (List.cons.{u_1} α a l) a) l
Case conversion may be inaccurate. Consider using '#align list.erase_cons_head List.erase_cons_headₓ'. -/
@[simp]
theorem erase_cons_head (a : α) (l : List α) : (a :: l).erase a = l := by
  simp only [erase_cons, if_pos rfl]
#align list.erase_cons_head List.erase_cons_head

/- warning: list.erase_cons_tail -> List.erase_cons_tail is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {b : α} (l : List.{u} α), (Ne.{succ u} α b a) -> (Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u} α b l) a) (List.cons.{u} α b (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.20582 : DecidableEq.{succ u_1} α] {a : α} {b : α} (l : List.{u_1} α), (Ne.{succ u_1} α b a) -> (Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.20582 a b)) (List.cons.{u_1} α b l) a) (List.cons.{u_1} α b (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.20582 a b)) l a)))
Case conversion may be inaccurate. Consider using '#align list.erase_cons_tail List.erase_cons_tailₓ'. -/
-- @[simp]
-- theorem erase_cons_tail {a b : α} (l : List α) (h : b ≠ a) : (b :: l).erase a = b :: l.erase a := by
--   simp only [erase_cons, if_neg h] <;> constructor <;> rfl
#align list.erase_cons_tail List.erase_cons_tail

-- in Std
-- theorem erase_eq_eraseP (a : α) (l : List α) :
--     l.erase a = l.eraseP (Eq a) := by
--   induction' l with b l
--   · rfl
--   by_cases a = b <;> [simp [h], simp [h, Ne.symm h, *]]
#align list.erase_eq_erasep List.erase_eq_eraseP

/- warning: list.erase_of_not_mem -> List.erase_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {l : List.{u} α}, (Not (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l)) -> (Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a) l)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.20735 : DecidableEq.{succ u_1} α] {a : α} {l : List.{u_1} α}, (Not (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l)) -> (Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.20735 a b)) l a) l)
Case conversion may be inaccurate. Consider using '#align list.erase_of_not_mem List.erase_of_not_memₓ'. -/
-- in Std
-- @[simp]
-- theorem erase_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.erase a = l := by
--   rw [erase_eq_erasep, erasep_of_forall_not] <;> rintro b h' rfl <;> exact h h'
#align list.erase_of_not_mem List.erase_of_not_mem

/- warning: list.exists_erase_eq -> List.exists_erase_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {l : List.{u} α}, (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (Exists.{succ u} (List.{u} α) (fun (l₁ : List.{u} α) => Exists.{succ u} (List.{u} α) (fun (l₂ : List.{u} α) => And (Not (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l₁)) (And (Eq.{succ u} (List.{u} α) l (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l₁ (List.cons.{u} α a l₂))) (Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a) (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l₁ l₂))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.20882 : DecidableEq.{succ u_1} α] {a : α} {l : List.{u_1} α}, (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (Exists.{succ u_1} (List.{u_1} α) (fun (l₁ : List.{u_1} α) => Exists.{succ u_1} (List.{u_1} α) (fun (l₂ : List.{u_1} α) => And (Not (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l₁)) (And (Eq.{succ u_1} (List.{u_1} α) l (HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) l₁ (List.cons.{u_1} α a l₂))) (Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.20882 a b)) l a) (HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) l₁ l₂))))))
Case conversion may be inaccurate. Consider using '#align list.exists_erase_eq List.exists_erase_eqₓ'. -/
-- theorem exists_erase_eq {a : α} {l : List α} (h : a ∈ l) :
--     ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ := by
--   rcases exists_of_erasep h rfl with ⟨_, l₁, l₂, h₁, rfl, h₂, h₃⟩ <;> rw [erase_eq_erasep] <;>
--     exact ⟨l₁, l₂, fun h => h₁ _ h rfl, h₂, h₃⟩
-- in Std
#align list.exists_erase_eq List.exists_erase_eq

/- warning: list.length_erase_of_mem -> List.length_erase_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {l : List.{u} α}, (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l) -> (Eq.{1} Nat (List.length.{u} α (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a)) (Nat.pred (List.length.{u} α l)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21072 : DecidableEq.{succ u_1} α] {a : α} {l : List.{u_1} α}, (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l) -> (Eq.{1} Nat (List.length.{u_1} α (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21072 a b)) l a)) (Nat.pred (List.length.{u_1} α l)))
Case conversion may be inaccurate. Consider using '#align list.length_erase_of_mem List.length_erase_of_memₓ'. -/
-- in Std
-- @[simp]
-- theorem length_erase_of_mem {a : α} {l : List α} (h : a ∈ l) :
--     length (l.erase a) = pred (length l) := by
--   rw [erase_eq_erasep] <;> exact length_erasep_of_mem h rfl
#align list.length_erase_of_mem List.length_erase_of_mem

@[simp]
theorem length_erase_add_one {a : α} {l : List α} (h : a ∈ l) : (l.erase a).length + 1 = l.length :=
  by rw [erase_eq_eraseP, length_erasep_add_one h rfl]
#align list.length_erase_add_one List.length_erase_add_one

/- warning: list.erase_append_left -> List.erase_append_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {l₁ : List.{u} α} (l₂ : List.{u} α), (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l₁) -> (Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l₁ l₂) a) (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l₁ a) l₂))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21139 : DecidableEq.{succ u_1} α] {a : α} {l₁ : List.{u_1} α} (l₂ : List.{u_1} α), (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l₁) -> (Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21139 a b)) (HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) l₁ l₂) a) (HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21139 a b)) l₁ a) l₂))
Case conversion may be inaccurate. Consider using '#align list.erase_append_left List.erase_append_leftₓ'. -/
theorem erase_append_left {a : α} {l₁ : List α} (l₂) (h : a ∈ l₁) :
    (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ := by
  simp [erase_eq_erasep] <;> exact erasep_append_left (by rfl) l₂ h
#align list.erase_append_left List.erase_append_left

/- warning: list.erase_append_right -> List.erase_append_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {l₁ : List.{u} α} (l₂ : List.{u} α), (Not (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l₁)) -> (Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l₁ l₂) a) (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l₁ (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l₂ a)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21193 : DecidableEq.{succ u_1} α] {a : α} {l₁ : List.{u_1} α} (l₂ : List.{u_1} α), (Not (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l₁)) -> (Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21193 a b)) (HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) l₁ l₂) a) (HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) l₁ (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21193 a b)) l₂ a)))
Case conversion may be inaccurate. Consider using '#align list.erase_append_right List.erase_append_rightₓ'. -/
theorem erase_append_right {a : α} {l₁ : List α} (l₂) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = l₁ ++ l₂.erase a := by
  rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right] <;> rintro b h' rfl <;> exact h h'
#align list.erase_append_right List.erase_append_right

/- warning: list.erase_sublist -> List.erase_sublist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] (a : α) (l : List.{u} α), List.Sublist.{u} α (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a) l
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21298 : DecidableEq.{succ u_1} α] (a : α) (l : List.{u_1} α), List.Sublist.{u_1} α (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21298 a b)) l a) l
Case conversion may be inaccurate. Consider using '#align list.erase_sublist List.erase_sublistₓ'. -/
theorem erase_sublist (a : α) (l : List α) : l.erase a <+ l := by
  rw [erase_eq_erasep] <;> apply erasep_sublist
#align list.erase_sublist List.erase_sublist

/- warning: list.erase_subset -> List.erase_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] (a : α) (l : List.{u} α), HasSubset.Subset.{u} (List.{u} α) (List.hasSubset.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a) l
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21322 : DecidableEq.{succ u_1} α] (a : α) (l : List.{u_1} α), HasSubset.Subset.{u_1} (List.{u_1} α) (List.instHasSubsetList.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21322 a b)) l a) l
Case conversion may be inaccurate. Consider using '#align list.erase_subset List.erase_subsetₓ'. -/
theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l :=
  (erase_sublist a l).Subset
#align list.erase_subset List.erase_subset

theorem Sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a := by
  simp [erase_eq_erasep] <;> exact sublist.erasep h
#align list.sublist.erase List.Sublist.erase

/- warning: list.mem_of_mem_erase -> List.mem_of_mem_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {b : α} {l : List.{u} α}, (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l b)) -> (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21378 : DecidableEq.{succ u_1} α] {a : α} {b : α} {l : List.{u_1} α}, (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21378 a b)) l b)) -> (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l)
Case conversion may be inaccurate. Consider using '#align list.mem_of_mem_erase List.mem_of_mem_eraseₓ'. -/
theorem mem_of_mem_erase {a b : α} {l : List α} : a ∈ l.erase b → a ∈ l :=
  @erase_subset _ _ _ _ _
#align list.mem_of_mem_erase List.mem_of_mem_erase

/- warning: list.mem_erase_of_ne -> List.mem_erase_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] {a : α} {b : α} {l : List.{u} α}, (Ne.{succ u} α a b) -> (Iff (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l b)) (Membership.Mem.{u, u} α (List.{u} α) (List.hasMem.{u} α) a l))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21404 : DecidableEq.{succ u_1} α] {a : α} {b : α} {l : List.{u_1} α}, (Ne.{succ u_1} α a b) -> (Iff (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21404 a b)) l b)) (Membership.mem.{u_1, u_1} α (List.{u_1} α) (List.instMembershipList.{u_1} α) a l))
Case conversion may be inaccurate. Consider using '#align list.mem_erase_of_ne List.mem_erase_of_neₓ'. -/
@[simp]
theorem mem_erase_of_ne {a b : α} {l : List α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l := by
  rw [erase_eq_erasep] <;> exact mem_erasep_of_neg ab.symm
#align list.mem_erase_of_ne List.mem_erase_of_ne

/- warning: list.erase_comm -> List.erase_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : DecidableEq.{succ u} α] (a : α) (b : α) (l : List.{u} α), Eq.{succ u} (List.{u} α) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l a) b) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) (List.eraseₓ.{u} α (fun (a : α) (b : α) => _inst_1 a b) l b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Std.Data.List.Lemmas._hyg.21446 : DecidableEq.{succ u_1} α] (a : α) (b : α) (l : List.{u_1} α), Eq.{succ u_1} (List.{u_1} α) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21446 a b)) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21446 a b)) l a) b) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21446 a b)) (List.erase.{u_1} α (instBEq.{u_1} α (fun (a : α) (b : α) => inst._@.Std.Data.List.Lemmas._hyg.21446 a b)) l b) a)
Case conversion may be inaccurate. Consider using '#align list.erase_comm List.erase_commₓ'. -/
theorem erase_comm (a b : α) (l : List α) : (l.erase a).erase b = (l.erase b).erase a :=
  if ab : a = b then by rw [ab]
  else
    if ha : a ∈ l then
      if hb : b ∈ l then
        match l, l.erase a, exists_erase_eq ha, hb with
        | _, _, ⟨l₁, l₂, ha', rfl, rfl⟩, hb =>
          if h₁ : b ∈ l₁ then by
            rw [erase_append_left _ h₁, erase_append_left _ h₁,
              erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
          else by
            rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
              erase_cons_tail _ ab, erase_cons_head]
      else by simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
    else by simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]
#align list.erase_comm List.erase_comm

theorem map_erase [DecidableEq β] {f : α → β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) := by
  have this : Eq a = Eq (f a) ∘ f := by ext b; simp [finj.eq_iff]
  simp [erase_eq_erasep, erase_eq_erasep, erasep_map, this]
#align list.map_erase List.map_erase

theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl, simp only [foldl_cons, map_erase finj, *]]
#align list.map_foldl_erase List.map_foldl_erase

end Erase

/-! ### diff -/


section Diff

variable [DecidableEq α]

@[simp]
theorem diff_nil (l : List α) : l.diff [] = l :=
  rfl
#align list.diff_nil List.diff_nil

@[simp]
theorem diff_cons (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ :=
  if h : a ∈ l₁ then by simp only [List.diff, if_pos h]
  else by simp only [List.diff, if_neg h, erase_of_not_mem h]
#align list.diff_cons List.diff_cons

theorem diff_cons_right (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.diff l₂).erase a := by
  induction' l₂ with b l₂ ih generalizing l₁ a
  · simp_rw [diff_cons, diff_nil]
  · rw [diff_cons, diff_cons, erase_comm, ← diff_cons, ih, ← diff_cons]
#align list.diff_cons_right List.diff_cons_right

theorem diff_erase (l₁ l₂ : List α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ := by
  rw [← diff_cons_right, diff_cons]
#align list.diff_erase List.diff_erase

@[simp]
theorem nil_diff (l : List α) : [].diff l = [] := by
  induction l <;> [rfl, simp only [*, diff_cons, erase_of_not_mem (not_mem_nil _)]]
#align list.nil_diff List.nil_diff

theorem cons_diff (a : α) (l₁ l₂ : List α) :
    (a :: l₁).diff l₂ = if a ∈ l₂ then l₁.diff (l₂.erase a) else a :: l₁.diff l₂ := by
  induction' l₂ with b l₂ ih; · rfl
  rcases eq_or_ne a b with (rfl | hne)
  · simp
  · simp only [mem_cons_iff, *, false_or_iff, diff_cons_right]
    split_ifs with h₂ <;> simp [diff_erase, List.erase, hne, hne.symm]
#align list.cons_diff List.cons_diff

theorem cons_diff_of_mem {a : α} {l₂ : List α} (h : a ∈ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = l₁.diff (l₂.erase a) := by rw [cons_diff, if_pos h]
#align list.cons_diff_of_mem List.cons_diff_of_mem

theorem cons_diff_of_not_mem {a : α} {l₂ : List α} (h : a ∉ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = a :: l₁.diff l₂ := by rw [cons_diff, if_neg h]
#align list.cons_diff_of_not_mem List.cons_diff_of_not_mem

theorem diff_eq_foldl : ∀ l₁ l₂ : List α, l₁.diff l₂ = foldl List.erase l₁ l₂
  | l₁, [] => rfl
  | l₁, a :: l₂ => (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)
#align list.diff_eq_foldl List.diff_eq_foldl

@[simp]
theorem diff_append (l₁ l₂ l₃ : List α) : l₁.diff (l₂ ++ l₃) = (l₁.diff l₂).diff l₃ := by
  simp only [diff_eq_foldl, foldl_append]
#align list.diff_append List.diff_append

@[simp]
theorem map_diff [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]
#align list.map_diff List.map_diff

theorem diff_sublist : ∀ l₁ l₂ : List α, l₁.diff l₂ <+ l₁
  | l₁, [] => Sublist.refl _
  | l₁, a :: l₂ =>
    calc
      l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := diff_cons _ _ _
      _ <+ l₁.erase a := diff_sublist _ _
      _ <+ l₁ := List.erase_sublist _ _

#align list.diff_sublist List.diff_sublist

theorem diff_subset (l₁ l₂ : List α) : l₁.diff l₂ ⊆ l₁ :=
  (diff_sublist _ _).Subset
#align list.diff_subset List.diff_subset

theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
  | l₁, [], h₁, h₂ => h₁
  | l₁, b :: l₂, h₁, h₂ => by
    rw [diff_cons] <;>
      exact
        mem_diff_of_mem ((mem_erase_of_ne (ne_of_not_mem_cons h₂)).2 h₁)
          (not_mem_of_not_mem_cons h₂)
#align list.mem_diff_of_mem List.mem_diff_of_mem

theorem Sublist.diff_right : ∀ {l₁ l₂ l₃ : List α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
  | l₁, l₂, [], h => h
  | l₁, l₂, a :: l₃, h => by simp only [diff_cons, (h.erase _).diff_right]
#align list.sublist.diff_right List.Sublist.diff_right

theorem erase_diff_erase_sublist_of_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], l₂, h => erase_sublist _ _
  | b :: l₁, l₂, h =>
    if heq : b = a then by simp only [HEq, erase_cons_head, diff_cons]
    else by
      simpa only [erase_cons_head, erase_cons_tail _ HEq, diff_cons, erase_comm a b l₂] using
        erase_diff_erase_sublist_of_sublist (h.erase b)
#align list.erase_diff_erase_sublist_of_sublist List.erase_diff_erase_sublist_of_sublist

end Diff

/-! ### enum -/


theorem length_enum_from : ∀ (n) (l : List α), length (enumFrom n l) = length l
  | n, [] => rfl
  | n, a :: l => congr_arg Nat.succ (length_enum_from _ _)
#align list.length_enum_from List.length_enum_from

theorem length_enum : ∀ l : List α, length (enum l) = length l :=
  length_enum_from _
#align list.length_enum List.length_enum

@[simp]
theorem enum_from_nth :
    ∀ (n) (l : List α) (m), nth (enumFrom n l) m = (fun a => (n + m, a)) <$> nth l m
  | n, [], m => rfl
  | n, a :: l, 0 => rfl
  | n, a :: l, m + 1 => (enum_from_nth (n + 1) l m).trans <| by rw [add_right_comm] <;> rfl
#align list.enum_from_nth List.enum_from_nth

@[simp]
theorem enum_nth : ∀ (l : List α) (n), nth (enum l) n = (fun a => (n, a)) <$> nth l n := by
  simp only [enum, enum_from_nth, zero_add] <;> intros <;> rfl
#align list.enum_nth List.enum_nth

@[simp]
theorem enum_from_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | n, [] => rfl
  | n, a :: l => congr_arg (cons _) (enum_from_map_snd _ _)
#align list.enum_from_map_snd List.enum_from_map_snd

@[simp]
theorem enum_map_snd : ∀ l : List α, map Prod.snd (enum l) = l :=
  enum_from_map_snd _
#align list.enum_map_snd List.enum_map_snd

theorem mem_enum_from {x : α} {i : ℕ} :
    ∀ {j : ℕ} (xs : List α), (i, x) ∈ xs.enumFrom j → j ≤ i ∧ i < j + xs.length ∧ x ∈ xs
  | j, [] => by simp [enum_from]
  | j, y :: ys => by
    suffices
      i = j ∧ x = y ∨ (i, x) ∈ enumFrom (j + 1) ys →
        j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys)
      by simpa [enum_from, mem_enum_from ys]
    rintro (h | h)
    · refine' ⟨le_of_eq h.1.symm, h.1 ▸ _, Or.inl h.2⟩
      apply Nat.lt_add_of_pos_right <;> simp
    · obtain ⟨hji, hijlen, hmem⟩ := mem_enum_from _ h
      refine' ⟨_, _, _⟩
      · exact le_trans (Nat.le_succ _) hji
      · convert hijlen using 1
        ac_rfl
      · simp [hmem]
#align list.mem_enum_from List.mem_enum_from

@[simp]
theorem enum_nil : enum ([] : List α) = [] :=
  rfl
#align list.enum_nil List.enum_nil

@[simp]
theorem enum_from_nil (n : ℕ) : enumFrom n ([] : List α) = [] :=
  rfl
#align list.enum_from_nil List.enum_from_nil

@[simp]
theorem enum_from_cons (x : α) (xs : List α) (n : ℕ) :
    enumFrom n (x :: xs) = (n, x) :: enumFrom (n + 1) xs :=
  rfl
#align list.enum_from_cons List.enum_from_cons

@[simp]
theorem enum_cons (x : α) (xs : List α) : enum (x :: xs) = (0, x) :: enumFrom 1 xs :=
  rfl
#align list.enum_cons List.enum_cons

@[simp]
theorem enum_from_singleton (x : α) (n : ℕ) : enumFrom n [x] = [(n, x)] :=
  rfl
#align list.enum_from_singleton List.enum_from_singleton

@[simp]
theorem enum_singleton (x : α) : enum [x] = [(0, x)] :=
  rfl
#align list.enum_singleton List.enum_singleton

theorem enum_from_append (xs ys : List α) (n : ℕ) :
    enumFrom n (xs ++ ys) = enumFrom n xs ++ enumFrom (n + xs.length) ys := by
  induction' xs with x xs IH generalizing ys n
  · simp
  ·
    rw [cons_append, enum_from_cons, IH, ← cons_append, ← enum_from_cons, length, add_right_comm,
      add_assoc]
#align list.enum_from_append List.enum_from_append

theorem enum_append (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enum_from_append]
#align list.enum_append List.enum_append

theorem map_fst_add_enum_from_eq_enum_from (l : List α) (n k : ℕ) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l := by
  induction' l with hd tl IH generalizing n k
  · simp [enum_from]
  · simp only [enum_from, map, zero_add, Prod.map_mk, id.def, eq_self_iff_true, true_and_iff]
    simp [IH, add_comm n k, add_assoc, add_left_comm]
#align list.map_fst_add_enum_from_eq_enum_from List.map_fst_add_enum_from_eq_enum_from

theorem map_fst_add_enum_eq_enum_from (l : List α) (n : ℕ) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enum_from_eq_enum_from l _ _
#align list.map_fst_add_enum_eq_enum_from List.map_fst_add_enum_eq_enum_from

theorem nth_le_enum_from (l : List α) (n i : ℕ) (hi' : i < (l.enumFrom n).length)
    (hi : i < l.length := by simpa [length_enum_from] using hi') :
    (l.enumFrom n).nthLe i hi' = (n + i, l.nthLe i hi) := by
  rw [← Option.some_inj, ← nth_le_nth]
  simp [enum_from_nth, nth_le_nth hi]
#align list.nth_le_enum_from List.nth_le_enum_from

theorem nth_le_enum (l : List α) (i : ℕ) (hi' : i < l.enum.length)
    (hi : i < l.length := by simpa [length_enum] using hi') :
    l.enum.nthLe i hi' = (i, l.nthLe i hi) := by
  convert nth_le_enum_from _ _ _ hi'
  exact (zero_add _).symm
#align list.nth_le_enum List.nth_le_enum

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

theorem choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
#align list.choose_spec List.choose_spec

theorem choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
#align list.choose_mem List.choose_mem

theorem choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2
#align list.choose_property List.choose_property

end Choose

/-! ### map₂_left' -/


section Map₂Left'

-- The definitional equalities for `map₂_left'` can already be used by the
-- simplifie because `map₂_left'` is marked `@[simp]`.
@[simp]
theorem map₂_left'_nil_right (f : α → Option β → γ) (as) :
    map₂Left' f as [] = (as.map fun a => f a none, []) := by cases as <;> rfl
#align list.map₂_left'_nil_right List.map₂_left'_nil_right

end Map₂Left'

/-! ### map₂_right' -/


section Map₂Right'

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂_right'_nil_left : map₂Right' f [] bs = (bs.map (f none), []) := by cases bs <;> rfl
#align list.map₂_right'_nil_left List.map₂_right'_nil_left

@[simp]
theorem map₂_right'_nil_right : map₂Right' f as [] = ([], as) :=
  rfl
#align list.map₂_right'_nil_right List.map₂_right'_nil_right

@[simp]
theorem map₂_right'_nil_cons : map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl
#align list.map₂_right'_nil_cons List.map₂_right'_nil_cons

@[simp]
theorem map₂_right'_cons_cons :
    map₂Right' f (a :: as) (b :: bs) =
      let rec := map₂Right' f as bs
      (f (some a) b :: rec.fst, rec.snd) :=
  rfl
#align list.map₂_right'_cons_cons List.map₂_right'_cons_cons

end Map₂Right'

/-! ### zip_left' -/


section ZipLeft'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zip_left'_nil_right : zipLeft' as ([] : List β) = (as.map fun a => (a, none), []) := by
  cases as <;> rfl
#align list.zip_left'_nil_right List.zip_left'_nil_right

@[simp]
theorem zip_left'_nil_left : zipLeft' ([] : List α) bs = ([], bs) :=
  rfl
#align list.zip_left'_nil_left List.zip_left'_nil_left

@[simp]
theorem zip_left'_cons_nil :
    zipLeft' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl
#align list.zip_left'_cons_nil List.zip_left'_cons_nil

@[simp]
theorem zip_left'_cons_cons :
    zipLeft' (a :: as) (b :: bs) =
      let rec := zipLeft' as bs
      ((a, some b) :: rec.fst, rec.snd) :=
  rfl
#align list.zip_left'_cons_cons List.zip_left'_cons_cons

end ZipLeft'

/-! ### zip_right' -/


section ZipRight'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zip_right'_nil_left : zipRight' ([] : List α) bs = (bs.map fun b => (none, b), []) := by
  cases bs <;> rfl
#align list.zip_right'_nil_left List.zip_right'_nil_left

@[simp]
theorem zip_right'_nil_right : zipRight' as ([] : List β) = ([], as) :=
  rfl
#align list.zip_right'_nil_right List.zip_right'_nil_right

@[simp]
theorem zip_right'_nil_cons :
    zipRight' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl
#align list.zip_right'_nil_cons List.zip_right'_nil_cons

@[simp]
theorem zip_right'_cons_cons :
    zipRight' (a :: as) (b :: bs) =
      let rec := zipRight' as bs
      ((some a, b) :: rec.fst, rec.snd) :=
  rfl
#align list.zip_right'_cons_cons List.zip_right'_cons_cons

end ZipRight'

/-! ### map₂_left -/


section Map₂Left

variable (f : α → Option β → γ) (as : List α)

-- The definitional equalities for `map₂_left` can already be used by the
-- simplifier because `map₂_left` is marked `@[simp]`.
@[simp]
theorem map₂_left_nil_right : map₂Left f as [] = as.map fun a => f a none := by cases as <;> rfl
#align list.map₂_left_nil_right List.map₂_left_nil_right

theorem map₂_left_eq_map₂_left' : ∀ as bs, map₂Left f as bs = (map₂Left' f as bs).fst
  | [], bs => by simp!
  | a :: as, [] => by simp!
  | a :: as, b :: bs => by simp! [*]
#align list.map₂_left_eq_map₂_left' List.map₂_left_eq_map₂_left'

theorem map₂_left_eq_map₂ :
    ∀ as bs, length as ≤ length bs → map₂Left f as bs = map₂ (fun a b => f a (some b)) as bs
  | [], [], h => by simp!
  | [], b :: bs, h => by simp!
  | a :: as, [], h => by
    simp at h
    contradiction
  | a :: as, b :: bs, h => by
    simp at h
    simp! [*]
#align list.map₂_left_eq_map₂ List.map₂_left_eq_map₂

end Map₂Left

/-! ### map₂_right -/


section Map₂Right

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂_right_nil_left : map₂Right f [] bs = bs.map (f none) := by cases bs <;> rfl
#align list.map₂_right_nil_left List.map₂_right_nil_left

@[simp]
theorem map₂_right_nil_right : map₂Right f as [] = [] :=
  rfl
#align list.map₂_right_nil_right List.map₂_right_nil_right

@[simp]
theorem map₂_right_nil_cons : map₂Right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl
#align list.map₂_right_nil_cons List.map₂_right_nil_cons

@[simp]
theorem map₂_right_cons_cons :
    map₂Right f (a :: as) (b :: bs) = f (some a) b :: map₂Right f as bs :=
  rfl
#align list.map₂_right_cons_cons List.map₂_right_cons_cons

theorem map₂_right_eq_map₂_right' : map₂Right f as bs = (map₂Right' f as bs).fst := by
  simp only [map₂_right, map₂_right', map₂_left_eq_map₂_left']
#align list.map₂_right_eq_map₂_right' List.map₂_right_eq_map₂_right'

theorem map₂_right_eq_map₂ (h : length bs ≤ length as) :
    map₂Right f as bs = map₂ (fun a b => f (some a) b) as bs := by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂_right, map₂_left_eq_map₂, map₂_flip, *]
#align list.map₂_right_eq_map₂ List.map₂_right_eq_map₂

end Map₂Right

/-! ### zip_left -/


section ZipLeft

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zip_left_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none) := by
  cases as <;> rfl
#align list.zip_left_nil_right List.zip_left_nil_right

@[simp]
theorem zip_left_nil_left : zipLeft ([] : List α) bs = [] :=
  rfl
#align list.zip_left_nil_left List.zip_left_nil_left

@[simp]
theorem zip_left_cons_nil :
    zipLeft (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl
#align list.zip_left_cons_nil List.zip_left_cons_nil

@[simp]
theorem zip_left_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs :=
  rfl
#align list.zip_left_cons_cons List.zip_left_cons_cons

theorem zip_left_eq_zip_left' : zipLeft as bs = (zipLeft' as bs).fst := by
  simp only [zip_left, zip_left', map₂_left_eq_map₂_left']
#align list.zip_left_eq_zip_left' List.zip_left_eq_zip_left'

end ZipLeft

/-! ### zip_right -/


section ZipRight

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zip_right_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b) := by
  cases bs <;> rfl
#align list.zip_right_nil_left List.zip_right_nil_left

@[simp]
theorem zip_right_nil_right : zipRight as ([] : List β) = [] :=
  rfl
#align list.zip_right_nil_right List.zip_right_nil_right

@[simp]
theorem zip_right_nil_cons :
    zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl
#align list.zip_right_nil_cons List.zip_right_nil_cons

@[simp]
theorem zip_right_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs :=
  rfl
#align list.zip_right_cons_cons List.zip_right_cons_cons

theorem zip_right_eq_zip_right' : zipRight as bs = (zipRight' as bs).fst := by
  simp only [zip_right, zip_right', map₂_right_eq_map₂_right']
#align list.zip_right_eq_zip_right' List.zip_right_eq_zip_right'

end ZipRight

/-! ### to_chunks -/


section ToChunks

@[simp]
theorem to_chunks_nil (n) : @toChunks α n [] = [] := by cases n <;> rfl
#align list.to_chunks_nil List.to_chunks_nil

theorem to_chunks_aux_eq (n) :
    ∀ xs i, @toChunksAux α n xs i = (xs.take i, (xs.drop i).toChunks (n + 1))
  | [], i => by cases i <;> rfl
  | x :: xs, 0 => by rw [to_chunks_aux, drop, to_chunks] <;> cases to_chunks_aux n xs n <;> rfl
  | x :: xs, i + 1 => by rw [to_chunks_aux, to_chunks_aux_eq] <;> rfl
#align list.to_chunks_aux_eq List.to_chunks_aux_eq

theorem to_chunks_eq_cons' (n) :
    ∀ {xs : List α} (h : xs ≠ []),
      xs.toChunks (n + 1) = xs.take (n + 1) :: (xs.drop (n + 1)).toChunks (n + 1)
  | [], e => (e rfl).elim
  | x :: xs, _ => by rw [to_chunks, to_chunks_aux_eq] <;> rfl
#align list.to_chunks_eq_cons' List.to_chunks_eq_cons'

theorem to_chunks_eq_cons :
    ∀ {n} {xs : List α} (n0 : n ≠ 0) (x0 : xs ≠ []),
      xs.toChunks n = xs.take n :: (xs.drop n).toChunks n
  | 0, _, e => (e rfl).elim
  | n + 1, xs, _ => to_chunks_eq_cons' _
#align list.to_chunks_eq_cons List.to_chunks_eq_cons

theorem to_chunks_aux_join {n} : ∀ {xs i l L}, @toChunksAux α n xs i = (l, L) → l ++ L.join = xs
  | [], _, _, _, rfl => rfl
  | x :: xs, i, l, L, e => by
    cases i <;> [cases' e' : to_chunks_aux n xs n with l L,
        cases' e' : to_chunks_aux n xs i with l L] <;>
      · rw [to_chunks_aux, e', to_chunks_aux] at e
        cases e
        exact (congr_arg (cons x) (to_chunks_aux_join e') : _)
#align list.to_chunks_aux_join List.to_chunks_aux_join

@[simp]
theorem to_chunks_join : ∀ n xs, (@toChunks α n xs).join = xs
  | n, [] => by cases n <;> rfl
  | 0, x :: xs => by simp only [to_chunks, join] <;> rw [append_nil]
  | n + 1, x :: xs => by
    rw [to_chunks]
    cases' e : to_chunks_aux n xs n with l L
    exact (congr_arg (cons x) (to_chunks_aux_join e) : _)
#align list.to_chunks_join List.to_chunks_join

theorem to_chunks_length_le : ∀ n xs, n ≠ 0 → ∀ l : List α, l ∈ @toChunks α n xs → l.length ≤ n
  | 0, _, e, _ => (e rfl).elim
  | n + 1, xs, _, l => by
    refine' (measure_wf length).induction xs _; intro xs IH h
    by_cases x0 : xs = [];
    · subst xs
      cases h
    rw [to_chunks_eq_cons' _ x0] at h; rcases h with (rfl | h)
    · apply length_take_le
    · refine' IH _ _ h
      simp only [Measure, InvImage, length_drop]
      exact tsub_lt_self (length_pos_iff_ne_nil.2 x0) (succ_pos _)
#align list.to_chunks_length_le List.to_chunks_length_le

end ToChunks

/-! ### all₂ -/


section All₂

variable {p q : α → Prop} {l : List α}

@[simp]
theorem all₂_cons (p : α → Prop) (x : α) : ∀ l : List α, All₂ p (x :: l) ↔ p x ∧ All₂ p l
  | [] => (and_true_iff _).symm
  | x :: l => Iff.rfl
#align list.all₂_cons List.all₂_cons

theorem all₂_iff_forall : ∀ {l : List α}, All₂ p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| ball_nil _).symm
  | x :: l => by rw [ball_cons, all₂_cons, all₂_iff_forall]
#align list.all₂_iff_forall List.all₂_iff_forall

theorem All₂.imp (h : ∀ x, p x → q x) : ∀ {l : List α}, All₂ p l → All₂ q l
  | [] => id
  | x :: l => by simpa using And.imp (h x) all₂.imp
#align list.all₂.imp List.All₂.imp

@[simp]
theorem all₂_map_iff {p : β → Prop} (f : α → β) : All₂ p (l.map f) ↔ All₂ (p ∘ f) l := by
  induction l <;> simp [*]
#align list.all₂_map_iff List.all₂_map_iff

instance (p : α → Prop) [DecidablePred p] : DecidablePred (All₂ p) := fun l =>
  decidable_of_iff' _ all₂_iff_forall

end All₂

/-! ### Retroattributes

The list definitions happen earlier than `to_additive`, so here we tag the few multiplicative
definitions that couldn't be tagged earlier.
-/


attribute [to_additive] List.prod

-- `list.sum`
attribute [to_additive] alternating_prod

/-! ### Miscellaneous lemmas -/


-- `list.alternating_sum`
theorem last_reverse {l : List α} (hl : l.reverse ≠ [])
    (hl' : 0 < l.length := by
      contrapose! hl
      simpa [length_eq_zero] using hl) :
    l.reverse.last hl = l.nthLe 0 hl' := by
  rw [last_eq_nth_le, nth_le_reverse']
  · simp
  · simpa using hl'
#align list.last_reverse List.last_reverse

theorem ilast'_mem : ∀ a l, @ilast' α a l ∈ a :: l
  | a, [] => Or.inl rfl
  | a, b :: l => Or.inr (ilast'_mem b l)
#align list.ilast'_mem List.ilast'_mem

@[simp]
theorem nth_le_attach (L : List α) (i) (H : i < L.attach.length) :
    (L.attach.nthLe i H).1 = L.nthLe i (length_attach L ▸ H) :=
  calc
    (L.attach.nthLe i H).1 = (L.attach.map Subtype.val).nthLe i (by simpa using H) := by
      rw [nth_le_map']
    _ = L.nthLe i _ := by congr <;> apply attach_map_val

#align list.nth_le_attach List.nth_le_attach

@[simp]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs := by
  induction' xs with x xs
  · simp only [not_mem_nil, map_nil]
  · cases' x with a b
    simp only [mem_cons_iff, Prod.mk.inj_iff, map, Prod.swap_prod_mk, Prod.exists, xs_ih, and_comm']
#align list.mem_map_swap List.mem_map_swap

theorem slice_eq (xs : List α) (n m : ℕ) : slice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs
  · simp [slice]
  · cases xs <;> simp [slice, *, Nat.succ_add]
#align list.slice_eq List.slice_eq

theorem sizeof_slice_lt [SizeOf α] (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    SizeOf.sizeOf (List.slice i j xs) < SizeOf.sizeOf xs := by
  induction xs generalizing i j
  case nil i j h => cases hi
  case cons x xs xs_ih i j h =>
    cases i <;> simp only [-slice_eq, List.slice]
    · cases j
      cases h
      dsimp only [drop]
      unfold_wf
      apply @lt_of_le_of_lt _ _ _ xs.sizeof
      · clear * -
        induction xs generalizing j <;> unfold_wf
        case nil j => rfl
        case cons xs_hd xs_tl xs_ih j =>
          cases j <;> unfold_wf; rfl
          trans; apply xs_ih
          simp
      unfold_wf
    · unfold_wf
      apply xs_ih _ _ h
      apply lt_of_succ_lt_succ hi
#align list.sizeof_slice_lt List.sizeof_slice_lt

/-! ### nthd and inth -/


section Nthd

variable (l : List α) (x : α) (xs : List α) (d : α) (n : ℕ)

@[simp]
theorem nthd_nil : nthd d [] n = d :=
  rfl
#align list.nthd_nil List.nthd_nil

@[simp]
theorem nthd_cons_zero : nthd d (x :: xs) 0 = x :=
  rfl
#align list.nthd_cons_zero List.nthd_cons_zero

@[simp]
theorem nthd_cons_succ : nthd d (x :: xs) (n + 1) = nthd d xs n :=
  rfl
#align list.nthd_cons_succ List.nthd_cons_succ

theorem nthd_eq_nth_le {n : ℕ} (hn : n < l.length) : l.nthd d n = l.nthLe n hn := by
  induction' l with hd tl IH generalizing n
  · exact absurd hn (not_lt_of_ge (Nat.zero_le _))
  · cases n
    · exact nthd_cons_zero _ _ _
    · exact IH _
#align list.nthd_eq_nth_le List.nthd_eq_nth_le

theorem nthd_eq_default {n : ℕ} (hn : l.length ≤ n) : l.nthd d n = d := by
  induction' l with hd tl IH generalizing n
  · exact nthd_nil _ _
  · cases n
    · refine' absurd (Nat.zero_lt_succ _) (not_lt_of_ge hn)
    · exact IH (Nat.le_of_succ_le_succ hn)
#align list.nthd_eq_default List.nthd_eq_default

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `decidable_eq α`. -/
def decidableNthdNilNe {α} (a : α) : DecidablePred fun i : ℕ => nthd a ([] : List α) i ≠ a :=
  fun i => is_false fun H => H (nthd_nil _ _)
#align list.decidable_nthd_nil_ne List.decidableNthdNilNe

@[simp]
theorem nthd_singleton_default_eq (n : ℕ) : [d].nthd d n = d := by cases n <;> simp
#align list.nthd_singleton_default_eq List.nthd_singleton_default_eq

@[simp]
theorem nthd_repeat_default_eq (r n : ℕ) : (repeat d r).nthd d n = d := by
  induction' r with r IH generalizing n
  · simp
  · cases n <;> simp [IH]
#align list.nthd_repeat_default_eq List.nthd_repeat_default_eq

theorem nthd_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').nthd d n = l.nthd d n := by
  rw [nthd_eq_nth_le _ _ h', nth_le_append h' h, nthd_eq_nth_le]
#align list.nthd_append List.nthd_append

theorem nthd_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').nthd d n = l'.nthd d (n - l.length) := by
  cases' lt_or_le _ _ with h' h'
  · rw [nthd_eq_nth_le _ _ h', nth_le_append_right h h', nthd_eq_nth_le]
  · rw [nthd_eq_default _ _ h', nthd_eq_default]
    rwa [le_tsub_iff_left h, ← length_append]
#align list.nthd_append_right List.nthd_append_right

theorem nthd_eq_get_or_else_nth (n : ℕ) : l.nthd d n = (l.nth n).getOrElse d := by
  cases' lt_or_le _ _ with h h
  · rw [nthd_eq_nth_le _ _ h, nth_le_nth h, Option.get_or_else_some]
  · rw [nthd_eq_default _ _ h, nth_eq_none_iff.mpr h, Option.get_or_else_none]
#align list.nthd_eq_get_or_else_nth List.nthd_eq_get_or_else_nth

end Nthd

section Inth

variable [Inhabited α] (l : List α) (x : α) (xs : List α) (n : ℕ)

@[simp]
theorem inth_nil : inth ([] : List α) n = default :=
  rfl
#align list.inth_nil List.inth_nil

@[simp]
theorem inth_cons_zero : inth (x :: xs) 0 = x :=
  rfl
#align list.inth_cons_zero List.inth_cons_zero

@[simp]
theorem inth_cons_succ : inth (x :: xs) (n + 1) = inth xs n :=
  rfl
#align list.inth_cons_succ List.inth_cons_succ

theorem inth_eq_nth_le {n : ℕ} (hn : n < l.length) : l.inth n = l.nthLe n hn :=
  nthd_eq_nth_le _ _ _
#align list.inth_eq_nth_le List.inth_eq_nth_le

theorem inth_eq_default {n : ℕ} (hn : l.length ≤ n) : l.inth n = default :=
  nthd_eq_default _ _ hn
#align list.inth_eq_default List.inth_eq_default

theorem nthd_default_eq_inth : l.nthd default = l.inth :=
  rfl
#align list.nthd_default_eq_inth List.nthd_default_eq_inth

theorem inth_append (l l' : List α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').inth n = l.inth n :=
  nthd_append _ _ _ _ h h'
#align list.inth_append List.inth_append

theorem inth_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').inth n = l'.inth (n - l.length) :=
  nthd_append_right _ _ _ _ h
#align list.inth_append_right List.inth_append_right

theorem inth_eq_iget_nth (n : ℕ) : l.inth n = (l.nth n).iget := by
  rw [← nthd_default_eq_inth, nthd_eq_get_or_else_nth, Option.getD_default_eq_iget]
#align list.inth_eq_iget_nth List.inth_eq_iget_nth

theorem inth_zero_eq_head : l.inth 0 = l.head := by cases l <;> rfl
#align list.inth_zero_eq_head List.inth_zero_eq_head

end Inth

end List

-- import Mathlib.Logic.Basic
-- import Mathlib.Logic.Function.Basic
-- import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Option.Basic
-- import Mathlib.Data.Subtype
-- import Std.Tactic.Simpa
-- import Std.Data.List.Lemmas
-- import Lean

-- open Function

-- namespace List

-- /-!
-- # Basic properties of Lists
-- -/


-- /-! ### set-theoretic notation of Lists -/

-- /-! ### bounded quantifiers over Lists -/

-- alias exists_mem_cons ↔ or_exists_of_exists_mem_cons _

-- theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) :
--   ∃ x ∈ a :: l, p x :=
-- exists_mem_cons.2 (.inl h)
-- exists_mem_cons.2 (.inr h)

-- /-! ### List subset -/

-- -- theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : injective f) :
-- --   map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ :=
-- -- begin
-- --   refine ⟨_, map_subset f⟩, intros h2 x hx,
-- --   rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩,
-- --   cases h hxx', exact hx'
-- -- end

-- /-! ### append -/

-- -- theorem append_eq_append_iff {a b c d : List α} :
-- --   a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b := by
-- --   induction a generalizing c with
-- --   | nil =>
-- --     rw [nil_append]; constructor
-- --     · rintro rfl; left; exact ⟨_, rfl, rfl⟩
-- --     · rintro (⟨a', rfl, rfl⟩ | ⟨a', H, rfl⟩); {rfl}; rw [←append_assoc, ←H]; rfl
-- --   | cons a as ih =>
-- --     cases c
-- --     · simp only [cons_append, nil_append, false_and, exists_false, false_or, exists_eq_left']
-- --       exact eq_comm
-- --     · simp only [cons_append, @eq_comm _ a, ih, and_assoc, and_or_distrib_left,
-- --         exists_and_distrib_left]

-- -- @[simp] theorem split_at_eq_take_drop :
-- --   ∀ (n : ℕ) (l : List α), split_at n l = (take n l, drop n l)
-- -- | 0, a => rfl
-- -- | n+1, [] => rfl
-- -- | n+1, x :: xs => by simp only [split_at, split_at_eq_take_drop n xs, take, drop]




-- /-! ### nth element -/

-- theorem get?_injective {α : Type u} {xs : List α} {i j : ℕ}
--   (h₀ : i < xs.length)
--   (h₁ : Nodup xs)
--   (h₂ : xs.get? i = xs.get? j) : i = j := by
--   induction xs generalizing i j with
--   | nil => cases h₀
--   | cons x xs ih =>
--     match i, j with
--     | 0, 0 => rfl
--     | i+1, j+1 => simp; cases h₁ with
--       | cons ha h₁ => exact ih (Nat.lt_of_sugitc_lt_succ h₀) h₁ h₂
--     | i+1, 0 => ?_ | 0, j+1 => ?_
--     all_goals
--       simp at h₂
--       cases h₁; rename_i h' h
--       have := h x ?_ rfl; cases this
--       rw [mem_iff_get?]
--     exact ⟨_, h₂⟩; exact ⟨_ , h₂.symm⟩

-- /--
-- List.prod satisfies a specification of cartesian product on lists.
-- -/
-- theorem product_spec (xs : List α) (ys : List β) (x : α) (y : β) :
--   (x, y) ∈ product xs ys ↔ x ∈ xs ∧ y ∈ ys := by
--   constructor
--   · simp only [List.product, and_imp, exists_prop, List.mem_map, Prod.mk.injEq,
--       exists_eq_right_right', List.mem_bind]
--     exact And.intro
--   · simp only [product, mem_bind, mem_map, Prod.mk.injEq, exists_eq_right_right', exists_prop]
--     exact id

-- /-- Partial map. If `f : Π a, p a → β` is a partial function defined on
--   `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
--   but is defined only when all members of `l` satisfy `p`, using the proof
--   to apply `f`. -/
-- @[simp]
-- def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
--   | [], _ => []
--   | a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap f l (forall_mem_cons.1 H).2

-- /-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
--   with the same elements but in the type `{x // x ∈ l}`. -/
-- def attach (l : List α) : List { x // x ∈ l } :=
--   pmap Subtype.mk l (fun _ ↦ id)

-- @[simp]
-- theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
--     @pmap _ _ p (fun a _ ↦ f a) l H = map f l := by
--   induction l with
--   | nil => rfl
--   | cons => simp only [*, pmap, map]

-- theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
--     (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
--   induction l with
--   | nil => rfl
--   | cons a l ih =>
--     rw [pmap, pmap, h _ (mem_cons_self _ _), ih (fun a ha ↦ h a (mem_cons_of_mem _ ha))]

-- theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
--     map g (pmap f l H) = pmap (fun a h ↦ g (f a h)) l H := by
--   induction l with
--   | nil => rfl
--   | cons => simp only [*, pmap, map]

-- theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
--     pmap g (map f l) H = pmap (fun a h ↦ g (f a) h) l fun a h ↦ H _ (mem_map_of_mem _ h) := by
--   induction l with
--   | nil => rfl
--   | cons => simp only [*, pmap, map]

-- theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
--     pmap f l H = l.attach.map fun x ↦ f x.1 (H _ x.2) := by
--   rw [attach, map_pmap]; exact pmap_congr l fun _ _ _ _ ↦ rfl

-- theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l := by
--   rw [attach, map_pmap]; exact (pmap_eq_map ..).trans (map_id l)

-- @[simp]
-- theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
--   | ⟨a, h⟩ => by
--     have := mem_map.1 (by rw [attach_map_val] <;> exact h)
--     rcases this with ⟨⟨_, _⟩, m, rfl⟩
--     exact m

-- @[simp]
-- theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
--     b ∈ pmap f l H ↔ ∃ (a : _)(h : a ∈ l), f a (H a h) = b := by
--   simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists, eq_comm]
--   rfl
