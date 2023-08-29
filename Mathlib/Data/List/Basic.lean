/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Init.Data.List.Instances
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.List.Defs
import Mathlib.Init.Core
import Std.Data.List.Lemmas

#align_import data.list.basic from "leanprover-community/mathlib"@"9da1b3534b65d9661eb8f42443598a92bbb49211"

/-!
# Basic properties of lists
-/

open Function

open Nat hiding one_pos

assert_not_exists Set.range

namespace List

universe u v w x

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {l₁ l₂ : List α}

-- Porting note: Delete this attribute
-- attribute [inline] List.head!

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

#align list.cons_ne_nil List.cons_ne_nil
#align list.cons_ne_self List.cons_ne_self

#align list.head_eq_of_cons_eq List.head_eq_of_cons_eqₓ -- implicits order
#align list.tail_eq_of_cons_eq List.tail_eq_of_cons_eqₓ -- implicits order

@[simp] theorem cons_injective {a : α} : Injective (cons a) := fun _ _ => tail_eq_of_cons_eq
#align list.cons_injective List.cons_injective

#align list.cons_inj List.cons_inj

theorem cons_eq_cons {a b : α} {l l' : List α} : a :: l = b :: l' ↔ a = b ∧ l = l' :=
  ⟨List.cons.inj, fun h => h.1 ▸ h.2 ▸ rfl⟩
#align list.cons_eq_cons List.cons_eq_cons

theorem singleton_injective : Injective fun a : α => [a] := fun _ _ h => (cons_eq_cons.1 h).1
#align list.singleton_injective List.singleton_injective

theorem singleton_inj {a b : α} : [a] = [b] ↔ a = b :=
  singleton_injective.eq_iff
#align list.singleton_inj List.singleton_inj

#align list.exists_cons_of_ne_nil List.exists_cons_of_ne_nil

theorem set_of_mem_cons (l : List α) (a : α) : { x | x ∈ a :: l } = insert a { x | x ∈ l } :=
  Set.ext fun _ => mem_cons
#align list.set_of_mem_cons List.set_of_mem_cons

/-! ### mem -/

#align list.mem_singleton_self List.mem_singleton_self
#align list.eq_of_mem_singleton List.eq_of_mem_singleton
#align list.mem_singleton List.mem_singleton
#align list.mem_of_mem_cons_of_mem List.mem_of_mem_cons_of_mem

theorem _root_.Decidable.List.eq_or_ne_mem_of_mem [DecidableEq α]
    {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ a ≠ b ∧ a ∈ l := by
  by_cases hab : a = b
  -- ⊢ a = b ∨ a ≠ b ∧ a ∈ l
  · exact Or.inl hab
    -- 🎉 no goals
  · exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))
    -- 🎉 no goals
#align decidable.list.eq_or_ne_mem_of_mem Decidable.List.eq_or_ne_mem_of_mem

#align list.eq_or_ne_mem_of_mem List.eq_or_ne_mem_of_mem

#align list.not_mem_append List.not_mem_append

#align list.ne_nil_of_mem List.ne_nil_of_mem

theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t := by
  induction' l with b l ih; {cases h}; rcases h with (_ | ⟨_, h⟩)
  -- ⊢ ∃ s t, [] = s ++ a :: t
                            -- ⊢ ∃ s t, b :: l = s ++ a :: t
                                       -- ⊢ ∃ s t, a :: l = s ++ a :: t
  · exact ⟨[], l, rfl⟩
    -- 🎉 no goals
  · rcases ih h with ⟨s, t, rfl⟩
    -- ⊢ ∃ s_1 t_1, b :: (s ++ a :: t) = s_1 ++ a :: t_1
    exact ⟨b :: s, t, rfl⟩
    -- 🎉 no goals
#align list.mem_split List.mem_split

#align list.mem_of_ne_of_mem List.mem_of_ne_of_mem

#align list.ne_of_not_mem_cons List.ne_of_not_mem_cons

#align list.not_mem_of_not_mem_cons List.not_mem_of_not_mem_cons

#align list.not_mem_cons_of_ne_of_not_mem List.not_mem_cons_of_ne_of_not_mem

#align list.ne_and_not_mem_of_not_mem_cons List.ne_and_not_mem_of_not_mem_cons

#align list.mem_map List.mem_map

#align list.exists_of_mem_map List.exists_of_mem_map

#align list.mem_map_of_mem List.mem_map_of_memₓ -- implicits order

-- The simpNF linter says that the LHS can be simplified via `List.mem_map`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
    f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem _⟩
#align list.mem_map_of_injective List.mem_map_of_injective

@[simp]
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff {f : α → α}
    (hf : Function.Involutive f) (x : α) (l : List α) : (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩
      -- ⊢ f (f y) ∈ l
                          -- 🎉 no goals
#align function.involutive.exists_mem_and_apply_eq_iff Function.Involutive.exists_mem_and_apply_eq_iff

theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
    a ∈ map f l ↔ f a ∈ l := by rw [mem_map, hf.exists_mem_and_apply_eq_iff]
                                -- 🎉 no goals
#align list.mem_map_of_involutive List.mem_map_of_involutive

#align list.forall_mem_map_iff List.forall_mem_map_iffₓ -- universe order

#align list.map_eq_nil List.map_eq_nilₓ -- universe order

attribute [simp] List.mem_join
#align list.mem_join List.mem_join

#align list.exists_of_mem_join List.exists_of_mem_join

#align list.mem_join_of_mem List.mem_join_of_memₓ -- implicits order

attribute [simp] List.mem_bind
#align list.mem_bind List.mem_bindₓ -- implicits order

-- Porting note: bExists in Lean3, And in Lean4
#align list.exists_of_mem_bind List.exists_of_mem_bindₓ -- implicits order

#align list.mem_bind_of_mem List.mem_bind_of_memₓ -- implicits order

#align list.bind_map List.bind_mapₓ -- implicits order

theorem map_bind (g : β → List γ) (f : α → β) :
    ∀ l : List α, (List.map f l).bind g = l.bind fun a => g (f a)
  | [] => rfl
  | a :: l => by simp only [cons_bind, map_cons, map_bind _ _ l]
                 -- 🎉 no goals
#align list.map_bind List.map_bind

/-! ### length -/

#align list.length_eq_zero List.length_eq_zero

#align list.length_singleton List.length_singleton

#align list.length_pos_of_mem List.length_pos_of_mem

#align list.exists_mem_of_length_pos List.exists_mem_of_length_pos

#align list.length_pos_iff_exists_mem List.length_pos_iff_exists_mem

alias ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩ := length_pos
#align list.ne_nil_of_length_pos List.ne_nil_of_length_pos
#align list.length_pos_of_ne_nil List.length_pos_of_ne_nil

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩
#align list.length_pos_iff_ne_nil List.length_pos_iff_ne_nil

#align list.exists_mem_of_ne_nil List.exists_mem_of_ne_nil

#align list.length_eq_one List.length_eq_one

theorem exists_of_length_succ {n} : ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
  | [], H => absurd H.symm <| succ_ne_zero n
  | h :: t, _ => ⟨h, t, rfl⟩
#align list.exists_of_length_succ List.exists_of_length_succ

@[simp] lemma length_injective_iff : Injective (List.length : List α → ℕ) ↔ Subsingleton α := by
  constructor
  -- ⊢ Injective length → Subsingleton α
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
    -- ⊢ Subsingleton α
             -- ⊢ x = y
                                      -- ⊢ [x] = [y]
                                                                               -- ⊢ length [x] = length [y]
                                                                                        -- 🎉 no goals
  · intros hα l1 l2 hl
    -- ⊢ l1 = l2
    induction l1 generalizing l2 <;> cases l2
    -- ⊢ [] = l2
                                     -- ⊢ [] = []
                                     -- ⊢ head✝ :: tail✝ = []
    · rfl
      -- 🎉 no goals
    · cases hl
      -- 🎉 no goals
    · cases hl
      -- 🎉 no goals
    · next ih _ _ =>
      congr
      · exact Subsingleton.elim _ _
      · apply ih; simpa using hl
#align list.length_injective_iff List.length_injective_iff

@[simp default+1] -- Porting note: this used to be just @[simp]
lemma length_injective [Subsingleton α] : Injective (length : List α → ℕ) :=
  length_injective_iff.mpr inferInstance
#align list.length_injective List.length_injective

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩
#align list.length_eq_two List.length_eq_two

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩
#align list.length_eq_three List.length_eq_three

#align list.sublist.length_le List.Sublist.length_le

/-! ### set-theoretic notation of lists -/

-- ADHOC Porting note: instance from Lean3 core
instance instSingletonList : Singleton α (List α) := ⟨fun x => [x]⟩
#align list.has_singleton List.instSingletonList

-- ADHOC Porting note: instance from Lean3 core
instance [DecidableEq α] : Insert α (List α) := ⟨List.insert⟩

-- ADHOC Porting note: instance from Lean3 core
instance [DecidableEq α]: IsLawfulSingleton α (List α) :=
  { insert_emptyc_eq := fun x =>
      show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg (not_mem_nil _) }

#align list.empty_eq List.empty_eq

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
  -- ⊢ ¬x ∈ {y}
  rwa [singleton_eq, mem_singleton]
  -- 🎉 no goals
#align list.doubleton_eq List.doubleton_eq

/-! ### bounded quantifiers over lists -/

#align list.forall_mem_nil List.forall_mem_nil

#align list.forall_mem_cons List.forall_mem_cons

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∀ x ∈ a :: l, p x) :
    ∀ x ∈ l, p x := (forall_mem_cons.1 h).2
#align list.forall_mem_of_forall_mem_cons List.forall_mem_of_forall_mem_cons

#align list.forall_mem_singleton List.forall_mem_singleton

#align list.forall_mem_append List.forall_mem_append

theorem not_exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x :=
  fun.
#align list.not_exists_mem_nil List.not_exists_mem_nilₓ -- bExists change

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ x ∈ a :: l, p x :=
  ⟨a, mem_cons_self _ _, h⟩
#align list.exists_mem_cons_of List.exists_mem_cons_ofₓ -- bExists change

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ l, p x) →
    ∃ x ∈ a :: l, p x :=
  fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩
#align list.exists_mem_cons_of_exists List.exists_mem_cons_of_existsₓ -- bExists change

-- Porting note: bExists in Lean3 and And in Lean4
theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ a :: l, p x) →
    p a ∨ ∃ x ∈ l, p x :=
  fun ⟨x, xal, px⟩ =>
    Or.elim (eq_or_mem_of_mem_cons xal) (fun h : x = a => by rw [← h]; left; exact px)
                                                             -- ⊢ p x ∨ ∃ x, x ∈ l ∧ p x
                                                                       -- ⊢ p x
                                                                             -- 🎉 no goals
      fun h : x ∈ l => Or.inr ⟨x, h, px⟩
#align list.or_exists_of_exists_mem_cons List.or_exists_of_exists_mem_consₓ -- bExists change

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  Iff.intro or_exists_of_exists_mem_cons fun h =>
    Or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists
#align list.exists_mem_cons_iff List.exists_mem_cons_iff

/-! ### list subset -/

instance : IsTrans (List α) Subset where
  trans := fun _ _ _ => List.Subset.trans

#align list.subset_def List.subset_def

#align list.subset_append_of_subset_left List.subset_append_of_subset_left

@[deprecated subset_append_of_subset_right]
theorem subset_append_of_subset_right' (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ :=
  subset_append_of_subset_right _
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

-- Porting note: in Std
#align list.append_subset_iff List.append_subset

alias ⟨eq_nil_of_subset_nil, _⟩ := subset_nil
#align list.eq_nil_of_subset_nil List.eq_nil_of_subset_nil

#align list.eq_nil_iff_forall_not_mem List.eq_nil_iff_forall_not_mem

#align list.map_subset List.map_subset

theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := by
  refine' ⟨_, map_subset f⟩; intro h2 x hx
  -- ⊢ map f l₁ ⊆ map f l₂ → l₁ ⊆ l₂
                             -- ⊢ x ∈ l₂
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩
  -- ⊢ x ∈ l₂
  cases h hxx'; exact hx'
  -- ⊢ x ∈ l₂
                -- 🎉 no goals
#align list.map_subset_iff List.map_subset_iff

/-! ### append -/

theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl
#align list.append_eq_has_append List.append_eq_has_append

#align list.singleton_append List.singleton_append

#align list.append_ne_nil_of_ne_nil_left List.append_ne_nil_of_ne_nil_left

#align list.append_ne_nil_of_ne_nil_right List.append_ne_nil_of_ne_nil_right

#align list.append_eq_nil List.append_eq_nil

-- Porting note: in Std
#align list.nil_eq_append_iff List.nil_eq_append

theorem append_eq_cons_iff {a b c : List α} {x : α} :
    a ++ b = x :: c ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  cases a <;>
  -- ⊢ [] ++ b = x :: c ↔ [] = [] ∧ b = x :: c ∨ ∃ a', [] = x :: a' ∧ c = a' ++ b
    simp only [and_assoc, @eq_comm _ c, nil_append, cons_append, cons.injEq, true_and_iff,
      false_and_iff, exists_false, false_or_iff, or_false_iff, exists_and_left, exists_eq_left']
#align list.append_eq_cons_iff List.append_eq_cons_iff

theorem cons_eq_append_iff {a b c : List α} {x : α} :
    (x :: c : List α) = a ++ b ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  rw [eq_comm, append_eq_cons_iff]
  -- 🎉 no goals
#align list.cons_eq_append_iff List.cons_eq_append_iff

#align list.append_eq_append_iff List.append_eq_append_iff

#align list.take_append_drop List.take_append_drop

#align list.append_inj List.append_inj

#align list.append_inj_right List.append_inj_rightₓ -- implicits order

#align list.append_inj_left List.append_inj_leftₓ -- implicits order

#align list.append_inj' List.append_inj'ₓ -- implicits order

#align list.append_inj_right' List.append_inj_right'ₓ -- implicits order

#align list.append_inj_left' List.append_inj_left'ₓ -- implicits order

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

/-! ### replicate -/

@[simp] lemma replicate_zero (a : α) : replicate 0 a = [] := rfl
#align list.replicate_zero List.replicate_zero

attribute [simp] replicate_succ
#align list.replicate_succ List.replicate_succ

lemma replicate_one (a : α) : replicate 1 a = [a] := rfl
#align list.replicate_one List.replicate_one

#align list.length_replicate List.length_replicate
#align list.mem_replicate List.mem_replicate
#align list.eq_of_mem_replicate List.eq_of_mem_replicate

theorem eq_replicate_length {a : α} : ∀ {l : List α}, l = replicate l.length a ↔ ∀ b ∈ l, b = a
  | [] => by simp
             -- 🎉 no goals
  | (b :: l) => by simp [eq_replicate_length]
                   -- 🎉 no goals
#align list.eq_replicate_length List.eq_replicate_length

#align list.eq_replicate_of_mem List.eq_replicate_of_mem

#align list.eq_replicate List.eq_replicate

theorem replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ replicate n a := by
  induction m <;> simp [*, zero_add, succ_add, replicate]
  -- ⊢ replicate (zero + n) a = replicate zero a ++ replicate n a
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.replicate_add List.replicate_add

theorem replicate_succ' (n) (a : α) : replicate (n + 1) a = replicate n a ++ [a] :=
  replicate_add n 1 a
#align list.replicate_succ' List.replicate_succ'

theorem replicate_subset_singleton (n) (a : α) : replicate n a ⊆ [a] := fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)
#align list.replicate_subset_singleton List.replicate_subset_singleton

theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a := by
  simp only [eq_replicate, subset_def, mem_singleton, exists_eq_left']
  -- 🎉 no goals
#align list.subset_singleton_iff List.subset_singleton_iff

@[simp] theorem map_replicate (f : α → β) (n) (a : α) :
    map f (replicate n a) = replicate n (f a) := by
  induction n <;> [rfl; simp only [*, replicate, map]]
  -- 🎉 no goals
#align list.map_replicate List.map_replicate

@[simp] theorem tail_replicate (a : α) (n) :
    tail (replicate n a) = replicate (n - 1) a := by cases n <;> rfl
                                                     -- ⊢ tail (replicate zero a) = replicate (zero - 1) a
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
#align list.tail_replicate List.tail_replicate

@[simp] theorem join_replicate_nil (n : ℕ) : join (replicate n []) = @nil α := by
  induction n <;> [rfl; simp only [*, replicate, join, append_nil]]
  -- 🎉 no goals
#align list.join_replicate_nil List.join_replicate_nil

theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (@replicate α n) :=
  fun _ _ h => (eq_replicate.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩
#align list.replicate_right_injective List.replicate_right_injective

theorem replicate_right_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective hn).eq_iff
#align list.replicate_right_inj List.replicate_right_inj

@[simp] theorem replicate_right_inj' {a b : α} : ∀ {n},
    replicate n a = replicate n b ↔ n = 0 ∨ a = b
  | 0 => by simp
            -- 🎉 no goals
  | n + 1 => (replicate_right_inj n.succ_ne_zero).trans <| by simp only [n.succ_ne_zero, false_or]
                                                              -- 🎉 no goals
#align list.replicate_right_inj' List.replicate_right_inj'

theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (length_replicate · a)
#align list.replicate_left_injective List.replicate_left_injective

@[simp] theorem replicate_left_inj {a : α} {n m : ℕ} : replicate n a = replicate m a ↔ n = m :=
  (replicate_left_injective a).eq_iff
#align list.replicate_left_inj List.replicate_left_inj

/-! ### pure -/

@[simp]
theorem mem_pure {α} (x y : α) : x ∈ (pure y : List α) ↔ x = y :=
  show x ∈ [y] ↔ x = y by simp
                          -- 🎉 no goals
#align list.mem_pure List.mem_pure

/-! ### bind -/

@[simp]
theorem bind_eq_bind {α β} (f : α → List β) (l : List α) : l >>= f = l.bind f :=
  rfl
#align list.bind_eq_bind List.bind_eq_bind

#align list.bind_append List.append_bind

/-! ### concat -/

theorem concat_nil (a : α) : concat [] a = [a] :=
  rfl
#align list.concat_nil List.concat_nil

theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl
#align list.concat_cons List.concat_cons

@[deprecated concat_eq_append]
theorem concat_eq_append' (a : α) (l : List α) : concat l a = l ++ [a] :=
  concat_eq_append l a
#align list.concat_eq_append List.concat_eq_append'

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ := by
  intro h
  -- ⊢ l₁ = l₂
  rw [concat_eq_append, concat_eq_append] at h
  -- ⊢ l₁ = l₂
  exact append_right_cancel h
  -- 🎉 no goals
#align list.init_eq_of_concat_eq List.init_eq_of_concat_eq

theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b := by
  intro h
  -- ⊢ a = b
  rw [concat_eq_append, concat_eq_append] at h
  -- ⊢ a = b
  exact head_eq_of_cons_eq (append_left_cancel h)
  -- 🎉 no goals
#align list.last_eq_of_concat_eq List.last_eq_of_concat_eq

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by simp
                                                                   -- 🎉 no goals
#align list.concat_ne_nil List.concat_ne_nil

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by simp
                                                                                         -- 🎉 no goals
#align list.concat_append List.concat_append

@[deprecated length_concat]
theorem length_concat' (a : α) (l : List α) : length (concat l a) = succ (length l) := by
  simp only [concat_eq_append, length_append, length]
  -- 🎉 no goals
#align list.length_concat List.length_concat'

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by simp
                                                                                               -- 🎉 no goals
#align list.append_concat List.append_concat

/-! ### reverse -/

#align list.reverse_nil List.reverse_nil

#align list.reverse_core List.reverseAux

-- Porting note: Do we need this?
attribute [local simp] reverseAux

#align list.reverse_cons List.reverse_cons

#align list.reverse_core_eq List.reverseAux_eq

theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]
  -- 🎉 no goals
#align list.reverse_cons' List.reverse_cons'

-- Porting note: simp can prove this
-- @[simp]
theorem reverse_singleton (a : α) : reverse [a] = [a] :=
  rfl
#align list.reverse_singleton List.reverse_singleton

#align list.reverse_append List.reverse_append
#align list.reverse_concat List.reverse_concat
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
  -- 🎉 no goals
#align list.concat_eq_reverse_cons List.concat_eq_reverse_cons

#align list.length_reverse List.length_reverse

-- Porting note: This one was @[simp] in mathlib 3,
-- but Std contains a competing simp lemma reverse_map.
-- For now we remove @[simp] to avoid simplification loops.
-- TODO: Change Std lemma to match mathlib 3?
theorem map_reverse (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) :=
  (reverse_map f l).symm
#align list.map_reverse List.map_reverse

theorem map_reverseAux (f : α → β) (l₁ l₂ : List α) :
    map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverseAux_eq, map_append, map_reverse]
  -- 🎉 no goals
#align list.map_reverse_core List.map_reverseAux

#align list.mem_reverse List.mem_reverse

@[simp] theorem reverse_replicate (n) (a : α) : reverse (replicate n a) = replicate n a :=
  eq_replicate.2
    ⟨by rw [length_reverse, length_replicate],
        -- 🎉 no goals
     fun b h => eq_of_mem_replicate (mem_reverse.1 h)⟩
#align list.reverse_replicate List.reverse_replicate

/-! ### empty -/

-- Porting note: this does not work as desired
-- attribute [simp] List.isEmpty

theorem isEmpty_iff_eq_nil {l : List α} : l.isEmpty ↔ l = [] := by cases l <;> simp [isEmpty]
                                                                   -- ⊢ isEmpty [] = true ↔ [] = []
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
#align list.empty_iff_eq_nil List.isEmpty_iff_eq_nil

/-! ### dropLast -/

@[simp]
theorem length_dropLast : ∀ l : List α, length l.dropLast = length l - 1
  | [] | [_] => rfl
  | a::b::l => by
    rw [dropLast, length_cons, length_cons, length_dropLast (b::l), succ_sub_one, length_cons,
      succ_sub_one]
    simp
    -- 🎉 no goals
#align list.length_init List.length_dropLast

-- Porting note: `rw [dropLast]` in Lean4 generates a goal `(b::l) ≠ []`
-- so we use this lemma instead
theorem dropLast_cons_cons (a b : α) (l : List α) : dropLast (a::b::l) = a::dropLast (b::l) := rfl

/-! ### getLast -/

@[simp]
theorem getLast_cons {a : α} {l : List α} :
    ∀ h : l ≠ nil, getLast (a :: l) (cons_ne_nil a l) = getLast l h := by
  induction l <;> intros
  -- ⊢ ∀ (h : [] ≠ []), getLast [a] (_ : [a] ≠ []) = getLast [] h
                  -- ⊢ getLast [a] (_ : [a] ≠ []) = getLast [] h✝
                  -- ⊢ getLast (a :: head✝ :: tail✝) (_ : a :: head✝ :: tail✝ ≠ []) = getLast (head …
  contradiction
  -- ⊢ getLast (a :: head✝ :: tail✝) (_ : a :: head✝ :: tail✝ ≠ []) = getLast (head …
  rfl
  -- 🎉 no goals
#align list.last_cons List.getLast_cons

theorem getLast_append_singleton {a : α} (l : List α) :
    getLast (l ++ [a]) (append_ne_nil_of_ne_nil_right l _ (cons_ne_nil a _)) = a := by
  simp only [getLast_append]
  -- 🎉 no goals
#align list.last_append_singleton List.getLast_append_singleton

-- Porting note: name should be fixed upstream
theorem getLast_append' (l₁ l₂ : List α) (h : l₂ ≠ []) :
    getLast (l₁ ++ l₂) (append_ne_nil_of_ne_nil_right l₁ l₂ h) = getLast l₂ h := by
  induction' l₁ with _ _ ih
  -- ⊢ getLast ([] ++ l₂) (_ : [] ++ l₂ ≠ []) = getLast l₂ h
  · simp
    -- 🎉 no goals
  · simp only [cons_append]
    -- ⊢ getLast (head✝ :: (tail✝ ++ l₂)) (_ : head✝ :: (tail✝ ++ l₂) ≠ []) = getLast …
    rw [List.getLast_cons]
    -- ⊢ getLast (tail✝ ++ l₂) ?cons = getLast l₂ h
    exact ih
    -- 🎉 no goals
#align list.last_append List.getLast_append'

theorem getLast_concat' {a : α} (l : List α) : getLast (concat l a) (concat_ne_nil a l) = a :=
  getLast_concat ..
#align list.last_concat List.getLast_concat'

@[simp]
theorem getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a := rfl
#align list.last_singleton List.getLast_singleton'

-- Porting note: simp can prove this
-- @[simp]
theorem getLast_cons_cons (a₁ a₂ : α) (l : List α) :
    getLast (a₁ :: a₂ :: l) (cons_ne_nil _ _) = getLast (a₂ :: l) (cons_ne_nil a₂ l) :=
  rfl
#align list.last_cons_cons List.getLast_cons_cons

theorem dropLast_append_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [a], h => rfl
  | a :: b :: l, h => by
    rw [dropLast_cons_cons, cons_append, getLast_cons (cons_ne_nil _ _)]
    -- ⊢ a :: (dropLast (b :: l) ++ [getLast (b :: l) (_ : b :: l ≠ [])]) = a :: b :: l
    congr
    -- ⊢ dropLast (b :: l) ++ [getLast (b :: l) (_ : b :: l ≠ [])] = b :: l
    exact dropLast_append_getLast (cons_ne_nil b l)
    -- 🎉 no goals
#align list.init_append_last List.dropLast_append_getLast

theorem getLast_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
    getLast l₁ h₁ = getLast l₂ h₂ := by subst l₁; rfl
                                        -- ⊢ getLast l₂ h₁ = getLast l₂ h₂
                                                  -- 🎉 no goals
#align list.last_congr List.getLast_congr

theorem getLast_mem : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ l
  | [], h => absurd rfl h
  | [a], _ => by simp only [getLast, mem_singleton]
                 -- 🎉 no goals
  | a :: b :: l, h =>
    List.mem_cons.2 <| Or.inr <| by
        rw [getLast_cons_cons]
        -- ⊢ getLast (b :: l) (_ : b :: l ≠ []) ∈ b :: l
        exact getLast_mem (cons_ne_nil b l)
        -- 🎉 no goals
#align list.last_mem List.getLast_mem

theorem getLast_replicate_succ (m : ℕ) (a : α) :
    (replicate (m + 1) a).getLast (ne_nil_of_length_eq_succ (length_replicate _ _)) = a := by
  simp only [replicate_succ']
  -- ⊢ getLast (replicate m a ++ [a]) (_ : replicate m a ++ [a] ≠ []) = a
  exact getLast_append_singleton _
  -- 🎉 no goals
#align list.last_replicate_succ List.getLast_replicate_succ

/-! ### getLast? -/

-- Porting note: New lemma, since definition of getLast? is slightly different.
@[simp]
theorem getLast?_singleton (a : α) :
    getLast? [a] = a := rfl

-- Porting note: Moved earlier in file, for use in subsequent lemmas.
@[simp]
theorem getLast?_cons_cons (a b : α) (l : List α) :
    getLast? (a :: b :: l) = getLast? (b :: l) := rfl

@[simp]
theorem getLast?_isNone : ∀ {l : List α}, (getLast? l).isNone ↔ l = []
  | [] => by simp
             -- 🎉 no goals
  | [a] => by simp
              -- 🎉 no goals
  | a :: b :: l => by simp [@getLast?_isNone (b :: l)]
                      -- 🎉 no goals
#align list.last'_is_none List.getLast?_isNone

@[simp]
theorem getLast?_isSome : ∀ {l : List α}, l.getLast?.isSome ↔ l ≠ []
  | [] => by simp
             -- 🎉 no goals
  | [a] => by simp
              -- 🎉 no goals
  | a :: b :: l => by simp [@getLast?_isSome (b :: l)]
                      -- 🎉 no goals
#align list.last'_is_some List.getLast?_isSome

theorem mem_getLast?_eq_getLast : ∀ {l : List α} {x : α}, x ∈ l.getLast? → ∃ h, x = getLast l h
  | [], x, hx => False.elim <| by simp at hx
                                  -- 🎉 no goals
  | [a], x, hx =>
    have : a = x := by simpa using hx
                       -- 🎉 no goals
    this ▸ ⟨cons_ne_nil a [], rfl⟩
  | a :: b :: l, x, hx => by
    rw [getLast?_cons_cons] at hx
    -- ⊢ ∃ h, x = getLast (a :: b :: l) h
    rcases mem_getLast?_eq_getLast hx with ⟨_, h₂⟩
    -- ⊢ ∃ h, x = getLast (a :: b :: l) h
    use cons_ne_nil _ _
    -- ⊢ x = getLast (a :: b :: l) (_ : a :: b :: l ≠ [])
    assumption
    -- 🎉 no goals
#align list.mem_last'_eq_last List.mem_getLast?_eq_getLast

theorem getLast?_eq_getLast_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.getLast? = some (l.getLast h)
  | [], h => (h rfl).elim
  | [_], _ => rfl
  | _ :: b :: l, _ => @getLast?_eq_getLast_of_ne_nil (b :: l) (cons_ne_nil _ _)
#align list.last'_eq_last_of_ne_nil List.getLast?_eq_getLast_of_ne_nil

theorem mem_getLast?_cons {x y : α} : ∀ {l : List α}, x ∈ l.getLast? → x ∈ (y :: l).getLast?
  | [], _ => by contradiction
                -- 🎉 no goals
  | _ :: _, h => h
#align list.mem_last'_cons List.mem_getLast?_cons

theorem mem_of_mem_getLast? {l : List α} {a : α} (ha : a ∈ l.getLast?) : a ∈ l :=
  let ⟨_, h₂⟩ := mem_getLast?_eq_getLast ha
  h₂.symm ▸ getLast_mem _
#align list.mem_of_mem_last' List.mem_of_mem_getLast?

theorem dropLast_append_getLast? : ∀ {l : List α}, ∀ a ∈ l.getLast?, dropLast l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [getLast?_cons_cons] at hc
    -- ⊢ dropLast (a :: b :: l) ++ [c] = a :: b :: l
    rw [dropLast_cons_cons, cons_append, dropLast_append_getLast? _ hc]
    -- 🎉 no goals
#align list.init_append_last' List.dropLast_append_getLast?

theorem getLastI_eq_getLast? [Inhabited α] : ∀ l : List α, l.getLastI = l.getLast?.iget
  | [] => by simp [getLastI, Inhabited.default]
             -- 🎉 no goals
  | [a] => rfl
  | [a, b] => rfl
  | [a, b, c] => rfl
  | _ :: _ :: c :: l => by simp [getLastI, getLastI_eq_getLast? (c :: l)]
                           -- 🎉 no goals
#align list.ilast_eq_last' List.getLastI_eq_getLast?

@[simp]
theorem getLast?_append_cons :
    ∀ (l₁ : List α) (a : α) (l₂ : List α), getLast? (l₁ ++ a :: l₂) = getLast? (a :: l₂)
  | [], a, l₂ => rfl
  | [b], a, l₂ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, getLast?_cons_cons,
    ← cons_append, getLast?_append_cons (c :: l₁)]
#align list.last'_append_cons List.getLast?_append_cons

#align list.last'_cons_cons List.getLast?_cons_cons

theorem getLast?_append_of_ne_nil (l₁ : List α) :
    ∀ {l₂ : List α} (_ : l₂ ≠ []), getLast? (l₁ ++ l₂) = getLast? l₂
  | [], hl₂ => by contradiction
                  -- 🎉 no goals
  | b :: l₂, _ => getLast?_append_cons l₁ b l₂
#align list.last'_append_of_ne_nil List.getLast?_append_of_ne_nil

theorem getLast?_append {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.getLast?) :
    x ∈ (l₁ ++ l₂).getLast? := by
  cases l₂
  -- ⊢ x ∈ getLast? (l₁ ++ [])
  · contradiction
    -- 🎉 no goals
  · rw [List.getLast?_append_cons]
    -- ⊢ x ∈ getLast? (head✝ :: tail✝)
    exact h
    -- 🎉 no goals
#align list.last'_append List.getLast?_append

/-! ### head(!?) and tail -/

theorem head!_eq_head? [Inhabited α] (l : List α) : head! l = (head? l).iget := by cases l <;> rfl
                                                                                   -- ⊢ head! [] = Option.iget (head? [])
                                                                                               -- 🎉 no goals
                                                                                               -- 🎉 no goals
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

theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: tail l
  | [], h => (Option.not_mem_none _ h).elim
  | a :: l, h => by
    simp only [head?, Option.mem_def, Option.some_inj] at h
    -- ⊢ a :: l = x :: tail (a :: l)
    exact h ▸ rfl
    -- 🎉 no goals
#align list.eq_cons_of_mem_head' List.eq_cons_of_mem_head?

theorem mem_of_mem_head? {x : α} {l : List α} (h : x ∈ l.head?) : x ∈ l :=
  (eq_cons_of_mem_head? h).symm ▸ mem_cons_self _ _
#align list.mem_of_mem_head' List.mem_of_mem_head?

@[simp] theorem head!_cons [Inhabited α] (a : α) (l : List α) : head! (a :: l) = a := rfl
#align list.head_cons List.head!_cons

#align list.tail_nil List.tail_nil
#align list.tail_cons List.tail_cons

@[simp]
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
    head! (s ++ t) = head! s := by induction s; contradiction; rfl
                                   -- ⊢ head! ([] ++ t) = head! []
                                                -- ⊢ head! (head✝ :: tail✝ ++ t) = head! (head✝ :: tail✝)
                                                               -- 🎉 no goals
#align list.head_append List.head!_append

theorem head?_append {s t : List α} {x : α} (h : x ∈ s.head?) : x ∈ (s ++ t).head? := by
  cases s; contradiction; exact h
  -- ⊢ x ∈ head? ([] ++ t)
           -- ⊢ x ∈ head? (head✝ :: tail✝ ++ t)
                          -- 🎉 no goals
#align list.head'_append List.head?_append

theorem head?_append_of_ne_nil :
    ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []), head? (l₁ ++ l₂) = head? l₁
  | _ :: _, _, _ => rfl
#align list.head'_append_of_ne_nil List.head?_append_of_ne_nil

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
    tail (l ++ [a]) = tail l ++ [a] := by
  induction l; contradiction; rw [tail, cons_append, tail]
  -- ⊢ tail ([] ++ [a]) = tail [] ++ [a]
               -- ⊢ tail (head✝ :: tail✝ ++ [a]) = tail (head✝ :: tail✝) ++ [a]
                              -- 🎉 no goals
#align list.tail_append_singleton_of_ne_nil List.tail_append_singleton_of_ne_nil

theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ head? l → a :: tail l = l
  | [], a, h => by contradiction
                   -- 🎉 no goals
  | b :: l, a, h => by
    simp at h
    -- ⊢ a :: tail (b :: l) = b :: l
    simp [h]
    -- 🎉 no goals
#align list.cons_head'_tail List.cons_head?_tail

theorem head!_mem_head? [Inhabited α] : ∀ {l : List α}, l ≠ [] → head! l ∈ head? l
  | [], h => by contradiction
                -- 🎉 no goals
  | a :: l, _ => rfl
#align list.head_mem_head' List.head!_mem_head?

theorem cons_head!_tail [Inhabited α] {l : List α} (h : l ≠ []) : head! l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)
#align list.cons_head_tail List.cons_head!_tail

theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  have h' := mem_cons_self l.head! l.tail
  -- ⊢ head! l ∈ l
  rwa [cons_head!_tail h] at h'
  -- 🎉 no goals
#align list.head_mem_self List.head!_mem_self

@[simp]
theorem head?_map (f : α → β) (l) : head? (map f l) = (head? l).map f := by cases l <;> rfl
                                                                            -- ⊢ head? (map f []) = Option.map f (head? [])
                                                                                        -- 🎉 no goals
                                                                                        -- 🎉 no goals
#align list.head'_map List.head?_map

theorem tail_append_of_ne_nil (l l' : List α) (h : l ≠ []) : (l ++ l').tail = l.tail ++ l' := by
  cases l
  -- ⊢ tail ([] ++ l') = tail [] ++ l'
  · contradiction
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align list.tail_append_of_ne_nil List.tail_append_of_ne_nil

section deprecated
set_option linter.deprecated false -- TODO(Mario): make replacements for theorems in this section

@[simp] theorem nthLe_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length := (by simpa [← lt_tsub_iff_right] using h)) :
                                  -- 🎉 no goals
    l.tail.nthLe i h = l.nthLe (i + 1) h' := by
  -- Porting note: cases l <;> [cases h; rfl] fails
  cases l
  -- ⊢ nthLe (tail []) i h = nthLe [] (i + 1) h'
  · cases h
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align list.nth_le_tail List.nthLe_tail

theorem nthLe_cons_aux {l : List α} {a : α} {n} (hn : n ≠ 0) (h : n < (a :: l).length) :
    n - 1 < l.length := by
  contrapose! h
  -- ⊢ length (a :: l) ≤ n
  rw [length_cons]
  -- ⊢ succ (length l) ≤ n
  convert succ_le_succ h
  -- ⊢ n = succ (n - 1)
  exact (Nat.succ_pred_eq_of_pos hn.bot_lt).symm
  -- 🎉 no goals
#align list.nth_le_cons_aux List.nthLe_cons_aux

theorem nthLe_cons {l : List α} {a : α} {n} (hl) :
    (a :: l).nthLe n hl = if hn : n = 0 then a else l.nthLe (n - 1) (nthLe_cons_aux hn hl) := by
  split_ifs with h
  -- ⊢ nthLe (a :: l) n hl = a
  · simp [nthLe, h]
    -- 🎉 no goals
  cases l
  -- ⊢ nthLe [a] n hl = nthLe [] (n - 1) (_ : n - 1 < length [])
  · rw [length_singleton, lt_succ_iff, nonpos_iff_eq_zero] at hl
    -- ⊢ nthLe [a] n hl✝ = nthLe [] (n - 1) (_ : n - 1 < length [])
    contradiction
    -- 🎉 no goals
  cases n
  -- ⊢ nthLe (a :: head✝ :: tail✝) zero hl = nthLe (head✝ :: tail✝) (zero - 1) (_ : …
  · contradiction
    -- 🎉 no goals
  rfl
  -- 🎉 no goals
#align list.nth_le_cons List.nthLe_cons

end deprecated

-- Porting note: List.modifyHead has @[simp], and Lean 4 treats this as
-- an invitation to unfold modifyHead in any context,
-- not just use the equational lemmas.

-- @[simp]
@[simp 1100, nolint simpNF]
theorem modifyHead_modifyHead (l : List α) (f g : α → α) :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp
                                                               -- ⊢ modifyHead g (modifyHead f []) = modifyHead (g ∘ f) []
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
#align list.modify_head_modify_head List.modifyHead_modifyHead

/-! ### Induction from the right -/

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
def reverseRecOn {C : List α → Sort*} (l : List α) (H0 : C [])
    (H1 : ∀ (l : List α) (a : α), C l → C (l ++ [a])) : C l := by
  rw [← reverse_reverse l]
  -- ⊢ C (reverse (reverse l))
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

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectionalRec {C : List α → Sort*} (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : ∀ l, C l
  | [] => H0
  | [a] => H1 a
  | a :: b :: l => by
    let l' := dropLast (b :: l)
    -- ⊢ C (a :: b :: l)
    let b' := getLast (b :: l) (cons_ne_nil _ _)
    -- ⊢ C (a :: b :: l)
    rw [← dropLast_append_getLast (cons_ne_nil b l)]
    -- ⊢ C (a :: (dropLast (b :: l) ++ [getLast (b :: l) (_ : b :: l ≠ [])]))
    have : C l' := bidirectionalRec H0 H1 Hn l'
    -- ⊢ C (a :: (dropLast (b :: l) ++ [getLast (b :: l) (_ : b :: l ≠ [])]))
    exact Hn a l' b' this
    -- 🎉 no goals
termination_by _ l => l.length
#align list.bidirectional_rec List.bidirectionalRecₓ -- universe order

/-- Like `bidirectionalRec`, but with the list parameter placed first. -/
@[elab_as_elim]
def bidirectionalRecOn {C : List α → Sort*} (l : List α) (H0 : C []) (H1 : ∀ a : α, C [a])
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

#align list.reverse_sublist_iff List.reverse_sublist

#align list.append_sublist_append_right List.append_sublist_append_right
#align list.sublist.append List.Sublist.append
#align list.sublist.subset List.Sublist.subset

#align list.singleton_sublist List.singleton_sublist

theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil <| s.subset
#align list.eq_nil_of_sublist_nil List.eq_nil_of_sublist_nil

-- Porting note: this lemma seems to have been renamed on the occasion of its move to Std4
alias sublist_nil_iff_eq_nil := sublist_nil
#align list.sublist_nil_iff_eq_nil List.sublist_nil_iff_eq_nil

#align list.replicate_sublist_replicate List.replicate_sublist_replicate

theorem sublist_replicate_iff {l : List α} {a : α} {n : ℕ} :
    l <+ replicate n a ↔ ∃ k ≤ n, l = replicate k a :=
  ⟨fun h =>
    ⟨l.length, h.length_le.trans_eq (length_replicate _ _),
      eq_replicate_length.mpr fun b hb => eq_of_mem_replicate (h.subset hb)⟩,
    by rintro ⟨k, h, rfl⟩; exact (replicate_sublist_replicate _).mpr h⟩
       -- ⊢ replicate k a <+ replicate n a
                           -- 🎉 no goals
#align list.sublist_replicate_iff List.sublist_replicate_iff

#align list.sublist.eq_of_length List.Sublist.eq_of_length

#align list.sublist.eq_of_length_le List.Sublist.eq_of_length_le

theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le
#align list.sublist.antisymm List.Sublist.antisymm

instance decidableSublist [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+ l₂)
  | [], _ => isTrue <| nil_sublist _
  | _ :: _, [] => isFalse fun h => List.noConfusion <| eq_nil_of_sublist_nil h
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      @decidable_of_decidable_of_iff _ _ (decidableSublist l₁ l₂) <|
        h ▸ ⟨Sublist.cons_cons _, sublist_of_cons_sublist_cons⟩
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

-- Porting note: simp can prove this
-- @[simp]
theorem indexOf_nil (a : α) : indexOf a [] = 0 :=
  rfl
#align list.index_of_nil List.indexOf_nil

/-
  Porting note: The following proofs were simpler prior to the port. These proofs use the low-level
  `findIdx.go`.
  * `indexOf_cons_self`
  * `indexOf_cons_eq`
  * `indexOf_cons_ne`
  * `indexOf_cons`

  The ported versions of the earlier proofs are given in comments.
-/

-- Porting note: these lemmas recover the Lean 3 definition of `findIdx`
@[simp] theorem findIdx_nil {α : Type*} (p : α → Bool) :
  [].findIdx p = 0 := rfl

theorem findIdx_cons (p : α → Bool) (b : α) (l : List α) :
    (b :: l).findIdx p = bif p b then 0 else (l.findIdx p) + 1 := by
    cases H : p b with
      | true => simp [H, findIdx, findIdx.go]
      | false => simp [H, findIdx, findIdx.go, findIdx_go_succ]
  where
    findIdx_go_succ (p : α → Bool) (l : List α) (n : ℕ) :
        List.findIdx.go p l (n + 1) = (List.findIdx.go p l n) + 1 := by
      cases l with
      | nil => unfold List.findIdx.go; exact Nat.succ_eq_add_one n
      | cons head tail =>
        unfold List.findIdx.go
        cases p head <;> simp only [cond_false, cond_true]
        exact findIdx_go_succ p tail (n + 1)

-- indexOf_cons_eq _ rfl
@[simp]
theorem indexOf_cons_self (a : α) (l : List α) : indexOf a (a :: l) = 0 := by
  rw [indexOf, findIdx_cons, beq_self_eq_true, cond]
  -- 🎉 no goals
#align list.index_of_cons_self List.indexOf_cons_self

-- fun e => if_pos e
theorem indexOf_cons_eq {a b : α} (l : List α) : a = b → indexOf a (b :: l) = 0
  | e => by rw [e]; exact indexOf_cons_self b l
            -- ⊢ indexOf b (b :: l) = 0
                    -- 🎉 no goals
#align list.index_of_cons_eq List.indexOf_cons_eq

-- fun n => if_neg n
@[simp]
theorem indexOf_cons_ne {a b : α} (l : List α) : a ≠ b → indexOf a (b :: l) = succ (indexOf a l)
  | h => by simp only [indexOf, findIdx_cons, Bool.cond_eq_ite, beq_iff_eq, h, ite_false]
            -- 🎉 no goals
#align list.index_of_cons_ne List.indexOf_cons_ne

-- rfl
theorem indexOf_cons (a b : α) (l : List α) :
    indexOf a (b :: l) = if a = b then 0 else succ (indexOf a l) := by
  simp only [indexOf, findIdx_cons, Bool.cond_eq_ite, beq_iff_eq]
  -- 🎉 no goals
#align list.index_of_cons List.indexOf_cons

theorem indexOf_eq_length {a : α} {l : List α} : indexOf a l = length l ↔ a ∉ l := by
  induction' l with b l ih
  -- ⊢ indexOf a [] = length [] ↔ ¬a ∈ []
  · exact iff_of_true rfl (not_mem_nil _)
    -- 🎉 no goals
  simp only [length, mem_cons, indexOf_cons]; split_ifs with h
  -- ⊢ (if a = b then 0 else succ (indexOf a l)) = length l + 1 ↔ ¬(a = b ∨ a ∈ l)
                                              -- ⊢ 0 = length l + 1 ↔ ¬(a = b ∨ a ∈ l)
  · exact iff_of_false (by rintro ⟨⟩) fun H => H <| Or.inl h
    -- 🎉 no goals
  · simp only [h, false_or_iff]
    -- ⊢ succ (indexOf a l) = length l + 1 ↔ ¬a ∈ l
    rw [← ih]
    -- ⊢ succ (indexOf a l) = length l + 1 ↔ indexOf a l = length l
    exact succ_inj'
    -- 🎉 no goals
#align list.index_of_eq_length List.indexOf_eq_length

@[simp]
theorem indexOf_of_not_mem {l : List α} {a : α} : a ∉ l → indexOf a l = length l :=
  indexOf_eq_length.2
#align list.index_of_of_not_mem List.indexOf_of_not_mem

theorem indexOf_le_length {a : α} {l : List α} : indexOf a l ≤ length l := by
  induction' l with b l ih; · rfl
  -- ⊢ indexOf a [] ≤ length []
                              -- 🎉 no goals
  simp only [length, indexOf_cons]
  -- ⊢ (if a = b then 0 else succ (indexOf a l)) ≤ length l + 1
  by_cases h : a = b
  -- ⊢ (if a = b then 0 else succ (indexOf a l)) ≤ length l + 1
  · rw [if_pos h]; exact Nat.zero_le _
    -- ⊢ 0 ≤ length l + 1
                   -- 🎉 no goals
  · rw [if_neg h]; exact succ_le_succ ih
    -- ⊢ succ (indexOf a l) ≤ length l + 1
                   -- 🎉 no goals
#align list.index_of_le_length List.indexOf_le_length

theorem indexOf_lt_length {a} {l : List α} : indexOf a l < length l ↔ a ∈ l :=
  ⟨fun h => Decidable.by_contradiction fun al => Nat.ne_of_lt h <| indexOf_eq_length.2 al,
   fun al => (lt_of_le_of_ne indexOf_le_length) fun h => indexOf_eq_length.1 h al⟩
#align list.index_of_lt_length List.indexOf_lt_length

theorem indexOf_append_of_mem {a : α} (h : a ∈ l₁) : indexOf a (l₁ ++ l₂) = indexOf a l₁ := by
  induction' l₁ with d₁ t₁ ih
  -- ⊢ indexOf a ([] ++ l₂) = indexOf a []
  · exfalso
    -- ⊢ False
    exact not_mem_nil a h
    -- 🎉 no goals
  rw [List.cons_append]
  -- ⊢ indexOf a (d₁ :: (t₁ ++ l₂)) = indexOf a (d₁ :: t₁)
  by_cases hh : a = d₁
  -- ⊢ indexOf a (d₁ :: (t₁ ++ l₂)) = indexOf a (d₁ :: t₁)
  · iterate 2 rw [indexOf_cons_eq _ hh]
    -- 🎉 no goals
  rw [indexOf_cons_ne _ hh, indexOf_cons_ne _ hh, ih (mem_of_ne_of_mem hh h)]
  -- 🎉 no goals
#align list.index_of_append_of_mem List.indexOf_append_of_mem

theorem indexOf_append_of_not_mem {a : α} (h : a ∉ l₁) :
    indexOf a (l₁ ++ l₂) = l₁.length + indexOf a l₂ := by
  induction' l₁ with d₁ t₁ ih
  -- ⊢ indexOf a ([] ++ l₂) = length [] + indexOf a l₂
  · rw [List.nil_append, List.length, zero_add]
    -- 🎉 no goals
  rw [List.cons_append, indexOf_cons_ne _ (ne_of_not_mem_cons h), List.length,
    ih (not_mem_of_not_mem_cons h), Nat.succ_add]
#align list.index_of_append_of_not_mem List.indexOf_append_of_not_mem

end IndexOf

/-! ### nth element -/

section deprecated
set_option linter.deprecated false

@[deprecated get_of_mem]
theorem nthLe_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n h, nthLe l n h = a :=
  let ⟨i, h⟩ := get_of_mem h; ⟨i.1, i.2, h⟩
#align list.nth_le_of_mem List.nthLe_of_mem

@[deprecated get?_eq_get]
theorem nthLe_get? {l : List α} {n} (h) : get? l n = some (nthLe l n h) := get?_eq_get _
#align list.nth_le_nth List.nthLe_get?

#align list.nth_len_le List.get?_len_le

@[simp]
theorem get?_length (l : List α) : l.get? l.length = none := get?_len_le le_rfl
#align list.nth_length List.get?_length

@[deprecated get?_eq_some]
theorem get?_eq_some' {l : List α} {n a} : get? l n = some a ↔ ∃ h, nthLe l n h = a := get?_eq_some
#align list.nth_eq_some List.get?_eq_some'

#align list.nth_eq_none_iff List.get?_eq_none
#align list.nth_of_mem List.get?_of_mem

@[deprecated get_mem]
theorem nthLe_mem (l : List α) (n h) : nthLe l n h ∈ l := get_mem ..
#align list.nth_le_mem List.nthLe_mem

#align list.nth_mem List.get?_mem

@[deprecated mem_iff_get]
theorem mem_iff_nthLe {a} {l : List α} : a ∈ l ↔ ∃ n h, nthLe l n h = a :=
  mem_iff_get.trans ⟨fun ⟨⟨n, h⟩, e⟩ => ⟨n, h, e⟩, fun ⟨n, h, e⟩ => ⟨⟨n, h⟩, e⟩⟩
#align list.mem_iff_nth_le List.mem_iff_nthLe

#align list.mem_iff_nth List.mem_iff_get?
#align list.nth_zero List.get?_zero

-- Porting note: couldn't synthesize _ in cases h x _ rfl anymore, needed to be given explicitly
theorem get?_injective {α : Type u} {xs : List α} {i j : ℕ} (h₀ : i < xs.length) (h₁ : Nodup xs)
    (h₂ : xs.get? i = xs.get? j) : i = j := by
  induction xs generalizing i j with
  | nil => cases h₀
  | cons x xs tail_ih =>
    cases i <;> cases j
    case zero.zero => rfl
    case succ.succ =>
      congr; cases h₁
      apply tail_ih <;> solve_by_elim [lt_of_succ_lt_succ]
    all_goals ( dsimp at h₂; cases' h₁ with _ _ h h')
    · cases (h x (mem_iff_get?.mpr ⟨_, h₂.symm⟩) rfl)
    · cases (h x (mem_iff_get?.mpr ⟨_, h₂⟩) rfl)
#align list.nth_injective List.get?_injective

#align list.nth_map List.get?_map

@[deprecated get_map]
theorem nthLe_map (f : α → β) {l n} (H1 H2) : nthLe (map f l) n H1 = f (nthLe l n H2) := get_map ..
#align list.nth_le_map List.nthLe_map

/-- A version of `get_map` that can be used for rewriting. -/
theorem get_map_rev (f : α → β) {l n} :
    f (get l n) = get (map f l) ⟨n.1, (l.length_map f).symm ▸ n.2⟩ := Eq.symm (get_map _)

/-- A version of `nthLe_map` that can be used for rewriting. -/
@[deprecated get_map_rev]
theorem nthLe_map_rev (f : α → β) {l n} (H) :
    f (nthLe l n H) = nthLe (map f l) n ((l.length_map f).symm ▸ H) :=
  (nthLe_map f _ _).symm
#align list.nth_le_map_rev List.nthLe_map_rev

@[simp, deprecated get_map]
theorem nthLe_map' (f : α → β) {l n} (H) :
    nthLe (map f l) n H = f (nthLe l n (l.length_map f ▸ H)) := nthLe_map f _ _
#align list.nth_le_map' List.nthLe_map'

/-- If one has `nthLe L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
@[deprecated get_of_eq]
theorem nthLe_of_eq {L L' : List α} (h : L = L') {i : ℕ} (hi : i < L.length) :
    nthLe L i hi = nthLe L' i (h ▸ hi) := by congr
                                             -- 🎉 no goals
#align list.nth_le_of_eq List.nthLe_of_eq

@[simp, deprecated get_singleton]
theorem nthLe_singleton (a : α) {n : ℕ} (hn : n < 1) : nthLe [a] n hn = a := get_singleton ..
#align list.nth_le_singleton List.nthLe_singleton

@[deprecated] -- FIXME: replacement -- it's not `get_zero` and it's not `get?_zero`
theorem nthLe_zero [Inhabited α] {L : List α} (h : 0 < L.length) : List.nthLe L 0 h = L.head! := by
  cases L
  -- ⊢ nthLe [] 0 h = head! []
  cases h
  -- ⊢ nthLe (head✝ :: tail✝) 0 h = head! (head✝ :: tail✝)
  simp [nthLe]
  -- 🎉 no goals
#align list.nth_le_zero List.nthLe_zero

@[deprecated get_append]
theorem nthLe_append {l₁ l₂ : List α} {n : ℕ} (hn₁) (hn₂) :
    (l₁ ++ l₂).nthLe n hn₁ = l₁.nthLe n hn₂ := get_append _ hn₂
#align list.nth_le_append List.nthLe_append

@[deprecated get_append_right']
theorem nthLe_append_right {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂) :
    (l₁ ++ l₂).nthLe n h₂ = l₂.nthLe (n - l₁.length) (get_append_right_aux h₁ h₂) :=
  get_append_right' h₁ h₂
#align list.nth_le_append_right_aux List.get_append_right_aux
#align list.nth_le_append_right List.nthLe_append_right

@[deprecated get_replicate]
theorem nthLe_replicate (a : α) {n m : ℕ} (h : m < (replicate n a).length) :
    (replicate n a).nthLe m h = a := get_replicate ..
#align list.nth_le_replicate List.nthLe_replicate

#align list.nth_append List.get?_append
#align list.nth_append_right List.get?_append_right

@[deprecated getLast_eq_get]
theorem getLast_eq_nthLe (l : List α) (h : l ≠ []) :
    getLast l h = l.nthLe (l.length - 1) (Nat.sub_lt (length_pos_of_ne_nil h) one_pos) :=
  getLast_eq_get ..
#align list.last_eq_nth_le List.getLast_eq_nthLe

theorem get_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.get ⟨l.length - 1, h⟩ = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
                                            -- ⊢ False
                                                        -- 🎉 no goals
  (getLast_eq_get l _).symm

@[deprecated get_length_sub_one]
theorem nthLe_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.nthLe (l.length - 1) h = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
                                             -- ⊢ False
                                                         -- 🎉 no goals
  get_length_sub_one _
#align list.nth_le_length_sub_one List.nthLe_length_sub_one

#align list.nth_concat_length List.get?_concat_length

@[deprecated get_cons_length]
theorem nthLe_cons_length : ∀ (x : α) (xs : List α) (n : ℕ) (h : n = xs.length),
    (x :: xs).nthLe n (by simp [h]) = (x :: xs).getLast (cons_ne_nil x xs) := get_cons_length
                          -- 🎉 no goals
#align list.nth_le_cons_length List.nthLe_cons_length

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  induction' l with x l ih generalizing n
  -- ⊢ take 1 (drop n []) = [get [] { val := n, isLt := h }]
  · cases h
    -- 🎉 no goals
  · by_cases h₁ : l = []
    -- ⊢ take 1 (drop n (x :: l)) = [get (x :: l) { val := n, isLt := h }]
    · subst h₁
      -- ⊢ take 1 (drop n [x]) = [get [x] { val := n, isLt := h }]
      rw [get_singleton]
      -- ⊢ take 1 (drop n [x]) = [x]
      simp [lt_succ_iff] at h
      -- ⊢ take 1 (drop n [x]) = [x]
      subst h
      -- ⊢ take 1 (drop 0 [x]) = [x]
      simp
      -- 🎉 no goals
    have h₂ := h
    -- ⊢ take 1 (drop n (x :: l)) = [get (x :: l) { val := n, isLt := h }]
    rw [length_cons, Nat.lt_succ_iff, le_iff_eq_or_lt] at h₂
    -- ⊢ take 1 (drop n (x :: l)) = [get (x :: l) { val := n, isLt := h }]
    cases n
    -- ⊢ take 1 (drop zero (x :: l)) = [get (x :: l) { val := zero, isLt := h }]
    · simp [get]
      -- 🎉 no goals
    rw [drop, get]
    -- ⊢ take 1 (drop n✝ l) = [get l { val := n✝, isLt := (_ : succ n✝ ≤ length l) }]
    apply ih
    -- 🎉 no goals

@[deprecated take_one_drop_eq_of_lt_length]
theorem take_one_drop_eq_of_lt_length' {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.nthLe n h] := take_one_drop_eq_of_lt_length h
#align list.take_one_drop_eq_of_lt_length List.take_one_drop_eq_of_lt_length'

#align list.ext List.ext

@[deprecated ext_get]
theorem ext_nthLe {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ n h₁ h₂, nthLe l₁ n h₁ = nthLe l₂ n h₂) : l₁ = l₂ :=
  ext_get hl h
#align list.ext_le List.ext_nthLe

@[simp]
theorem indexOf_get [DecidableEq α] {a : α} : ∀ {l : List α} (h), get l ⟨indexOf a l, h⟩ = a
  | b :: l, h => by
    by_cases h' : a = b <;>
    -- ⊢ get (b :: l) { val := indexOf a (b :: l), isLt := h } = a
      simp only [h', if_pos, if_false, indexOf_cons, get, @indexOf_get _ _ l]
      -- 🎉 no goals
      -- 🎉 no goals

@[simp, deprecated indexOf_get]
theorem indexOf_nthLe [DecidableEq α] {a : α} : ∀ {l : List α} (h), nthLe l (indexOf a l) h = a :=
  indexOf_get
#align list.index_of_nth_le List.indexOf_nthLe

@[simp]
theorem indexOf_get? [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    get? l (indexOf a l) = some a := by rw [nthLe_get?, indexOf_nthLe (indexOf_lt_length.2 h)]
                                        -- 🎉 no goals
#align list.index_of_nth List.indexOf_get?

@[deprecated]
theorem get_reverse_aux₁ :
    ∀ (l r : List α) (i h1 h2), get (reverseAux l r) ⟨i + length l, h1⟩ = get r ⟨i, h2⟩
  | [], r, i => fun h1 _ => rfl
  | a :: l, r, i => by
    rw [show i + length (a :: l) = i + 1 + length l from add_right_comm i (length l) 1]
    -- ⊢ ∀ (h1 : i + 1 + length l < length (reverseAux (a :: l) r)) (h2 : i < length  …
    exact fun h1 h2 => get_reverse_aux₁ l (a :: r) (i + 1) h1 (succ_lt_succ h2)
    -- 🎉 no goals
#align list.nth_le_reverse_aux1 List.get_reverse_aux₁

theorem indexOf_inj [DecidableEq α] {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    indexOf x l = indexOf y l ↔ x = y :=
  ⟨fun h => by
    have x_eq_y :
        get l ⟨indexOf x l, indexOf_lt_length.2 hx⟩ =
        get l ⟨indexOf y l, indexOf_lt_length.2 hy⟩ := by
      simp only [h]
    simp only [indexOf_get] at x_eq_y; exact x_eq_y, fun h => by subst h; rfl⟩
    -- ⊢ x = y
                                       -- 🎉 no goals
                                                                 -- ⊢ indexOf x l = indexOf x l
                                                                          -- 🎉 no goals
#align list.index_of_inj List.indexOf_inj

theorem get_reverse_aux₂ :
    ∀ (l r : List α) (i : Nat) (h1) (h2),
      get (reverseAux l r) ⟨length l - 1 - i, h1⟩ = get l ⟨i, h2⟩
  | [], r, i, h1, h2 => absurd h2 (Nat.not_lt_zero _)
  | a :: l, r, 0, h1, _ => by
    have aux := get_reverse_aux₁ l (a :: r) 0
    -- ⊢ get (reverseAux (a :: l) r) { val := length (a :: l) - 1 - 0, isLt := h1 } = …
    rw [zero_add] at aux
    -- ⊢ get (reverseAux (a :: l) r) { val := length (a :: l) - 1 - 0, isLt := h1 } = …
    exact aux _ (zero_lt_succ _)
    -- 🎉 no goals
  | a :: l, r, i + 1, h1, h2 => by
    have aux := get_reverse_aux₂ l (a :: r) i
    -- ⊢ get (reverseAux (a :: l) r) { val := length (a :: l) - 1 - (i + 1), isLt :=  …
    have heq :=
      calc
        length (a :: l) - 1 - (i + 1) = length l - (1 + i) := by rw [add_comm]; rfl
        _ = length l - 1 - i := by rw [← tsub_add_eq_tsub_tsub]
    rw [← heq] at aux
    -- ⊢ get (reverseAux (a :: l) r) { val := length (a :: l) - 1 - (i + 1), isLt :=  …
    apply aux
    -- 🎉 no goals
#align list.nth_le_reverse_aux2 List.get_reverse_aux₂

@[simp] theorem get_reverse (l : List α) (i : Nat) (h1 h2) :
    get (reverse l) ⟨length l - 1 - i, h1⟩ = get l ⟨i, h2⟩ :=
  get_reverse_aux₂ _ _ _ _ _

@[simp, deprecated get_reverse]
theorem nthLe_reverse (l : List α) (i : Nat) (h1 h2) :
    nthLe (reverse l) (length l - 1 - i) h1 = nthLe l i h2 :=
  get_reverse ..
#align list.nth_le_reverse List.nthLe_reverse

theorem nthLe_reverse' (l : List α) (n : ℕ) (hn : n < l.reverse.length) (hn') :
    l.reverse.nthLe n hn = l.nthLe (l.length - 1 - n) hn' := by
  rw [eq_comm]
  -- ⊢ nthLe l (length l - 1 - n) hn' = nthLe (reverse l) n hn
  convert nthLe_reverse l.reverse n (by simpa) hn using 1
  -- ⊢ nthLe l (length l - 1 - n) hn' = nthLe (reverse (reverse l)) (length (revers …
  simp
  -- 🎉 no goals
#align list.nth_le_reverse' List.nthLe_reverse'

theorem get_reverse' (l : List α) (n) (hn') :
    l.reverse.get n = l.get ⟨l.length - 1 - n, hn'⟩ := nthLe_reverse' ..

-- FIXME: prove it the other way around
attribute [deprecated get_reverse'] nthLe_reverse'

theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) :
    l = [l.nthLe 0 (h.symm ▸ zero_lt_one)] := by
  refine' ext_get (by convert h) fun n h₁ h₂ => _
  -- ⊢ get l { val := n, isLt := h₁ } = get [nthLe l 0 (_ : 0 < length l)] { val := …
  simp only [get_singleton]
  -- ⊢ get l { val := n, isLt := h₁ } = nthLe l 0 (_ : 0 < length l)
  congr
  -- ⊢ n = 0
  exact eq_bot_iff.mpr (Nat.lt_succ_iff.mp h₂)
  -- 🎉 no goals
#align list.eq_cons_of_length_one List.eq_cons_of_length_one

theorem get_eq_iff {l : List α} {n : Fin l.length} {x : α} : l.get n = x ↔ l.get? n.1 = some x := by
  rw [get?_eq_some]
  -- ⊢ get l n = x ↔ ∃ h, get l { val := ↑n, isLt := h } = x
  simp [n.2]
  -- 🎉 no goals

@[deprecated get_eq_iff]
theorem nthLe_eq_iff {l : List α} {n : ℕ} {x : α} {h} : l.nthLe n h = x ↔ l.get? n = some x :=
  get_eq_iff
#align list.nth_le_eq_iff List.nthLe_eq_iff

@[deprecated get?_eq_get]
theorem some_nthLe_eq {l : List α} {n : ℕ} {h} : some (l.nthLe n h) = l.get? n :=
  (get?_eq_get _).symm
#align list.some_nth_le_eq List.some_nthLe_eq

end deprecated

theorem modifyNthTail_modifyNthTail {f g : List α → List α} (m : ℕ) :
    ∀ (n) (l : List α),
      (l.modifyNthTail f n).modifyNthTail g (m + n) =
        l.modifyNthTail (fun l => (f l).modifyNthTail g m) n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => congr_arg (List.cons a) (modifyNthTail_modifyNthTail m n l)
#align list.modify_nth_tail_modify_nth_tail List.modifyNthTail_modifyNthTail

theorem modifyNthTail_modifyNthTail_le {f g : List α → List α} (m n : ℕ) (l : List α)
    (h : n ≤ m) :
    (l.modifyNthTail f n).modifyNthTail g m =
      l.modifyNthTail (fun l => (f l).modifyNthTail g (m - n)) n := by
  rcases exists_add_of_le h with ⟨m, rfl⟩
  -- ⊢ modifyNthTail g (n + m) (modifyNthTail f n l) = modifyNthTail (fun l => modi …
  rw [@add_tsub_cancel_left, add_comm, modifyNthTail_modifyNthTail]
  -- 🎉 no goals
#align list.modify_nth_tail_modify_nth_tail_le List.modifyNthTail_modifyNthTail_le

theorem modifyNthTail_modifyNthTail_same {f g : List α → List α} (n : ℕ) (l : List α) :
    (l.modifyNthTail f n).modifyNthTail g n = l.modifyNthTail (g ∘ f) n := by
  rw [modifyNthTail_modifyNthTail_le n n l (le_refl n), tsub_self]; rfl
  -- ⊢ modifyNthTail (fun l => modifyNthTail g 0 (f l)) n l = modifyNthTail (g ∘ f) …
                                                                    -- 🎉 no goals
#align list.modify_nth_tail_modify_nth_tail_same List.modifyNthTail_modifyNthTail_same

#align list.modify_nth_tail_id List.modifyNthTail_id

theorem removeNth_eq_nthTail : ∀ (n) (l : List α), removeNth l n = modifyNthTail tail n l
  | 0, l => by cases l <;> rfl
               -- ⊢ removeNth [] 0 = modifyNthTail tail 0 []
                           -- 🎉 no goals
                           -- 🎉 no goals
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (cons _) (removeNth_eq_nthTail _ _)
#align list.remove_nth_eq_nth_tail List.removeNth_eq_nthTail

#align list.update_nth_eq_modify_nth List.set_eq_modifyNth

theorem modifyNth_eq_set (f : α → α) :
    ∀ (n) (l : List α), modifyNth f n l = ((fun a => set l n (f a)) <$> get? l n).getD l
  | 0, l => by cases l <;> rfl
               -- ⊢ modifyNth f 0 [] = Option.getD ((fun a => set [] 0 (f a)) <$> get? [] 0) []
                           -- 🎉 no goals
                           -- 🎉 no goals
  | n + 1, [] => rfl
  | n + 1, b :: l =>
    (congr_arg (cons b) (modifyNth_eq_set f n l)).trans <| by cases get? l n <;> rfl
                                                              -- ⊢ b :: Option.getD ((fun a => set l n (f a)) <$> none) l = Option.getD ((fun a …
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align list.modify_nth_eq_update_nth List.modifyNth_eq_set

#align list.nth_modify_nth List.get?_modifyNth

theorem length_modifyNthTail (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyNthTail f n l) = length l
  | 0, _ => H _
  | _ + 1, [] => rfl
  | _ + 1, _ :: _ => @congr_arg _ _ _ _ (· + 1) (length_modifyNthTail _ H _ _)
#align list.modify_nth_tail_length List.length_modifyNthTail

-- Porting note: Duplicate of `modify_get?_length`
-- (but with a substantially better name?)
-- @[simp]
theorem length_modifyNth (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  modify_get?_length f
#align list.modify_nth_length List.length_modifyNth

#align list.update_nth_length List.length_set

#align list.nth_modify_nth_eq List.get?_modifyNth_eq
#align list.nth_modify_nth_ne List.get?_modifyNth_ne
#align list.nth_update_nth_eq List.get?_set_eq
#align list.nth_update_nth_of_lt List.get?_set_eq_of_lt
#align list.nth_update_nth_ne List.get?_set_ne
#align list.update_nth_nil List.set_nil
#align list.update_nth_succ List.set_succ
#align list.update_nth_comm List.set_comm

@[simp, deprecated get_set_eq]
theorem nthLe_set_eq (l : List α) (i : ℕ) (a : α) (h : i < (l.set i a).length) :
    (l.set i a).nthLe i h = a := get_set_eq ..
#align list.nth_le_update_nth_eq List.nthLe_set_eq

@[simp]
theorem get_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simpa using hj⟩ := by
                                           -- 🎉 no goals
  rw [← Option.some_inj, ← List.get?_eq_get, List.get?_set_ne _ _ h, List.get?_eq_get]
  -- 🎉 no goals

@[simp, deprecated get_set_of_ne]
theorem nthLe_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).nthLe j hj = l.nthLe j (by simpa using hj) :=
                                           -- 🎉 no goals
  get_set_of_ne h _ hj
#align list.nth_le_update_nth_of_ne List.nthLe_set_of_ne

#align list.mem_or_eq_of_mem_update_nth List.mem_or_eq_of_mem_set

section InsertNth

variable {a : α}

@[simp]
theorem insertNth_zero (s : List α) (x : α) : insertNth 0 x s = x :: s :=
  rfl
#align list.insert_nth_zero List.insertNth_zero

@[simp]
theorem insertNth_succ_nil (n : ℕ) (a : α) : insertNth (n + 1) a [] = [] :=
  rfl
#align list.insert_nth_succ_nil List.insertNth_succ_nil

@[simp]
theorem insertNth_succ_cons (s : List α) (hd x : α) (n : ℕ) :
    insertNth (n + 1) x (hd :: s) = hd :: insertNth n x s :=
  rfl
#align list.insert_nth_succ_cons List.insertNth_succ_cons

theorem length_insertNth : ∀ n as, n ≤ length as → length (insertNth n a as) = length as + 1
  | 0, _, _ => rfl
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, _ :: as, h => congr_arg Nat.succ <| length_insertNth n as (Nat.le_of_succ_le_succ h)
#align list.length_insert_nth List.length_insertNth

theorem removeNth_insertNth (n : ℕ) (l : List α) : (l.insertNth n a).removeNth n = l := by
  rw [removeNth_eq_nth_tail, insertNth, modifyNthTail_modifyNthTail_same]
  -- ⊢ modifyNthTail (tail ∘ cons a) n l = l
  exact modifyNthTail_id _ _
  -- 🎉 no goals
#align list.remove_nth_insert_nth List.removeNth_insertNth

theorem insertNth_removeNth_of_ge :
    ∀ n m as,
      n < length as → n ≤ m → insertNth m a (as.removeNth n) = (as.insertNth (m + 1) a).removeNth n
  | 0, 0, [], has, _ => (lt_irrefl _ has).elim
  | 0, 0, _ :: as, _, _ => by simp [removeNth, insertNth]
                              -- 🎉 no goals
  | 0, m + 1, a :: as, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertNth_removeNth_of_ge n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_ge List.insertNth_removeNth_of_ge

theorem insertNth_removeNth_of_le :
    ∀ n m as,
      n < length as → m ≤ n → insertNth m a (as.removeNth n) = (as.insertNth m a).removeNth (n + 1)
  | _, 0, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertNth_removeNth_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_le List.insertNth_removeNth_of_le

theorem insertNth_comm (a b : α) :
    ∀ (i j : ℕ) (l : List α) (_ : i ≤ j) (_ : j ≤ length l),
      (l.insertNth i a).insertNth (j + 1) b = (l.insertNth j b).insertNth i a
  | 0, j, l => by simp [insertNth]
                  -- 🎉 no goals
  | i + 1, 0, l => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
                           -- 🎉 no goals
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp [insertNth]
    -- ⊢ modifyNthTail (cons b) (j + 1) (modifyNthTail (cons a) i l) = modifyNthTail  …
    exact insertNth_comm a b i j l (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)
    -- 🎉 no goals
#align list.insert_nth_comm List.insertNth_comm

theorem mem_insertNth {a b : α} :
    ∀ {n : ℕ} {l : List α} (_ : n ≤ l.length), a ∈ l.insertNth n b ↔ a = b ∨ a ∈ l
  | 0, as, _ => by simp
                   -- 🎉 no goals
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    rw [List.insertNth_succ_cons, mem_cons, mem_insertNth (Nat.le_of_succ_le_succ h),
      ← or_assoc, @or_comm (a = a'), or_assoc, mem_cons]
#align list.mem_insert_nth List.mem_insertNth

theorem insertNth_of_length_lt (l : List α) (x : α) (n : ℕ) (h : l.length < n) :
    insertNth n x l = l := by
  induction' l with hd tl IH generalizing n
  -- ⊢ insertNth n x [] = []
  · cases n
    -- ⊢ insertNth zero x [] = []
    · simp at h
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  · cases n
    -- ⊢ insertNth zero x (hd :: tl) = hd :: tl
    · simp at h
      -- 🎉 no goals
    · simp only [Nat.succ_lt_succ_iff, length] at h
      -- ⊢ insertNth (succ n✝) x (hd :: tl) = hd :: tl
      simpa using IH _ h
      -- 🎉 no goals
#align list.insert_nth_of_length_lt List.insertNth_of_length_lt

@[simp]
theorem insertNth_length_self (l : List α) (x : α) : insertNth l.length x l = l ++ [x] := by
  induction' l with hd tl IH
  -- ⊢ insertNth (length []) x [] = [] ++ [x]
  · simp
    -- 🎉 no goals
  · simpa using IH
    -- 🎉 no goals
#align list.insert_nth_length_self List.insertNth_length_self

theorem length_le_length_insertNth (l : List α) (x : α) (n : ℕ) :
    l.length ≤ (insertNth n x l).length := by
  cases' le_or_lt n l.length with hn hn
  -- ⊢ length l ≤ length (insertNth n x l)
  · rw [length_insertNth _ _ hn]
    -- ⊢ length l ≤ length l + 1
    exact (Nat.lt_succ_self _).le
    -- 🎉 no goals
  · rw [insertNth_of_length_lt _ _ _ hn]
    -- 🎉 no goals
#align list.length_le_length_insert_nth List.length_le_length_insertNth

theorem length_insertNth_le_succ (l : List α) (x : α) (n : ℕ) :
    (insertNth n x l).length ≤ l.length + 1 := by
  cases' le_or_lt n l.length with hn hn
  -- ⊢ length (insertNth n x l) ≤ length l + 1
  · rw [length_insertNth _ _ hn]
    -- 🎉 no goals
  · rw [insertNth_of_length_lt _ _ _ hn]
    -- ⊢ length l ≤ length l + 1
    exact (Nat.lt_succ_self _).le
    -- 🎉 no goals
#align list.length_insert_nth_le_succ List.length_insertNth_le_succ

theorem get_insertNth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)) :
    (insertNth n x l).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  induction' n with n IH generalizing k l
  -- ⊢ get (insertNth zero x l) { val := k, isLt := hk' } = get l { val := k, isLt  …
  · simp at hn
    -- 🎉 no goals
  · cases' l with hd tl
    -- ⊢ get (insertNth (succ n) x []) { val := k, isLt := hk' } = get [] { val := k, …
    · simp
      -- 🎉 no goals
    · cases k
      -- ⊢ get (insertNth (succ n) x (hd :: tl)) { val := zero, isLt := hk' } = get (hd …
      · simp [get]
        -- 🎉 no goals
      · rw [Nat.succ_lt_succ_iff] at hn
        -- ⊢ get (insertNth (succ n) x (hd :: tl)) { val := succ n✝, isLt := hk' } = get  …
        simpa using IH _ _ hn _
        -- 🎉 no goals

@[deprecated get_insertNth_of_lt]
theorem nthLe_insertNth_of_lt : ∀ (l : List α) (x : α) (n k : ℕ), k < n → ∀ (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)),
    (insertNth n x l).nthLe k hk' = l.nthLe k hk := @get_insertNth_of_lt _
#align list.nth_le_insert_nth_of_lt List.nthLe_insertNth_of_lt

@[simp]
theorem get_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
                                               -- 🎉 no goals
    (insertNth n x l).get ⟨n, hn'⟩ = x := by
  induction' l with hd tl IH generalizing n
  -- ⊢ get (insertNth n x []) { val := n, isLt := hn' } = x
  · simp only [length, nonpos_iff_eq_zero] at hn
    -- ⊢ get (insertNth n x []) { val := n, isLt := hn' } = x
    cases hn
    -- ⊢ get (insertNth 0 x []) { val := 0, isLt := hn' } = x
    simp only [insertNth_zero, get_singleton]
    -- 🎉 no goals
  · cases n
    -- ⊢ get (insertNth zero x (hd :: tl)) { val := zero, isLt := hn' } = x
    · simp
      -- 🎉 no goals
    · simp only [Nat.succ_le_succ_iff, length] at hn
      -- ⊢ get (insertNth (succ n✝) x (hd :: tl)) { val := succ n✝, isLt := hn' } = x
      simpa using IH _ hn
      -- 🎉 no goals

@[simp, deprecated get_insertNth_self]
theorem nthLe_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
                                               -- 🎉 no goals
    (insertNth n x l).nthLe n hn' = x := get_insertNth_self _ _ _ hn
#align list.nth_le_insert_nth_self List.nthLe_insertNth_self

theorem get_insertNth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      -- Porting note: the original proof fails
      -- rwa [length_insertNth _ _ (le_self_add.trans hk'.le), Nat.succ_lt_succ_iff]
      rw [length_insertNth _ _ (le_self_add.trans hk'.le)]; exact Nat.succ_lt_succ_iff.2 hk')) :
      -- ⊢ n + k + 1 < length l + 1
                                                            -- 🎉 no goals
    (insertNth n x l).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  induction' l with hd tl IH generalizing n k
  -- ⊢ get (insertNth n x []) { val := n + k + 1, isLt := hk } = get [] { val := n  …
  · simp at hk'
    -- 🎉 no goals
  · cases n
    -- ⊢ get (insertNth zero x (hd :: tl)) { val := zero + k + 1, isLt := hk } = get  …
    · simp
      -- 🎉 no goals
    · simpa [succ_add] using IH _ _ _
      -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated get_insertNth_add_succ]
theorem nthLe_insertNth_add_succ : ∀ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      -- Porting note: the original proof fails
      -- rwa [length_insertNth _ _ (le_self_add.trans hk'.le), Nat.succ_lt_succ_iff]
      rw [length_insertNth _ _ (le_self_add.trans hk'.le)]; exact Nat.succ_lt_succ_iff.2 hk')),
      -- ⊢ n + k + 1 < length l + 1
                                                            -- 🎉 no goals
    (insertNth n x l).nthLe (n + k + 1) hk = nthLe l (n + k) hk' :=
  @get_insertNth_add_succ _
#align list.nth_le_insert_nth_add_succ List.nthLe_insertNth_add_succ

set_option linter.unnecessarySimpa false in
theorem insertNth_injective (n : ℕ) (x : α) : Function.Injective (insertNth n x) := by
  induction' n with n IH
  -- ⊢ Injective (insertNth zero x)
  · have : insertNth 0 x = cons x := funext fun _ => rfl
    -- ⊢ Injective (insertNth zero x)
    simp [this]
    -- 🎉 no goals
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> simpa [IH.eq_iff] using h
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
#align list.insert_nth_injective List.insertNth_injective

end InsertNth

/-! ### map -/

#align list.map_nil List.map_nil

theorem map_eq_foldr (f : α → β) (l : List α) : map f l = foldr (fun a bs => f a :: bs) [] l := by
  induction l <;> simp [*]
  -- ⊢ map f [] = foldr (fun a bs => f a :: bs) [] []
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.map_eq_foldr List.map_eq_foldr

theorem map_congr {f g : α → β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    -- ⊢ map f (a :: l) = map g (a :: l)
    rw [map, map, h₁, map_congr h₂]
    -- 🎉 no goals
#align list.map_congr List.map_congr

theorem map_eq_map_iff {f g : α → β} {l : List α} : map f l = map g l ↔ ∀ x ∈ l, f x = g x := by
  refine' ⟨_, map_congr⟩; intro h x hx
  -- ⊢ map f l = map g l → ∀ (x : α), x ∈ l → f x = g x
                          -- ⊢ f x = g x
  rw [mem_iff_get] at hx; rcases hx with ⟨n, hn, rfl⟩
  -- ⊢ f x = g x
                          -- ⊢ f (get l n) = g (get l n)
  rw [get_map_rev f, get_map_rev g]
  -- ⊢ get (map f l) { val := ↑n, isLt := (_ : ↑n < length (map f l)) } = get (map  …
  congr!
  -- 🎉 no goals
#align list.map_eq_map_iff List.map_eq_map_iff

theorem map_concat (f : α → β) (a : α) (l : List α) :
    map f (concat l a) = concat (map f l) (f a) := by
  induction l <;> [rfl; simp only [*, concat_eq_append, cons_append, map, map_append]]
  -- 🎉 no goals
#align list.map_concat List.map_concat

@[simp]
theorem map_id'' (l : List α) : map (fun x => x) l = l :=
  map_id _
#align list.map_id'' List.map_id''

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : List α) : map f l = l := by
  simp [show f = id from funext h]
  -- 🎉 no goals
#align list.map_id' List.map_id'

theorem eq_nil_of_map_eq_nil {f : α → β} {l : List α} (h : map f l = nil) : l = nil :=
  eq_nil_of_length_eq_zero <| by rw [← length_map l f, h]; rfl
                                 -- ⊢ length [] = 0
                                                           -- 🎉 no goals
#align list.eq_nil_of_map_eq_nil List.eq_nil_of_map_eq_nil

@[simp]
theorem map_join (f : α → β) (L : List (List α)) : map f (join L) = join (map (map f) L) := by
  induction L <;> [rfl; simp only [*, join, map, map_append]]
  -- 🎉 no goals
#align list.map_join List.map_join

theorem bind_ret_eq_map (f : α → β) (l : List α) : l.bind (List.ret ∘ f) = map f l := by
  unfold List.bind
  -- ⊢ join (map (List.ret ∘ f) l) = map f l
  induction l <;> simp [map, join, List.ret, cons_append, nil_append, *] at *
  -- ⊢ join (map (List.ret ∘ f) []) = map f []
                  -- 🎉 no goals
                  -- ⊢ join (map ((fun a => [a]) ∘ f) tail✝) = map f tail✝
  assumption
  -- 🎉 no goals
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
                                                                         -- ⊢ map f (tail []) = tail (map f [])
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
#align list.map_tail List.map_tail

@[simp]
theorem map_injective_iff {f : α → β} : Injective (map f) ↔ Injective f := by
  constructor <;> intro h x y hxy
  -- ⊢ Injective (map f) → Injective f
                  -- ⊢ x = y
                  -- ⊢ x = y
  · suffices [x] = [y] by simpa using this
    -- ⊢ [x] = [y]
    apply h
    -- ⊢ map f [x] = map f [y]
    simp [hxy]
    -- 🎉 no goals
  · induction' y with yh yt y_ih generalizing x
    -- ⊢ x = []
    · simpa using hxy
      -- 🎉 no goals
    cases x
    -- ⊢ [] = yh :: yt
    · simp at hxy
      -- 🎉 no goals
    · simp only [map, cons.injEq] at hxy
      -- ⊢ head✝ :: tail✝ = yh :: yt
      simp [y_ih hxy.2, h hxy.1]
      -- 🎉 no goals
#align list.map_injective_iff List.map_injective_iff

/-- A single `List.map` of a composition of functions is equal to
composing a `List.map` with another `List.map`, fully applied.
This is the reverse direction of `List.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  (map_map _ _ _).symm
#align list.comp_map List.comp_map

/-- Composing a `List.map` with another `List.map` is equal to
a single `List.map` of composed functions.
-/
@[simp]
theorem map_comp_map (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) := by
  ext l; rw [comp_map, Function.comp_apply]
  -- ⊢ a✝ ∈ get? ((map g ∘ map f) l) n✝ ↔ a✝ ∈ get? (map (g ∘ f) l) n✝
         -- 🎉 no goals
#align list.map_comp_map List.map_comp_map

theorem map_filter_eq_foldr (f : α → β) (p : α → Bool) (as : List α) :
    map f (filter p as) = foldr (fun a bs => bif p a then f a :: bs else bs) [] as := by
  induction' as with head tail
  -- ⊢ map f (filter p []) = foldr (fun a bs => bif p a then f a :: bs else bs) [] []
  · rfl
    -- 🎉 no goals
  · simp only [foldr]
    -- ⊢ map f (filter p (head :: tail)) = bif p head then f head :: foldr (fun a bs  …
    cases hp : p head <;> simp [filter, *]
    -- ⊢ map f (filter p (head :: tail)) = bif false then f head :: foldr (fun a bs = …
                          -- 🎉 no goals
                          -- 🎉 no goals
#align list.map_filter_eq_foldr List.map_filter_eq_foldr

theorem getLast_map (f : α → β) {l : List α} (hl : l ≠ []) :
    (l.map f).getLast (mt eq_nil_of_map_eq_nil hl) = f (l.getLast hl) := by
  induction' l with l_hd l_tl l_ih
  -- ⊢ getLast (map f []) (_ : ¬map f [] = []) = f (getLast [] hl)
  · apply (hl rfl).elim
    -- 🎉 no goals
  · cases l_tl
    -- ⊢ getLast (map f [l_hd]) (_ : ¬map f [l_hd] = []) = f (getLast [l_hd] hl)
    · simp
      -- 🎉 no goals
    · simpa using l_ih _
      -- 🎉 no goals
#align list.last_map List.getLast_map

theorem map_eq_replicate_iff {l : List α} {f : α → β} {b : β} :
    l.map f = replicate l.length b ↔ ∀ x ∈ l, f x = b := by
  simp [eq_replicate]
  -- 🎉 no goals
#align list.map_eq_replicate_iff List.map_eq_replicate_iff

@[simp] theorem map_const (l : List α) (b : β) : map (const α b) l = replicate l.length b :=
  map_eq_replicate_iff.mpr fun _ _ => rfl
#align list.map_const List.map_const

@[simp] theorem map_const' (l : List α) (b : β) : map (fun _ => b) l = replicate l.length b :=
  map_const l b
#align list.map_const' List.map_const'

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (const α b₂) l) :
    b₁ = b₂ := by rw [map_const] at h; exact eq_of_mem_replicate h
                  -- ⊢ b₁ = b₂
                                       -- 🎉 no goals
#align list.eq_of_mem_map_const List.eq_of_mem_map_const

/-! ### zipWith -/

theorem nil_zipWith (f : α → β → γ) (l : List β) : zipWith f [] l = [] := by cases l <;> rfl
                                                                             -- ⊢ zipWith f [] [] = []
                                                                                         -- 🎉 no goals
                                                                                         -- 🎉 no goals
#align list.nil_map₂ List.nil_zipWith

theorem zipWith_nil (f : α → β → γ) (l : List α) : zipWith f l [] = [] := by cases l <;> rfl
                                                                             -- ⊢ zipWith f [] [] = []
                                                                                         -- 🎉 no goals
                                                                                         -- 🎉 no goals
#align list.map₂_nil List.zipWith_nil

@[simp]
theorem zipWith_flip (f : α → β → γ) : ∀ as bs, zipWith (flip f) bs as = zipWith f as bs
  | [], [] => rfl
  | [], b :: bs => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => by
    simp! [zipWith_flip]
    -- ⊢ flip f b a = f a b
    rfl
    -- 🎉 no goals
#align list.map₂_flip List.zipWith_flip

/-! ### take, drop -/

@[simp]
theorem take_zero (l : List α) : take 0 l = [] :=
  rfl
#align list.take_zero List.take_zero

#align list.take_nil List.take_nil

theorem take_cons (n) (a : α) (l : List α) : take (succ n) (a :: l) = a :: take n l :=
  rfl
#align list.take_cons List.take_cons

#align list.take_length List.take_length

theorem take_all_of_le : ∀ {n} {l : List α}, length l ≤ n → take n l = l
  | 0, [], _ => rfl
  | 0, a :: l, h => absurd h (not_le_of_gt (zero_lt_succ _))
  | n + 1, [], _ => rfl
  | n + 1, a :: l, h => by
    change a :: take n l = a :: l
    -- ⊢ a :: take n l = a :: l
    rw [take_all_of_le (le_of_succ_le_succ h)]
    -- 🎉 no goals
#align list.take_all_of_le List.take_all_of_le

@[simp]
theorem take_left : ∀ l₁ l₂ : List α, take (length l₁) (l₁ ++ l₂) = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congr_arg (cons a) (take_left l₁ l₂)
#align list.take_left List.take_left

theorem take_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left
  -- ⊢ take (length l₁) (l₁ ++ l₂) = l₁
            -- 🎉 no goals
#align list.take_left' List.take_left'

theorem take_take : ∀ (n m) (l : List α), take n (take m l) = take (min n m) l
  | n, 0, l => by rw [min_zero, take_zero, take_nil]
                  -- 🎉 no goals
  | 0, m, l => by rw [zero_min, take_zero, take_zero]
                  -- 🎉 no goals
  | succ n, succ m, nil => by simp only [take_nil]
                              -- 🎉 no goals
  | succ n, succ m, a :: l => by
    simp only [take, min_succ_succ, take_take n m l]
    -- 🎉 no goals
#align list.take_take List.take_take

theorem take_replicate (a : α) : ∀ n m : ℕ, take n (replicate m a) = replicate (min n m) a
  | n, 0 => by simp
               -- 🎉 no goals
  | 0, m => by simp
               -- 🎉 no goals
  | succ n, succ m => by simp [min_succ_succ, take_replicate]
                         -- 🎉 no goals
#align list.take_replicate List.take_replicate

theorem map_take {α β : Type*} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.take i).map f = (L.map f).take i
  | [], i => by simp
                -- 🎉 no goals
  | _, 0 => by simp
               -- 🎉 no goals
  | h :: t, n + 1 => by dsimp; rw [map_take f t n]
                        -- ⊢ f h :: map f (take n t) = f h :: take n (map f t)
                               -- 🎉 no goals
#align list.map_take List.map_take

/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
theorem take_append_eq_append_take {l₁ l₂ : List α} {n : ℕ} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := by
  induction l₁ generalizing n; {simp}
  -- ⊢ take n ([] ++ l₂) = take n [] ++ take (n - length []) l₂
                               -- ⊢ take n (head✝ :: tail✝ ++ l₂) = take n (head✝ :: tail✝) ++ take (n - length  …
  cases n <;> simp [*]
  -- ⊢ take zero (head✝ :: tail✝ ++ l₂) = take zero (head✝ :: tail✝) ++ take (zero  …
              -- 🎉 no goals
              -- 🎉 no goals
#align list.take_append_eq_append_take List.take_append_eq_append_take

theorem take_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by simp [take_append_eq_append_take, tsub_eq_zero_iff_le.mpr h]
                                        -- 🎉 no goals
#align list.take_append_of_le_length List.take_append_of_le_length

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
theorem take_append {l₁ l₂ : List α} (i : ℕ) : take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ take i l₂ :=
  by simp [take_append_eq_append_take, take_all_of_le le_self_add]
     -- 🎉 no goals
#align list.take_append List.take_append

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem get_take (L : List α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
    get L ⟨i, hi⟩ = get (L.take j) ⟨i, length_take .. ▸ lt_min hj hi⟩ :=
  get_of_eq (take_append_drop j L).symm _ ▸ get_append ..

set_option linter.deprecated false in
/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
@[deprecated get_take]
theorem nthLe_take (L : List α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
    nthLe L i hi = nthLe (L.take j) i (length_take .. ▸ lt_min hj hi) :=
  get_take _ hi hj
#align list.nth_le_take List.nthLe_take

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
theorem get_take' (L : List α) {j i} :
    get (L.take j) i = get L ⟨i.1, lt_of_lt_of_le i.2 (by simp [le_refl])⟩ := by
                                                          -- 🎉 no goals
  let ⟨i, hi⟩ := i; simp at hi; rw [get_take L _ hi.1]
  -- ⊢ get (take j L) { val := i, isLt := hi } = get L { val := ↑{ val := i, isLt : …
                    -- ⊢ get (take j L) { val := i, isLt := hi✝ } = get L { val := ↑{ val := i, isLt  …
                                -- 🎉 no goals

set_option linter.deprecated false in
/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
@[deprecated get_take']
theorem nthLe_take' (L : List α) {i j : ℕ} (hi : i < (L.take j).length) :
    nthLe (L.take j) i hi = nthLe L i (lt_of_lt_of_le hi (by simp [le_refl])) := get_take' _
                                                             -- 🎉 no goals
#align list.nth_le_take' List.nthLe_take'

theorem get?_take {l : List α} {n m : ℕ} (h : m < n) : (l.take n).get? m = l.get? m := by
  induction' n with n hn generalizing l m
  -- ⊢ get? (take zero l) m = get? l m
  · simp only [Nat.zero_eq] at h
    -- ⊢ get? (take zero l) m = get? l m
    exact absurd h (not_lt_of_le m.zero_le)
    -- 🎉 no goals
  · cases' l with hd tl
    -- ⊢ get? (take (succ n) []) m = get? [] m
    · simp only [take_nil]
      -- 🎉 no goals
    · cases m
      -- ⊢ get? (take (succ n) (hd :: tl)) zero = get? (hd :: tl) zero
      · simp only [get?, take]
        -- 🎉 no goals
      · simpa only using hn (Nat.lt_of_succ_lt_succ h)
        -- 🎉 no goals
#align list.nth_take List.get?_take

@[simp]
theorem nth_take_of_succ {l : List α} {n : ℕ} : (l.take (n + 1)).get? n = l.get? n :=
  get?_take (Nat.lt_succ_self n)
#align list.nth_take_of_succ List.nth_take_of_succ

theorem take_succ {l : List α} {n : ℕ} : l.take (n + 1) = l.take n ++ (l.get? n).toList := by
  induction' l with hd tl hl generalizing n
  -- ⊢ take (n + 1) [] = take n [] ++ Option.toList (get? [] n)
  · simp only [Option.toList, get?, take_nil, append_nil]
    -- 🎉 no goals
  · cases n
    -- ⊢ take (zero + 1) (hd :: tl) = take zero (hd :: tl) ++ Option.toList (get? (hd …
    · simp only [Option.toList, get?, eq_self_iff_true, and_self_iff, take, nil_append]
      -- 🎉 no goals
    · simp only [hl, cons_append, get?, eq_self_iff_true, and_self_iff, take]
      -- 🎉 no goals
#align list.take_succ List.take_succ

@[simp]
theorem take_eq_nil_iff {l : List α} {k : ℕ} : l.take k = [] ↔ l = [] ∨ k = 0 := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]
  -- ⊢ take k [] = [] ↔ [] = [] ∨ k = 0
              -- ⊢ take zero [] = [] ↔ [] = [] ∨ zero = 0
              -- ⊢ take zero (head✝ :: tail✝) = [] ↔ head✝ :: tail✝ = [] ∨ zero = 0
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
#align list.take_eq_nil_iff List.take_eq_nil_iff

theorem take_eq_take :
    ∀ {l : List α} {m n : ℕ}, l.take m = l.take n ↔ min m l.length = min n l.length
  | [], m, n => by simp
                   -- 🎉 no goals
  | _ :: xs, 0, 0 => by simp
                        -- 🎉 no goals
  | x :: xs, m + 1, 0 => by simp
                            -- 🎉 no goals
  | x :: xs, 0, n + 1 => by simp [@eq_comm ℕ 0]
                            -- 🎉 no goals
  | x :: xs, m + 1, n + 1 => by simp [Nat.min_succ_succ, take_eq_take]
                                -- 🎉 no goals
#align list.take_eq_take List.take_eq_take

theorem take_add (l : List α) (m n : ℕ) : l.take (m + n) = l.take m ++ (l.drop m).take n := by
  convert_to take (m + n) (take m l ++ drop m l) = take m l ++ take n (drop m l)
  -- ⊢ take (m + n) l = take (m + n) (take m l ++ drop m l)
  · rw [take_append_drop]
    -- 🎉 no goals
  rw [take_append_eq_append_take, take_all_of_le, append_right_inj]
  -- ⊢ take (m + n - length (take m l)) (drop m l) = take n (drop m l)
  · simp only [take_eq_take, length_take, length_drop]
    -- ⊢ min (m + n - min m (length l)) (length l - m) = min n (length l - m)
    generalize l.length = k; by_cases h : m ≤ k
    -- ⊢ min (m + n - min m k) (k - m) = min n (k - m)
                             -- ⊢ min (m + n - min m k) (k - m) = min n (k - m)
    · simp [min_eq_left_iff.mpr h]
      -- 🎉 no goals
    · push_neg at h
      -- ⊢ min (m + n - min m k) (k - m) = min n (k - m)
      simp [Nat.sub_eq_zero_of_le (le_of_lt h)]
      -- 🎉 no goals
  · trans m
    -- ⊢ length (take m l) ≤ m
    · apply length_take_le
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
#align list.take_add List.take_add

theorem dropLast_eq_take (l : List α) : l.dropLast = l.take l.length.pred := by
  cases' l with x l
  -- ⊢ dropLast [] = take (pred (length [])) []
  · simp [dropLast]
    -- 🎉 no goals
  · induction' l with hd tl hl generalizing x
    -- ⊢ dropLast [x] = take (pred (length [x])) [x]
    · simp [dropLast]
      -- 🎉 no goals
    · simp [dropLast, hl]
      -- 🎉 no goals
#align list.init_eq_take List.dropLast_eq_take

theorem dropLast_take {n : ℕ} {l : List α} (h : n < l.length) :
    (l.take n).dropLast = l.take n.pred := by
  simp [dropLast_eq_take, min_eq_left_of_lt h, take_take, pred_le]
  -- 🎉 no goals
#align list.init_take List.dropLast_take

theorem dropLast_cons_of_ne_nil {α : Type*} {x : α}
    {l : List α} (h : l ≠ []) : (x :: l).dropLast = x :: l.dropLast := by simp [h]
                                                                          -- 🎉 no goals
#align list.init_cons_of_ne_nil List.dropLast_cons_of_ne_nil

@[simp]
theorem dropLast_append_of_ne_nil {α : Type*} {l : List α} :
    ∀ (l' : List α) (_ : l ≠ []), (l' ++ l).dropLast = l' ++ l.dropLast
  | [], _ => by simp only [nil_append]
                -- 🎉 no goals
  | a :: l', h => by
    rw [cons_append, dropLast, dropLast_append_of_ne_nil l' h, cons_append]
    -- ⊢ l' ++ l = [] → False
    simp [h]
    -- 🎉 no goals
#align list.init_append_of_ne_nil List.dropLast_append_of_ne_nil

#align list.drop_eq_nil_of_le List.drop_eq_nil_of_le

theorem drop_eq_nil_iff_le {l : List α} {k : ℕ} : l.drop k = [] ↔ l.length ≤ k := by
  refine' ⟨fun h => _, drop_eq_nil_of_le⟩
  -- ⊢ length l ≤ k
  induction' k with k hk generalizing l
  -- ⊢ length l ≤ zero
  · simp only [drop] at h
    -- ⊢ length l ≤ zero
    simp [h]
    -- 🎉 no goals
  · cases l
    -- ⊢ length [] ≤ succ k
    · simp
      -- 🎉 no goals
    · simp only [drop] at h
      -- ⊢ length (head✝ :: tail✝) ≤ succ k
      simpa [Nat.succ_le_succ_iff] using hk h
      -- 🎉 no goals
#align list.drop_eq_nil_iff_le List.drop_eq_nil_iff_le

theorem tail_drop (l : List α) (n : ℕ) : (l.drop n).tail = l.drop (n + 1) := by
  induction' l with hd tl hl generalizing n
  -- ⊢ tail (drop n []) = drop (n + 1) []
  · simp
    -- 🎉 no goals
  · cases n
    -- ⊢ tail (drop zero (hd :: tl)) = drop (zero + 1) (hd :: tl)
    · simp
      -- 🎉 no goals
    · simp [hl]
      -- 🎉 no goals
#align list.tail_drop List.tail_drop

theorem cons_get_drop_succ {l : List α} {n} :
    l.get n :: l.drop (n.1 + 1) = l.drop n.1 := by
  induction' l with hd tl hl
  -- ⊢ get [] n :: drop (↑n + 1) [] = drop ↑n []
  · exact absurd n.1.zero_le (not_le_of_lt (nomatch n))
    -- 🎉 no goals
  · match n with
    | ⟨0, _⟩ => simp [get]
    | ⟨n+1, hn⟩ =>
      simp only [Nat.succ_lt_succ_iff, List.length] at hn
      simpa [List.get, List.drop] using hl

@[deprecated cons_get_drop_succ]
theorem cons_nthLe_drop_succ {l : List α} {n : ℕ} (hn : n < l.length) :
    l.nthLe n hn :: l.drop (n + 1) = l.drop n := cons_get_drop_succ
#align list.cons_nth_le_drop_succ List.cons_nthLe_drop_succ

#align list.drop_nil List.drop_nil

@[simp]
theorem drop_one : ∀ l : List α, drop 1 l = tail l
  | [] | _ :: _ => rfl
#align list.drop_one List.drop_one

theorem drop_add : ∀ (m n) (l : List α), drop (m + n) l = drop m (drop n l)
  | _, 0, _ => rfl
  | _, _ + 1, [] => drop_nil.symm
  | m, n + 1, _ :: _ => drop_add m n _
#align list.drop_add List.drop_add

@[simp]
theorem drop_left : ∀ l₁ l₂ : List α, drop (length l₁) (l₁ ++ l₂) = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_left l₁ l₂
#align list.drop_left List.drop_left

theorem drop_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : drop n (l₁ ++ l₂) = l₂ := by
  rw [← h]; apply drop_left
  -- ⊢ drop (length l₁) (l₁ ++ l₂) = l₂
            -- 🎉 no goals
#align list.drop_left' List.drop_left'

theorem drop_eq_get_cons : ∀ {n} {l : List α} (h), drop n l = get l ⟨n, h⟩ :: drop (n + 1) l
  | 0, _ :: _, _ => rfl
  | n + 1, _ :: _, _ => @drop_eq_get_cons n _ _
#align list.drop_eq_nth_le_cons List.drop_eq_get_consₓ -- nth_le vs get

#align list.drop_length List.drop_length

theorem drop_length_cons {l : List α} (h : l ≠ []) (a : α) :
    (a :: l).drop l.length = [l.getLast h] := by
  induction' l with y l ih generalizing a
  -- ⊢ drop (length []) [a] = [getLast [] h]
  · cases h rfl
    -- 🎉 no goals
  · simp only [drop, length]
    -- ⊢ drop (Nat.add (length l) 0) (y :: l) = [getLast (y :: l) h]
    by_cases h₁ : l = []
    -- ⊢ drop (Nat.add (length l) 0) (y :: l) = [getLast (y :: l) h]
    · simp [h₁]
      -- 🎉 no goals
    rw [getLast_cons h₁]
    -- ⊢ drop (Nat.add (length l) 0) (y :: l) = [getLast l h₁]
    exact ih h₁ y
    -- 🎉 no goals
#align list.drop_length_cons List.drop_length_cons

/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
theorem drop_append_eq_append_drop {l₁ l₂ : List α} {n : ℕ} :
    drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ := by
  induction l₁ generalizing n; · simp
  -- ⊢ drop n ([] ++ l₂) = drop n [] ++ drop (n - length []) l₂
                                 -- 🎉 no goals
  cases n <;> simp [*]
  -- ⊢ drop zero (head✝ :: tail✝ ++ l₂) = drop zero (head✝ :: tail✝) ++ drop (zero  …
              -- 🎉 no goals
              -- 🎉 no goals
#align list.drop_append_eq_append_drop List.drop_append_eq_append_drop

theorem drop_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, tsub_eq_zero_iff_le.mpr h]
  -- 🎉 no goals
#align list.drop_append_of_le_length List.drop_append_of_le_length

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
theorem drop_append {l₁ l₂ : List α} (i : ℕ) : drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ := by
  rw [drop_append_eq_append_drop, drop_eq_nil_of_le] <;> simp
  -- ⊢ [] ++ drop (length l₁ + i - length l₁) l₂ = drop i l₂
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
#align list.drop_append List.drop_append

theorem drop_sizeOf_le [SizeOf α] (l : List α) : ∀ n : ℕ, sizeOf (l.drop n) ≤ sizeOf l := by
  induction' l with _ _ lih <;> intro n
  -- ⊢ ∀ (n : ℕ), sizeOf (drop n []) ≤ sizeOf []
                                -- ⊢ sizeOf (drop n []) ≤ sizeOf []
                                -- ⊢ sizeOf (drop n (head✝ :: tail✝)) ≤ sizeOf (head✝ :: tail✝)
  · rw [drop_nil]
    -- 🎉 no goals
  · induction' n with n
    -- ⊢ sizeOf (drop zero (head✝ :: tail✝)) ≤ sizeOf (head✝ :: tail✝)
    · rfl
      -- 🎉 no goals
    · exact Trans.trans (lih _) le_add_self
      -- 🎉 no goals
#align list.drop_sizeof_le List.drop_sizeOf_le

set_option linter.deprecated false in -- FIXME
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem get_drop (L : List α) {i j : ℕ} (h : i + j < L.length) :
    get L ⟨i + j, h⟩ = get (L.drop i) ⟨j, by
      have A : i < L.length := lt_of_le_of_lt (Nat.le.intro rfl) h
      -- ⊢ j < length (drop i L)
      rw [(take_append_drop i L).symm] at h
      -- ⊢ j < length (drop i L)
      simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take,
        length_append] using h⟩ := by
  rw [← nthLe_eq, ← nthLe_eq]
  -- ⊢ nthLe L (i + j) h = nthLe (drop i L) j (_ : j < length (drop i L))
  rw [nthLe_of_eq (take_append_drop i L).symm h, nthLe_append_right] <;>
  -- ⊢ nthLe (drop i L) (i + j - length (take i L)) (_ : i + j - length (take i L)  …
  simp [min_eq_left (show i ≤ length L from le_trans (by simp) (le_of_lt h))]
  -- 🎉 no goals
  -- 🎉 no goals

set_option linter.deprecated false in
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
@[deprecated get_drop]
theorem nthLe_drop (L : List α) {i j : ℕ} (h : i + j < L.length) :
    nthLe L (i + j) h = nthLe (L.drop i) j (by
      have A : i < L.length := lt_of_le_of_lt (Nat.le.intro rfl) h
      -- ⊢ j < length (drop i L)
      rw [(take_append_drop i L).symm] at h
      -- ⊢ j < length (drop i L)
      simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take,
        length_append] using h) := get_drop ..
#align list.nth_le_drop List.nthLe_drop

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
theorem get_drop' (L : List α) {i j} :
    get (L.drop i) j = get L ⟨i + j, lt_tsub_iff_left.mp (length_drop i L ▸ j.2)⟩ := by
  rw [get_drop]
  -- 🎉 no goals

set_option linter.deprecated false in
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
@[deprecated get_drop']
theorem nthLe_drop' (L : List α) {i j : ℕ} (h : j < (L.drop i).length) :
    nthLe (L.drop i) j h = nthLe L (i + j) (lt_tsub_iff_left.mp (length_drop i L ▸ h)) :=
  get_drop' ..
#align list.nth_le_drop' List.nthLe_drop'

theorem get?_drop (L : List α) (i j : ℕ) : get? (L.drop i) j = get? L (i + j) := by
  ext
  -- ⊢ a✝ ∈ get? (drop i L) j ↔ a✝ ∈ get? L (i + j)
  simp only [get?_eq_some, get_drop', Option.mem_def]
  -- ⊢ (∃ h, get L { val := i + j, isLt := (_ : i + ↑{ val := j, isLt := (_ : j < l …
  constructor <;> exact fun ⟨h, ha⟩ => ⟨by simpa [lt_tsub_iff_left] using h, ha⟩
  -- ⊢ (∃ h, get L { val := i + j, isLt := (_ : i + ↑{ val := j, isLt := (_ : j < l …
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.nth_drop List.get?_drop

@[simp]
theorem drop_drop (n : ℕ) : ∀ (m) (l : List α), drop n (drop m l) = drop (n + m) l
  | m, [] => by simp
                -- 🎉 no goals
  | 0, l => by simp
               -- 🎉 no goals
  | m + 1, a :: l =>
    calc
      drop n (drop (m + 1) (a :: l)) = drop n (drop m l) := rfl
      _ = drop (n + m) l := drop_drop n m l
      _ = drop (n + (m + 1)) (a :: l) := rfl
#align list.drop_drop List.drop_drop

theorem drop_take : ∀ (m : ℕ) (n : ℕ) (l : List α), drop m (take (m + n) l) = take n (drop m l)
  | 0, n, _ => by simp
                  -- 🎉 no goals
  | m + 1, n, nil => by simp
                        -- 🎉 no goals
  | m + 1, n, _ :: l => by
    have h : m + 1 + n = m + n + 1 := by ac_rfl
    -- ⊢ drop (m + 1) (take (m + 1 + n) (head✝ :: l)) = take n (drop (m + 1) (head✝ : …
    simpa [take_cons, h] using drop_take m n l
    -- 🎉 no goals
#align list.drop_take List.drop_take

theorem map_drop {α β : Type*} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.drop i).map f = (L.map f).drop i
  | [], i => by simp
                -- 🎉 no goals
  | L, 0 => by simp
               -- 🎉 no goals
  | h :: t, n + 1 => by
    dsimp
    -- ⊢ map f (drop n t) = drop n (map f t)
    rw [map_drop f t]
    -- 🎉 no goals
#align list.map_drop List.map_drop

theorem modifyNthTail_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ n l, modifyNthTail f n l = take n l ++ f (drop n l)
  | 0, _ => rfl
  | _ + 1, [] => H.symm
  | n + 1, b :: l => congr_arg (cons b) (modifyNthTail_eq_take_drop f H n l)
#align list.modify_nth_tail_eq_take_drop List.modifyNthTail_eq_take_drop

theorem modifyNth_eq_take_drop (f : α → α) :
    ∀ n l, modifyNth f n l = take n l ++ modifyHead f (drop n l) :=
  modifyNthTail_eq_take_drop _ rfl
#align list.modify_nth_eq_take_drop List.modifyNth_eq_take_drop

theorem modifyNth_eq_take_cons_drop (f : α → α) {n l} (h) :
    modifyNth f n l = take n l ++ f (get l ⟨n, h⟩) :: drop (n + 1) l := by
  rw [modifyNth_eq_take_drop, drop_eq_get_cons h]; rfl
  -- ⊢ take n l ++ modifyHead f (get l { val := n, isLt := h } :: drop (n + 1) l) = …
                                                   -- 🎉 no goals
#align list.modify_nth_eq_take_cons_drop List.modifyNth_eq_take_cons_drop

theorem set_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
    set l n a = take n l ++ a :: drop (n + 1) l := by
  rw [set_eq_modifyNth, modifyNth_eq_take_cons_drop _ h]
  -- 🎉 no goals
#align list.update_nth_eq_take_cons_drop List.set_eq_take_cons_drop

theorem reverse_take {α} {xs : List α} (n : ℕ) (h : n ≤ xs.length) :
    xs.reverse.take n = (xs.drop (xs.length - n)).reverse := by
  induction' xs with xs_hd xs_tl xs_ih generalizing n <;>
  -- ⊢ take n (reverse []) = reverse (drop (length [] - n) [])
    simp only [reverse_cons, drop, reverse_nil, zero_tsub, length, take_nil]
    -- 🎉 no goals
    -- ⊢ take n (reverse xs_tl ++ [xs_hd]) = reverse (drop (length xs_tl + 1 - n) (xs …
  cases' h.lt_or_eq_dec with h' h'
  -- ⊢ take n (reverse xs_tl ++ [xs_hd]) = reverse (drop (length xs_tl + 1 - n) (xs …
  · replace h' := le_of_succ_le_succ h'
    -- ⊢ take n (reverse xs_tl ++ [xs_hd]) = reverse (drop (length xs_tl + 1 - n) (xs …
    rw [take_append_of_le_length, xs_ih _ h']
    -- ⊢ reverse (drop (length xs_tl - n) xs_tl) = reverse (drop (length xs_tl + 1 -  …
    rw [show xs_tl.length + 1 - n = succ (xs_tl.length - n) from _, drop]
    -- ⊢ length xs_tl + 1 - n = succ (length xs_tl - n)
    · rwa [succ_eq_add_one, ← @tsub_add_eq_add_tsub]
      -- 🎉 no goals
    · rwa [length_reverse]
      -- 🎉 no goals
  · subst h'
    -- ⊢ take (length (xs_hd :: xs_tl)) (reverse xs_tl ++ [xs_hd]) = reverse (drop (l …
    rw [length, tsub_self, drop]
    -- ⊢ take (length xs_tl + 1) (reverse xs_tl ++ [xs_hd]) = reverse (xs_hd :: xs_tl)
    suffices xs_tl.length + 1 = (xs_tl.reverse ++ [xs_hd]).length by
      rw [this, take_length, reverse_cons]
    rw [length_append, length_reverse]
    -- ⊢ length xs_tl + 1 = length xs_tl + length [xs_hd]
    rfl
    -- 🎉 no goals
#align list.reverse_take List.reverse_take

@[simp]
theorem set_eq_nil (l : List α) (n : ℕ) (a : α) : l.set n a = [] ↔ l = [] := by
  cases l <;> cases n <;> simp only [set]
  -- ⊢ set [] n a = [] ↔ [] = []
              -- ⊢ set [] zero a = [] ↔ [] = []
              -- ⊢ set (head✝ :: tail✝) zero a = [] ↔ head✝ :: tail✝ = []
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
#align list.update_nth_eq_nil List.set_eq_nil

section TakeI

variable [Inhabited α]

@[simp]
theorem takeI_length : ∀ n l, length (@takeI α _ n l) = n
  | 0, _ => rfl
  | _ + 1, _ => congr_arg succ (takeI_length _ _)
#align list.take'_length List.takeI_length

@[simp]
theorem takeI_nil : ∀ n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | _ + 1 => congr_arg (cons _) (takeI_nil _)
#align list.take'_nil List.takeI_nil

theorem takeI_eq_take : ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l
  | 0, _, _ => rfl
  | _ + 1, _ :: _, h => congr_arg (cons _) <| takeI_eq_take <| le_of_succ_le_succ h
#align list.take'_eq_take List.takeI_eq_take

@[simp]
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)
                     -- 🎉 no goals
#align list.take'_left List.takeI_left

theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply takeI_left
  -- ⊢ takeI (length l₁) (l₁ ++ l₂) = l₁
            -- 🎉 no goals
#align list.take'_left' List.takeI_left'

end TakeI

/- Porting note: in mathlib3 we just had `take` and `take'`. Now we have `take`, `takeI`, and
  `takeD`. The following section replicates the theorems above but for `takeD`. -/
section TakeD

@[simp]
theorem takeD_length : ∀ n l a, length (@takeD α n l a) = n
  | 0, _, _ => rfl
  | _ + 1, _, _ => congr_arg succ (takeD_length _ _ _)

-- Porting note: `takeD_nil` is already in std

theorem takeD_eq_take : ∀ {n} {l : List α} a, n ≤ length l → takeD n l a = take n l
  | 0, _, _, _ => rfl
  | _ + 1, _ :: _, a, h => congr_arg (cons _) <| takeD_eq_take a <| le_of_succ_le_succ h

@[simp]
theorem takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁ :=
  (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)
                       -- 🎉 no goals

theorem takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ l₂) a = l₁ :=
  by rw [← h]; apply takeD_left
     -- ⊢ takeD (length l₁) (l₁ ++ l₂) a = l₁
               -- 🎉 no goals

end TakeD

/-! ### foldl, foldr -/

theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
    foldl f a l = foldl g a l := by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin, H a hd (mem_cons_self _ _)]
#align list.foldl_ext List.foldl_ext

theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction' l with hd tl ih; · rfl
  -- ⊢ foldr f b [] = foldr g b []
                                -- 🎉 no goals
  simp only [mem_cons, or_imp, forall_and, forall_eq] at H
  -- ⊢ foldr f b (hd :: tl) = foldr g b (hd :: tl)
  simp only [foldr, ih H.2, H.1]
  -- 🎉 no goals
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

theorem foldl_concat
    (f : β → α → β) (b : β) (x : α) (xs : List α) :
    List.foldl f b (xs ++ [x]) = f (List.foldl f b xs) x := by
  simp only [List.foldl_append, List.foldl]
  -- 🎉 no goals

theorem foldr_concat
    (f : α → β → β) (b : β) (x : α) (xs : List α) :
    List.foldr f b (xs ++ [x]) = (List.foldr f (f x b) xs) := by
  simp only [List.foldr_append, List.foldr]
  -- 🎉 no goals

theorem foldl_fixed' {f : α → β → α} {a : α} (hf : ∀ b, f a b = a) : ∀ l : List β, foldl f a l = a
  | [] => rfl
  | b :: l => by rw [foldl_cons, hf b, foldl_fixed' hf l]
                 -- 🎉 no goals
#align list.foldl_fixed' List.foldl_fixed'

theorem foldr_fixed' {f : α → β → β} {b : β} (hf : ∀ a, f a b = b) : ∀ l : List α, foldr f b l = b
  | [] => rfl
  | a :: l => by rw [foldr_cons, foldr_fixed' hf l, hf a]
                 -- 🎉 no goals
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
  | a, l :: L => by simp only [join, foldl_append, foldl_cons, foldl_join f (foldl f a l) L]
                    -- 🎉 no goals
#align list.foldl_join List.foldl_join

@[simp]
theorem foldr_join (f : α → β → β) :
    ∀ (b : β) (L : List (List α)), foldr f b (join L) = foldr (fun l b => foldr f b l) b L
  | a, [] => rfl
  | a, l :: L => by simp only [join, foldr_append, foldr_join f a L, foldr_cons]
                    -- 🎉 no goals
#align list.foldr_join List.foldr_join

#align list.foldl_reverse List.foldl_reverse

#align list.foldr_reverse List.foldr_reverse

-- Porting note: simp can prove this
-- @[simp]
theorem foldr_eta : ∀ l : List α, foldr cons [] l = l :=
  by simp only [foldr_self_append, append_nil, forall_const]
     -- 🎉 no goals
#align list.foldr_eta List.foldr_eta

@[simp]
theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  rw [← foldr_reverse]; simp only [foldr_self_append, append_nil, reverse_reverse]
  -- ⊢ reverse (foldr (fun h t => h :: t) [] (reverse l)) = l
                        -- 🎉 no goals
#align list.reverse_foldl List.reverse_foldl

#align list.foldl_map List.foldl_map

#align list.foldr_map List.foldr_map

theorem foldl_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldl f' (g a) (l.map g) = g (List.foldl f a l) := by
  induction l generalizing a
  -- ⊢ foldl f' (g a) (map g []) = g (foldl f a [])
  · simp
    -- 🎉 no goals
  · simp [*, h]
    -- 🎉 no goals
#align list.foldl_map' List.foldl_map'

theorem foldr_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldr f' (g a) (l.map g) = g (List.foldr f a l) := by
  induction l generalizing a
  -- ⊢ foldr f' (g a) (map g []) = g (foldr f a [])
  · simp
    -- 🎉 no goals
  · simp [*, h]
    -- 🎉 no goals
#align list.foldr_map' List.foldr_map'

#align list.foldl_hom List.foldl_hom

#align list.foldr_hom List.foldr_hom

theorem foldl_hom₂ (l : List ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β)
    (op₃ : γ → ι → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
    foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
  Eq.symm <| by
    revert a b
    -- ⊢ ∀ (a : α) (b : β), f (foldl op₁ a l) (foldl op₂ b l) = foldl op₃ (f a b) l
    induction l <;> intros <;> [rfl; simp only [*, foldl]]
    -- 🎉 no goals
#align list.foldl_hom₂ List.foldl_hom₂

theorem foldr_hom₂ (l : List ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β)
    (op₃ : ι → γ → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
    foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) := by
  revert a
  -- ⊢ ∀ (a : α), foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l)
  induction l <;> intros <;> [rfl; simp only [*, foldr]]
  -- 🎉 no goals
#align list.foldr_hom₂ List.foldr_hom₂

theorem injective_foldl_comp {α : Type*} {l : List (α → α)} {f : α → α}
    (hl : ∀ f ∈ l, Function.Injective f) (hf : Function.Injective f) :
    Function.Injective (@List.foldl (α → α) (α → α) Function.comp f l) := by
  induction' l with lh lt l_ih generalizing f
  -- ⊢ Injective (foldl comp f [])
  · exact hf
    -- 🎉 no goals
  · apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    -- ⊢ Injective (f ∘ lh)
    apply Function.Injective.comp hf
    -- ⊢ Injective lh
    apply hl _ (List.mem_cons_self _ _)
    -- 🎉 no goals
#align list.injective_foldl_comp List.injective_foldl_comp

/- Porting note: couldn't do induction proof because "code generator does not support recursor
  'List.rec' yet". Earlier proof:

  induction l with
  | nil => exact hb
  | cons hd tl IH =>
    refine' hl _ _ hd (mem_cons_self hd tl)
    refine' IH _
    intro y hy x hx
    exact hl y hy x (mem_cons_of_mem hd hx)
-/
/-- Induction principle for values produced by a `foldr`: if a property holds
for the seed element `b : β` and for all incremental `op : α → β → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldrRecOn {C : β → Sort*} (l : List α) (op : α → β → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ l), C (op a b)) : C (foldr op b l) := by
  cases l with
  | nil => exact hb
  | cons hd tl =>
    have IH : ((b : β) → C b → (a : α) → a ∈ tl → C (op a b)) → C (foldr op b tl) :=
      foldrRecOn _ _ _ hb
    refine' hl _ _ hd (mem_cons_self hd tl)
    refine' IH _
    intro y hy x hx
    exact hl y hy x (mem_cons_of_mem hd hx)
#align list.foldr_rec_on List.foldrRecOn

/- Porting note: couldn't do induction proof because "code generator does not support recursor
  'List.rec' yet". Earlier proof:

  induction l generalizing b with
  | nil => exact hb
  | cons hd tl IH =>
    refine' IH _ _ _
    · exact hl b hb hd (mem_cons_self hd tl)
    · intro y hy x hx
      exact hl y hy x (mem_cons_of_mem hd hx)
-/
/-- Induction principle for values produced by a `foldl`: if a property holds
for the seed element `b : β` and for all incremental `op : β → α → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldlRecOn {C : β → Sort*} (l : List α) (op : β → α → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ l), C (op b a)) : C (foldl op b l) := by
  cases l with
  | nil => exact hb
  | cons hd tl =>
    have IH : (b : β) → C b → ((b : β) → C b → (a : α) → a ∈ tl → C (op b a)) → C (foldl op b tl) :=
      foldlRecOn _ _
    refine' IH _ _ _
    · exact hl b hb hd (mem_cons_self hd tl)
    · intro y hy x hx
      exact hl y hy x (mem_cons_of_mem hd hx)
#align list.foldl_rec_on List.foldlRecOn

@[simp]
theorem foldrRecOn_nil {C : β → Sort*} (op : α → β → β) (b) (hb : C b) (hl) :
    foldrRecOn [] op b hb hl = hb :=
  rfl
#align list.foldr_rec_on_nil List.foldrRecOn_nil

@[simp]
theorem foldrRecOn_cons {C : β → Sort*} (x : α) (l : List α) (op : α → β → β) (b) (hb : C b)
    (hl : ∀ (b : β) (_ : C b) (a : α) (_ : a ∈ x :: l), C (op a b)) :
    foldrRecOn (x :: l) op b hb hl =
      hl _ (foldrRecOn l op b hb fun b hb a ha => hl b hb a (mem_cons_of_mem _ ha)) x
        (mem_cons_self _ _) :=
  rfl
#align list.foldr_rec_on_cons List.foldrRecOn_cons

@[simp]
theorem foldlRecOn_nil {C : β → Sort*} (op : β → α → β) (b) (hb : C b) (hl) :
    foldlRecOn [] op b hb hl = hb :=
  rfl
#align list.foldl_rec_on_nil List.foldlRecOn_nil

section Scanl

variable {f : β → α → β} {b : β} {a : α} {l : List α}

theorem length_scanl : ∀ a l, length (scanl f a l) = l.length + 1
  | a, [] => rfl
  | a, x :: l => by
    rw [scanl, length_cons, length_cons, ←succ_eq_add_one, congr_arg succ]
    -- ⊢ length (scanl f (f a x) l) = length l + 1
    exact length_scanl _ _
    -- 🎉 no goals
#align list.length_scanl List.length_scanl

@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl
#align list.scanl_nil List.scanl_nil

@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := by
  simp only [scanl, eq_self_iff_true, singleton_append, and_self_iff]
  -- 🎉 no goals
#align list.scanl_cons List.scanl_cons

@[simp]
theorem get?_zero_scanl : (scanl f b l).get? 0 = some b := by
  cases l
  -- ⊢ get? (scanl f b []) 0 = some b
  · simp only [get?, scanl_nil]
    -- 🎉 no goals
  · simp only [get?, scanl_cons, singleton_append]
    -- 🎉 no goals
#align list.nth_zero_scanl List.get?_zero_scanl

@[simp]
theorem get_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).get ⟨0, h⟩ = b := by
  cases l
  -- ⊢ get (scanl f b []) { val := 0, isLt := h } = b
  · simp only [get, scanl_nil]
    -- 🎉 no goals
  · simp only [get, scanl_cons, singleton_append]
    -- 🎉 no goals

set_option linter.deprecated false in
@[simp, deprecated get_zero_scanl]
theorem nthLe_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).nthLe 0 h = b :=
  get_zero_scanl
#align list.nth_le_zero_scanl List.nthLe_zero_scanl

theorem get?_succ_scanl {i : ℕ} : (scanl f b l).get? (i + 1) =
    ((scanl f b l).get? i).bind fun x => (l.get? i).map fun y => f x y := by
  induction' l with hd tl hl generalizing b i
  -- ⊢ get? (scanl f b []) (i + 1) = Option.bind (get? (scanl f b []) i) fun x => O …
  · symm
    -- ⊢ (Option.bind (get? (scanl f b []) i) fun x => Option.map (fun y => f x y) (g …
    simp only [Option.bind_eq_none', get?, forall₂_true_iff, not_false_iff, Option.map_none',
      scanl_nil, Option.not_mem_none, forall_true_iff]
  · simp only [scanl_cons, singleton_append]
    -- ⊢ get? (b :: scanl f (f b hd) tl) (i + 1) = Option.bind (get? (b :: scanl f (f …
    cases i
    -- ⊢ get? (b :: scanl f (f b hd) tl) (zero + 1) = Option.bind (get? (b :: scanl f …
    · simp only [Option.map_some', get?_zero_scanl, get?, Option.some_bind']
      -- 🎉 no goals
    · simp only [hl, get?]
      -- 🎉 no goals
#align list.nth_succ_scanl List.get?_succ_scanl

set_option linter.deprecated false in
theorem nthLe_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
    (scanl f b l).nthLe (i + 1) h =
      f ((scanl f b l).nthLe i (Nat.lt_of_succ_lt h))
        (l.nthLe i (Nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l))))) := by
  induction i generalizing b l with
  | zero =>
    cases l
    · simp only [length, zero_add, scanl_nil] at h
    · simp [scanl_cons, singleton_append, nthLe_zero_scanl, nthLe_cons]
  | succ i hi =>
    cases l
    · simp only [length, add_lt_iff_neg_right, scanl_nil] at h
      exact absurd h (not_lt_of_lt Nat.succ_pos')
    · simp_rw [scanl_cons]
      rw [nthLe_append_right]
      · simp only [length, zero_add 1, succ_add_sub_one, hi]; rfl
      · simp only [length, Nat.zero_le, le_add_iff_nonneg_left]
#align list.nth_le_succ_scanl List.nthLe_succ_scanl

theorem get_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
    (scanl f b l).get ⟨i + 1, h⟩ =
      f ((scanl f b l).get ⟨i, Nat.lt_of_succ_lt h⟩)
        (l.get ⟨i, Nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l)))⟩) :=
  nthLe_succ_scanl

-- FIXME: we should do the proof the other way around
attribute [deprecated get_succ_scanl] nthLe_succ_scanl

end Scanl

-- scanr
@[simp]
theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl
#align list.scanr_nil List.scanr_nil

#noalign list.scanr_aux_cons

@[simp]
theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, foldr, cons.injEq, and_true]
  -- ⊢ f a (foldr (fun a x => (f a x.fst, x.fst :: x.snd)) (b, []) l).fst = f a (fo …
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih => simp only [foldr, ih]
#align list.scanr_cons List.scanr_cons

section FoldlEqFoldr

-- foldl and foldr coincide when f is commutative and associative
variable {f : α → α → α} (hcomm : Commutative f) (hassoc : Associative f)

theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l ++ [b]) = foldr f b (a :: l)
  | a, b, nil => rfl
  | a, b, c :: l => by
    simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l]; rw [hassoc]
    -- ⊢ f (f a c) (foldr f b l) = f a (f c (foldr f b l))
                                                                             -- 🎉 no goals
#align list.foldl1_eq_foldr1 List.foldl1_eq_foldr1

theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b :: l) = f b (foldl f a l)
  | a, b, nil => hcomm a b
  | a, b, c :: l => by
    simp only [foldl_cons]
    -- ⊢ foldl f (f (f a b) c) l = f b (foldl f (f a c) l)
    rw [← foldl_eq_of_comm_of_assoc .., right_comm _ hcomm hassoc]; rfl
    -- ⊢ foldl f (f (f a c) b) l = foldl f (f a c) (b :: l)
                                                                    -- 🎉 no goals
#align list.foldl_eq_of_comm_of_assoc List.foldl_eq_of_comm_of_assoc

theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a, nil => rfl
  | a, b :: l => by
    simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc]; rw [foldl_eq_foldr a l]
    -- ⊢ f b (foldl f a l) = f b (foldr f a l)
                                                                    -- 🎉 no goals
#align list.foldl_eq_foldr List.foldl_eq_foldr

end FoldlEqFoldr

section FoldlEqFoldlr'

variable {f : α → β → α}

variable (hf : ∀ a b c, f (f a b) c = f (f a c) b)

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b :: l) = f (foldl f a l) b
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldl, foldl, foldl, ← foldl_eq_of_comm' .., foldl, hf]
                       -- 🎉 no goals
#align list.foldl_eq_of_comm' List.foldl_eq_of_comm'

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
  | a, [] => rfl
  | a, b :: l => by rw [foldl_eq_of_comm' hf, foldr, foldl_eq_foldr' ..]; rfl
                    -- ⊢ f (foldr (flip f) a l) b = flip f b (foldr (flip f) a l)
                                                                          -- 🎉 no goals
#align list.foldl_eq_foldr' List.foldl_eq_foldr'

end FoldlEqFoldlr'

section FoldlEqFoldlr'

variable {f : α → β → β}

variable (hf : ∀ a b c, f a (f b c) = f b (f a c))

theorem foldr_eq_of_comm' : ∀ a b l, foldr f a (b :: l) = foldr f (f b a) l
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldr, foldr, foldr, hf, ← foldr_eq_of_comm' ..]; rfl
                       -- ⊢ f c (f b (foldr f a l)) = f c (foldr f a (b :: l))
                                                                             -- 🎉 no goals
#align list.foldr_eq_of_comm' List.foldr_eq_of_comm'

end FoldlEqFoldlr'

section

variable {op : α → α → α} [ha : IsAssociative α op] [hc : IsCommutative α op]

/-- Notation for `op a b`. -/
local notation a " ⋆ " b => op a b

/-- Notation for `foldl op a l`. -/
local notation l " <*> " a => foldl op a l

theorem foldl_assoc : ∀ {l : List α} {a₁ a₂}, (l <*> a₁ ⋆ a₂) = a₁ ⋆ l <*> a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ =>
    calc
      ((a :: l) <*> a₁ ⋆ a₂) = l <*> a₁ ⋆ a₂ ⋆ a := by simp only [foldl_cons, ha.assoc]
                                                       -- 🎉 no goals
      _ = a₁ ⋆ (a :: l) <*> a₂ := by rw [foldl_assoc, foldl_cons]
                                     -- 🎉 no goals
#align list.foldl_assoc List.foldl_assoc

theorem foldl_op_eq_op_foldr_assoc :
    ∀ {l : List α} {a₁ a₂}, ((l <*> a₁) ⋆ a₂) = a₁ ⋆ l.foldr (· ⋆ ·) a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ => by
    simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc]; rw [foldl_op_eq_op_foldr_assoc]
    -- ⊢ op a₁ (op (l <*> a) a₂) = op a₁ (op a (foldr (fun x x_1 => op x x_1) a₂ l))
                                                               -- 🎉 no goals
#align list.foldl_op_eq_op_foldr_assoc List.foldl_op_eq_op_foldr_assoc

theorem foldl_assoc_comm_cons {l : List α} {a₁ a₂} : ((a₁ :: l) <*> a₂) = a₁ ⋆ l <*> a₂ := by
  rw [foldl_cons, hc.comm, foldl_assoc]
  -- 🎉 no goals
#align list.foldl_assoc_comm_cons List.foldl_assoc_comm_cons

end

/-! ### foldlM, foldrM, mapM -/

section FoldlMFoldrM

variable {m : Type v → Type w} [Monad m]

@[simp]
theorem foldlM_nil (f : β → α → m β) {b} : List.foldlM f b [] = pure b :=
  rfl
#align list.mfoldl_nil List.foldlM_nil

-- Porting note: now in std
#align list.mfoldr_nil List.foldrM_nil

@[simp]
theorem foldlM_cons {f : β → α → m β} {b a l} :
    List.foldlM f b (a :: l) = f b a >>= fun b' => List.foldlM f b' l :=
  rfl
#align list.mfoldl_cons List.foldlM_cons

/- Porting note: now in std; now assumes an instance of `LawfulMonad m`, so we make everything
  `foldrM_eq_foldr` depend on one as well. (An instance of `LawfulMonad m` was already present for
  everything following; this just moves it a few lines up.) -/
#align list.mfoldr_cons List.foldrM_cons

variable [LawfulMonad m]

theorem foldrM_eq_foldr (f : α → β → m β) (b l) :
    foldrM f b l = foldr (fun a mb => mb >>= f a) (pure b) l := by induction l <;> simp [*]
                                                                   -- ⊢ foldrM f b [] = foldr (fun a mb => mb >>= f a) (pure b) []
                                                                                   -- 🎉 no goals
                                                                                   -- 🎉 no goals
#align list.mfoldr_eq_foldr List.foldrM_eq_foldr

attribute [simp] mapM mapM'

theorem foldlM_eq_foldl (f : β → α → m β) (b l) :
    List.foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l := by
  suffices h :
    ∀ mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
  · simp [← h (pure b)]
    -- 🎉 no goals
  induction l with
  | nil => intro; simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ←l_ih, functor_norm]
#align list.mfoldl_eq_foldl List.foldlM_eq_foldl

-- Porting note: now in std
#align list.mfoldl_append List.foldlM_append

--Porting note: now in std
#align list.mfoldr_append List.foldrM_append

end FoldlMFoldrM

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

/-! ### splitAt and splitOn -/

section SplitAtOn

/- Porting note: the new version of `splitOnP` uses a `Bool`-valued predicate instead of a
  `Prop`-valued one. All downstream definitions have been updated to match. -/

variable (p : α → Bool) (xs ys : List α) (ls : List (List α)) (f : List α → List α)

/- Porting note: this had to be rewritten because of the new implementation of `splitAt`. It's
  long in large part because `splitAt.go` (`splitAt`'s auxiliary function) works differently
  in the case where n ≥ length l, requiring two separate cases (and two separate inductions). Still,
  this can hopefully be golfed. -/

@[simp]
theorem splitAt_eq_take_drop (n : ℕ) (l : List α) : splitAt n l = (take n l, drop n l) := by
  by_cases h : n < l.length <;> rw [splitAt, go_eq_take_drop]
  -- ⊢ splitAt n l = (take n l, drop n l)
                                -- ⊢ (if n < length l then (Array.toList #[] ++ take n l, drop n l) else (l, [])) …
                                -- ⊢ (if n < length l then (Array.toList #[] ++ take n l, drop n l) else (l, [])) …
  · rw [if_pos h]; rfl
    -- ⊢ (Array.toList #[] ++ take n l, drop n l) = (take n l, drop n l)
                   -- 🎉 no goals
    -- ⊢ splitAt.go l xs n acc = (Array.toList acc ++ take n xs, drop n xs)
  · rw [if_neg h, take_all_of_le <| le_of_not_lt h, drop_eq_nil_of_le <| le_of_not_lt h]
    -- 🎉 no goals
where
  go_eq_take_drop (n : ℕ) (l xs : List α) (acc : Array α) : splitAt.go l xs n acc =
      if n < xs.length then (acc.toList ++ take n xs, drop n xs) else (l, []) := by
    split_ifs with h
    · induction n generalizing xs acc with
      | zero =>
        rw [splitAt.go, take, drop, append_nil]
        · intros h₁; rw [h₁] at h; contradiction
        · intros; contradiction
      | succ _ ih =>
        cases xs with
        | nil => contradiction
        | cons hd tl =>
          rw [length, succ_eq_add_one] at h
          rw [splitAt.go, take, drop, append_cons, Array.toList_eq, ←Array.push_data,
            ←Array.toList_eq]
          exact ih _ _ <| lt_of_add_lt_add_right h
    · induction n generalizing xs acc with
      | zero =>
        rw [zero_eq, not_lt, nonpos_iff_eq_zero] at h
        rw [eq_nil_of_length_eq_zero h, splitAt.go]
      | succ _ ih =>
        cases xs with
        | nil => rw [splitAt.go]
        | cons hd tl =>
          rw [length, succ_eq_add_one] at h
          rw [splitAt.go]
          exact ih _ _ <| not_imp_not.mpr (Nat.add_lt_add_right · 1) h
#align list.split_at_eq_take_drop List.splitAt_eq_take_drop

@[simp]
theorem splitOn_nil {α : Type u} [DecidableEq α] (a : α) : [].splitOn a = [[]] :=
  rfl
#align list.split_on_nil List.splitOn_nil

@[simp]
theorem splitOnP_nil : [].splitOnP p = [[]] :=
  rfl
#align list.split_on_p_nil List.splitOnP_nilₓ

/- Porting note: `split_on_p_aux` and `split_on_p_aux'` were used to prove facts about
  `split_on_p`. `splitOnP` has a different structure, and we need different facts about
  `splitOnP.go`. Theorems involving `split_on_p_aux` have been omitted where possible. -/

#noalign list.split_on_p_aux_ne_nil
#noalign list.split_on_p_aux_spec
#noalign list.split_on_p_aux'
#noalign list.split_on_p_aux_eq
#noalign list.split_on_p_aux_nil

theorem splitOnP.go_ne_nil (xs acc : List α) : splitOnP.go p xs acc ≠ [] := by
  induction xs generalizing acc <;> simp [go]; split <;> simp [*]
  -- ⊢ go p [] acc ≠ []
                                    -- 🎉 no goals
                                    -- ⊢ ¬(if p head✝ = true then reverse acc :: go p tail✝ [] else go p tail✝ (head✝ …
                                               -- ⊢ ¬False
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals

theorem splitOnP.go_acc (xs acc : List α) :
    splitOnP.go p xs acc = modifyHead (acc.reverse ++ ·) (splitOnP p xs) := by
  induction xs generalizing acc with
  | nil => simp only [go, modifyHead, splitOnP_nil, append_nil]
  | cons hd tl ih =>
    simp only [splitOnP, go]; split
    · simp only [modifyHead, reverse_nil, append_nil]
    · rw [ih [hd], modifyHead_modifyHead, ih]
      congr; funext x; simp only [reverse_cons, append_assoc]; rfl

theorem splitOnP_ne_nil (xs : List α) : xs.splitOnP p ≠ [] := splitOnP.go_ne_nil _ _ _
#align list.split_on_p_ne_nil List.splitOnP_ne_nilₓ

@[simp]
theorem splitOnP_cons (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) := by
  rw [splitOnP, splitOnP.go]; split <;> [rfl; simp [splitOnP.go_acc]]
  -- ⊢ (if p x = true then reverse [] :: splitOnP.go p xs [] else splitOnP.go p xs  …
                              -- 🎉 no goals
#align list.split_on_p_cons List.splitOnP_consₓ

/-- The original list `L` can be recovered by joining the lists produced by `splitOnP p L`,
interspersed with the elements `L.filter p`. -/
theorem splitOnP_spec (as : List α) :
    join (zipWith (· ++ ·) (splitOnP p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    rw [splitOnP_cons, filter]
    by_cases h : p a
    · rw [if_pos h, h, map, cons_append, zipWith, nil_append, join, cons_append, cons_inj]
      exact ih
    · rw [if_neg h, eq_false_of_ne_true h, join_zipWith (splitOnP_ne_nil _ _)
        (append_ne_nil_of_ne_nil_right _ [[]] (cons_ne_nil [] [])), cons_inj]
      exact ih
where
  join_zipWith {xs ys : List (List α)} {a : α} (hxs : xs ≠ []) (hys : ys ≠ []) :
      join (zipWith (fun x x_1 ↦ x ++ x_1) (modifyHead (cons a) xs) ys) =
        a :: join (zipWith (fun x x_1 ↦ x ++ x_1) xs ys) := by
    cases xs with | nil => contradiction | cons =>
      cases ys with | nil => contradiction | cons => rfl
#align list.split_on_p_spec List.splitOnP_specₓ

/-- If no element satisfies `p` in the list `xs`, then `xs.splitOnP p = [xs]` -/
theorem splitOnP_eq_single (h : ∀ x ∈ xs, ¬p x) : xs.splitOnP p = [xs] := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [splitOnP_cons, h hd (mem_cons_self hd tl), if_neg]
    rw [ih <| forall_mem_of_forall_mem_cons h]
    rfl
#align list.split_on_p_eq_single List.splitOnP_eq_singleₓ

/-- When a list of the form `[...xs, sep, ...as]` is split on `p`, the first element is `xs`,
  assuming no element in `xs` satisfies `p` but `sep` does satisfy `p` -/
theorem splitOnP_first (h : ∀ x ∈ xs, ¬p x) (sep : α) (hsep : p sep) (as : List α) :
    (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p := by
  induction xs with
  | nil => simp [hsep]
  | cons hd tl ih => simp [h hd _, ih <| forall_mem_of_forall_mem_cons h]
#align list.split_on_p_first List.splitOnP_firstₓ

/-- `intercalate [x]` is the left inverse of `splitOn x`  -/
theorem intercalate_splitOn (x : α) [DecidableEq α] : [x].intercalate (xs.splitOn x) = xs := by
  simp only [intercalate, splitOn]
  -- ⊢ join (intersperse [x] (splitOnP (fun x_1 => x_1 == x) xs)) = xs
  induction' xs with hd tl ih; · simp [join]
  -- ⊢ join (intersperse [x] (splitOnP (fun x_1 => x_1 == x) [])) = []
                                 -- 🎉 no goals
  cases' h' : splitOnP (· == x) tl with hd' tl'; · exact (splitOnP_ne_nil _ tl h').elim
  -- ⊢ join (intersperse [x] (splitOnP (fun x_1 => x_1 == x) (hd :: tl))) = hd :: tl
                                                   -- 🎉 no goals
  rw [h'] at ih
  -- ⊢ join (intersperse [x] (splitOnP (fun x_1 => x_1 == x) (hd :: tl))) = hd :: tl
  rw [splitOnP_cons]
  -- ⊢ join (intersperse [x] (if (hd == x) = true then [] :: splitOnP (fun x_1 => x …
  split_ifs with h
  -- ⊢ join (intersperse [x] ([] :: splitOnP (fun x_1 => x_1 == x) tl)) = hd :: tl
  · rw [beq_iff_eq] at h
    -- ⊢ join (intersperse [x] ([] :: splitOnP (fun x_1 => x_1 == x) tl)) = hd :: tl
    subst h
    -- ⊢ join (intersperse [hd] ([] :: splitOnP (fun x => x == hd) tl)) = hd :: tl
    simp [ih, join, h']
    -- 🎉 no goals
  cases tl' <;> simpa [join, h'] using ih
  -- ⊢ join (intersperse [x] (modifyHead (cons hd) (splitOnP (fun x_1 => x_1 == x)  …
                -- 🎉 no goals
                -- 🎉 no goals
#align list.intercalate_split_on List.intercalate_splitOn

/-- `splitOn x` is the left inverse of `intercalate [x]`, on the domain
  consisting of each nonempty list of lists `ls` whose elements do not contain `x`  -/
theorem splitOn_intercalate [DecidableEq α] (x : α) (hx : ∀ l ∈ ls, x ∉ l) (hls : ls ≠ []) :
    ([x].intercalate ls).splitOn x = ls := by
  simp only [intercalate]
  -- ⊢ splitOn x (join (intersperse [x] ls)) = ls
  induction' ls with hd tl ih; · contradiction
  -- ⊢ splitOn x (join (intersperse [x] [])) = []
                                 -- 🎉 no goals
  cases tl
  -- ⊢ splitOn x (join (intersperse [x] [hd])) = [hd]
  · suffices hd.splitOn x = [hd] by simpa [join]
    -- ⊢ splitOn x hd = [hd]
    refine' splitOnP_eq_single _ _ _
    -- ⊢ ∀ (x_1 : α), x_1 ∈ hd → ¬(x_1 == x) = true
    intro y hy H
    -- ⊢ False
    rw [eq_of_beq H] at hy
    -- ⊢ False
    refine' hx hd _ hy
    -- ⊢ hd ∈ [hd]
    simp
    -- 🎉 no goals
  · simp only [intersperse_cons_cons, singleton_append, join]
    -- ⊢ splitOn x (hd ++ x :: join (intersperse [x] (head✝ :: tail✝))) = hd :: head✝ …
    specialize ih _ _
    · intro l hl
      -- ⊢ ¬x ∈ l
      apply hx l
      -- ⊢ l ∈ hd :: head✝ :: tail✝
      simp at hl ⊢
      -- ⊢ l = hd ∨ l = head✝ ∨ l ∈ tail✝
      exact Or.inr hl
      -- 🎉 no goals
    · exact List.noConfusion
      -- 🎉 no goals
    have := splitOnP_first (· == x) hd ?h x (beq_self_eq_true _)
    -- ⊢ splitOn x (hd ++ x :: join (intersperse [x] (head✝ :: tail✝))) = hd :: head✝ …
    case h =>
      intro y hy H
      rw [eq_of_beq H] at hy
      exact hx hd (.head _) hy
    simp only [splitOn] at ih ⊢
    -- ⊢ splitOnP (fun x_1 => x_1 == x) (hd ++ x :: join (intersperse [x] (head✝ :: t …
    rw [this, ih]
    -- 🎉 no goals
#align list.split_on_intercalate List.splitOn_intercalate

end SplitAtOn

/- Porting note: new; here tentatively -/
/-! ### modifyLast -/

section ModifyLast

theorem modifyLast.go_append_one (f : α → α) (a : α) (tl : List α) (r : Array α) :
    modifyLast.go f (tl ++ [a]) r = (r.toListAppend <| modifyLast.go f (tl ++ [a]) #[]) := by
  cases tl with
  | nil =>
    simp only [nil_append, modifyLast.go]; rfl
  | cons hd tl =>
    simp only [cons_append]
    rw [modifyLast.go, modifyLast.go]
    case x_3 | x_3 => exact append_ne_nil_of_ne_nil_right tl [a] (cons_ne_nil a [])
    rw [modifyLast.go_append_one _ _ tl _, modifyLast.go_append_one _ _ tl (Array.push #[] hd)]
    simp only [Array.toListAppend_eq, Array.push_data, Array.data_toArray, nil_append, append_assoc]

theorem modifyLast_append_one (f : α → α) (a : α) (l : List α) :
    modifyLast f (l ++ [a]) = l ++ [f a] := by
  cases l with
  | nil =>
    simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq, Array.data_toArray]
  | cons _ tl =>
    simp only [cons_append, modifyLast]
    rw [modifyLast.go]
    case x_3 => exact append_ne_nil_of_ne_nil_right tl [a] (cons_ne_nil a [])
    rw [modifyLast.go_append_one, Array.toListAppend_eq, Array.push_data, Array.data_toArray,
      nil_append, cons_append, nil_append, cons_inj]
    exact modifyLast_append_one _ _ tl

theorem modifyLast_append (f : α → α) (l₁ l₂ : List α) (_ : l₂ ≠ []) :
    modifyLast f (l₁ ++ l₂) = l₁ ++ modifyLast f l₂ := by
  cases l₂ with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil => exact modifyLast_append_one _ hd _
    | cons hd' tl' =>
      rw [append_cons, ←nil_append (hd :: hd' :: tl'), append_cons [], nil_append,
        modifyLast_append _ (l₁ ++ [hd]) (hd' :: tl') _, modifyLast_append _ [hd] (hd' :: tl') _,
        append_assoc]
      all_goals { exact cons_ne_nil _ _ }

end ModifyLast

/-! ### map for partial functions -/

#align list.pmap List.pmap
#align list.attach List.attach

theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) :
    SizeOf.sizeOf x < SizeOf.sizeOf l := by
  induction' l with h t ih <;> cases hx <;> rw [cons.sizeOf_spec]
  -- ⊢ sizeOf x < sizeOf []
                               -- 🎉 no goals
                               -- ⊢ sizeOf x < sizeOf (x :: t)
                                            -- ⊢ sizeOf x < 1 + sizeOf x + sizeOf t
                                            -- ⊢ sizeOf x < 1 + sizeOf h + sizeOf t
  · exact lt_add_of_lt_of_nonneg (lt_one_add _) (Nat.zero_le _)
    -- 🎉 no goals
  · refine lt_add_of_pos_of_le ?_ (le_of_lt (ih ‹_›))
    -- ⊢ 0 < 1 + sizeOf h
    rw [add_comm]; exact succ_pos _
    -- ⊢ 0 < sizeOf h + 1
                   -- 🎉 no goals
#align list.sizeof_lt_sizeof_of_mem List.sizeOf_lt_sizeOf_of_mem

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l <;> [rfl; simp only [*, pmap, map]]
  -- 🎉 no goals
#align list.pmap_eq_map List.pmap_eq_map

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  induction' l with _ _ ih
  -- ⊢ pmap f [] H₁ = pmap g [] H₂
  · rfl
    -- 🎉 no goals
  · rw [pmap, pmap, h _ (mem_cons_self _ _), ih fun a ha => h a (mem_cons_of_mem _ ha)]
    -- 🎉 no goals
#align list.pmap_congr List.pmap_congr

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l <;> [rfl; simp only [*, pmap, map]]
  -- 🎉 no goals
#align list.map_pmap List.map_pmap

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun a h => H _ (mem_map_of_mem _ h) := by
  induction l <;> [rfl; simp only [*, pmap, map]]
  -- 🎉 no goals
#align list.pmap_map List.pmap_map

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, map_pmap]; exact pmap_congr l fun _ _ _ _ => rfl
  -- ⊢ pmap f l H = pmap (fun a h => f ↑{ val := a, property := h } (_ : p ↑{ val : …
                         -- 🎉 no goals
#align list.pmap_eq_map_attach List.pmap_eq_map_attach

-- @[simp] -- Porting note: lean 4 simp can't rewrite with this
theorem attach_map_coe' (l : List α) (f : α → β) :
    (l.attach.map fun (i : {i // i ∈ l}) => f i) = l.map f := by
  rw [attach, map_pmap]; exact pmap_eq_map _ _ _ _
  -- ⊢ pmap (fun a h => f ↑{ val := a, property := h }) l (_ : ∀ (x : α), x ∈ l → x …
                         -- 🎉 no goals
#align list.attach_map_coe' List.attach_map_coe'

theorem attach_map_val' (l : List α) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe' _ _
#align list.attach_map_val' List.attach_map_val'

@[simp]
theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l :=
  (attach_map_coe' _ _).trans l.map_id
-- porting note: coe is expanded eagerly, so "attach_map_coe" would have the same syntactic form.
#align list.attach_map_coe List.attach_map_val
#align list.attach_map_val List.attach_map_val

@[simp]
theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_val] <;> exact h)
    -- ⊢ { val := a, property := h } ∈ attach l
    rcases this with ⟨⟨_, _⟩, m, rfl⟩
    -- ⊢ { val := ↑{ val := val✝, property := property✝ }, property := h } ∈ attach l
    exact m
    -- 🎉 no goals
#align list.mem_attach List.mem_attach

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and_iff, Subtype.exists, eq_comm]
  -- 🎉 no goals
#align list.mem_pmap List.mem_pmap

@[simp]
theorem length_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l <;> [rfl; simp only [*, pmap, length]]
  -- 🎉 no goals
#align list.length_pmap List.length_pmap

@[simp]
theorem length_attach (L : List α) : L.attach.length = L.length :=
  length_pmap
#align list.length_attach List.length_attach

@[simp]
theorem pmap_eq_nil {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] := by
  rw [← length_eq_zero, length_pmap, length_eq_zero]
  -- 🎉 no goals
#align list.pmap_eq_nil List.pmap_eq_nil

@[simp]
theorem attach_eq_nil (l : List α) : l.attach = [] ↔ l = [] :=
  pmap_eq_nil
#align list.attach_eq_nil List.attach_eq_nil

theorem getLast_pmap {α β : Type*} (p : α → Prop) (f : ∀ a, p a → β) (l : List α)
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
    (l.pmap f hl₁).getLast (mt List.pmap_eq_nil.1 hl₂) =
      f (l.getLast hl₂) (hl₁ _ (List.getLast_mem hl₂)) := by
  induction' l with l_hd l_tl l_ih
  -- ⊢ getLast (pmap f [] hl₁) (_ : ¬pmap f [] hl₁ = []) = f (getLast [] hl₂) (_ :  …
  · apply (hl₂ rfl).elim
    -- 🎉 no goals
  · by_cases hl_tl : l_tl = []
    -- ⊢ getLast (pmap f (l_hd :: l_tl) hl₁) (_ : ¬pmap f (l_hd :: l_tl) hl₁ = []) =  …
    · simp [hl_tl]
      -- 🎉 no goals
    · simp only [pmap]
      -- ⊢ getLast (f l_hd (_ : p l_hd) :: pmap f l_tl (_ : ∀ (x : α), x ∈ l_tl → p x)) …
      rw [getLast_cons, l_ih _ hl_tl]
      -- ⊢ f (getLast l_tl hl_tl) (_ : p (getLast l_tl hl_tl)) = f (getLast (l_hd :: l_ …
      simp only [getLast_cons hl_tl]
      -- 🎉 no goals
#align list.last_pmap List.getLast_pmap

theorem get?_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) (n : ℕ) :
    get? (pmap f l h) n = Option.pmap f (get? l n) fun x H => h x (get?_mem H) := by
  induction' l with hd tl hl generalizing n
  -- ⊢ get? (pmap f [] h) n = Option.pmap f (get? [] n) (_ : ∀ (x : α), x ∈ get? [] …
  · simp
    -- 🎉 no goals
  · cases' n with n
    -- ⊢ get? (pmap f (hd :: tl) h) zero = Option.pmap f (get? (hd :: tl) zero) (_ :  …
    · simp
      -- 🎉 no goals
    · simp [hl]
      -- 🎉 no goals
#align list.nth_pmap List.get?_pmap

theorem get_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : ℕ}
    (hn : n < (pmap f l h).length) :
    get (pmap f l h) ⟨n, hn⟩ =
      f (get l ⟨n, @length_pmap _ _ p f l h ▸ hn⟩)
        (h _ (get_mem l n (@length_pmap _ _ p f l h ▸ hn))) := by
  induction' l with hd tl hl generalizing n
  -- ⊢ get (pmap f [] h) { val := n, isLt := hn } = f (get [] { val := n, isLt := ( …
  · simp only [length, pmap] at hn
    -- ⊢ get (pmap f [] h) { val := n, isLt := hn } = f (get [] { val := n, isLt := ( …
    exact absurd hn (not_lt_of_le n.zero_le)
    -- 🎉 no goals
  · cases n
    -- ⊢ get (pmap f (hd :: tl) h) { val := zero, isLt := hn } = f (get (hd :: tl) {  …
    · simp
      -- 🎉 no goals
    · simp [hl]
      -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated get_pmap]
theorem nthLe_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : ℕ}
    (hn : n < (pmap f l h).length) :
    nthLe (pmap f l h) n hn =
      f (nthLe l n (@length_pmap _ _ p f l h ▸ hn))
        (h _ (get_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
  get_pmap ..

#align list.nth_le_pmap List.nthLe_pmap

theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ l₂ : List ι)
    (h : ∀ a ∈ l₁ ++ l₂, p a) :
    (l₁ ++ l₂).pmap f h =
      (l₁.pmap f fun a ha => h a (mem_append_left l₂ ha)) ++
        l₂.pmap f fun a ha => h a (mem_append_right l₁ ha) := by
  induction' l₁ with _ _ ih
  -- ⊢ pmap f ([] ++ l₂) h = pmap f [] (_ : ∀ (a : ι), a ∈ [] → p a) ++ pmap f l₂ ( …
  · rfl
    -- 🎉 no goals
  · dsimp only [pmap, cons_append]
    -- ⊢ f head✝ (_ : p head✝) :: pmap f (tail✝ ++ l₂) (_ : ∀ (x : ι), x ∈ tail✝ ++ l …
    rw [ih]
    -- 🎉 no goals
#align list.pmap_append List.pmap_append

theorem pmap_append' {α β : Type*} {p : α → Prop} (f : ∀ a : α, p a → β) (l₁ l₂ : List α)
    (h₁ : ∀ a ∈ l₁, p a) (h₂ : ∀ a ∈ l₂, p a) :
    ((l₁ ++ l₂).pmap f fun a ha => (List.mem_append.1 ha).elim (h₁ a) (h₂ a)) =
      l₁.pmap f h₁ ++ l₂.pmap f h₂ :=
  pmap_append f l₁ l₂ _
#align list.pmap_append' List.pmap_append'

/-! ### find -/

section find?

variable {p : α → Bool} {l : List α} {a : α}

@[simp]
theorem find?_nil (p : α → Bool) : find? p [] = none :=
  rfl
#align list.find_nil List.find?_nil

-- Porting note: List.find? is given @[simp] in Std.Data.List.Init.Lemmas
-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] find?_cons_of_pos
#align list.find_cons_of_pos List.find?_cons_of_pos

-- Porting note: List.find? is given @[simp] in Std.Data.List.Init.Lemmas
-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] find?_cons_of_neg
#align list.find_cons_of_neg List.find?_cons_of_neg

attribute [simp] find?_eq_none
#align list.find_eq_none List.find?_eq_none

#align list.find_some List.find?_some

@[simp]
theorem find?_mem (H : find? p l = some a) : a ∈ l := by
  induction' l with b l IH; · contradiction
  -- ⊢ a ∈ []
                              -- 🎉 no goals
  by_cases h : p b
  -- ⊢ a ∈ b :: l
  · rw [find?_cons_of_pos _ h] at H
    -- ⊢ a ∈ b :: l
    cases H
    -- ⊢ a ∈ a :: l
    apply mem_cons_self
    -- 🎉 no goals
  · rw [find?_cons_of_neg _ h] at H
    -- ⊢ a ∈ b :: l
    exact mem_cons_of_mem _ (IH H)
    -- 🎉 no goals
#align list.find_mem List.find?_mem

end find?

/-! ### lookmap -/

section Lookmap

variable (f : α → Option α)

/- Porting note: need a helper theorem for lookmap.go. -/
theorem lookmap.go_append (l : List α) (acc : Array α) :
    lookmap.go f l acc = acc.toListAppend (lookmap f l) := by
  cases l with
  | nil => rfl
  | cons hd tl =>
    rw [lookmap, go, go]
    cases f hd with
    | none => simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.push_data]; rfl
    | some a => rfl

@[simp]
theorem lookmap_nil : [].lookmap f = [] :=
  rfl
#align list.lookmap_nil List.lookmap_nil

@[simp]
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) :
    (a :: l).lookmap f = a :: l.lookmap f := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, Array.data_toArray, nil_append]
  -- ⊢ (match f a with
  rw [lookmap.go_append, h]; rfl
  -- ⊢ (match none with
                             -- 🎉 no goals
#align list.lookmap_cons_none List.lookmap_cons_none

@[simp]
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) :
    (a :: l).lookmap f = b :: l := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, Array.data_toArray, nil_append]
  -- ⊢ (match f a with
  rw [h]
  -- 🎉 no goals
#align list.lookmap_cons_some List.lookmap_cons_some

theorem lookmap_some : ∀ l : List α, l.lookmap some = l
  | [] => rfl
  | _ :: _ => rfl
#align list.lookmap_some List.lookmap_some

theorem lookmap_none : ∀ l : List α, (l.lookmap fun _ => none) = l
  | [] => rfl
  | a :: l => (lookmap_cons_none _ l rfl).trans (congr_arg (cons a) (lookmap_none l))
#align list.lookmap_none List.lookmap_none

theorem lookmap_congr {f g : α → Option α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
  | [], _ => rfl
  | a :: l, H => by
    cases' forall_mem_cons.1 H with H₁ H₂
    -- ⊢ lookmap f (a :: l) = lookmap g (a :: l)
    cases' h : g a with b
    -- ⊢ lookmap f (a :: l) = lookmap g (a :: l)
    · simp [h, H₁.trans h, lookmap_congr H₂]
      -- 🎉 no goals
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]
      -- 🎉 no goals
#align list.lookmap_congr List.lookmap_congr

theorem lookmap_of_forall_not {l : List α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)
#align list.lookmap_of_forall_not List.lookmap_of_forall_not

theorem lookmap_map_eq (g : α → β) (h : ∀ (a), ∀ b ∈ f a, g a = g b) :
    ∀ l : List α, map g (l.lookmap f) = map g l
  | [] => rfl
  | a :: l => by
    cases' h' : f a with b
    -- ⊢ map g (lookmap f (a :: l)) = map g (a :: l)
    · simp [h']; exact lookmap_map_eq _ h l
      -- ⊢ map g (lookmap f l) = map g l
                 -- 🎉 no goals
    · simp [lookmap_cons_some _ _ h', h _ _ h']
      -- 🎉 no goals
#align list.lookmap_map_eq List.lookmap_map_eq

theorem lookmap_id' (h : ∀ (a), ∀ b ∈ f a, a = b) (l : List α) : l.lookmap f = l := by
  rw [← map_id (l.lookmap f), lookmap_map_eq, map_id]; exact h
  -- ⊢ ∀ (a b : α), b ∈ f a → id a = id b
                                                       -- 🎉 no goals
#align list.lookmap_id' List.lookmap_id'

theorem length_lookmap (l : List α) : length (l.lookmap f) = length l := by
  rw [← length_map, lookmap_map_eq _ fun _ => (), length_map]; simp
  -- ⊢ ∀ (a b : α), b ∈ f a → () = ()
                                                               -- 🎉 no goals
#align list.length_lookmap List.length_lookmap

end Lookmap

/-! ### filter -/
/-! ### filterMap -/

#align list.filter_map_nil List.filterMap_nil

-- Porting note: List.filterMap is given @[simp] in Std.Data.List.Init.Lemmas
-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] filterMap_cons_none
#align list.filter_map_cons_none List.filterMap_cons_none

-- @[simp]
-- Later porting note (at time of this lemma moving to Std): removing attribute `nolint simpNF`
attribute [simp 1100] filterMap_cons_some
#align list.filter_map_cons_some List.filterMap_cons_some

#align list.filter_map_cons List.filterMap_cons

#align list.filter_map_append List.filterMap_append

#align list.filter_map_eq_map List.filterMap_eq_map

#align list.filter_map_eq_filter List.filterMap_eq_filter

#align list.filter_map_filter_map List.filterMap_filterMap

#align list.map_filter_map List.map_filterMap

#align list.filter_map_map List.filterMap_map

#align list.filter_filter_map List.filter_filterMap

#align list.filter_map_filter List.filterMap_filter

#align list.filter_map_some List.filterMap_some

#align list.map_filter_map_some_eq_filter_map_is_some List.map_filterMap_some_eq_filter_map_is_some

#align list.mem_filter_map List.mem_filterMap

#align list.filter_map_join List.filterMap_join

#align list.map_filter_map_of_inv List.map_filterMap_of_inv

#align list.length_filter_le List.length_filter_leₓ

#align list.length_filter_map_le List.length_filterMap_le

#align list.sublist.filter_map List.Sublist.filterMap

theorem Sublist.map (f : α → β) {l₁ l₂ : List α} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
  filterMap_eq_map f ▸ s.filterMap _
#align list.sublist.map List.Sublist.map

/-! ### reduceOption -/

@[simp]
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id.def, eq_self_iff_true, and_self_iff]
  -- 🎉 no goals
#align list.reduce_option_cons_of_some List.reduceOption_cons_of_some

@[simp]
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id.def]
                                                    -- 🎉 no goals
#align list.reduce_option_cons_of_none List.reduceOption_cons_of_none

@[simp]
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl
#align list.reduce_option_nil List.reduceOption_nil

@[simp]
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction' l with hd tl hl
  -- ⊢ reduceOption (map (Option.map f) []) = map f (reduceOption [])
  · simp only [reduceOption_nil, map_nil]
    -- 🎉 no goals
  ·cases hd <;>
   -- ⊢ reduceOption (map (Option.map f) (none :: tl)) = map f (reduceOption (none : …
      simpa [true_and_iff, Option.map_some', map, eq_self_iff_true,
        reduceOption_cons_of_some] using hl
#align list.reduce_option_map List.reduceOption_map

theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append l l' id
#align list.reduce_option_append List.reduceOption_append

theorem reduceOption_length_le (l : List (Option α)) : l.reduceOption.length ≤ l.length := by
  induction' l with hd tl hl
  -- ⊢ length (reduceOption []) ≤ length []
  · simp only [reduceOption_nil, length]
    -- 🎉 no goals
  · cases hd
    -- ⊢ length (reduceOption (none :: tl)) ≤ length (none :: tl)
    · exact Nat.le_succ_of_le hl
      -- 🎉 no goals
    · simpa only [length, add_le_add_iff_right, reduceOption_cons_of_some] using hl
      -- 🎉 no goals
#align list.reduce_option_length_le List.reduceOption_length_le

theorem reduceOption_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x := by
  induction' l with hd tl hl
  -- ⊢ length (reduceOption []) = length [] ↔ ∀ (x : Option α), x ∈ [] → Option.isS …
  · simp only [forall_const, reduceOption_nil, not_mem_nil, forall_prop_of_false, eq_self_iff_true,
      length, not_false_iff]
  · cases hd
    -- ⊢ length (reduceOption (none :: tl)) = length (none :: tl) ↔ ∀ (x : Option α), …
    · simp only [mem_cons, forall_eq_or_imp, Bool.coe_sort_false, false_and_iff,
        reduceOption_cons_of_none, length, Option.isSome_none, iff_false_iff]
      intro H
      -- ⊢ False
      have := reduceOption_length_le tl
      -- ⊢ False
      rw [H] at this
      -- ⊢ False
      exact absurd (Nat.lt_succ_self _) (not_lt_of_le this)
      -- 🎉 no goals
    · simp only [length, add_left_inj, find?, mem_cons, forall_eq_or_imp, Option.isSome_some,
        ← hl, reduceOption, true_and]
#align list.reduce_option_length_eq_iff List.reduceOption_length_eq_iff

theorem reduceOption_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none ∈ l := by
  rw [(reduceOption_length_le l).lt_iff_ne, Ne, reduceOption_length_eq_iff]
  -- ⊢ (¬∀ (x : Option α), x ∈ l → Option.isSome x = true) ↔ none ∈ l
  induction l <;> simp [*]
  -- ⊢ (¬∀ (x : Option α), x ∈ [] → Option.isSome x = true) ↔ none ∈ []
                  -- 🎉 no goals
                  -- ⊢ (Option.isSome head✝ = true → ∃ x, x ∈ tail✝ ∧ Option.isNone x = true) ↔ non …
  rw [@eq_comm _ none, ← Option.not_isSome_iff_eq_none, Decidable.imp_iff_not_or]
  -- ⊢ (¬Option.isSome head✝ = true ∨ ∃ x, x ∈ tail✝ ∧ Option.isNone x = true) ↔ ¬O …
  simp [Option.isNone_iff_eq_none]
  -- 🎉 no goals
#align list.reduce_option_length_lt_iff List.reduceOption_length_lt_iff

theorem reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl
                                                                                  -- ⊢ reduceOption [none] = Option.toList none
                                                                                              -- 🎉 no goals
                                                                                              -- 🎉 no goals
#align list.reduce_option_singleton List.reduceOption_singleton

theorem reduceOption_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList := by
  induction' l with hd tl hl generalizing x
  -- ⊢ reduceOption (concat [] x) = reduceOption [] ++ Option.toList x
  · cases x <;> simp [Option.toList]
    -- ⊢ reduceOption (concat [] none) = reduceOption [] ++ Option.toList none
                -- 🎉 no goals
                -- 🎉 no goals
  · simp only [concat_eq_append, reduceOption_append] at hl
    -- ⊢ reduceOption (concat (hd :: tl) x) = reduceOption (hd :: tl) ++ Option.toLis …
    cases hd <;> simp [hl, reduceOption_append]
    -- ⊢ reduceOption (concat (none :: tl) x) = reduceOption (none :: tl) ++ Option.t …
                 -- 🎉 no goals
                 -- 🎉 no goals
#align list.reduce_option_concat List.reduceOption_concat

theorem reduceOption_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]
  -- 🎉 no goals
#align list.reduce_option_concat_of_some List.reduceOption_concat_of_some

theorem reduceOption_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduceOption ↔ some x ∈ l := by
  simp only [reduceOption, id.def, mem_filterMap, exists_eq_right]
  -- 🎉 no goals
#align list.reduce_option_mem_iff List.reduceOption_mem_iff

theorem reduceOption_get?_iff {l : List (Option α)} {x : α} :
    (∃ i, l.get? i = some (some x)) ↔ ∃ i, l.reduceOption.get? i = some x := by
  rw [← mem_iff_get?, ← mem_iff_get?, reduceOption_mem_iff]
  -- 🎉 no goals
#align list.reduce_option_nth_iff List.reduceOption_get?_iff

/-! ### filter -/

section Filter

-- Porting note: Lemmas for `filter` are stated in terms of `p : α → Bool`
-- rather than `p : α → Prop` with `DecidablePred p`, since `filter` itself is.
-- Likewise, `if` sometimes becomes `bif`.
variable {p : α → Bool}

theorem filter_singleton {a : α} : [a].filter p = bif p a then [a] else [] :=
  rfl
#align list.filter_singleton List.filter_singleton

theorem filter_eq_foldr (p : α → Bool) (l : List α) :
    filter p l = foldr (fun a out => bif p a then a :: out else out) [] l := by
  induction l <;> simp [*, filter]; rfl
  -- ⊢ filter p [] = foldr (fun a out => bif p a then a :: out else out) [] []
                  -- 🎉 no goals
                  -- ⊢ (match p head✝ with
                                    -- 🎉 no goals
#align list.filter_eq_foldr List.filter_eq_foldr

#align list.filter_congr' List.filter_congr'

@[simp]
theorem filter_subset (l : List α) : filter p l ⊆ l :=
  (filter_sublist l).subset
#align list.filter_subset List.filter_subset

theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
  | b :: l, ain =>
    if pb : p b then
      have : a ∈ b :: filter p l := by simpa only [filter_cons_of_pos _ pb] using ain
                                       -- 🎉 no goals
      Or.elim (eq_or_mem_of_mem_cons this) (fun h : a = b => by rw [← h] at pb; exact pb)
                                                                -- ⊢ p a = true
                                                                                -- 🎉 no goals
        fun h : a ∈ filter p l => of_mem_filter h
    else by simp only [filter_cons_of_neg _ pb] at ain; exact of_mem_filter ain
            -- ⊢ p a = true
                                                        -- 🎉 no goals
#align list.of_mem_filter List.of_mem_filter

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset l h
#align list.mem_of_mem_filter List.mem_of_mem_filter

theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
  | x :: l, h, h1 => by
    rcases mem_cons.1 h with rfl | h
    -- ⊢ a ∈ filter p (a :: l)
    · simp [filter, h1]
      -- 🎉 no goals
    · rw [filter]
      -- ⊢ a ∈
      cases p x <;> simp [mem_filter_of_mem h h1]
                    -- 🎉 no goals
                    -- 🎉 no goals
#align list.mem_filter_of_mem List.mem_filter_of_mem

#align list.mem_filter List.mem_filter

theorem monotone_filter_left (p : α → Bool) ⦃l l' : List α⦄ (h : l ⊆ l') :
    filter p l ⊆ filter p l' := by
  intro x hx
  -- ⊢ x ∈ filter p l'
  rw [mem_filter] at hx ⊢
  -- ⊢ x ∈ l' ∧ p x = true
  exact ⟨h hx.left, hx.right⟩
  -- 🎉 no goals
#align list.monotone_filter_left List.monotone_filter_left

#align list.filter_eq_self List.filter_eq_self

#align list.filter_length_eq_length List.filter_length_eq_length

#align list.filter_eq_nil List.filter_eq_nil

variable (p)

#align list.sublist.filter List.Sublist.filter

theorem monotone_filter_right (l : List α) ⦃p q : α → Bool⦄
    (h : ∀ a, p a → q a) : l.filter p <+ l.filter q := by
  induction' l with hd tl IH
  -- ⊢ filter p [] <+ filter q []
  · rfl
    -- 🎉 no goals
  · by_cases hp : p hd
    -- ⊢ filter p (hd :: tl) <+ filter q (hd :: tl)
    · rw [filter_cons_of_pos _ hp, filter_cons_of_pos _ (h _ hp)]
      -- ⊢ hd :: filter p tl <+ hd :: filter q tl
      exact IH.cons_cons hd
      -- 🎉 no goals
    · rw [filter_cons_of_neg _ hp]
      -- ⊢ filter p tl <+ filter q (hd :: tl)
      by_cases hq : q hd
      -- ⊢ filter p tl <+ filter q (hd :: tl)
      · rw [filter_cons_of_pos _ hq]
        -- ⊢ filter p tl <+ hd :: filter q tl
        exact sublist_cons_of_sublist hd IH
        -- 🎉 no goals
      · rw [filter_cons_of_neg _ hq]
        -- ⊢ filter p tl <+ filter q tl
        exact IH
        -- 🎉 no goals
#align list.monotone_filter_right List.monotone_filter_right

#align list.map_filter List.map_filter

#align list.filter_filter List.filter_filter

@[simp]
theorem filter_true (l : List α) :
    filter (fun _ => true) l = l := by induction l <;> simp [*, filter]
                                       -- ⊢ filter (fun x => true) [] = []
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
#align list.filter_true List.filter_true

@[simp]
theorem filter_false (l : List α) :
    filter (fun _ => false) l = [] := by induction l <;> simp [*, filter]
                                         -- ⊢ filter (fun x => false) [] = []
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
#align list.filter_false List.filter_false

/- Porting note: need a helper theorem for span.loop. -/
theorem span.loop_eq_take_drop :
  ∀ l₁ l₂ : List α, span.loop p l₁ l₂ = (l₂.reverse ++ takeWhile p l₁, dropWhile p l₁)
  | [], l₂ => by simp [span.loop, takeWhile, dropWhile]
                 -- 🎉 no goals
  | (a :: l), l₂ => by
    cases hp : p a <;> simp [hp, span.loop, span.loop_eq_take_drop, takeWhile, dropWhile]
    -- ⊢ loop p (a :: l) l₂ = (reverse l₂ ++ takeWhile p (a :: l), dropWhile p (a ::  …
                       -- 🎉 no goals
                       -- 🎉 no goals

@[simp]
theorem span_eq_take_drop (l : List α) : span p l = (takeWhile p l, dropWhile p l) := by
  simpa using span.loop_eq_take_drop p l []
  -- 🎉 no goals
#align list.span_eq_take_drop List.span_eq_take_drop

#align list.take_while_append_drop List.takeWhile_append_dropWhile

theorem dropWhile_nthLe_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).nthLe 0 hl) := by
  induction' l with hd tl IH
  -- ⊢ ¬p (nthLe (dropWhile p []) 0 hl) = true
  · cases hl
    -- 🎉 no goals
  · simp only [dropWhile]
    -- ⊢ ¬p
    by_cases hp : p hd
    · simp [hp, IH]
      -- 🎉 no goals
    · simp [hp, nthLe_cons]
      -- 🎉 no goals
-- porting note: How did the Lean 3 proof work,
-- without mentioning nthLe_cons?
-- Same question for takeWhile_eq_nil_iff below
#align list.drop_while_nth_le_zero_not List.dropWhile_nthLe_zero_not

variable {p} {l : List α}

@[simp]
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  -- ⊢ dropWhile p [] = [] ↔ ∀ (x : α), x ∈ [] → p x = true
  · simp [dropWhile]
    -- 🎉 no goals
  · by_cases hp : p x <;> simp [hp, dropWhile, IH]
    -- ⊢ dropWhile p (x :: xs) = [] ↔ ∀ (x_1 : α), x_1 ∈ x :: xs → p x_1 = true
                          -- 🎉 no goals
                          -- 🎉 no goals
#align list.drop_while_eq_nil_iff List.dropWhile_eq_nil_iff

@[simp]
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  -- ⊢ takeWhile p [] = [] ↔ ∀ (x : α), x ∈ [] → p x = true
  · simp [takeWhile]
    -- 🎉 no goals
  · by_cases hp : p x <;> simp [hp, takeWhile, IH]
    -- ⊢ takeWhile p (x :: xs) = x :: xs ↔ ∀ (x_1 : α), x_1 ∈ x :: xs → p x_1 = true
                          -- 🎉 no goals
                          -- 🎉 no goals
#align list.take_while_eq_self_iff List.takeWhile_eq_self_iff

@[simp]
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.nthLe 0 hl) := by
  induction' l with x xs IH
  -- ⊢ takeWhile p [] = [] ↔ ∀ (hl : 0 < length []), ¬p (nthLe [] 0 hl) = true
  · simp [takeWhile, true_iff]
    -- ⊢ ∀ (hl : 0 < length []), p (nthLe [] 0 hl) = false
    intro h
    -- ⊢ p (nthLe [] 0 h) = false
    simp at h
    -- 🎉 no goals
  · by_cases hp : p x <;> simp [hp, takeWhile, IH, nthLe_cons]
    -- ⊢ takeWhile p (x :: xs) = [] ↔ ∀ (hl : 0 < length (x :: xs)), ¬p (nthLe (x ::  …
                          -- 🎉 no goals
                          -- 🎉 no goals
#align list.take_while_eq_nil_iff List.takeWhile_eq_nil_iff

theorem mem_takeWhile_imp {x : α} (hx : x ∈ takeWhile p l) : p x := by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx
#align list.mem_take_while_imp List.mem_takeWhile_imp

theorem takeWhile_takeWhile (p q : α → Bool) (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction' l with hd tl IH
  -- ⊢ takeWhile p (takeWhile q []) = takeWhile (fun a => decide (p a = true ∧ q a  …
  · simp [takeWhile]
    -- 🎉 no goals
  · by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]
    -- ⊢ takeWhile p (takeWhile q (hd :: tl)) = takeWhile (fun a => decide (p a = tru …
                           -- ⊢ takeWhile p (takeWhile q (hd :: tl)) = takeWhile (fun a => decide (p a = tru …
                           -- ⊢ takeWhile p (takeWhile q (hd :: tl)) = takeWhile (fun a => decide (p a = tru …
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align list.take_while_take_while List.takeWhile_takeWhile

theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]
  -- 🎉 no goals
#align list.take_while_idem List.takeWhile_idem

end Filter

/-! ### erasep -/

section eraseP

variable {p : α → Bool}

#align list.erasep_nil List.eraseP_nilₓ -- prop -> bool
#align list.erasep_cons List.eraseP_consₓ -- prop -> bool

#align list.erasep_cons_of_pos List.eraseP_cons_of_posₓ -- prop -> bool
#align list.erasep_cons_of_neg List.eraseP_cons_of_negₓ -- prop -> bool
#align list.erasep_of_forall_not List.eraseP_of_forall_notₓ -- prop -> bool
#align list.exists_of_erasep List.exists_of_erasePₓ -- prop -> bool
#align list.exists_or_eq_self_of_erasep List.exists_or_eq_self_of_erasePₓ -- prop -> bool
#align list.length_erasep_of_mem List.length_eraseP_of_memₓ -- prop -> bool

@[simp]
theorem length_eraseP_add_one {l : List α} {a} (al : a ∈ l) (pa : p a) :
    (l.eraseP p).length + 1 = l.length := by
  let ⟨_, l₁, l₂, _, _, h₁, h₂⟩ := exists_of_eraseP al pa
  -- ⊢ length (eraseP p l) + 1 = length l
  rw [h₂, h₁, length_append, length_append]
  -- ⊢ length l₁ + length l₂ + 1 = length l₁ + length (w✝ :: l₂)
  rfl
  -- 🎉 no goals
#align list.length_erasep_add_one List.length_eraseP_add_oneₓ -- prop -> bool

#align list.erasep_append_left List.eraseP_append_leftₓ -- prop -> bool
#align list.erasep_append_right List.eraseP_append_rightₓ -- prop -> bool
#align list.erasep_sublist List.eraseP_sublistₓ -- prop -> bool
#align list.erasep_subset List.eraseP_subsetₓ -- prop -> bool
#align list.sublist.erasep List.Sublist.erasePₓ -- prop -> bool
#align list.mem_of_mem_erasep List.mem_of_mem_erasePₓ -- prop -> bool
#align list.mem_erasep_of_neg List.mem_eraseP_of_negₓ -- prop -> bool
#align list.erasep_map List.eraseP_mapₓ -- prop -> bool
#align list.extractp_eq_find_erasep List.extractP_eq_find?_erasePₓ -- prop -> bool

end eraseP

/-! ### erase -/

section Erase

variable [DecidableEq α]

#align list.erase_nil List.erase_nil

#align list.erase_cons List.erase_consₓ -- DecidableEq -> BEq
#align list.erase_cons_head List.erase_cons_headₓ -- DecidableEq -> BEq
#align list.erase_cons_tail List.erase_cons_tailₓ -- DecidableEq -> BEq
#align list.erase_eq_erasep List.erase_eq_erasePₓ -- DecidableEq -> BEq
#align list.erase_of_not_mem List.erase_of_not_memₓ -- DecidableEq -> BEq
#align list.exists_erase_eq List.exists_erase_eqₓ -- DecidableEq -> BEq
#align list.length_erase_of_mem List.length_erase_of_memₓ -- DecidableEq -> BEq

@[simp] theorem length_erase_add_one {a : α} {l : List α} (h : a ∈ l) :
    (l.erase a).length + 1 = l.length := by
  rw [erase_eq_eraseP, length_eraseP_add_one h (decide_eq_true rfl)]
  -- 🎉 no goals
#align list.length_erase_add_one List.length_erase_add_oneₓ -- DecidableEq -> BEq

#align list.erase_append_left List.erase_append_leftₓ -- DecidableEq -> BEq
#align list.erase_append_right List.erase_append_rightₓ -- DecidableEq -> BEq
#align list.erase_sublist List.erase_sublistₓ -- DecidableEq -> BEq
#align list.erase_subset List.erase_subsetₓ -- DecidableEq -> BEq

#align list.sublist.erase List.Sublist.eraseₓ -- DecidableEq -> BEq

#align list.mem_of_mem_erase List.mem_of_mem_eraseₓ -- DecidableEq -> BEq
#align list.mem_erase_of_ne List.mem_erase_of_neₓ -- DecidableEq -> BEq
#align list.erase_comm List.erase_commₓ -- DecidableEq -> BEq

theorem map_erase [DecidableEq β] {f : α → β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) := by
  have this : Eq a = Eq (f a) ∘ f := by ext b; simp [finj.eq_iff]
  -- ⊢ map f (List.erase l a) = List.erase (map f l) (f a)
  simp [erase_eq_eraseP, erase_eq_eraseP, eraseP_map, this]; rfl
  -- ⊢ map f (eraseP (fun b => decide (f a = f b)) l) = map f (eraseP ((fun b => de …
                                                             -- 🎉 no goals
#align list.map_erase List.map_erase

theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]
  -- 🎉 no goals
#align list.map_foldl_erase List.map_foldl_erase

end Erase

/-! ### diff -/

section Diff

variable [DecidableEq α]

#align list.diff_nil List.diff_nil

#align list.diff_cons List.diff_cons

#align list.diff_cons_right List.diff_cons_right

#align list.diff_erase List.diff_erase

#align list.nil_diff List.nil_diff

#align list.cons_diff List.cons_diff

#align list.cons_diff_of_mem List.cons_diff_of_mem

#align list.cons_diff_of_not_mem List.cons_diff_of_not_mem

#align list.diff_eq_foldl List.diff_eq_foldl

#align list.diff_append List.diff_append

@[simp]
theorem map_diff [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]
  -- 🎉 no goals
#align list.map_diff List.map_diff

#align list.diff_sublist List.diff_sublist

#align list.diff_subset List.diff_subset

#align list.mem_diff_of_mem List.mem_diff_of_mem

#align list.sublist.diff_right List.Sublist.diff_right

theorem erase_diff_erase_sublist_of_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], l₂, _ => erase_sublist _ _
  | b :: l₁, l₂, h =>
    if heq : b = a then by simp only [heq, erase_cons_head, diff_cons]; rfl
                           -- ⊢ List.diff (List.erase l₂ a) l₁ <+ List.diff (List.erase l₂ a) l₁
                                                                        -- 🎉 no goals
    else by
      simp only [erase_cons_head b l₁, erase_cons_tail l₁ heq,
        diff_cons ((List.erase l₂ a)) (List.erase l₁ a) b, diff_cons l₂ l₁ b, erase_comm a b l₂]
      have h' := h.erase b
      -- ⊢ List.diff (List.erase (List.erase l₂ b) a) (List.erase l₁ a) <+ List.diff (L …
      rw [erase_cons_head] at h'
      -- ⊢ List.diff (List.erase (List.erase l₂ b) a) (List.erase l₁ a) <+ List.diff (L …
      exact @erase_diff_erase_sublist_of_sublist _ l₁ (l₂.erase b) h'
      -- 🎉 no goals
#align list.erase_diff_erase_sublist_of_sublist List.erase_diff_erase_sublist_of_sublist

end Diff

/-! ### enum -/

theorem length_enumFrom : ∀ (n) (l : List α), length (enumFrom n l) = length l
  | _, [] => rfl
  | _, _ :: _ => congr_arg Nat.succ (length_enumFrom _ _)
#align list.length_enum_from List.length_enumFrom

theorem length_enum : ∀ l : List α, length (enum l) = length l :=
  length_enumFrom _
#align list.length_enum List.length_enum

@[simp]
theorem enumFrom_get? :
    ∀ (n) (l : List α) (m), get? (enumFrom n l) m = (fun a => (n + m, a)) <$> get? l m
  | n, [], m => rfl
  | n, a :: l, 0 => rfl
  | n, a :: l, m + 1 => (enumFrom_get? (n + 1) l m).trans <| by rw [add_right_comm]; rfl
                                                                -- ⊢ (fun a => (n + m + 1, a)) <$> get? l m = (fun a => (n + (m + 1), a)) <$> get …
                                                                                     -- 🎉 no goals
#align list.enum_from_nth List.enumFrom_get?

@[simp]
theorem enum_get? : ∀ (l : List α) (n), get? (enum l) n = (fun a => (n, a)) <$> get? l n := by
  simp only [enum, enumFrom_get?, zero_add]; intros; trivial
  -- ⊢ List α → ℕ → True
                                             -- ⊢ True
                                                     -- 🎉 no goals
#align list.enum_nth List.enum_get?

@[simp]
theorem enumFrom_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | _, [] => rfl
  | _, _ :: _ => congr_arg (cons _) (enumFrom_map_snd _ _)
#align list.enum_from_map_snd List.enumFrom_map_snd

@[simp]
theorem enum_map_snd : ∀ l : List α, map Prod.snd (enum l) = l :=
  enumFrom_map_snd _
#align list.enum_map_snd List.enum_map_snd

theorem mem_enumFrom {x : α} {i : ℕ} :
    ∀ {j : ℕ} (xs : List α), (i, x) ∈ xs.enumFrom j → j ≤ i ∧ i < j + xs.length ∧ x ∈ xs
  | j, [] => by simp [enumFrom]
                -- 🎉 no goals
  | j, y :: ys => by
    suffices
      i = j ∧ x = y ∨ (i, x) ∈ enumFrom (j + 1) ys →
        j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys)
      by simpa [enumFrom, mem_enumFrom ys]
    rintro (h | h)
    -- ⊢ j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys)
    · refine' ⟨le_of_eq h.1.symm, h.1 ▸ _, Or.inl h.2⟩
      -- ⊢ i < i + (length ys + 1)
      apply Nat.lt_add_of_pos_right; simp
      -- ⊢ 0 < length ys + 1
                                     -- 🎉 no goals
    · have ⟨hji, hijlen, hmem⟩ := mem_enumFrom _ h
      -- ⊢ j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys)
      refine' ⟨_, _, _⟩
      · exact le_trans (Nat.le_succ _) hji
        -- 🎉 no goals
      · convert hijlen using 1
        -- ⊢ j + (length ys + 1) = j + 1 + length ys
        ac_rfl
        -- 🎉 no goals
      · simp [hmem]
        -- 🎉 no goals
#align list.mem_enum_from List.mem_enumFrom

@[simp]
theorem enum_nil : enum ([] : List α) = [] :=
  rfl
#align list.enum_nil List.enum_nil

@[simp]
theorem enumFrom_nil (n : ℕ) : enumFrom n ([] : List α) = [] :=
  rfl
#align list.enum_from_nil List.enumFrom_nil

@[simp]
theorem enumFrom_cons (x : α) (xs : List α) (n : ℕ) :
    enumFrom n (x :: xs) = (n, x) :: enumFrom (n + 1) xs :=
  rfl
#align list.enum_from_cons List.enumFrom_cons

@[simp]
theorem enum_cons (x : α) (xs : List α) : enum (x :: xs) = (0, x) :: enumFrom 1 xs :=
  rfl
#align list.enum_cons List.enum_cons

@[simp]
theorem enumFrom_singleton (x : α) (n : ℕ) : enumFrom n [x] = [(n, x)] :=
  rfl
#align list.enum_from_singleton List.enumFrom_singleton

@[simp]
theorem enum_singleton (x : α) : enum [x] = [(0, x)] :=
  rfl
#align list.enum_singleton List.enum_singleton

theorem enumFrom_append (xs ys : List α) (n : ℕ) :
    enumFrom n (xs ++ ys) = enumFrom n xs ++ enumFrom (n + xs.length) ys := by
  induction' xs with x xs IH generalizing ys n
  -- ⊢ enumFrom n ([] ++ ys) = enumFrom n [] ++ enumFrom (n + length []) ys
  · simp
    -- 🎉 no goals
  · rw [cons_append, enumFrom_cons, IH, ← cons_append, ← enumFrom_cons, length, add_right_comm,
      add_assoc]
#align list.enum_from_append List.enumFrom_append

theorem enum_append (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]
  -- 🎉 no goals
#align list.enum_append List.enum_append

theorem map_fst_add_enumFrom_eq_enumFrom (l : List α) (n k : ℕ) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l := by
  induction' l with hd tl IH generalizing n k
  -- ⊢ map (Prod.map (fun x => x + n) id) (enumFrom k []) = enumFrom (n + k) []
  · simp [enumFrom]
    -- 🎉 no goals
  · simp only [enumFrom, map, zero_add, Prod.map_mk, id.def, eq_self_iff_true, true_and_iff]
    -- ⊢ (k + n, hd) :: map (Prod.map (fun x => x + n) id) (enumFrom (k + 1) tl) = (n …
    simp [IH, add_comm n k, add_assoc, add_left_comm]
    -- 🎉 no goals
#align list.map_fst_add_enum_from_eq_enum_from List.map_fst_add_enumFrom_eq_enumFrom

theorem map_fst_add_enum_eq_enumFrom (l : List α) (n : ℕ) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enumFrom_eq_enumFrom l _ _
#align list.map_fst_add_enum_eq_enum_from List.map_fst_add_enum_eq_enumFrom

theorem enumFrom_cons' (n : ℕ) (x : α) (xs : List α) :
    enumFrom n (x :: xs) = (n, x) :: (enumFrom n xs).map (Prod.map Nat.succ id) := by
  rw [enumFrom_cons, add_comm, ← map_fst_add_enumFrom_eq_enumFrom]
  -- 🎉 no goals
#align list.enum_from_cons' List.enumFrom_cons'

theorem enum_cons' (x : α) (xs : List α) :
    enum (x :: xs) = (0, x) :: (enum xs).map (Prod.map Nat.succ id) :=
  enumFrom_cons' _ _ _
#align list.enum_cons' List.enum_cons'

theorem enumFrom_map (n : ℕ) (l : List α) (f : α → β) :
    enumFrom n (l.map f) = (enumFrom n l).map (Prod.map id f) := by
  induction' l with hd tl IH
  -- ⊢ enumFrom n (map f []) = map (Prod.map id f) (enumFrom n [])
  · rfl
    -- 🎉 no goals
  · rw [map_cons, enumFrom_cons', enumFrom_cons', map_cons, map_map, IH, map_map]
    -- ⊢ (n, f hd) :: map (Prod.map succ id ∘ Prod.map id f) (enumFrom n tl) = Prod.m …
    rfl
    -- 🎉 no goals
#align list.enum_from_map List.enumFrom_map

theorem enum_map (l : List α) (f : α → β) : (l.map f).enum = l.enum.map (Prod.map id f) :=
  enumFrom_map _ _ _
#align list.enum_map List.enum_map

theorem get_enumFrom (l : List α) (n) (i : Fin (l.enumFrom n).length)
    (hi : i.1 < l.length := (by simpa [length_enumFrom] using i.2)) :
                                -- 🎉 no goals
    (l.enumFrom n).get i = (n + i, l.get ⟨i, hi⟩) := by
  rw [← Option.some_inj, ← get?_eq_get]
  -- ⊢ get? (enumFrom n l) ↑i = some (n + ↑i, get l { val := ↑i, isLt := hi })
  simp [enumFrom_get?, get?_eq_get hi]
  -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated get_enumFrom]
theorem nthLe_enumFrom (l : List α) (n i : ℕ) (hi' : i < (l.enumFrom n).length)
    (hi : i < l.length := (by simpa [length_enumFrom] using hi')) :
                              -- 🎉 no goals
    (l.enumFrom n).nthLe i hi' = (n + i, l.nthLe i hi) :=
  get_enumFrom ..
#align list.nth_le_enum_from List.nthLe_enumFrom

theorem get_enum (l : List α) (i : Fin l.enum.length)
    (hi : i < l.length := (by simpa [length_enum] using i.2)) :
                              -- 🎉 no goals
    l.enum.get i = (i.1, l.get ⟨i, hi⟩) := by
  convert get_enumFrom _ _ i
  -- ⊢ ↑i = 0 + ↑i
  exact (zero_add _).symm
  -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated get_enum]
theorem nthLe_enum (l : List α) (i : ℕ) (hi' : i < l.enum.length)
    (hi : i < l.length := (by simpa [length_enum] using hi')) :
                              -- 🎉 no goals
    l.enum.nthLe i hi' = (i, l.nthLe i hi) := get_enum ..
#align list.nth_le_enum List.nthLe_enum

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

/-! ### map₂Left' -/

section Map₂Left'

-- The definitional equalities for `map₂Left'` can already be used by the
-- simplifier because `map₂Left'` is marked `@[simp]`.
@[simp]
theorem map₂Left'_nil_right (f : α → Option β → γ) (as) :
    map₂Left' f as [] = (as.map fun a => f a none, []) := by cases as <;> rfl
                                                             -- ⊢ map₂Left' f [] [] = (map (fun a => f a none) [], [])
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
#align list.map₂_left'_nil_right List.map₂Left'_nil_right

end Map₂Left'

/-! ### map₂Right' -/

section Map₂Right'

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂Right'_nil_left : map₂Right' f [] bs = (bs.map (f none), []) := by cases bs <;> rfl
                                                                               -- ⊢ map₂Right' f [] [] = (map (f none) [], [])
                                                                                            -- 🎉 no goals
                                                                                            -- 🎉 no goals
#align list.map₂_right'_nil_left List.map₂Right'_nil_left

@[simp]
theorem map₂Right'_nil_right : map₂Right' f as [] = ([], as) :=
  rfl
#align list.map₂_right'_nil_right List.map₂Right'_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem map₂Right'_nil_cons : map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl
#align list.map₂_right'_nil_cons List.map₂Right'_nil_cons

@[simp]
theorem map₂Right'_cons_cons :
    map₂Right' f (a :: as) (b :: bs) =
      let r := map₂Right' f as bs
      (f (some a) b :: r.fst, r.snd) :=
  rfl
#align list.map₂_right'_cons_cons List.map₂Right'_cons_cons

end Map₂Right'

/-! ### zipLeft' -/

section ZipLeft'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map fun a => (a, none), []) := by
  cases as <;> rfl
  -- ⊢ zipLeft' [] [] = (map (fun a => (a, none)) [], [])
               -- 🎉 no goals
               -- 🎉 no goals
#align list.zip_left'_nil_right List.zipLeft'_nil_right

@[simp]
theorem zipLeft'_nil_left : zipLeft' ([] : List α) bs = ([], bs) :=
  rfl
#align list.zip_left'_nil_left List.zipLeft'_nil_left

-- Porting note: simp can prove this
-- @[simp]
theorem zipLeft'_cons_nil :
    zipLeft' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl
#align list.zip_left'_cons_nil List.zipLeft'_cons_nil

@[simp]
theorem zipLeft'_cons_cons :
    zipLeft' (a :: as) (b :: bs) =
      let r := zipLeft' as bs
      ((a, some b) :: r.fst, r.snd) :=
  rfl
#align list.zip_left'_cons_cons List.zipLeft'_cons_cons

end ZipLeft'

/-! ### zipRight' -/

section ZipRight'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.map fun b => (none, b), []) := by
  cases bs <;> rfl
  -- ⊢ zipRight' [] [] = (map (fun b => (none, b)) [], [])
               -- 🎉 no goals
               -- 🎉 no goals
#align list.zip_right'_nil_left List.zipRight'_nil_left

@[simp]
theorem zipRight'_nil_right : zipRight' as ([] : List β) = ([], as) :=
  rfl
#align list.zip_right'_nil_right List.zipRight'_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem zipRight'_nil_cons :
    zipRight' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl
#align list.zip_right'_nil_cons List.zipRight'_nil_cons

@[simp]
theorem zipRight'_cons_cons :
    zipRight' (a :: as) (b :: bs) =
      let r := zipRight' as bs
      ((some a, b) :: r.fst, r.snd) :=
  rfl
#align list.zip_right'_cons_cons List.zipRight'_cons_cons

end ZipRight'

/-! ### map₂Left -/

section Map₂Left

variable (f : α → Option β → γ) (as : List α)

-- The definitional equalities for `map₂Left` can already be used by the
-- simplifier because `map₂Left` is marked `@[simp]`.
@[simp]
theorem map₂Left_nil_right : map₂Left f as [] = as.map fun a => f a none := by cases as <;> rfl
                                                                               -- ⊢ map₂Left f [] [] = map (fun a => f a none) []
                                                                                            -- 🎉 no goals
                                                                                            -- 🎉 no goals
#align list.map₂_left_nil_right List.map₂Left_nil_right

theorem map₂Left_eq_map₂Left' : ∀ as bs, map₂Left f as bs = (map₂Left' f as bs).fst
  | [], _ => by simp
                -- 🎉 no goals
  | a :: as, [] => by simp
                      -- 🎉 no goals
  | a :: as, b :: bs => by simp [map₂Left_eq_map₂Left']
                           -- 🎉 no goals
#align list.map₂_left_eq_map₂_left' List.map₂Left_eq_map₂Left'

theorem map₂Left_eq_zipWith :
    ∀ as bs, length as ≤ length bs → map₂Left f as bs = zipWith (fun a b => f a (some b)) as bs
  | [], [], _ => by simp
                    -- 🎉 no goals
  | [], _ :: _, _ => by simp
                        -- 🎉 no goals
  | a :: as, [], h => by
    simp at h
    -- 🎉 no goals
  | a :: as, b :: bs, h => by
    simp [Nat.succ_le_succ_iff] at h
    -- ⊢ map₂Left f (a :: as) (b :: bs) = zipWith (fun a b => f a (some b)) (a :: as) …
    simp [h, map₂Left_eq_zipWith]
    -- 🎉 no goals
#align list.map₂_left_eq_map₂ List.map₂Left_eq_zipWith

end Map₂Left

/-! ### map₂Right -/

section Map₂Right

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂Right_nil_left : map₂Right f [] bs = bs.map (f none) := by cases bs <;> rfl
                                                                       -- ⊢ map₂Right f [] [] = map (f none) []
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
#align list.map₂_right_nil_left List.map₂Right_nil_left

@[simp]
theorem map₂Right_nil_right : map₂Right f as [] = [] :=
  rfl
#align list.map₂_right_nil_right List.map₂Right_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem map₂Right_nil_cons : map₂Right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl
#align list.map₂_right_nil_cons List.map₂Right_nil_cons

@[simp]
theorem map₂Right_cons_cons :
    map₂Right f (a :: as) (b :: bs) = f (some a) b :: map₂Right f as bs :=
  rfl
#align list.map₂_right_cons_cons List.map₂Right_cons_cons

theorem map₂Right_eq_map₂Right' : map₂Right f as bs = (map₂Right' f as bs).fst := by
  simp only [map₂Right, map₂Right', map₂Left_eq_map₂Left']
  -- 🎉 no goals
#align list.map₂_right_eq_map₂_right' List.map₂Right_eq_map₂Right'

theorem map₂Right_eq_zipWith (h : length bs ≤ length as) :
    map₂Right f as bs = zipWith (fun a b => f (some a) b) as bs := by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  -- ⊢ map₂Right f as bs = zipWith (fun a b => f (some a) b) as bs
  simp only [map₂Right, map₂Left_eq_zipWith, zipWith_flip, *]
  -- 🎉 no goals
#align list.map₂_right_eq_map₂ List.map₂Right_eq_zipWith

end Map₂Right

/-! ### zipLeft -/

section ZipLeft

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipLeft_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none) := by
  cases as <;> rfl
  -- ⊢ zipLeft [] [] = map (fun a => (a, none)) []
               -- 🎉 no goals
               -- 🎉 no goals
#align list.zip_left_nil_right List.zipLeft_nil_right

@[simp]
theorem zipLeft_nil_left : zipLeft ([] : List α) bs = [] :=
  rfl
#align list.zip_left_nil_left List.zipLeft_nil_left

-- Porting note: simp can prove this
-- @[simp]
theorem zipLeft_cons_nil :
    zipLeft (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl
#align list.zip_left_cons_nil List.zipLeft_cons_nil

@[simp]
theorem zipLeft_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs :=
  rfl
#align list.zip_left_cons_cons List.zipLeft_cons_cons

-- Porting note: arguments explicit for recursion
theorem zipLeft_eq_zipLeft' (as : List α) (bs : List β) : zipLeft as bs = (zipLeft' as bs).fst := by
  rw [zipLeft, zipLeft']
  -- ⊢ zipWithLeft Prod.mk as bs = (zipWithLeft' Prod.mk as bs).fst
  cases as with
  | nil => rfl
  | cons _ atl =>
    cases bs with
    | nil => rfl
    | cons _ btl => rw [zipWithLeft, zipWithLeft', cons_inj]; exact @zipLeft_eq_zipLeft' atl btl
#align list.zip_left_eq_zip_left' List.zipLeft_eq_zipLeft'

end ZipLeft

/-! ### zipRight -/

section ZipRight

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipRight_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b) := by
  cases bs <;> rfl
  -- ⊢ zipRight [] [] = map (fun b => (none, b)) []
               -- 🎉 no goals
               -- 🎉 no goals
#align list.zip_right_nil_left List.zipRight_nil_left

@[simp]
theorem zipRight_nil_right : zipRight as ([] : List β) = [] :=
  rfl
#align list.zip_right_nil_right List.zipRight_nil_right

-- Porting note: simp can prove this
-- @[simp]
theorem zipRight_nil_cons :
    zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl
#align list.zip_right_nil_cons List.zipRight_nil_cons

@[simp]
theorem zipRight_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs :=
  rfl
#align list.zip_right_cons_cons List.zipRight_cons_cons

theorem zipRight_eq_zipRight' : zipRight as bs = (zipRight' as bs).fst := by
  induction as generalizing bs <;> cases bs <;> simp [*]
  -- ⊢ zipRight [] bs = (zipRight' [] bs).fst
                                   -- ⊢ zipRight [] [] = (zipRight' [] []).fst
                                   -- ⊢ zipRight (head✝ :: tail✝) [] = (zipRight' (head✝ :: tail✝) []).fst
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align list.zip_right_eq_zip_right' List.zipRight_eq_zipRight'

end ZipRight

/-! ### toChunks -/

-- Porting note:
-- The definition of `toChunks` has changed substantially from Lean 3.
-- The theorems about `toChunks` are not used anywhere in mathlib, anyways.
-- TODO: Prove these theorems for the new definitions.

#noalign list.to_chunks_nil
#noalign list.to_chunks_aux_eq
#noalign list.to_chunks_eq_cons'
#noalign list.to_chunks_eq_cons
#noalign list.to_chunks_aux_join
#noalign list.to_chunks_join
#noalign list.to_chunks_length_le

/-! ### all₂ -/

section All₂

variable {p q : α → Prop} {l : List α}

@[simp]
theorem all₂_cons (p : α → Prop) (x : α) : ∀ l : List α, All₂ p (x :: l) ↔ p x ∧ All₂ p l
  | [] => (and_true_iff _).symm
  | _ :: _ => Iff.rfl
#align list.all₂_cons List.all₂_cons

theorem all₂_iff_forall : ∀ {l : List α}, All₂ p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [forall_mem_cons, all₂_cons, all₂_iff_forall]
                 -- 🎉 no goals
#align list.all₂_iff_forall List.all₂_iff_forall

theorem All₂.imp (h : ∀ x, p x → q x) : ∀ {l : List α}, All₂ p l → All₂ q l
  | [] => id
  | x :: l => by simp; rw [←and_imp]; exact And.imp (h x) (All₂.imp h)
                 -- ⊢ p x → All₂ p l → q x ∧ All₂ q l
                       -- ⊢ p x ∧ All₂ p l → q x ∧ All₂ q l
                                      -- 🎉 no goals
#align list.all₂.imp List.All₂.imp

@[simp]
theorem all₂_map_iff {p : β → Prop} (f : α → β) : All₂ p (l.map f) ↔ All₂ (p ∘ f) l := by
  induction l <;> simp [*]
  -- ⊢ All₂ p (map f []) ↔ All₂ (p ∘ f) []
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.all₂_map_iff List.all₂_map_iff

instance (p : α → Prop) [DecidablePred p] : DecidablePred (All₂ p) := fun _ =>
  decidable_of_iff' _ all₂_iff_forall

end All₂

/-! ### Retroattributes

The list definitions happen earlier than `to_additive`, so here we tag the few multiplicative
definitions that couldn't be tagged earlier.
-/

attribute [to_additive existing] List.prod -- `List.sum`
attribute [to_additive existing] alternatingProd -- `List.alternatingSum`

/-! ### Miscellaneous lemmas -/

theorem getLast_reverse {l : List α} (hl : l.reverse ≠ [])
    (hl' : 0 < l.length := (by
      contrapose! hl
      -- ⊢ reverse l = []
      simpa [length_eq_zero] using hl)) :
      -- 🎉 no goals
    l.reverse.getLast hl = l.get ⟨0, hl'⟩ := by
  rw [getLast_eq_get, get_reverse']
  -- ⊢ get l { val := length l - 1 - ↑{ val := length (reverse l) - 1, isLt := (_ : …
  · simp
    -- 🎉 no goals
  · simpa using hl'
    -- 🎉 no goals
#align list.last_reverse List.getLast_reverse

theorem ilast'_mem : ∀ a l, @ilast' α a l ∈ a :: l
  | a, [] => by simp [ilast']
                -- 🎉 no goals
  | a, b :: l => by rw [mem_cons]; exact Or.inr (ilast'_mem b l)
                    -- ⊢ ilast' a (b :: l) = a ∨ ilast' a (b :: l) ∈ b :: l
                                   -- 🎉 no goals
#align list.ilast'_mem List.ilast'_mem

@[simp]
theorem get_attach (L : List α) (i) :
    (L.attach.get i).1 = L.get ⟨i, length_attach L ▸ i.2⟩ :=
  calc
    (L.attach.get i).1 = (L.attach.map Subtype.val).get ⟨i, by simpa using i.2⟩ :=
                                                               -- 🎉 no goals
      by rw [get_map]
         -- 🎉 no goals
    _ = L.get { val := i, isLt := _ } := by congr 2 <;> simp
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals

@[simp, deprecated get_attach]
theorem nthLe_attach (L : List α) (i) (H : i < L.attach.length) :
    (L.attach.nthLe i H).1 = L.nthLe i (length_attach L ▸ H) := get_attach ..
#align list.nth_le_attach List.nthLe_attach

@[simp 1100]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs := by
  induction' xs with x xs xs_ih
  -- ⊢ (y, x) ∈ map Prod.swap [] ↔ (x, y) ∈ []
  · simp only [not_mem_nil, map_nil]
    -- 🎉 no goals
  · cases' x with a b
    -- ⊢ (y, x) ∈ map Prod.swap ((a, b) :: xs) ↔ (x, y) ∈ (a, b) :: xs
    simp only [mem_cons, Prod.mk.inj_iff, map, Prod.swap_prod_mk, Prod.exists, xs_ih, and_comm]
    -- 🎉 no goals
#align list.mem_map_swap List.mem_map_swap

theorem dropSlice_eq (xs : List α) (n m : ℕ) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs
  -- ⊢ dropSlice zero m xs = take zero xs ++ drop (zero + m) xs
  · cases xs <;> simp [dropSlice]
    -- ⊢ dropSlice zero m [] = take zero [] ++ drop (zero + m) []
                 -- 🎉 no goals
                 -- 🎉 no goals
  · cases xs <;> simp [dropSlice, *, Nat.succ_add]
    -- ⊢ dropSlice (succ n✝) m [] = take (succ n✝) [] ++ drop (succ n✝ + m) []
                 -- 🎉 no goals
                 -- 🎉 no goals
#align list.slice_eq List.dropSlice_eq

theorem sizeOf_dropSlice_lt [SizeOf α] (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    SizeOf.sizeOf (List.dropSlice i j xs) < SizeOf.sizeOf xs := by
  induction xs generalizing i j hj with
  | nil => cases hi
  | cons x xs xs_ih =>
    cases i <;> simp only [List.dropSlice]
    · cases j with
      | zero => contradiction
      | succ n =>
        dsimp only [drop]; apply @lt_of_le_of_lt _ _ _ (sizeOf xs)
        induction xs generalizing n with
        | nil => rw [drop_nil]
        | cons _ xs_tl =>
          cases n
          · simp
          · simp [drop]
            rw [←Nat.zero_add (sizeOf (drop _ xs_tl))]
            exact Nat.add_le_add (Nat.zero_le _) (drop_sizeOf_le xs_tl _)
        · simp
    · simp
      apply xs_ih _ j hj
      apply lt_of_succ_lt_succ hi
#align list.sizeof_slice_lt List.sizeOf_dropSlice_lt

/-! ### getD and getI -/

section getD

variable (l : List α) (x : α) (xs : List α) (d : α) (n : ℕ)

@[simp]
theorem getD_nil : getD [] n d = d :=
  rfl
#align list.nthd_nil List.getD_nilₓ -- argument order

@[simp]
theorem getD_cons_zero : getD (x :: xs) 0 d = x :=
  rfl
#align list.nthd_cons_zero List.getD_cons_zeroₓ -- argument order

@[simp]
theorem getD_cons_succ : getD (x :: xs) (n + 1) d = getD xs n d :=
  rfl
#align list.nthd_cons_succ List.getD_cons_succₓ -- argument order

theorem getD_eq_get {n : ℕ} (hn : n < l.length) : l.getD n d = l.get ⟨n, hn⟩ := by
  induction' l with hd tl IH generalizing n
  -- ⊢ getD [] n d = get [] { val := n, isLt := hn }
  · exact absurd hn (not_lt_of_ge (Nat.zero_le _))
    -- 🎉 no goals
  · cases n
    -- ⊢ getD (hd :: tl) zero d = get (hd :: tl) { val := zero, isLt := hn }
    · exact getD_cons_zero _ _ _
      -- 🎉 no goals
    · exact IH _
      -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated getD_eq_get]
theorem getD_eq_nthLe {n : ℕ} (hn : n < l.length) : l.getD n d = l.nthLe n hn :=
  getD_eq_get ..
#align list.nthd_eq_nth_le List.getD_eq_nthLeₓ -- argument order

theorem getD_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getD n d = d := by
  induction' l with hd tl IH generalizing n
  -- ⊢ getD [] n d = d
  · exact getD_nil _ _
    -- 🎉 no goals
  · cases n
    -- ⊢ getD (hd :: tl) zero d = d
    · refine' absurd (Nat.zero_lt_succ _) (not_lt_of_ge hn)
      -- 🎉 no goals
    · exact IH (Nat.le_of_succ_le_succ hn)
      -- 🎉 no goals
#align list.nthd_eq_default List.getD_eq_defaultₓ -- argument order

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`. -/
def decidableGetDNilNe {α} (a : α) : DecidablePred fun i : ℕ => getD ([] : List α) i a ≠ a :=
  fun _ => isFalse fun H => H (getD_nil _ _)
#align list.decidable_nthd_nil_ne List.decidableGetDNilNeₓ -- argument order

@[simp]
theorem getD_singleton_default_eq (n : ℕ) : [d].getD n d = d := by cases n <;> simp
                                                                   -- ⊢ getD [d] zero d = d
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
#align list.nthd_singleton_default_eq List.getD_singleton_default_eqₓ -- argument order

@[simp]
theorem getD_replicate_default_eq (r n : ℕ) : (replicate r d).getD n d = d := by
  induction' r with r IH generalizing n
  -- ⊢ getD (replicate zero d) n d = d
  · simp
    -- 🎉 no goals
  · cases n <;> simp [IH]
    -- ⊢ getD (replicate (succ r) d) zero d = d
                -- 🎉 no goals
                -- 🎉 no goals
#align list.nthd_replicate_default_eq List.getD_replicate_default_eqₓ -- argument order

theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').getD n d = l.getD n d := by
  rw [getD_eq_get _ _ h', get_append _ h, getD_eq_get]
  -- 🎉 no goals
#align list.nthd_append List.getD_appendₓ -- argument order

theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  cases' lt_or_le n (l ++l').length with h' h'
  -- ⊢ getD (l ++ l') n d = getD l' (n - length l) d
  · rw [getD_eq_get (l ++ l') d h', get_append_right, getD_eq_get]
    -- ⊢ n - length l < length l'
    · rw [length_append] at h'
      -- ⊢ n - length l < length l'
      exact Nat.sub_lt_left_of_lt_add h h'
      -- 🎉 no goals
    · exact not_lt_of_le h
      -- 🎉 no goals
  · rw [getD_eq_default _ _ h', getD_eq_default]
    -- ⊢ length l' ≤ n - length l
    rwa [le_tsub_iff_left h, ← length_append]
    -- 🎉 no goals
#align list.nthd_append_right List.getD_append_rightₓ -- argument order

theorem getD_eq_getD_get? (n : ℕ) : l.getD n d = (l.get? n).getD d := by
  cases' lt_or_le n l.length with h h
  -- ⊢ getD l n d = Option.getD (get? l n) d
  · rw [getD_eq_get _ _ h, get?_eq_get h, Option.getD_some]
    -- 🎉 no goals
  · rw [getD_eq_default _ _ h, get?_eq_none.mpr h, Option.getD_none]
    -- 🎉 no goals
#align list.nthd_eq_get_or_else_nth List.getD_eq_getD_get?ₓ -- argument order

end getD

section getI

variable [Inhabited α] (l : List α) (x : α) (xs : List α) (n : ℕ)

@[simp]
theorem getI_nil : getI ([] : List α) n = default :=
  rfl
#align list.inth_nil List.getI_nil

@[simp]
theorem getI_cons_zero : getI (x :: xs) 0 = x :=
  rfl
#align list.inth_cons_zero List.getI_cons_zero

@[simp]
theorem getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n :=
  rfl
#align list.inth_cons_succ List.getI_cons_succ

theorem getI_eq_get {n : ℕ} (hn : n < l.length) : l.getI n = l.get ⟨n, hn⟩ :=
  getD_eq_get ..

@[deprecated getI_eq_get]
theorem getI_eq_nthLe {n : ℕ} (hn : n < l.length) : l.getI n = l.nthLe n hn :=
  getI_eq_get ..
#align list.inth_eq_nth_le List.getI_eq_nthLe

theorem getI_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getI n = default :=
  getD_eq_default _ _ hn
#align list.inth_eq_default List.getI_eq_default

theorem getD_default_eq_getI {n : ℕ} : l.getD n default = l.getI n :=
  rfl
#align list.nthd_default_eq_inth List.getD_default_eq_getIₓ -- new argument `n`

theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').getI n = l.getI n :=
  getD_append _ _ _ _ h h'
#align list.inth_append List.getI_append

theorem getI_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getI n = l'.getI (n - l.length) :=
  getD_append_right _ _ _ _ h
#align list.inth_append_right List.getI_append_right

theorem getI_eq_iget_get? (n : ℕ) : l.getI n = (l.get? n).iget := by
  rw [← getD_default_eq_getI, getD_eq_getD_get?, Option.getD_default_eq_iget]
  -- 🎉 no goals
#align list.inth_eq_iget_nth List.getI_eq_iget_get?

theorem getI_zero_eq_headI : l.getI 0 = l.headI := by cases l <;> rfl
                                                      -- ⊢ getI [] 0 = headI []
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
#align list.inth_zero_eq_head List.getI_zero_eq_headI

end getI

end List
