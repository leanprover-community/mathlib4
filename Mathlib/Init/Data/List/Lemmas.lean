/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Data.Nat.Lemmas

namespace List

open Nat

@[simp] theorem length_repeat' (a : α) (n : Nat) : length (repeat' a n) = n := by
  induction n <;> simp_all

@[simp] theorem length_tail (l : List α) : length (tail l) = length l - 1 := by cases l <;> rfl

@[simp] theorem length_drop : ∀ (i : Nat) (l : List α), length (drop i l) = length l - i
| 0, l => rfl
| succ i, [] => Eq.symm (Nat.zero_sub (succ i))
| succ i, x :: l => calc
  length (drop (succ i) (x :: l)) = length l - i := length_drop i l
  _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm

theorem map_nil {f : α → β} : map f [] = [] := rfl

theorem map_cons (f : α → β) a l : map f (a :: l) = f a :: map f l := rfl

@[simp] theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁ <;> induction l₁ <;> intros <;> simp_all

theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] := rfl

@[simp] theorem map_id (l : List α) : map id l = l := by induction l <;> simp_all

@[simp] theorem map_map (g : β → γ) (f : α → β) (l : List α) :
  map g (map f l) = map (g ∘ f) l := by induction l <;> simp_all

@[simp] theorem length_map (f : α → β) (l : List α) : length (map f l) = length l := by
  induction l <;> simp_all

@[simp] theorem nil_bind (f : α → List β) : List.bind [] f = [] := by simp [join, List.bind]

@[simp] theorem cons_bind x xs (f : α → List β) :
  List.bind (x :: xs) f = f x ++ List.bind xs f := by simp [join, List.bind]

@[simp] theorem append_bind xs ys (f : α → List β) :
  List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs; {rfl}; simp_all [cons_bind, append_assoc]

theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False := Iff.rfl

theorem not_mem_nil (a : α) : a ∉ ([] : List α) := not_false

theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l := Or.inl rfl

theorem mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) := rfl

theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := fun H => Or.inr H

theorem eq_or_mem_of_mem_cons {a y : α} {l : List α} : a ∈ y :: l → a = y ∨ a ∈ l := id

@[simp] theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp_all [or_assoc]

theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append

theorem mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)

theorem not_bex_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun ⟨x, hx, px⟩ => hx

theorem ball_nil (p : α → Prop) : ∀ x ∈ @nil α, p x := fun x => False.elim

theorem bex_cons (p : α → Prop) (a : α) (l : List α) :
  (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  ⟨fun
    | ⟨_, Or.inl rfl, px⟩ => Or.inl px
    | ⟨x, Or.inr h, px⟩ => Or.inr ⟨x, h, px⟩,
  fun o => o.elim
    (fun pa => ⟨a, mem_cons_self _ _, pa⟩)
    (fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_mem _ h, px⟩)⟩

theorem ball_cons (p : α → Prop) (a : α) (l : List α) : (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
  ⟨fun al => ⟨al a (mem_cons_self _ _), fun x h => al x (mem_cons_of_mem _ h)⟩,
    fun ⟨pa, al⟩ x o => o.elim (fun e => e.symm ▸ pa) (al x)⟩

protected def subset (l₁ l₂ : List α) :=
  ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : Subset (List α) := ⟨List.subset⟩

@[simp] theorem nil_subset (l : List α) : [] ⊆ l :=
  fun b i => False.elim (Iff.mp (mem_nil_iff b) i)

-- @[refl]
@[simp] theorem subset.refl (l : List α) : l ⊆ l := fun b i => i

-- @[trans]
theorem subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  fun b i => h₂ (h₁ i)

@[simp] theorem subset_cons (a : α) (l : List α) : l ⊆ a :: l := fun b i => Or.inr i

theorem subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
  fun s b i => s (mem_cons_of_mem _ i)

theorem cons_subset_cons {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ :=
  fun b hin => match eq_or_mem_of_mem_cons hin with
  | Or.inl e => Or.inl e
  | Or.inr i => Or.inr (s i)

@[simp]
theorem subset_append_left (l₁ l₂ : List α) : l₁ ⊆ l₁ ++ l₂ :=
  fun b => mem_append_left _

@[simp]
theorem subset_append_right (l₁ l₂ : List α) : l₂ ⊆ l₁ ++ l₂ :=
  fun b => mem_append_right _

theorem subset_cons_of_subset (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ :=
  fun s a i => Or.inr (s i)

theorem eq_nil_of_length_eq_zero {l : List α} : length l = 0 → l = [] :=   by
  induction l <;> intros; {rfl}; contradiction

theorem ne_nil_of_length_eq_succ {l : List α} : ∀ {n : Nat}, length l = succ n → l ≠ [] := by
  induction l <;> intros _ _ _ <;> contradiction

@[simp] theorem length_map₂ (f : α → β → γ) l₁ :
  ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;>
    simp_all [add_one, min_succ_succ, Nat.zero_min, Nat.min_zero]

@[simp] theorem length_take : ∀ (i : Nat) (l : List α), length (take i l) = min i (length l)
| 0, l => by simp [Nat.zero_min]
| succ n, [] => by simp [Nat.min_zero]
| succ n, a :: l => by simp [Nat.min_succ_succ, add_one, length_take]

theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [min_le_left]

theorem length_removeNth : ∀ (l : List α) (i : ℕ),
  i < length l → length (removeNth l i) = length l - 1
| [], _, h => rfl
| x::xs, 0, h => by simp [removeNth]; rfl
| x::xs, i+1, h => by
  have : i < length xs := Nat.lt_of_succ_lt_succ h
  simp [removeNth, ← Nat.add_one]
  rw [length_removeNth xs i this, Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le _) this)]; rfl

-- @[simp] theorem partition_eq_filter_filter (p : α → Bool) :
--   ∀ l : List α, partition p l = (filter p l, filter (not ∘ p) l)
-- | [] => rfl
-- | a :: l => by
--   cases pa: p a <;> simp [partition, partitionAux, filter, pa, partition_eq_filter_filter p l]

inductive sublist : List α → List α → Prop
  | slnil : sublist [] []
  | cons l₁ l₂ a : sublist l₁ l₂ → sublist l₁ (a :: l₂)
  | cons2 l₁ l₂ a : sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)

infixl:50 " <+ " => sublist

theorem length_le_of_sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ ≤ length l₂
| _, _, sublist.slnil => le_refl 0
| _, _, sublist.cons l₁ l₂ a s => le_succ_of_le (length_le_of_sublist s)
| _, _, sublist.cons2 l₁ l₂ a s => succ_le_succ (length_le_of_sublist s)
