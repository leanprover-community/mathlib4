/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Function
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Meta.Smt.Rsimp

#align_import init.data.list.lemmas from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

universe u v w w₁ w₂

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

open Nat

/-! append -/


#print List.nil_append /-
@[simp]
theorem nil_append (s : List α) : [] ++ s = s :=
  rfl
#align list.nil_append List.nil_append
-/

#print List.cons_append /-
@[simp]
theorem cons_append (x : α) (s t : List α) : x :: s ++ t = x :: (s ++ t) :=
  rfl
#align list.cons_append List.cons_append
-/

#print List.append_nil /-
@[simp]
theorem append_nil (t : List α) : t ++ [] = t := by induction t <;> simp [*]
#align list.append_nil List.append_nil
-/

#print List.append_assoc /-
@[simp]
theorem append_assoc (s t u : List α) : s ++ t ++ u = s ++ (t ++ u) := by induction s <;> simp [*]
#align list.append_assoc List.append_assoc
-/

/-! length -/


#print List.length_cons /-
theorem length_cons (a : α) (l : List α) : length (a :: l) = length l + 1 :=
  rfl
#align list.length_cons List.length_cons
-/

#print List.length_append /-
@[simp]
theorem length_append (s t : List α) : length (s ++ t) = length s + length t :=
  by
  induction s
  · show length t = 0 + length t; · rw [Nat.zero_add]
  · simp [*, Nat.add_comm, Nat.add_left_comm]
#align list.length_append List.length_append
-/

@[simp]
theorem length_repeat (a : α) (n : ℕ) : length (repeat a n) = n := by
  induction n <;> simp [*] <;> rfl
#align list.length_repeat List.length_repeat

#print List.length_tail /-
@[simp]
theorem length_tail (l : List α) : length (tail l) = length l - 1 := by cases l <;> rfl
#align list.length_tail List.length_tail
-/

#print List.length_drop /-
-- TODO(Leo): cleanup proof after arith dec proc
@[simp]
theorem length_drop : ∀ (i : ℕ) (l : List α), length (drop i l) = length l - i
  | 0, l => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l =>
    calc
      length (drop (succ i) (x :: l)) = length l - i := length_drop i l
      _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm
#align list.length_drop List.length_drop
-/

/-! map -/


#print List.map_cons /-
theorem map_cons (f : α → β) (a l) : map f (a :: l) = f a :: map f l :=
  rfl
#align list.map_cons List.map_cons
-/

#print List.map_append /-
@[simp]
theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁ <;> induction l₁ <;> intros <;> simp [*]
#align list.map_append List.map_append
-/

#print List.map_singleton /-
theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
  rfl
#align list.map_singleton List.map_singleton
-/

#print List.map_id /-
@[simp]
theorem map_id (l : List α) : map id l = l := by induction l <;> simp [*]
#align list.map_id List.map_id
-/

#print List.map_map /-
@[simp]
theorem map_map (g : β → γ) (f : α → β) (l : List α) : map g (map f l) = map (g ∘ f) l := by
  induction l <;> simp [*]
#align list.map_map List.map_map
-/

#print List.length_map /-
@[simp]
theorem length_map (f : α → β) (l : List α) : length (map f l) = length l := by
  induction l <;> simp [*]
#align list.length_map List.length_map
-/

/-! bind -/


#print List.nil_bind /-
@[simp]
theorem nil_bind (f : α → List β) : List.bind [] f = [] := by simp [join, List.bind]
#align list.nil_bind List.nil_bind
-/

#print List.cons_bind /-
@[simp]
theorem cons_bind (x xs) (f : α → List β) : List.bind (x :: xs) f = f x ++ List.bind xs f := by
  simp [join, List.bind]
#align list.cons_bind List.cons_bind
-/

#print List.append_bind /-
@[simp]
theorem append_bind (xs ys) (f : α → List β) :
    List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs <;> [rfl; simp [*, cons_bind]]
#align list.append_bind List.append_bind
-/

/-! mem -/


#print List.mem_nil_iff /-
theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False :=
  Iff.rfl
#align list.mem_nil_iff List.mem_nil_iff
-/

#print List.not_mem_nil /-
@[simp]
theorem not_mem_nil (a : α) : a ∉ ([] : List α) :=
  not_false
#align list.not_mem_nil List.not_mem_nil
-/

#print List.mem_cons_self /-
theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l :=
  Or.inl rfl
#align list.mem_cons_self List.mem_cons_self
-/

#print List.mem_cons /-
@[simp]
theorem mem_cons (a y : α) (l : List α) : a ∈ y :: l ↔ a = y ∨ a ∈ l :=
  Iff.rfl
#align list.mem_cons_iff List.mem_cons
-/

@[rsimp]
theorem mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
  rfl
#align list.mem_cons_eq List.mem_cons_eq

#print List.mem_cons_of_mem /-
theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := fun H => Or.inr H
#align list.mem_cons_of_mem List.mem_cons_of_mem
-/

#print List.eq_or_mem_of_mem_cons /-
theorem eq_or_mem_of_mem_cons {a y : α} {l : List α} : a ∈ y :: l → a = y ∨ a ∈ l := fun h => h
#align list.eq_or_mem_of_mem_cons List.eq_or_mem_of_mem_cons
-/

#print List.mem_append /-
@[simp]
theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp [*, or_assoc']
#align list.mem_append List.mem_append
-/

#print List.mem_append_eq /-
@[rsimp]
theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append
#align list.mem_append_eq List.mem_append_eq
-/

#print List.mem_append_left /-
theorem mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)
#align list.mem_append_left List.mem_append_left
-/

#print List.mem_append_right /-
theorem mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)
#align list.mem_append_right List.mem_append_right
-/

theorem not_bex_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun ⟨x, hx, px⟩ => hx
#align list.not_bex_nil List.not_bex_nil

#print List.forall_mem_nil /-
theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x := fun x => False.elim
#align list.ball_nil List.forall_mem_nil
-/

theorem bex_cons (p : α → Prop) (a : α) (l : List α) : (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  ⟨fun ⟨x, h, px⟩ => by simp at h ; cases' h with h h; · cases h; exact Or.inl px;
    · exact Or.inr ⟨x, h, px⟩, fun o =>
    o.elim (fun pa => ⟨a, mem_cons_self _ _, pa⟩) fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_mem _ h, px⟩⟩
#align list.bex_cons List.bex_cons

theorem forall_mem_cons (p : α → Prop) (a : α) (l : List α) :
    (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
  ⟨fun al => ⟨al a (mem_cons_self _ _), fun x h => al x (mem_cons_of_mem _ h)⟩, fun ⟨pa, al⟩ x o =>
    o.elim (fun e => e.symm ▸ pa) (al x)⟩
#align list.ball_cons List.forall_mem_consₓ

/-! list subset -/


#print List.Subset /-
protected def Subset (l₁ l₂ : List α) :=
  ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂
#align list.subset List.Subset
-/

instance : HasSubset (List α) :=
  ⟨List.Subset⟩

#print List.nil_subset /-
@[simp]
theorem nil_subset (l : List α) : [] ⊆ l := fun b i => False.elim (Iff.mp (mem_nil_iff b) i)
#align list.nil_subset List.nil_subset
-/

#print List.Subset.refl /-
@[refl, simp]
theorem Subset.refl (l : List α) : l ⊆ l := fun b i => i
#align list.subset.refl List.Subset.refl
-/

#print List.Subset.trans /-
@[trans]
theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ := fun b i =>
  h₂ (h₁ i)
#align list.subset.trans List.Subset.trans
-/

#print List.subset_cons /-
@[simp]
theorem subset_cons (a : α) (l : List α) : l ⊆ a :: l := fun b i => Or.inr i
#align list.subset_cons List.subset_cons
-/

#print List.subset_of_cons_subset /-
theorem subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ := fun s b i =>
  s (mem_cons_of_mem _ i)
#align list.subset_of_cons_subset List.subset_of_cons_subset
-/

#print List.cons_subset_cons /-
theorem cons_subset_cons {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ := fun b hin =>
  Or.elim (eq_or_mem_of_mem_cons hin) (fun e : b = a => Or.inl e) fun i : b ∈ l₁ => Or.inr (s i)
#align list.cons_subset_cons List.cons_subset_cons
-/

#print List.subset_append_left /-
@[simp]
theorem subset_append_left (l₁ l₂ : List α) : l₁ ⊆ l₁ ++ l₂ := fun b => mem_append_left _
#align list.subset_append_left List.subset_append_left
-/

#print List.subset_append_right /-
@[simp]
theorem subset_append_right (l₁ l₂ : List α) : l₂ ⊆ l₁ ++ l₂ := fun b => mem_append_right _
#align list.subset_append_right List.subset_append_right
-/

#print List.subset_cons_of_subset /-
theorem subset_cons_of_subset (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ :=
  fun (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁) => Or.inr (s i)
#align list.subset_cons_of_subset List.subset_cons_of_subset
-/

#print List.eq_nil_of_length_eq_zero /-
theorem eq_nil_of_length_eq_zero {l : List α} : length l = 0 → l = [] := by induction l <;> intros;
  rfl; contradiction
#align list.eq_nil_of_length_eq_zero List.eq_nil_of_length_eq_zero
-/

#print List.ne_nil_of_length_eq_succ /-
theorem ne_nil_of_length_eq_succ {l : List α} : ∀ {n : Nat}, length l = succ n → l ≠ [] := by
  induction l <;> intros <;> contradiction
#align list.ne_nil_of_length_eq_succ List.ne_nil_of_length_eq_succ
-/

#print List.length_zipWith /-
@[simp]
theorem length_zipWith (f : α → β → γ) (l₁) :
    ∀ l₂, length (zipWith f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;>
    simp [*, add_one, min_succ_succ, Nat.zero_min, Nat.min_zero]
#align list.length_map₂ List.length_zipWith
-/

#print List.length_take /-
@[simp]
theorem length_take : ∀ (i : ℕ) (l : List α), length (take i l) = min i (length l)
  | 0, l => by simp [Nat.zero_min]
  | succ n, [] => by simp [Nat.min_zero]
  | succ n, a :: l => by simp [*, Nat.min_succ_succ, add_one]
#align list.length_take List.length_take
-/

#print List.length_take_le /-
theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [min_le_left]
#align list.length_take_le List.length_take_le
-/

#print List.length_removeNth /-
theorem length_removeNth :
    ∀ (l : List α) (i : ℕ), i < length l → length (removeNth l i) = length l - 1
  | [], _, h => rfl
  | x :: xs, 0, h => by simp [remove_nth]
  | x :: xs, i + 1, h => by
    have : i < length xs := lt_of_succ_lt_succ h
    dsimp [remove_nth] <;>
        rw [length_remove_nth xs i this,
          Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le _) this)] <;>
      rfl
#align list.length_remove_nth List.length_removeNth
-/

@[simp]
theorem partition_eq_filter_filter (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, partition p l = (filter p l, filter (Not ∘ p) l)
  | [] => rfl
  | a :: l => by by_cases pa : p a <;> simp [partition, Filter, pa, partition_eq_filter_filter l]
#align list.partition_eq_filter_filter List.partitionₓ_eq_filterₓ_filterₓ

/-! sublists -/


#print List.Sublist /-
inductive Sublist : List α → List α → Prop
  | slnil : sublist [] []
  | cons (l₁ l₂ a) : sublist l₁ l₂ → sublist l₁ (a :: l₂)
  | cons2 (l₁ l₂ a) : sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)
#align list.sublist List.Sublist
-/

infixl:50 " <+ " => Sublist

#print List.length_le_of_sublist /-
theorem length_le_of_sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ ≤ length l₂
  | _, _, sublist.slnil => le_refl 0
  | _, _, sublist.cons l₁ l₂ a s => le_succ_of_le (length_le_of_sublist s)
  | _, _, sublist.cons2 l₁ l₂ a s => succ_le_succ (length_le_of_sublist s)
#align list.length_le_of_sublist List.length_le_of_sublist
-/

/-! filter -/


#print List.filter_nil /-
@[simp]
theorem filter_nil (p : α → Prop) [h : DecidablePred p] : filter p [] = [] :=
  rfl
#align list.filter_nil List.filter_nil
-/

#print List.filter_cons_of_pos /-
@[simp]
theorem filter_cons_of_pos {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, p a → filter p (a :: l) = a :: filter p l := fun l pa => if_pos pa
#align list.filter_cons_of_pos List.filter_cons_of_pos
-/

#print List.filter_cons_of_neg /-
@[simp]
theorem filter_cons_of_neg {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, ¬p a → filter p (a :: l) = filter p l := fun l pa => if_neg pa
#align list.filter_cons_of_neg List.filter_cons_of_neg
-/

#print List.filter_append /-
@[simp]
theorem filter_append {p : α → Prop} [h : DecidablePred p] :
    ∀ l₁ l₂ : List α, filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by by_cases pa : p a <;> simp [pa, filter_append]
#align list.filter_append List.filter_append
-/

#print List.filter_sublist /-
@[simp]
theorem filter_sublist {p : α → Prop} [h : DecidablePred p] : ∀ l : List α, filter p l <+ l
  | [] => Sublist.slnil
  | a :: l =>
    if pa : p a then by simp [pa] <;> apply sublist.cons2 <;> apply filter_sublist l
    else by simp [pa] <;> apply sublist.cons <;> apply filter_sublist l
#align list.filter_sublist List.filter_sublist
-/

/-! map_accumr -/


section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

#print List.mapAccumr /-
-- This runs a function over a list returning the intermediate results and a
-- a final result.
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := map_accumr yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)
#align list.map_accumr List.mapAccumr
-/

#print List.length_mapAccumr /-
@[simp]
theorem length_mapAccumr :
    ∀ (f : α → σ → σ × β) (x : List α) (s : σ), length (mapAccumr f x s).2 = length x
  | f, a :: x, s => congr_arg succ (length_map_accumr f x s)
  | f, [], s => rfl
#align list.length_map_accumr List.length_mapAccumr
-/

end MapAccumr

section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

#print List.mapAccumr₂ /-
-- This runs a function over two lists returning the intermediate results and a
-- a final result.
def mapAccumr₂ (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := map_accumr₂ xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)
#align list.map_accumr₂ List.mapAccumr₂
-/

#print List.length_mapAccumr₂ /-
@[simp]
theorem length_mapAccumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, a :: x, b :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_map_accumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succ (length x) (length y))
  | f, a :: x, [], c => rfl
  | f, [], b :: y, c => rfl
  | f, [], [], c => rfl
#align list.length_map_accumr₂ List.length_mapAccumr₂
-/

end MapAccumr₂

end List

