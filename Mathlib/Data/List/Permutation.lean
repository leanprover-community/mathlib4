/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

! This file was ported from Lean 3 source module data.list.permutation
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Join

/-!
# Permutations of a list

In this file we prove properties about `list.permutations`, a list of all permutations of a list. It
is defined in `data.list.defs`.

## Order of the permutations

Designed for performance, the order in which the permutations appear in `list.permutations` is
rather intricate and not very amenable to induction. That's why we also provide `list.permutations'`
as a less efficient but more straightforward way of listing permutations.

### `list.permutations`

TODO. In the meantime, you can try decrypting the docstrings.

### `list.permutations'`

The list of partitions is built by recursion. The permutations of `[]` are `[[]]`. Then, the
permutations of `a :: l` are obtained by taking all permutations of `l` in order and adding `a` in
all positions. Hence, to build `[0, 1, 2, 3].permutations'`, it does
* `[[]]`
* `[[3]]`
* `[[2, 3], [3, 2]]]`
* `[[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]]`
* `[[0, 1, 2, 3], [1, 0, 2, 3], [1, 2, 0, 3], [1, 2, 3, 0],`
   `[0, 2, 1, 3], [2, 0, 1, 3], [2, 1, 0, 3], [2, 1, 3, 0],`
   `[0, 2, 3, 1], [2, 0, 3, 1], [2, 3, 0, 1], [2, 3, 1, 0],`
   `[0, 1, 3, 2], [1, 0, 3, 2], [1, 3, 0, 2], [1, 3, 2, 0],`
   `[0, 3, 1, 2], [3, 0, 1, 2], [3, 1, 0, 2], [3, 1, 2, 0],`
   `[0, 3, 2, 1], [3, 0, 2, 1], [3, 2, 0, 1], [3, 2, 1, 0]]`

## TODO

Show that `l.nodup → l.permutations.nodup`. See `data.fintype.list`.
-/


open Nat

variable {α β : Type _}

namespace List

theorem permutations_aux2_fst (t : α) (ts : List α) (r : List β) :
    ∀ (ys : List α) (f : List α → β), (permutationsAux2 t ts r ys f).1 = ys ++ ts
  | [], f => rfl
  | y :: ys, f =>
    match (motive :=
      ∀ o : List α × List β, o.1 = ys ++ ts → (permutationsAux2._match1 t y f o).1 = y :: ys ++ ts)
      _, permutations_aux2_fst ys _ with
    | ⟨_, zs⟩, rfl => rfl
#align list.permutations_aux2_fst List.permutations_aux2_fst

@[simp]
theorem permutations_aux2_snd_nil (t : α) (ts : List α) (r : List β) (f : List α → β) :
    (permutationsAux2 t ts r [] f).2 = r :=
  rfl
#align list.permutations_aux2_snd_nil List.permutations_aux2_snd_nil

@[simp]
theorem permutations_aux2_snd_cons (t : α) (ts : List α) (r : List β) (y : α) (ys : List α)
    (f : List α → β) :
    (permutationsAux2 t ts r (y :: ys) f).2 =
      f (t :: y :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => f (y :: x)).2 :=
  match (motive :=
    ∀ o : List α × List β,
      o.1 = ys ++ ts → (permutationsAux2._match1 t y f o).2 = f (t :: y :: ys ++ ts) :: o.2)
    _, permutations_aux2_fst t ts r _ _ with
  | ⟨_, zs⟩, rfl => rfl
#align list.permutations_aux2_snd_cons List.permutations_aux2_snd_cons

/-- The `r` argument to `permutations_aux2` is the same as appending. -/
theorem permutations_aux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f <;> simp [*]
#align list.permutations_aux2_append List.permutations_aux2_append

/-- The `ts` argument to `permutations_aux2` can be folded into the `f` argument. -/
theorem permutations_aux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : List α → β) :
    ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutationsAux2 t ts r ys f).2 :=
  by
  induction ys generalizing f
  · simp
  · simp [ys_ih fun xs => f (ys_hd :: xs)]
#align list.permutations_aux2_comp_append List.permutations_aux2_comp_append

theorem map_permutations_aux2' {α β α' β'} (g : α → α') (g' : β → β') (t : α) (ts ys : List α)
    (r : List β) (f : List α → β) (f' : List α' → β') (H : ∀ a, g' (f a) = f' (map g a)) :
    map g' (permutationsAux2 t ts r ys f).2 =
      (permutationsAux2 (g t) (map g ts) (map g' r) (map g ys) f').2 :=
  by
  induction ys generalizing f f' <;> simp [*]
  apply ys_ih; simp [H]
#align list.map_permutations_aux2' List.map_permutations_aux2'

/-- The `f` argument to `permutations_aux2` when `r = []` can be eliminated. -/
theorem map_permutations_aux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2 :=
  by
  rw [map_permutations_aux2' id, map_id, map_id]; rfl
  simp
#align list.map_permutations_aux2 List.map_permutations_aux2

/-- An expository lemma to show how all of `ts`, `r`, and `f` can be eliminated from
`permutations_aux2`.

`(permutations_aux2 t [] [] ys id).2`, which appears on the RHS, is a list whose elements are
produced by inserting `t` into every non-terminal position of `ys` in order. As an example:
```lean
#eval permutations_aux2 1 [] [] [2, 3, 4] id
-- [[1, 2, 3, 4], [2, 1, 3, 4], [2, 3, 1, 4]]
```
-/
theorem permutations_aux2_snd_eq (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts r ys f).2 =
      ((permutationsAux2 t [] [] ys id).2.map fun x => f (x ++ ts)) ++ r :=
  by rw [← permutations_aux2_append, map_permutations_aux2, permutations_aux2_comp_append]
#align list.permutations_aux2_snd_eq List.permutations_aux2_snd_eq

theorem map_map_permutations_aux2 {α α'} (g : α → α') (t : α) (ts ys : List α) :
    map (map g) (permutationsAux2 t ts [] ys id).2 =
      (permutationsAux2 (g t) (map g ts) [] (map g ys) id).2 :=
  map_permutations_aux2' _ _ _ _ _ _ _ _ fun _ => rfl
#align list.map_map_permutations_aux2 List.map_map_permutations_aux2

theorem map_map_permutations'_aux (f : α → β) (t : α) (ts : List α) :
    map (map f) (permutations'Aux t ts) = permutations'Aux (f t) (map f ts) := by
  induction' ts with a ts ih <;> [rfl,
    · simp [← ih]
      rfl]
#align list.map_map_permutations'_aux List.map_map_permutations'_aux

theorem permutations'_aux_eq_permutations_aux2 (t : α) (ts : List α) :
    permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2 :=
  by
  induction' ts with a ts ih; · rfl
  simp [permutations'_aux, permutations_aux2_snd_cons, ih]
  simp (config := { singlePass := true }) only [← permutations_aux2_append]
  simp [map_permutations_aux2]
#align list.permutations'_aux_eq_permutations_aux2 List.permutations'_aux_eq_permutations_aux2

theorem mem_permutations_aux2 {t : α} {ts : List α} {ys : List α} {l l' : List α} :
    l' ∈ (permutationsAux2 t ts [] ys (append l)).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts :=
  by
  induction' ys with y ys ih generalizing l
  · simp (config := { contextual := true })
  rw [permutations_aux2_snd_cons,
    show (fun x : List α => l ++ y :: x) = append (l ++ [y]) by funext <;> simp, mem_cons_iff, ih]
  constructor
  · rintro (rfl | ⟨l₁, l₂, l0, rfl, rfl⟩)
    · exact ⟨[], y :: ys, by simp⟩
    · exact ⟨y :: l₁, l₂, l0, by simp⟩
  · rintro ⟨_ | ⟨y', l₁⟩, l₂, l0, ye, rfl⟩
    · simp [ye]
    · simp only [cons_append] at ye
      rcases ye with ⟨rfl, rfl⟩
      exact Or.inr ⟨l₁, l₂, l0, by simp⟩
#align list.mem_permutations_aux2 List.mem_permutations_aux2

theorem mem_permutations_aux2' {t : α} {ts : List α} {ys : List α} {l : List α} :
    l ∈ (permutationsAux2 t ts [] ys id).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts :=
  by rw [show @id (List α) = append nil by funext <;> rfl] <;> apply mem_permutations_aux2
#align list.mem_permutations_aux2' List.mem_permutations_aux2'

theorem length_permutations_aux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    length (permutationsAux2 t ts [] ys f).2 = length ys := by
  induction ys generalizing f <;> simp [*]
#align list.length_permutations_aux2 List.length_permutations_aux2

theorem foldr_permutations_aux2 (t : α) (ts : List α) (r L : List (List α)) :
    foldr (fun y r => (permutationsAux2 t ts r y id).2) r L =
      (L.bind fun y => (permutationsAux2 t ts [] y id).2) ++ r :=
  by
  induction' L with l L ih <;> [rfl,
    · simp [ih]
      rw [← permutations_aux2_append]]
#align list.foldr_permutations_aux2 List.foldr_permutations_aux2

theorem mem_foldr_permutations_aux2 {t : α} {ts : List α} {r L : List (List α)} {l' : List α} :
    l' ∈ foldr (fun y r => (permutationsAux2 t ts r y id).2) r L ↔
      l' ∈ r ∨ ∃ l₁ l₂, l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ ++ t :: l₂ ++ ts :=
  by
  have :
    (∃ a : List α,
        a ∈ L ∧ ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
      ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ l₁ ++ l₂ ∈ L ∧ l' = l₁ ++ t :: (l₂ ++ ts) :=
    ⟨fun ⟨a, aL, l₁, l₂, l0, e, h⟩ => ⟨l₁, l₂, l0, e ▸ aL, h⟩, fun ⟨l₁, l₂, l0, aL, h⟩ =>
      ⟨_, aL, l₁, l₂, l0, rfl, h⟩⟩
  rw [foldr_permutations_aux2] <;>
    simp [mem_permutations_aux2', this, or_comm, or_left_comm, or_assoc, and_comm, and_left_comm,
      and_assoc]
#align list.mem_foldr_permutations_aux2 List.mem_foldr_permutations_aux2

theorem length_foldr_permutations_aux2 (t : α) (ts : List α) (r L : List (List α)) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) =
      sum (map length L) + length r :=
  by simp [foldr_permutations_aux2, (· ∘ ·), length_permutations_aux2]
#align list.length_foldr_permutations_aux2 List.length_foldr_permutations_aux2

theorem length_foldr_permutations_aux2' (t : α) (ts : List α) (r L : List (List α)) (n)
    (H : ∀ l ∈ L, length l = n) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) = n * length L + length r :=
  by
  rw [length_foldr_permutations_aux2, (_ : Sum (map length L) = n * length L)]
  induction' L with l L ih; · simp
  have sum_map : Sum (map length L) = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
  have length_l : length l = n := H _ (mem_cons_self _ _)
  simp [sum_map, length_l, mul_add, add_comm]
#align list.length_foldr_permutations_aux2' List.length_foldr_permutations_aux2'

@[simp]
theorem permutations_aux_nil (is : List α) : permutationsAux [] is = [] := by
  rw [permutations_aux, permutations_aux.rec]
#align list.permutations_aux_nil List.permutations_aux_nil

@[simp]
theorem permutations_aux_cons (t : α) (ts is : List α) :
    permutationsAux (t :: ts) is =
      foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t :: is))
        (permutations is) :=
  by rw [permutations_aux, permutations_aux.rec] <;> rfl
#align list.permutations_aux_cons List.permutations_aux_cons

@[simp]
theorem permutations_nil : permutations ([] : List α) = [[]] := by
  rw [permutations, permutations_aux_nil]
#align list.permutations_nil List.permutations_nil

theorem map_permutations_aux (f : α → β) :
    ∀ ts is : List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (map f is) :=
  by
  refine' permutations_aux.rec (by simp) _
  introv IH1 IH2; rw [map] at IH2
  simp only [foldr_permutations_aux2, map_append, map, map_map_permutations_aux2, permutations,
    bind_map, IH1, append_assoc, permutations_aux_cons, cons_bind, ← IH2, map_bind]
#align list.map_permutations_aux List.map_permutations_aux

theorem map_permutations (f : α → β) (ts : List α) :
    map (map f) (permutations ts) = permutations (map f ts) := by
  rw [permutations, permutations, map, map_permutations_aux, map]
#align list.map_permutations List.map_permutations

theorem map_permutations' (f : α → β) (ts : List α) :
    map (map f) (permutations' ts) = permutations' (map f ts) := by
  induction' ts with t ts ih <;> [rfl, simp [← ih, map_bind, ← map_map_permutations'_aux, bind_map]]
#align list.map_permutations' List.map_permutations'

theorem permutations_aux_append (is is' ts : List α) :
    permutationsAux (is ++ ts) is' =
      (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++ is') :=
  by
  induction' is with t is ih generalizing is'; · simp
  simp [foldr_permutations_aux2, ih, bind_map]
  congr 2; funext ys; rw [map_permutations_aux2]
  simp (config := { singlePass := true }) only [← permutations_aux2_comp_append]
  simp only [id, append_assoc]
#align list.permutations_aux_append List.permutations_aux_append

theorem permutations_append (is ts : List α) :
    permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reverse := by
  simp [permutations, permutations_aux_append]
#align list.permutations_append List.permutations_append

end List

