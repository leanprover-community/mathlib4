/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Join

#align_import data.list.permutation from "leanprover-community/mathlib"@"dd71334db81d0bd444af1ee339a29298bef40734"

/-!
# Permutations of a list

In this file we prove properties about `List.Permutations`, a list of all permutations of a list. It
is defined in `Data.List.Defs`.

## Order of the permutations

Designed for performance, the order in which the permutations appear in `List.Permutations` is
rather intricate and not very amenable to induction. That's why we also provide `List.Permutations'`
as a less efficient but more straightforward way of listing permutations.

### `List.Permutations`

TODO. In the meantime, you can try decrypting the docstrings.

### `List.Permutations'`

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

Show that `l.Nodup → l.permutations.Nodup`. See `Data.Fintype.List`.
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat

variable {α β : Type*}

namespace List

theorem permutationsAux2_fst (t : α) (ts : List α) (r : List β) :
    ∀ (ys : List α) (f : List α → β), (permutationsAux2 t ts r ys f).1 = ys ++ ts
  | [], f => rfl
  | y :: ys, f => by simp [permutationsAux2, permutationsAux2_fst t _ _ ys]
#align list.permutations_aux2_fst List.permutationsAux2_fst

@[simp]
theorem permutationsAux2_snd_nil (t : α) (ts : List α) (r : List β) (f : List α → β) :
    (permutationsAux2 t ts r [] f).2 = r :=
  rfl
#align list.permutations_aux2_snd_nil List.permutationsAux2_snd_nil

@[simp]
theorem permutationsAux2_snd_cons (t : α) (ts : List α) (r : List β) (y : α) (ys : List α)
    (f : List α → β) :
    (permutationsAux2 t ts r (y :: ys) f).2 =
      f (t :: y :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => f (y :: x)).2 := by
  simp [permutationsAux2, permutationsAux2_fst t _ _ ys]
#align list.permutations_aux2_snd_cons List.permutationsAux2_snd_cons

/-- The `r` argument to `permutationsAux2` is the same as appending. -/
theorem permutationsAux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f <;> simp [*]
#align list.permutations_aux2_append List.permutationsAux2_append

/-- The `ts` argument to `permutationsAux2` can be folded into the `f` argument. -/
theorem permutationsAux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : List α → β) :
    ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutationsAux2 t ts r ys f).2 := by
  induction' ys with ys_hd _ ys_ih generalizing f
  · simp
  · simp [ys_ih fun xs => f (ys_hd :: xs)]
#align list.permutations_aux2_comp_append List.permutationsAux2_comp_append

theorem map_permutationsAux2' {α' β'} (g : α → α') (g' : β → β') (t : α) (ts ys : List α)
    (r : List β) (f : List α → β) (f' : List α' → β') (H : ∀ a, g' (f a) = f' (map g a)) :
    map g' (permutationsAux2 t ts r ys f).2 =
      (permutationsAux2 (g t) (map g ts) (map g' r) (map g ys) f').2 := by
  induction' ys with ys_hd _ ys_ih generalizing f f'
  · simp
  · simp only [map, permutationsAux2_snd_cons, cons_append, cons.injEq]
    rw [ys_ih, permutationsAux2_fst]
    · refine ⟨?_, rfl⟩
      simp only [← map_cons, ← map_append]; apply H
    · intro a; apply H
#align list.map_permutations_aux2' List.map_permutationsAux2'

/-- The `f` argument to `permutationsAux2` when `r = []` can be eliminated. -/
theorem map_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2 := by
  rw [map_permutationsAux2' id, map_id, map_id]
  · rfl
  simp
#align list.map_permutations_aux2 List.map_permutationsAux2

/-- An expository lemma to show how all of `ts`, `r`, and `f` can be eliminated from
`permutationsAux2`.

`(permutationsAux2 t [] [] ys id).2`, which appears on the RHS, is a list whose elements are
produced by inserting `t` into every non-terminal position of `ys` in order. As an example:
```lean
#eval permutationsAux2 1 [] [] [2, 3, 4] id
-- [[1, 2, 3, 4], [2, 1, 3, 4], [2, 3, 1, 4]]
```
-/
theorem permutationsAux2_snd_eq (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts r ys f).2 =
      ((permutationsAux2 t [] [] ys id).2.map fun x => f (x ++ ts)) ++ r := by
  rw [← permutationsAux2_append, map_permutationsAux2, permutationsAux2_comp_append]
#align list.permutations_aux2_snd_eq List.permutationsAux2_snd_eq

theorem map_map_permutationsAux2 {α'} (g : α → α') (t : α) (ts ys : List α) :
    map (map g) (permutationsAux2 t ts [] ys id).2 =
      (permutationsAux2 (g t) (map g ts) [] (map g ys) id).2 :=
  map_permutationsAux2' _ _ _ _ _ _ _ _ fun _ => rfl
#align list.map_map_permutations_aux2 List.map_map_permutationsAux2

theorem map_map_permutations'Aux (f : α → β) (t : α) (ts : List α) :
    map (map f) (permutations'Aux t ts) = permutations'Aux (f t) (map f ts) := by
  induction' ts with a ts ih
  · rfl
  · simp only [permutations'Aux, map_cons, map_map, ← ih, cons.injEq, true_and, Function.comp_def]
#align list.map_map_permutations'_aux List.map_map_permutations'Aux

theorem permutations'Aux_eq_permutationsAux2 (t : α) (ts : List α) :
    permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2 := by
  induction' ts with a ts ih; · rfl
  simp only [permutations'Aux, ih, cons_append, permutationsAux2_snd_cons, append_nil, id_eq,
    cons.injEq, true_and]
  simp (config := { singlePass := true }) only [← permutationsAux2_append]
  simp [map_permutationsAux2]
#align list.permutations'_aux_eq_permutations_aux2 List.permutations'Aux_eq_permutationsAux2

theorem mem_permutationsAux2 {t : α} {ts : List α} {ys : List α} {l l' : List α} :
    l' ∈ (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts := by
  induction' ys with y ys ih generalizing l
  · simp (config := { contextual := true })
  rw [permutationsAux2_snd_cons,
    show (fun x : List α => l ++ y :: x) = (l ++ [y] ++ ·) by funext _; simp, mem_cons, ih]
  constructor
  · rintro (rfl | ⟨l₁, l₂, l0, rfl, rfl⟩)
    · exact ⟨[], y :: ys, by simp⟩
    · exact ⟨y :: l₁, l₂, l0, by simp⟩
  · rintro ⟨_ | ⟨y', l₁⟩, l₂, l0, ye, rfl⟩
    · simp [ye]
    · simp only [cons_append] at ye
      rcases ye with ⟨rfl, rfl⟩
      exact Or.inr ⟨l₁, l₂, l0, by simp⟩
#align list.mem_permutations_aux2 List.mem_permutationsAux2

theorem mem_permutationsAux2' {t : α} {ts : List α} {ys : List α} {l : List α} :
    l ∈ (permutationsAux2 t ts [] ys id).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts := by
  rw [show @id (List α) = ([] ++ ·) by funext _; rfl]; apply mem_permutationsAux2
#align list.mem_permutations_aux2' List.mem_permutationsAux2'

theorem length_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    length (permutationsAux2 t ts [] ys f).2 = length ys := by
  induction ys generalizing f <;> simp [*]
#align list.length_permutations_aux2 List.length_permutationsAux2

theorem foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    foldr (fun y r => (permutationsAux2 t ts r y id).2) r L =
      (L.bind fun y => (permutationsAux2 t ts [] y id).2) ++ r := by
  induction' L with l L ih
  · rfl
  · simp_rw [foldr_cons, ih, cons_bind, append_assoc, permutationsAux2_append]
#align list.foldr_permutations_aux2 List.foldr_permutationsAux2

theorem mem_foldr_permutationsAux2 {t : α} {ts : List α} {r L : List (List α)} {l' : List α} :
    l' ∈ foldr (fun y r => (permutationsAux2 t ts r y id).2) r L ↔
      l' ∈ r ∨ ∃ l₁ l₂, l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ ++ t :: l₂ ++ ts := by
  have :
    (∃ a : List α,
        a ∈ L ∧ ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
      ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ l₁ ++ l₂ ∈ L ∧ l' = l₁ ++ t :: (l₂ ++ ts) :=
    ⟨fun ⟨_, aL, l₁, l₂, l0, e, h⟩ => ⟨l₁, l₂, l0, e ▸ aL, h⟩, fun ⟨l₁, l₂, l0, aL, h⟩ =>
      ⟨_, aL, l₁, l₂, l0, rfl, h⟩⟩
  rw [foldr_permutationsAux2]
  simp only [mem_permutationsAux2', ← this, or_comm, and_left_comm, mem_append, mem_bind,
    append_assoc, cons_append, exists_prop]
#align list.mem_foldr_permutations_aux2 List.mem_foldr_permutationsAux2

theorem length_foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) =
      Nat.sum (map length L) + length r := by
  simp [foldr_permutationsAux2, (· ∘ ·), length_permutationsAux2, length_bind']
#align list.length_foldr_permutations_aux2 List.length_foldr_permutationsAux2

theorem length_foldr_permutationsAux2' (t : α) (ts : List α) (r L : List (List α)) (n)
    (H : ∀ l ∈ L, length l = n) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) = n * length L + length r := by
  rw [length_foldr_permutationsAux2, (_ : Nat.sum (map length L) = n * length L)]
  induction' L with l L ih
  · simp
  have sum_map : Nat.sum (map length L) = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
  have length_l : length l = n := H _ (mem_cons_self _ _)
  simp [sum_map, length_l, Nat.mul_add, Nat.add_comm, mul_succ]
#align list.length_foldr_permutations_aux2' List.length_foldr_permutationsAux2'

@[simp]
theorem permutationsAux_nil (is : List α) : permutationsAux [] is = [] := by
  rw [permutationsAux, permutationsAux.rec]
#align list.permutations_aux_nil List.permutationsAux_nil

@[simp]
theorem permutationsAux_cons (t : α) (ts is : List α) :
    permutationsAux (t :: ts) is =
      foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t :: is))
        (permutations is) := by
  rw [permutationsAux, permutationsAux.rec]; rfl
#align list.permutations_aux_cons List.permutationsAux_cons

@[simp]
theorem permutations_nil : permutations ([] : List α) = [[]] := by
  rw [permutations, permutationsAux_nil]
#align list.permutations_nil List.permutations_nil

theorem map_permutationsAux (f : α → β) :
    ∀ ts is :
    List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (map f is) := by
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2; rw [map] at IH2
  simp only [foldr_permutationsAux2, map_append, map, map_map_permutationsAux2, permutations,
    bind_map, IH1, append_assoc, permutationsAux_cons, cons_bind, ← IH2, map_bind]
#align list.map_permutations_aux List.map_permutationsAux

theorem map_permutations (f : α → β) (ts : List α) :
    map (map f) (permutations ts) = permutations (map f ts) := by
  rw [permutations, permutations, map, map_permutationsAux, map]
#align list.map_permutations List.map_permutations

theorem map_permutations' (f : α → β) (ts : List α) :
    map (map f) (permutations' ts) = permutations' (map f ts) := by
  induction' ts with t ts ih <;> [rfl; simp [← ih, map_bind, ← map_map_permutations'Aux, bind_map]]
#align list.map_permutations' List.map_permutations'

theorem permutationsAux_append (is is' ts : List α) :
    permutationsAux (is ++ ts) is' =
      (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++ is') := by
  induction' is with t is ih generalizing is'; · simp
  simp only [foldr_permutationsAux2, ih, bind_map, cons_append, permutationsAux_cons, map_append,
    reverse_cons, append_assoc, singleton_append]
  congr 2
  funext _
  rw [map_permutationsAux2]
  simp (config := { singlePass := true }) only [← permutationsAux2_comp_append]
  simp only [id, append_assoc]
#align list.permutations_aux_append List.permutationsAux_append

theorem permutations_append (is ts : List α) :
    permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reverse := by
  simp [permutations, permutationsAux_append]
#align list.permutations_append List.permutations_append

end List
