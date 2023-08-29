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


open Nat

variable {α β : Type*}

namespace List

theorem permutationsAux2_fst (t : α) (ts : List α) (r : List β) :
    ∀ (ys : List α) (f : List α → β), (permutationsAux2 t ts r ys f).1 = ys ++ ts
  | [], f => rfl
  | y :: ys, f => by simp [permutationsAux2, permutationsAux2_fst t _ _ ys]
                     -- 🎉 no goals
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
      f (t :: y :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => f (y :: x)).2 :=
  by simp [permutationsAux2, permutationsAux2_fst t _ _ ys]
     -- 🎉 no goals
#align list.permutations_aux2_snd_cons List.permutationsAux2_snd_cons

/-- The `r` argument to `permutationsAux2` is the same as appending. -/
theorem permutationsAux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f <;> simp [*]
  -- ⊢ (permutationsAux2 t ts [] [] f).snd ++ r = (permutationsAux2 t ts r [] f).snd
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align list.permutations_aux2_append List.permutationsAux2_append

/-- The `ts` argument to `permutationsAux2` can be folded into the `f` argument. -/
theorem permutationsAux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : List α → β) :
    ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutationsAux2 t ts r ys f).2 := by
  induction' ys with ys_hd _ ys_ih generalizing f
  -- ⊢ (permutationsAux2 t [] r [] fun x => f (x ++ ts)).snd = (permutationsAux2 t  …
  · simp
    -- 🎉 no goals
  · simp [ys_ih fun xs => f (ys_hd :: xs)]
    -- 🎉 no goals
#align list.permutations_aux2_comp_append List.permutationsAux2_comp_append

theorem map_permutationsAux2' {α β α' β'} (g : α → α') (g' : β → β') (t : α) (ts ys : List α)
    (r : List β) (f : List α → β) (f' : List α' → β') (H : ∀ a, g' (f a) = f' (map g a)) :
    map g' (permutationsAux2 t ts r ys f).2 =
      (permutationsAux2 (g t) (map g ts) (map g' r) (map g ys) f').2 := by
  induction' ys with ys_hd _ ys_ih generalizing f f'
  -- ⊢ map g' (permutationsAux2 t ts r [] f).snd = (permutationsAux2 (g t) (map g t …
  · simp
    -- 🎉 no goals
  · simp only [map, permutationsAux2_snd_cons, cons_append, cons.injEq]
    -- ⊢ g' (f (t :: ys_hd :: (permutationsAux2 t ts r tail✝ fun x => f (ys_hd :: x)) …
    rw [ys_ih, permutationsAux2_fst]
    refine' ⟨_, rfl⟩
    -- ⊢ g' (f (t :: ys_hd :: (tail✝ ++ ts))) = f' (g t :: g ys_hd :: (map g tail✝ ++ …
    · simp only [← map_cons, ← map_append]; apply H
      -- ⊢ g' (f (t :: ys_hd :: (tail✝ ++ ts))) = f' (map g (t :: ys_hd :: (tail✝ ++ ts …
                                            -- 🎉 no goals
    · intro a; apply H
      -- ⊢ g' (f (ys_hd :: a)) = f' (g ys_hd :: map g a)
               -- 🎉 no goals
#align list.map_permutations_aux2' List.map_permutationsAux2'

/-- The `f` argument to `permutationsAux2` when `r = []` can be eliminated. -/
theorem map_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2 := by
  rw [map_permutationsAux2' id, map_id, map_id]; rfl
                                                 -- ⊢ ∀ (a : List α), f (id a) = f (map id a)
  simp
  -- 🎉 no goals
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
      ((permutationsAux2 t [] [] ys id).2.map fun x => f (x ++ ts)) ++ r :=
  by rw [← permutationsAux2_append, map_permutationsAux2, permutationsAux2_comp_append]
     -- 🎉 no goals
#align list.permutations_aux2_snd_eq List.permutationsAux2_snd_eq

theorem map_map_permutationsAux2 {α α'} (g : α → α') (t : α) (ts ys : List α) :
    map (map g) (permutationsAux2 t ts [] ys id).2 =
      (permutationsAux2 (g t) (map g ts) [] (map g ys) id).2 :=
  map_permutationsAux2' _ _ _ _ _ _ _ _ fun _ => rfl
#align list.map_map_permutations_aux2 List.map_map_permutationsAux2

theorem map_map_permutations'Aux (f : α → β) (t : α) (ts : List α) :
    map (map f) (permutations'Aux t ts) = permutations'Aux (f t) (map f ts) := by
  induction' ts with a ts ih <;> [rfl; (simp [← ih]; rfl)]
  -- 🎉 no goals
#align list.map_map_permutations'_aux List.map_map_permutations'Aux

theorem permutations'Aux_eq_permutationsAux2 (t : α) (ts : List α) :
    permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2 := by
  induction' ts with a ts ih; · rfl
  -- ⊢ permutations'Aux t [] = (permutationsAux2 t [] [[] ++ [t]] [] id).snd
                                -- 🎉 no goals
  simp [permutations'Aux, permutationsAux2_snd_cons, ih]
  -- ⊢ map (cons a) (permutationsAux2 t [] [ts ++ [t]] ts id).snd = (permutationsAu …
  simp (config := { singlePass := true }) only [← permutationsAux2_append]
  -- ⊢ map (cons a) ((permutationsAux2 t [] [] ts id).snd ++ [ts ++ [t]]) = (permut …
  simp [map_permutationsAux2]
  -- 🎉 no goals
#align list.permutations'_aux_eq_permutations_aux2 List.permutations'Aux_eq_permutationsAux2

theorem mem_permutationsAux2 {t : α} {ts : List α} {ys : List α} {l l' : List α} :
    l' ∈ (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts := by
  induction' ys with y ys ih generalizing l
  -- ⊢ l' ∈ (permutationsAux2 t ts [] [] fun x => l ++ x).snd ↔ ∃ l₁ l₂, l₂ ≠ [] ∧  …
  · simp (config := { contextual := true })
    -- 🎉 no goals
  rw [permutationsAux2_snd_cons,
    show (fun x : List α => l ++ y :: x) = (l ++ [y] ++ ·) by funext _; simp, mem_cons, ih]
  constructor
  -- ⊢ (l' = l ++ (t :: y :: ys ++ ts) ∨ ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l  …
  · rintro (rfl | ⟨l₁, l₂, l0, rfl, rfl⟩)
    -- ⊢ ∃ l₁ l₂, l₂ ≠ [] ∧ y :: ys = l₁ ++ l₂ ∧ l ++ (t :: y :: ys ++ ts) = l ++ l₁  …
    · exact ⟨[], y :: ys, by simp⟩
      -- 🎉 no goals
    · exact ⟨y :: l₁, l₂, l0, by simp⟩
      -- 🎉 no goals
  · rintro ⟨_ | ⟨y', l₁⟩, l₂, l0, ye, rfl⟩
    -- ⊢ l ++ [] ++ t :: l₂ ++ ts = l ++ (t :: y :: ys ++ ts) ∨ ∃ l₁ l₂_1, l₂_1 ≠ []  …
    · simp [ye]
      -- 🎉 no goals
    · simp only [cons_append] at ye
      -- ⊢ l ++ y' :: l₁ ++ t :: l₂ ++ ts = l ++ (t :: y :: ys ++ ts) ∨ ∃ l₁_1 l₂_1, l₂ …
      rcases ye with ⟨rfl, rfl⟩
      -- ⊢ l ++ y :: l₁ ++ t :: l₂ ++ ts = l ++ (t :: y :: (l₁ ++ l₂) ++ ts) ∨ ∃ l₁_1 l …
      exact Or.inr ⟨l₁, l₂, l0, by simp⟩
      -- 🎉 no goals
#align list.mem_permutations_aux2 List.mem_permutationsAux2

theorem mem_permutationsAux2' {t : α} {ts : List α} {ys : List α} {l : List α} :
    l ∈ (permutationsAux2 t ts [] ys id).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts :=
  by rw [show @id (List α) = ([] ++ ·) by funext _; rfl]; apply mem_permutationsAux2
     -- ⊢ l ∈ (permutationsAux2 t ts [] ys fun x => [] ++ x).snd ↔ ∃ l₁ l₂, l₂ ≠ [] ∧  …
                                                          -- 🎉 no goals
#align list.mem_permutations_aux2' List.mem_permutationsAux2'

theorem length_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    length (permutationsAux2 t ts [] ys f).2 = length ys := by
  induction ys generalizing f <;> simp [*]
  -- ⊢ length (permutationsAux2 t ts [] [] f).snd = length []
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align list.length_permutations_aux2 List.length_permutationsAux2

theorem foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    foldr (fun y r => (permutationsAux2 t ts r y id).2) r L =
      (L.bind fun y => (permutationsAux2 t ts [] y id).2) ++ r := by
  induction' L with l L ih
  -- ⊢ foldr (fun y r => (permutationsAux2 t ts r y id).snd) r [] = (List.bind [] f …
  · rfl
    -- 🎉 no goals
  · simp [ih]
    -- ⊢ (permutationsAux2 t ts ((List.bind L fun y => (permutationsAux2 t ts [] y id …
    rw [← permutationsAux2_append]
    -- 🎉 no goals
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
  -- ⊢ l' ∈ (List.bind L fun y => (permutationsAux2 t ts [] y id).snd) ++ r ↔ l' ∈  …
  simp only [mem_permutationsAux2', ← this, or_comm, and_left_comm, mem_append, mem_bind,
    append_assoc, cons_append, exists_prop]
#align list.mem_foldr_permutations_aux2 List.mem_foldr_permutationsAux2

theorem length_foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) =
      sum (map length L) + length r :=
  by simp [foldr_permutationsAux2, (· ∘ ·), length_permutationsAux2]
     -- 🎉 no goals
#align list.length_foldr_permutations_aux2 List.length_foldr_permutationsAux2

theorem length_foldr_permutationsAux2' (t : α) (ts : List α) (r L : List (List α)) (n)
    (H : ∀ l ∈ L, length l = n) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) = n * length L + length r := by
  rw [length_foldr_permutationsAux2, (_ : List.sum (map length L) = n * length L)]
  -- ⊢ sum (map length L) = n * length L
  induction' L with l L ih
  -- ⊢ sum (map length []) = n * length []
  · simp
    -- 🎉 no goals
  have sum_map : sum (map length L) = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
  -- ⊢ sum (map length (l :: L)) = n * length (l :: L)
  have length_l : length l = n := H _ (mem_cons_self _ _)
  -- ⊢ sum (map length (l :: L)) = n * length (l :: L)
  simp [sum_map, length_l, mul_add, add_comm, mul_succ]
  -- 🎉 no goals
#align list.length_foldr_permutations_aux2' List.length_foldr_permutationsAux2'

@[simp]
theorem permutationsAux_nil (is : List α) : permutationsAux [] is = [] := by
  rw [permutationsAux, permutationsAux.rec]
  -- 🎉 no goals
#align list.permutations_aux_nil List.permutationsAux_nil

@[simp]
theorem permutationsAux_cons (t : α) (ts is : List α) :
    permutationsAux (t :: ts) is =
      foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t :: is))
        (permutations is) :=
  by rw [permutationsAux, permutationsAux.rec]; rfl
     -- ⊢ foldr (fun y r => (permutationsAux2 t ts r y id).snd) (permutationsAux.rec ( …
                                                -- 🎉 no goals
#align list.permutations_aux_cons List.permutationsAux_cons

@[simp]
theorem permutations_nil : permutations ([] : List α) = [[]] := by
  rw [permutations, permutationsAux_nil]
  -- 🎉 no goals
#align list.permutations_nil List.permutations_nil

theorem map_permutationsAux (f : α → β) :
    ∀ ts is :
    List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (map f is) := by
  refine' permutationsAux.rec (by simp) _
  -- ⊢ ∀ (t : α) (ts is : List α), map (map f) (permutationsAux ts (t :: is)) = per …
  introv IH1 IH2; rw [map] at IH2
  -- ⊢ map (map f) (permutationsAux (t :: ts) is) = permutationsAux (map f (t :: ts …
                  -- ⊢ map (map f) (permutationsAux (t :: ts) is) = permutationsAux (map f (t :: ts …
  simp only [foldr_permutationsAux2, map_append, map, map_map_permutationsAux2, permutations,
    bind_map, IH1, append_assoc, permutationsAux_cons, cons_bind, ← IH2, map_bind]
#align list.map_permutations_aux List.map_permutationsAux

theorem map_permutations (f : α → β) (ts : List α) :
    map (map f) (permutations ts) = permutations (map f ts) := by
  rw [permutations, permutations, map, map_permutationsAux, map]
  -- 🎉 no goals
#align list.map_permutations List.map_permutations

theorem map_permutations' (f : α → β) (ts : List α) :
    map (map f) (permutations' ts) = permutations' (map f ts) := by
  induction' ts with t ts ih <;> [rfl; simp [← ih, map_bind, ← map_map_permutations'Aux, bind_map]]
  -- 🎉 no goals
#align list.map_permutations' List.map_permutations'

theorem permutationsAux_append (is is' ts : List α) :
    permutationsAux (is ++ ts) is' =
      (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++ is') := by
  induction' is with t is ih generalizing is'; · simp
  -- ⊢ permutationsAux ([] ++ ts) is' = map (fun x => x ++ ts) (permutationsAux []  …
                                                 -- 🎉 no goals
  simp only [foldr_permutationsAux2, ih, bind_map, cons_append, permutationsAux_cons, map_append,
    reverse_cons, append_assoc, singleton_append]
  congr 2
  -- ⊢ (fun y => (permutationsAux2 t (is ++ ts) [] y id).snd) = fun a => map (fun x …
  funext _
  -- ⊢ (permutationsAux2 t (is ++ ts) [] x✝ id).snd = map (fun x => x ++ ts) (permu …
  rw [map_permutationsAux2]
  -- ⊢ (permutationsAux2 t (is ++ ts) [] x✝ id).snd = (permutationsAux2 t is [] x✝  …
  simp (config := { singlePass := true }) only [← permutationsAux2_comp_append]
  -- ⊢ (permutationsAux2 t [] [] x✝ fun x => id (x ++ (is ++ ts))).snd = (permutati …
  simp only [id, append_assoc]
  -- 🎉 no goals
#align list.permutations_aux_append List.permutationsAux_append

theorem permutations_append (is ts : List α) :
    permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reverse := by
  simp [permutations, permutationsAux_append]
  -- 🎉 no goals
#align list.permutations_append List.permutations_append

end List
