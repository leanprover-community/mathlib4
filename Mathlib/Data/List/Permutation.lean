/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Duplicate
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Induction
import Batteries.Data.List.Perm
import Mathlib.Data.List.Perm.Basic

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
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat Function

variable {α β : Type*}

namespace List

theorem permutationsAux2_fst (t : α) (ts : List α) (r : List β) :
    ∀ (ys : List α) (f : List α → β), (permutationsAux2 t ts r ys f).1 = ys ++ ts
  | [], _ => rfl
  | y :: ys, f => by simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

@[simp]
theorem permutationsAux2_snd_nil (t : α) (ts : List α) (r : List β) (f : List α → β) :
    (permutationsAux2 t ts r [] f).2 = r :=
  rfl

@[simp]
theorem permutationsAux2_snd_cons (t : α) (ts : List α) (r : List β) (y : α) (ys : List α)
    (f : List α → β) :
    (permutationsAux2 t ts r (y :: ys) f).2 =
      f (t :: y :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => f (y :: x)).2 := by
  simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

/-- The `r` argument to `permutationsAux2` is the same as appending. -/
theorem permutationsAux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f <;> simp [*]

/-- The `ts` argument to `permutationsAux2` can be folded into the `f` argument. -/
theorem permutationsAux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : List α → β) :
    ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutationsAux2 t ts r ys f).2 := by
  induction' ys with ys_hd _ ys_ih generalizing f
  · simp
  · simp [ys_ih fun xs => f (ys_hd :: xs)]

theorem map_permutationsAux2' {α' β'} (g : α → α') (g' : β → β') (t : α) (ts ys : List α)
    (r : List β) (f : List α → β) (f' : List α' → β') (H : ∀ a, g' (f a) = f' (map g a)) :
    map g' (permutationsAux2 t ts r ys f).2 =
      (permutationsAux2 (g t) (map g ts) (map g' r) (map g ys) f').2 := by
  induction' ys with ys_hd _ ys_ih generalizing f f'
  · simp
  · simp only [map, permutationsAux2_snd_cons, cons_append, cons.injEq]
    rw [ys_ih]
    · refine ⟨?_, rfl⟩
      simp only [← map_cons, ← map_append]; apply H
    · intro a; apply H

/-- The `f` argument to `permutationsAux2` when `r = []` can be eliminated. -/
theorem map_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2 := by
  rw [map_permutationsAux2' id, map_id, map_id]
  · rfl
  simp

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

theorem map_map_permutationsAux2 {α'} (g : α → α') (t : α) (ts ys : List α) :
    map (map g) (permutationsAux2 t ts [] ys id).2 =
      (permutationsAux2 (g t) (map g ts) [] (map g ys) id).2 :=
  map_permutationsAux2' _ _ _ _ _ _ _ _ fun _ => rfl

theorem map_map_permutations'Aux (f : α → β) (t : α) (ts : List α) :
    map (map f) (permutations'Aux t ts) = permutations'Aux (f t) (map f ts) := by
  induction' ts with a ts ih
  · rfl
  · simp only [permutations'Aux, map_cons, map_map, ← ih, Function.comp_def]

theorem permutations'Aux_eq_permutationsAux2 (t : α) (ts : List α) :
    permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2 := by
  induction' ts with a ts ih; · rfl
  simp only [permutations'Aux, ih, cons_append, permutationsAux2_snd_cons, append_nil, id_eq,
    cons.injEq, true_and]
  simp +singlePass only [← permutationsAux2_append]
  simp [map_permutationsAux2]

theorem mem_permutationsAux2 {t : α} {ts : List α} {ys : List α} {l l' : List α} :
    l' ∈ (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts := by
  induction' ys with y ys ih generalizing l
  · simp +contextual
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

theorem mem_permutationsAux2' {t : α} {ts : List α} {ys : List α} {l : List α} :
    l ∈ (permutationsAux2 t ts [] ys id).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts := by
  rw [show @id (List α) = ([] ++ ·) by funext _; rfl]; apply mem_permutationsAux2

theorem length_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    length (permutationsAux2 t ts [] ys f).2 = length ys := by
  induction ys generalizing f <;> simp [*]

theorem foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    foldr (fun y r => (permutationsAux2 t ts r y id).2) r L =
      (L.flatMap fun y => (permutationsAux2 t ts [] y id).2) ++ r := by
  induction' L with l L ih
  · rfl
  · simp_rw [foldr_cons, ih, flatMap_cons, append_assoc, permutationsAux2_append]

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
  simp only [mem_permutationsAux2', ← this, or_comm, and_left_comm, mem_append, mem_flatMap,
    append_assoc, cons_append]

theorem length_foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) =
      (map length L).sum + length r := by
  simp [foldr_permutationsAux2, length_permutationsAux2, length_flatMap]

theorem length_foldr_permutationsAux2' (t : α) (ts : List α) (r L : List (List α)) (n)
    (H : ∀ l ∈ L, length l = n) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) = n * length L + length r := by
  rw [length_foldr_permutationsAux2, (_ : (map length L).sum = n * length L)]
  induction' L with l L ih
  · simp
  have sum_map : (map length L).sum = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
  have length_l : length l = n := H _ mem_cons_self
  simp [sum_map, length_l, Nat.add_comm, mul_succ]

@[simp]
theorem permutationsAux_nil (is : List α) : permutationsAux [] is = [] := by
  rw [permutationsAux, permutationsAux.rec]

@[simp]
theorem permutationsAux_cons (t : α) (ts is : List α) :
    permutationsAux (t :: ts) is =
      foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t :: is))
        (permutations is) := by
  rw [permutationsAux, permutationsAux.rec]; rfl

@[simp]
theorem permutations_nil : permutations ([] : List α) = [[]] := by
  rw [permutations, permutationsAux_nil]

theorem map_permutationsAux (f : α → β) :
    ∀ ts is :
    List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (map f is) := by
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2; rw [map] at IH2
  simp only [foldr_permutationsAux2, map_append, map, map_map_permutationsAux2, permutations,
    flatMap_map, IH1, append_assoc, permutationsAux_cons, flatMap_cons, ← IH2, map_flatMap]

theorem map_permutations (f : α → β) (ts : List α) :
    map (map f) (permutations ts) = permutations (map f ts) := by
  rw [permutations, permutations, map, map_permutationsAux, map]

theorem map_permutations' (f : α → β) (ts : List α) :
    map (map f) (permutations' ts) = permutations' (map f ts) := by
  induction' ts with t ts ih <;>
    [rfl; simp [← ih, map_flatMap, ← map_map_permutations'Aux, flatMap_map]]

theorem permutationsAux_append (is is' ts : List α) :
    permutationsAux (is ++ ts) is' =
      (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++ is') := by
  induction' is with t is ih generalizing is'; · simp
  simp only [foldr_permutationsAux2, ih, map_flatMap, cons_append, permutationsAux_cons, map_append,
    reverse_cons, append_assoc]
  congr 2
  funext _
  rw [map_permutationsAux2]
  simp +singlePass only [← permutationsAux2_comp_append]
  simp only [id, append_assoc]

theorem permutations_append (is ts : List α) :
    permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reverse := by
  simp [permutations, permutationsAux_append]

theorem perm_of_mem_permutationsAux :
    ∀ {ts is l : List α}, l ∈ permutationsAux ts is → l ~ ts ++ is := by
  show ∀ (ts is l : List α), l ∈ permutationsAux ts is → l ~ ts ++ is
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2 m
  rw [permutationsAux_cons, permutations, mem_foldr_permutationsAux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, rfl⟩)
  · exact (IH1 _ m).trans perm_middle
  · have p : l₁ ++ l₂ ~ is := by
      simp only [mem_cons] at m
      rcases m with e | m
      · simp [e]
      exact is.append_nil ▸ IH2 _ m
    exact ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _)

theorem perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
  (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutationsAux m

theorem length_permutationsAux :
    ∀ ts is : List α, length (permutationsAux ts is) + is.length ! = (length ts + length is)! := by
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2
  have IH2 : length (permutationsAux is nil) + 1 = is.length ! := by simpa using IH2
  simp only [length, factorial, Nat.mul_comm, add_eq] at IH1
  rw [permutationsAux_cons,
    length_foldr_permutationsAux2' _ _ _ _ _ fun l m => (perm_of_mem_permutations m).length_eq,
    permutations, length, length, IH2, Nat.succ_add, Nat.factorial_succ, Nat.mul_comm (_ + 1),
    ← Nat.succ_eq_add_one, ← IH1, Nat.add_comm (_ * _), Nat.add_assoc, Nat.mul_succ, Nat.mul_comm]

theorem length_permutations (l : List α) : length (permutations l) = (length l)! :=
  length_permutationsAux l []

theorem mem_permutations_of_perm_lemma {is l : List α}
    (H : l ~ [] ++ is → (∃ (ts' : _) (_ : ts' ~ []), l = ts' ++ is) ∨ l ∈ permutationsAux is []) :
    l ~ is → l ∈ permutations is := by simpa [permutations, perm_nil] using H

theorem mem_permutationsAux_of_perm :
    ∀ {ts is l : List α},
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is := by
  show ∀ (ts is l : List α),
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2 l p
  rw [permutationsAux_cons, mem_foldr_permutationsAux2]
  rcases IH1 _ (p.trans perm_middle) with (⟨is', p', e⟩ | m)
  · clear p
    subst e
    rcases append_of_mem (p'.symm.subset mem_cons_self) with ⟨l₁, l₂, e⟩
    subst is'
    have p := (perm_middle.symm.trans p').cons_inv
    rcases l₂ with - | ⟨a, l₂'⟩
    · exact Or.inl ⟨l₁, by simpa using p⟩
    · exact Or.inr (Or.inr ⟨l₁, a :: l₂', mem_permutations_of_perm_lemma (IH2 _) p, by simp⟩)
  · exact Or.inr (Or.inl m)

@[simp]
theorem mem_permutations {s t : List α} : s ∈ permutations t ↔ s ~ t :=
  ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutationsAux_of_perm⟩

-- Porting note: temporary theorem to solve diamond issue
private theorem DecEq_eq [DecidableEq α] :
    List.instBEq = @instBEqOfDecidableEq (List α) instDecidableEqList :=
  congr_arg BEq.mk <| by
    funext l₁ l₂
    change (l₁ == l₂) = _
    rw [Bool.eq_iff_iff, @beq_iff_eq _ (_), decide_eq_true_iff]

theorem perm_permutations'Aux_comm (a b : α) (l : List α) :
    (permutations'Aux a l).flatMap (permutations'Aux b) ~
      (permutations'Aux b l).flatMap (permutations'Aux a) := by
  induction' l with c l ih
  · exact Perm.swap [a, b] [b, a] []
  simp only [permutations'Aux, flatMap_cons, map_cons, map_map, cons_append]
  apply Perm.swap'
  have :
    ∀ a b,
      (map (cons c) (permutations'Aux a l)).flatMap (permutations'Aux b) ~
        map (cons b ∘ cons c) (permutations'Aux a l) ++
          map (cons c) ((permutations'Aux a l).flatMap (permutations'Aux b)) := by
    intros a' b'
    simp only [flatMap_map, permutations'Aux]
    change (permutations'Aux _ l).flatMap (fun a => ([b' :: c :: a] ++
      map (cons c) (permutations'Aux _ a))) ~ _
    refine (flatMap_append_perm _ (fun x => [b' :: c :: x]) _).symm.trans ?_
    rw [← map_eq_flatMap, ← map_flatMap]
    exact Perm.refl _
  refine (((this _ _).append_left _).trans ?_).trans ((this _ _).append_left _).symm
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append (ih.map _)

theorem Perm.permutations' {s t : List α} (p : s ~ t) : permutations' s ~ permutations' t := by
  induction p with
  | nil => simp
  | cons _ _ IH => exact IH.flatMap_right _
  | swap =>
    dsimp
    rw [flatMap_assoc, flatMap_assoc]
    apply Perm.flatMap_left
    intro l' _
    apply perm_permutations'Aux_comm
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

theorem permutations_perm_permutations' (ts : List α) : ts.permutations ~ ts.permutations' := by
  obtain ⟨n, h⟩ : ∃ n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction' n with n IH generalizing ts; · cases h
  refine List.reverseRecOn ts (fun _ => ?_) (fun ts t _ h => ?_) h; · simp [permutations]
  rw [← concat_eq_append, length_concat, Nat.succ_lt_succ_iff] at h
  have IH₂ := (IH ts.reverse (by rwa [length_reverse])).trans (reverse_perm _).permutations'
  simp only [permutations_append, foldr_permutationsAux2, permutationsAux_nil,
    permutationsAux_cons, append_nil]
  refine
    (perm_append_comm.trans ((IH₂.flatMap_right _).append ((IH _ h).map _))).trans
      (Perm.trans ?_ perm_append_comm.permutations')
  rw [map_eq_flatMap, singleton_append, permutations']
  refine (flatMap_append_perm _ _ _).trans ?_
  refine Perm.of_eq ?_
  congr
  funext _
  rw [permutations'Aux_eq_permutationsAux2, permutationsAux2_append]

@[simp]
theorem mem_permutations' {s t : List α} : s ∈ permutations' t ↔ s ~ t :=
  (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations

theorem Perm.permutations {s t : List α} (h : s ~ t) : permutations s ~ permutations t :=
  (permutations_perm_permutations' _).trans <|
    h.permutations'.trans (permutations_perm_permutations' _).symm

@[simp]
theorem perm_permutations_iff {s t : List α} : permutations s ~ permutations t ↔ s ~ t :=
  ⟨fun h => mem_permutations.1 <| h.mem_iff.1 <| mem_permutations.2 (Perm.refl _),
    Perm.permutations⟩

@[simp]
theorem perm_permutations'_iff {s t : List α} : permutations' s ~ permutations' t ↔ s ~ t :=
  ⟨fun h => mem_permutations'.1 <| h.mem_iff.1 <| mem_permutations'.2 (Perm.refl _),
    Perm.permutations'⟩

theorem getElem_permutations'Aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s)[n] = s.insertIdx n x := by
  induction' s with y s IH generalizing n
  · simp only [permutations'Aux, length, Nat.zero_add, lt_one_iff] at hn
    simp [hn]
  · cases n
    · simp
    · simpa [get] using IH _ _

theorem get_permutations'Aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s).get ⟨n, hn⟩ = s.insertIdx n x := by
  simp [getElem_permutations'Aux]

theorem count_permutations'Aux_self [DecidableEq α] (l : List α) (x : α) :
    count (x :: l) (permutations'Aux x l) = length (takeWhile (x = ·) l) + 1 := by
  induction' l with y l IH generalizing x
  · simp [takeWhile, count]
  · rw [permutations'Aux, count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [takeWhile, Nat.succ_inj, DecEq_eq] using IH _
    · rw [takeWhile]
      simp only [mem_map, cons.injEq, Ne.symm hx, false_and, and_false, exists_false,
        not_false_iff, count_eq_zero_of_not_mem, Nat.zero_add, hx, decide_false, length_nil]

@[simp]
theorem length_permutations'Aux (s : List α) (x : α) :
    length (permutations'Aux x s) = length s + 1 := by
  induction' s with y s IH
  · simp
  · simpa using IH

theorem injective_permutations'Aux (x : α) : Function.Injective (permutations'Aux x) := by
  intro s t h
  apply insertIdx_injective s.length x
  dsimp
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← get_permutations'Aux s x s.length (by simp),
    ← get_permutations'Aux t x s.length (by simp [hl])]
  simp only [get_eq_getElem, h, hl]

theorem nodup_permutations'Aux_of_notMem (s : List α) (x : α) (hx : x ∉ s) :
    Nodup (permutations'Aux x s) := by
  induction' s with y s IH
  · simp
  · simp only [not_or, mem_cons] at hx
    simp only [permutations'Aux, nodup_cons, mem_map, cons.injEq, exists_eq_right_right, not_and]
    refine ⟨fun _ => Ne.symm hx.left, ?_⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp

@[deprecated (since := "2025-05-23")]
alias nodup_permutations'Aux_of_not_mem := nodup_permutations'Aux_of_notMem

theorem nodup_permutations'Aux_iff {s : List α} {x : α} : Nodup (permutations'Aux x s) ↔ x ∉ s := by
  refine ⟨fun h H ↦ ?_, nodup_permutations'Aux_of_notMem _ _⟩
  obtain ⟨⟨k, hk⟩, hk'⟩ := get_of_mem H
  rw [nodup_iff_injective_get] at h
  apply k.succ_ne_self.symm
  have kl : k < (permutations'Aux x s).length := by simpa [Nat.lt_succ_iff] using hk.le
  have k1l : k + 1 < (permutations'Aux x s).length := by simpa using hk
  rw [← @Fin.mk.inj_iff _ _ _ kl k1l]; apply h
  rw [get_permutations'Aux, get_permutations'Aux]
  have hl : length (s.insertIdx k x) = length (s.insertIdx (k + 1) x) := by
    rw [length_insertIdx_of_le_length hk.le, length_insertIdx_of_le_length (Nat.succ_le_of_lt hk)]
  exact ext_get hl fun n hn hn' => by grind

theorem nodup_permutations (s : List α) (hs : Nodup s) : Nodup s.permutations := by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction hs with
  | nil => simp
  | @cons x l h h' IH =>
    rw [permutations']
    rw [nodup_flatMap]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'Aux_iff, hy.mem_iff]
      exact fun H => h x H rfl
    · refine IH.pairwise_of_forall_ne fun as ha bs hb H => ?_
      rw [Function.onFun, disjoint_iff_ne]
      rintro a ha' b hb' rfl
      obtain ⟨⟨n, hn⟩, hn'⟩ := get_of_mem ha'
      obtain ⟨⟨m, hm⟩, hm'⟩ := get_of_mem hb'
      rw [mem_permutations'] at ha hb
      have hl : as.length = bs.length := (ha.trans hb.symm).length_eq
      simp only [Nat.lt_succ_iff, length_permutations'Aux] at hn hm
      rw [get_permutations'Aux] at hn' hm'
      have hx : (as.insertIdx n x)[m]'(by
          rwa [length_insertIdx_of_le_length hn, Nat.lt_succ_iff, hl]) = x := by
        simp [hn', ← hm']
      have hx' : (bs.insertIdx m x)[n]'(by
          rwa [length_insertIdx_of_le_length hm, Nat.lt_succ_iff, ← hl]) = x := by
        simp [hm', ← hn']
      rcases lt_trichotomy n m with (ht | ht | ht)
      · suffices x ∈ bs by exact h x (hb.subset this) rfl
        rw [← hx', getElem_insertIdx_of_lt ht]
        exact getElem_mem _
      · simp only [ht] at hm' hn'
        rw [← hm'] at hn'
        exact H (insertIdx_injective _ _ hn')
      · suffices x ∈ as by exact h x (ha.subset this) rfl
        rw [← hx, getElem_insertIdx_of_lt ht]
        exact getElem_mem _

lemma permutations_take_two (x y : α) (s : List α) :
    (x :: y :: s).permutations.take 2 = [x :: y :: s, y :: x :: s] := by
  induction s <;> simp [permutations]

@[simp]
theorem nodup_permutations_iff {s : List α} : Nodup s.permutations ↔ Nodup s := by
  refine ⟨?_, nodup_permutations s⟩
  contrapose
  rw [← exists_duplicate_iff_not_nodup]
  intro ⟨x, hs⟩
  rw [duplicate_iff_sublist] at hs
  obtain ⟨l, ht⟩ := List.Sublist.exists_perm_append hs
  rw [List.Perm.nodup_iff (List.Perm.permutations ht), ← exists_duplicate_iff_not_nodup]
  use x :: x :: l
  rw [List.duplicate_iff_sublist, ← permutations_take_two]
  exact take_sublist 2 _

-- TODO: `count s s.permutations = (zipWith count s s.tails).prod`

end List
