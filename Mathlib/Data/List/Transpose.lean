/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Data.List.Zip
import Mathlib.Order.MinMax

/--
Truncating transpose, a transpose that truncates all the lists to the same length, e.g.
`[[1, 2, 3], [4, 5], [6, 7, 8, 9], [10, 11]].ttranspose = [[1, 4, 6, 10], [2, 5, 7, 11]]`.
-/
def List.ttranspose {α : Type*} : List (List α) → List (List α)
  | [] => []
  | [a] => a.map ([·])
  | a :: b => zipWith cons a (ttranspose b)

@[simp]
lemma List.ttranspose_nil {α : Type*} : ([] : List (List α)).ttranspose = [] := rfl

@[simp]
lemma List.ttranspose_single {α : Type*} (l : List α) : [l].ttranspose = l.map ([·]) := rfl

theorem List.length_of_mem_ttranspose {α : Type*} (l : List (List α)) :
    ∀ v ∈ l.ttranspose, v.length = l.length := by
  induction l
  · simp
  case cons head tail tail_ih =>
  cases tail
  · simp
  simp only [length_cons, ttranspose] at tail_ih ⊢
  intro v hv
  obtain ⟨_, _, v', hv', rfl⟩ := exists_mem_mem_of_mem_zipWith _ _ _ _ hv
  simp only [length_cons, Nat.add_left_inj]
  exact tail_ih _ hv'

theorem List.length_ttranspose {α : Type*} (l : List (List α)) :
    l.ttranspose.length = (l.map List.length).minimum?.getD 0 := by
  induction l
  · simp
  case cons head tail tail_ih =>
  cases tail
  · simp [List.minimum?_cons]
  simp only [ttranspose, length_zipWith, tail_ih, map_cons, minimum?_cons, Option.getD_some,
    foldl_cons, foldl_assoc]

theorem List.forall_ttranspose_length_le {α : Type*} (l : List (List α)) :
    ∀ v ∈ l, l.ttranspose.length ≤ v.length := by
  rw [List.length_ttranspose]
  intro v hv
  cases hl : (l.map length).minimum?
  · simp
  simp only [Option.getD_some]
  by_contra! nh
  apply Nat.add_one_le_of_lt at nh
  rw [List.le_minimum?_iff (fun _ _ _ ↦ Nat.le_min) hl] at nh
  specialize nh v.length (by simp only [mem_map]; use v, hv)
  omega

theorem List.ttranspose_getElem {α : Type*} (l : List (List α)) (i : ℕ)
    (hi : i < l.ttranspose.length) :
    l.ttranspose[i] = l.pmap (·[i]'·)
      (fun a ha ↦ hi.trans_le (forall_ttranspose_length_le l a ha)) := by
  induction l
  · simp at hi
  case cons head tail tail_ih =>
  cases tail
  · simp
  case cons head tail =>
  simp only [ttranspose, getElem_zipWith]
  rw [tail_ih]
  simp

theorem List.ttranspose_pmap_getElem {α : Type*} (l : List (List α)) (i : ℕ)
    (hi : i < l.length) (hl : ∀ a ∈ l, l[i].length ≤ a.length) :
    l.ttranspose.pmap (·[i]'·) (fun a ha ↦ List.length_of_mem_ttranspose l a ha ▸ hi) = l[i] := by
  induction l generalizing i
  · simp at hi
  case cons head tail tail_ih =>
  cases tail
  · simp [pmap_map]
  case cons head2 tail =>
    cases i
    · simp only [ttranspose, getElem_cons_zero]
      clear tail_ih
      generalize_proofs hp
      have : head.length ≤ (head2 :: tail).ttranspose.length := by
        simp only [length_ttranspose, map_cons, minimum?_cons, Option.getD_some]
        apply (List.le_minimum?_iff (fun _ _ _ ↦ Nat.le_min) (by rw [← minimum?_cons]) _).mpr
        simpa only [mem_cons, mem_map, forall_eq_or_imp, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, getElem_cons_zero, le_refl, true_and] using hl
      clear hl
      generalize (head2 :: tail).ttranspose = ml at hp this
      induction head generalizing ml
      · simp only [pmap]
      case cons head3 tail3 ih =>
        simp only [length_cons] at this
        obtain ⟨mh, mt, hp2⟩ := exists_cons_of_ne_nil (fun nh : ml = [] ↦ by simp [nh] at this)
        simp only [hp2, zipWith_cons_cons, pmap, getElem_cons_zero, cons.injEq, true_and]
        apply ih
        · simp only [length_cons, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]
        · simpa only [hp2, length_cons, Nat.add_le_add_iff_right] using this
    · simp only [ttranspose, getElem_cons_succ]
      rw [← tail_ih]
      · generalize_proofs hp hp2
        have : (head2 :: tail).ttranspose.length ≤ head.length := by
          have : (map length (head2 :: tail)).minimum? =
              some (foldl min head2.length (map length tail)) := by
            simp only [map_cons, minimum?_cons]
          rw [length_ttranspose, this, Option.getD_some]
          simp only [List.minimum?_eq_some_iff Nat.le_refl min_choice (by simp),
            mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at this
          exact (this.2 _ (getElem_mem ..)).trans (getElem_cons_succ .. ▸ hl head (by simp))
        generalize (head2 :: tail).ttranspose = ml at hp hp2 this
        clear hl
        induction ml generalizing head
        · simp only [zipWith_nil_right, pmap]
        case cons head3 tail3 ih =>
          simp only [pmap]
          simp only [length_cons] at this
          obtain ⟨hh, ht, hp2⟩ := exists_cons_of_ne_nil (fun nh : head = [] ↦ by simp [nh] at this)
          simp only [hp2, zipWith_cons_cons, pmap, getElem_cons_succ, cons.injEq, true_and]
          apply ih
          · simpa only [length_cons] using hi
          · simpa only [hp2, length_cons, Nat.add_le_add_iff_right] using this
      · simp only [mem_cons, getElem_cons_succ, forall_eq_or_imp] at hl
        simpa only [mem_cons, forall_eq_or_imp] using hl.2
