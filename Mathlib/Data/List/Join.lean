/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro, Martin Dvorak
-/
import Mathlib.Data.List.BigOperators.Basic

#align_import data.list.join from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"

/-!
# Join of a list of lists

This file proves basic properties of `List.join`, which concatenates a list of lists. It is defined
in `Init.Data.List.Basic`.
-/


variable {α β : Type*}

namespace List

attribute [simp] join

-- Porting note: simp can prove this
-- @[simp]
theorem join_singleton (l : List α) : [l].join = l := by rw [join, join, append_nil]
                                                         -- 🎉 no goals
#align list.join_singleton List.join_singleton

@[simp]
theorem join_eq_nil : ∀ {L : List (List α)}, join L = [] ↔ ∀ l ∈ L, l = []
  | [] => iff_of_true rfl (forall_mem_nil _)
  | l :: L => by simp only [join, append_eq_nil, join_eq_nil, forall_mem_cons]
                 -- 🎉 no goals
#align list.join_eq_nil List.join_eq_nil

@[simp]
theorem join_append (L₁ L₂ : List (List α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ := by
  induction L₁
  -- ⊢ join ([] ++ L₂) = join [] ++ join L₂
  · rfl
    -- 🎉 no goals
  · simp [*]
    -- 🎉 no goals
#align list.join_append List.join_append

theorem join_concat (L : List (List α)) (l : List α) : join (L.concat l) = join L ++ l := by simp
                                                                                             -- 🎉 no goals
#align list.join_concat List.join_concat

-- Porting note: `ff/tt` should be translated to `false/true`.
-- Porting note: `List.filter` now takes a `Bool` not a `Prop`.
--     Should the correct spelling now be `== false` instead?
@[simp]
theorem join_filter_isEmpty_eq_false [DecidablePred fun l : List α => l.isEmpty = false] :
    ∀ {L : List (List α)}, join (L.filter fun l => l.isEmpty = false) = L.join
  | [] => rfl
  | [] :: L => by
      simp [join_filter_isEmpty_eq_false (L := L), isEmpty_iff_eq_nil]
      -- 🎉 no goals
  | (a :: l) :: L => by
      have cons_not_empty : isEmpty (a :: l) = false := rfl
      -- ⊢ join (filter (fun l => decide (isEmpty l = false)) ((a :: l) :: L)) = join ( …
      simp [join_filter_isEmpty_eq_false (L := L), cons_not_empty]
      -- 🎉 no goals
#align list.join_filter_empty_eq_ff List.join_filter_isEmpty_eq_false

@[simp]
theorem join_filter_ne_nil [DecidablePred fun l : List α => l ≠ []] {L : List (List α)} :
    join (L.filter fun l => l ≠ []) = L.join := by
  simp [join_filter_isEmpty_eq_false, ← isEmpty_iff_eq_nil]
  -- 🎉 no goals
#align list.join_filter_ne_nil List.join_filter_ne_nil

theorem join_join (l : List (List (List α))) : l.join.join = (l.map join).join := by
  induction l <;> simp [*]
  -- ⊢ join (join []) = join (map join [])
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.join_join List.join_join

@[simp]
theorem length_join (L : List (List α)) : length (join L) = sum (map length L) := by
  induction L <;> [rfl; simp only [*, join, map, sum_cons, length_append]]
  -- 🎉 no goals
#align list.length_join List.length_join

@[simp]
theorem length_bind (l : List α) (f : α → List β) :
    length (List.bind l f) = sum (map (length ∘ f) l) := by rw [List.bind, length_join, map_map]
                                                            -- 🎉 no goals
#align list.length_bind List.length_bind

@[simp]
theorem bind_eq_nil {l : List α} {f : α → List β} : List.bind l f = [] ↔ ∀ x ∈ l, f x = [] :=
  join_eq_nil.trans <| by
    simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    -- 🎉 no goals
#align list.bind_eq_nil List.bind_eq_nil

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
theorem take_sum_join (L : List (List α)) (i : ℕ) :
    L.join.take ((L.map length).take i).sum = (L.take i).join := by
  induction L generalizing i
  -- ⊢ take (sum (take i (map length []))) (join []) = join (take i [])
  · simp
    -- 🎉 no goals
  · cases i <;> simp [take_append, *]
    -- ⊢ take (sum (take Nat.zero (map length (head✝ :: tail✝)))) (join (head✝ :: tai …
                -- 🎉 no goals
                -- 🎉 no goals
#align list.take_sum_join List.take_sum_join

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
theorem drop_sum_join (L : List (List α)) (i : ℕ) :
    L.join.drop ((L.map length).take i).sum = (L.drop i).join := by
  induction L generalizing i
  -- ⊢ drop (sum (take i (map length []))) (join []) = join (drop i [])
  · simp
    -- 🎉 no goals
  · cases i <;> simp [drop_append, *]
    -- ⊢ drop (sum (take Nat.zero (map length (head✝ :: tail✝)))) (join (head✝ :: tai …
                -- 🎉 no goals
                -- 🎉 no goals
#align list.drop_sum_join List.drop_sum_join

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_get (L : List α) (i : Fin L.length) :
    (L.take (i + 1)).drop i = [get L i] := by
  induction' L with head tail ih
  -- ⊢ drop (↑i) (take (↑i + 1) []) = [get [] i]
  · exact (Nat.not_succ_le_zero i i.isLt).elim
    -- 🎉 no goals
  rcases i with ⟨_ | i, hi⟩
  -- ⊢ drop (↑{ val := Nat.zero, isLt := hi }) (take (↑{ val := Nat.zero, isLt := h …
  · simp
    -- 🎉 no goals
  · simpa using ih ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    -- 🎉 no goals

set_option linter.deprecated false in
/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
@[deprecated drop_take_succ_eq_cons_get]
theorem drop_take_succ_eq_cons_nthLe (L : List α) {i : ℕ} (hi : i < L.length) :
    (L.take (i + 1)).drop i = [nthLe L i hi] := by
  induction' L with head tail generalizing i
  -- ⊢ drop i (take (i + 1) []) = [nthLe [] i hi]
  · simp only [length] at hi
    -- ⊢ drop i (take (i + 1) []) = [nthLe [] i hi]
    exact (Nat.not_succ_le_zero i hi).elim
    -- 🎉 no goals
  cases' i with i hi
  -- ⊢ drop Nat.zero (take (Nat.zero + 1) (head :: tail)) = [nthLe (head :: tail) N …
  · simp
    -- ⊢ head = nthLe (head :: tail) 0 hi
    rfl
    -- 🎉 no goals
  have : i < tail.length := by
    simp at hi
    exact Nat.lt_of_succ_lt_succ hi
  simp [*]
  -- ⊢ nthLe tail i (_ : i < length tail) = nthLe (head :: tail) (Nat.succ i) hi
  rfl
  -- 🎉 no goals
#align list.drop_take_succ_eq_cons_nth_le List.drop_take_succ_eq_cons_nthLe

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
theorem drop_take_succ_join_eq_get (L : List (List α)) (i : Fin L.length) :
    (L.join.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum =
      get L i := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take]
  simp only [this, length_map, take_sum_join, drop_sum_join, drop_take_succ_eq_cons_get,
    join, append_nil]

set_option linter.deprecated false in
/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
@[deprecated drop_take_succ_join_eq_get]
theorem drop_take_succ_join_eq_nthLe (L : List (List α)) {i : ℕ} (hi : i < L.length) :
    (L.join.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum =
      nthLe L i hi := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take]
  simp [take_sum_join, this, drop_sum_join, drop_take_succ_eq_cons_nthLe _ hi]
  -- 🎉 no goals
#align list.drop_take_succ_join_eq_nth_le List.drop_take_succ_join_eq_nthLe

set_option linter.deprecated false in
/-- Auxiliary lemma to control elements in a join. -/
@[deprecated]
theorem sum_take_map_length_lt1 (L : List (List α)) {i j : ℕ} (hi : i < L.length)
    (hj : j < (nthLe L i hi).length) :
    ((L.map length).take i).sum + j < ((L.map length).take (i + 1)).sum := by
  simp [hi, sum_take_succ, hj]
  -- 🎉 no goals
#align list.sum_take_map_length_lt1 List.sum_take_map_length_lt1

set_option linter.deprecated false in
/-- Auxiliary lemma to control elements in a join. -/
@[deprecated]
theorem sum_take_map_length_lt2 (L : List (List α)) {i j : ℕ} (hi : i < L.length)
    (hj : j < (nthLe L i hi).length) : ((L.map length).take i).sum + j < L.join.length := by
  convert lt_of_lt_of_le (sum_take_map_length_lt1 L hi hj) (monotone_sum_take _ hi)
  -- ⊢ length (join L) = (fun i => sum (take i (map length L))) (length L)
  have : L.length = (L.map length).length := by simp
  -- ⊢ length (join L) = (fun i => sum (take i (map length L))) (length L)
  simp [this, -length_map]
  -- 🎉 no goals
#align list.sum_take_map_length_lt2 List.sum_take_map_length_lt2

set_option linter.deprecated false in
/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
@[deprecated]
theorem nthLe_join (L : List (List α)) {i j : ℕ} (hi : i < L.length)
    (hj : j < (nthLe L i hi).length) :
    nthLe L.join (((L.map length).take i).sum + j) (sum_take_map_length_lt2 L hi hj) =
      nthLe (nthLe L i hi) j hj := by
  have := nthLe_take L.join (sum_take_map_length_lt2 L hi hj) (sum_take_map_length_lt1 L hi hj)
  -- ⊢ nthLe (join L) (sum (take i (map length L)) + j) (_ : sum (take i (map lengt …
  rw [this, nthLe_drop, nthLe_of_eq (drop_take_succ_join_eq_nthLe L hi)]
  -- 🎉 no goals
#align list.nth_le_join List.nthLe_join

/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq (L L' : List (List α)) :
    L = L' ↔ L.join = L'.join ∧ map length L = map length L' := by
  refine' ⟨fun H => by simp [H], _⟩
  -- ⊢ join L = join L' ∧ map length L = map length L' → L = L'
  rintro ⟨join_eq, length_eq⟩
  -- ⊢ L = L'
  apply ext_get
  -- ⊢ length L = length L'
  · have : length (map length L) = length (map length L') := by rw [length_eq]
    -- ⊢ length L = length L'
    simpa using this
    -- 🎉 no goals
  · intro n h₁ h₂
    -- ⊢ get L { val := n, isLt := h₁ } = get L' { val := n, isLt := h₂ }
    rw [← drop_take_succ_join_eq_get, ← drop_take_succ_join_eq_get, join_eq, length_eq]
    -- 🎉 no goals
#align list.eq_iff_join_eq List.eq_iff_join_eq

theorem join_drop_length_sub_one {L : List (List α)} (h : L ≠ []) :
    (L.drop (L.length - 1)).join = L.getLast h := by
  induction L using List.reverseRecOn
  -- ⊢ join (drop (length [] - 1) []) = getLast [] h
  · cases h rfl
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align list.join_drop_length_sub_one List.join_drop_length_sub_one

/-- We can rebracket `x ++ (l₁ ++ x) ++ (l₂ ++ x) ++ ... ++ (lₙ ++ x)` to
`(x ++ l₁) ++ (x ++ l₂) ++ ... ++ (x ++ lₙ) ++ x` where `L = [l₁, l₂, ..., lₙ]`. -/
theorem append_join_map_append (L : List (List α)) (x : List α) :
    x ++ (List.map (fun l => l ++ x) L).join = (List.map (fun l => x ++ l) L).join ++ x := by
  induction' L with _ _ ih
  -- ⊢ x ++ join (map (fun l => l ++ x) []) = join (map (fun l => x ++ l) []) ++ x
  · rw [map_nil, join, append_nil, map_nil, join, nil_append]
    -- 🎉 no goals
  · rw [map_cons, join, map_cons, join, append_assoc, ih, append_assoc, append_assoc]
    -- 🎉 no goals
#align list.append_join_map_append List.append_join_map_append

/-- Reversing a join is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_join (L : List (List α)) :
    L.join.reverse = (List.map List.reverse L).reverse.join := by
  induction' L with _ _ ih
  -- ⊢ reverse (join []) = join (reverse (map reverse []))
  · rfl
    -- 🎉 no goals
  · rw [join, reverse_append, ih, map_cons, reverse_cons', join_concat]
    -- 🎉 no goals
#align list.reverse_join List.reverse_join

/-- Joining a reverse is the same as reversing all parts and reversing the joined result. -/
theorem join_reverse (L : List (List α)) :
    L.reverse.join = (List.map List.reverse L).join.reverse := by
  simpa [reverse_reverse, map_reverse] using congr_arg List.reverse (reverse_join L.reverse)
  -- 🎉 no goals
#align list.join_reverse List.join_reverse

end List
